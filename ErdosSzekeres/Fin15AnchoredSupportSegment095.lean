module

public import ErdosSzekeres.Fin15AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 095. -/

theorem fin15Anchored_fiveFamily_mask09838 :
    (({1, 2, 3, 5, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 10, 13}, {3, 6, 9, 10, 13}, {3, 5, 9, 10, 13}, {3, 5, 6, 10, 13}, {3, 5, 6, 9, 13}, {3, 5, 6, 9, 10}, {2, 6, 9, 10, 13}, {2, 5, 9, 10, 13}, {2, 5, 6, 10, 13}, {2, 5, 6, 9, 13}, {2, 5, 6, 9, 10}, {2, 3, 9, 10, 13}, {2, 3, 6, 10, 13}, {2, 3, 6, 9, 13}, {2, 3, 6, 9, 10}, {2, 3, 5, 10, 13}, {2, 3, 5, 9, 13}, {2, 3, 5, 9, 10}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 10}, {2, 3, 5, 6, 9}, {1, 6, 9, 10, 13}, {1, 5, 9, 10, 13}, {1, 5, 6, 10, 13}, {1, 5, 6, 9, 13}, {1, 5, 6, 9, 10}, {1, 3, 9, 10, 13}, {1, 3, 6, 10, 13}, {1, 3, 6, 9, 13}, {1, 3, 6, 9, 10}, {1, 3, 5, 10, 13}, {1, 3, 5, 9, 13}, {1, 3, 5, 9, 10}, {1, 3, 5, 6, 13}, {1, 3, 5, 6, 10}, {1, 3, 5, 6, 9}, {1, 2, 9, 10, 13}, {1, 2, 6, 10, 13}, {1, 2, 6, 9, 13}, {1, 2, 6, 9, 10}, {1, 2, 5, 10, 13}, {1, 2, 5, 9, 13}, {1, 2, 5, 9, 10}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 10}, {1, 2, 5, 6, 9}, {1, 2, 3, 10, 13}, {1, 2, 3, 9, 13}, {1, 2, 3, 9, 10}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 10}, {1, 2, 3, 6, 9}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 9}, {1, 2, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09838 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 5, 6, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 9, 10, 13} ∨
        polygon = {3, 6, 9, 10, 13} ∨
        polygon = {3, 5, 9, 10, 13} ∨
        polygon = {3, 5, 6, 10, 13} ∨
        polygon = {3, 5, 6, 9, 13} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {2, 6, 9, 10, 13} ∨
        polygon = {2, 5, 9, 10, 13} ∨
        polygon = {2, 5, 6, 10, 13} ∨
        polygon = {2, 5, 6, 9, 13} ∨
        polygon = {2, 5, 6, 9, 10} ∨
        polygon = {2, 3, 9, 10, 13} ∨
        polygon = {2, 3, 6, 10, 13} ∨
        polygon = {2, 3, 6, 9, 13} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {2, 3, 5, 10, 13} ∨
        polygon = {2, 3, 5, 9, 13} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 5, 6, 13} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {1, 6, 9, 10, 13} ∨
        polygon = {1, 5, 9, 10, 13} ∨
        polygon = {1, 5, 6, 10, 13} ∨
        polygon = {1, 5, 6, 9, 13} ∨
        polygon = {1, 5, 6, 9, 10} ∨
        polygon = {1, 3, 9, 10, 13} ∨
        polygon = {1, 3, 6, 10, 13} ∨
        polygon = {1, 3, 6, 9, 13} ∨
        polygon = {1, 3, 6, 9, 10} ∨
        polygon = {1, 3, 5, 10, 13} ∨
        polygon = {1, 3, 5, 9, 13} ∨
        polygon = {1, 3, 5, 9, 10} ∨
        polygon = {1, 3, 5, 6, 13} ∨
        polygon = {1, 3, 5, 6, 10} ∨
        polygon = {1, 3, 5, 6, 9} ∨
        polygon = {1, 2, 9, 10, 13} ∨
        polygon = {1, 2, 6, 10, 13} ∨
        polygon = {1, 2, 6, 9, 13} ∨
        polygon = {1, 2, 6, 9, 10} ∨
        polygon = {1, 2, 5, 10, 13} ∨
        polygon = {1, 2, 5, 9, 13} ∨
        polygon = {1, 2, 5, 9, 10} ∨
        polygon = {1, 2, 5, 6, 13} ∨
        polygon = {1, 2, 5, 6, 10} ∨
        polygon = {1, 2, 5, 6, 9} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {1, 2, 3, 6, 9} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {1, 2, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 5, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09838] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask18030 :
    (({1, 2, 3, 5, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 10, 14}, {3, 6, 9, 10, 14}, {3, 5, 9, 10, 14}, {3, 5, 6, 10, 14}, {3, 5, 6, 9, 14}, {3, 5, 6, 9, 10}, {2, 6, 9, 10, 14}, {2, 5, 9, 10, 14}, {2, 5, 6, 10, 14}, {2, 5, 6, 9, 14}, {2, 5, 6, 9, 10}, {2, 3, 9, 10, 14}, {2, 3, 6, 10, 14}, {2, 3, 6, 9, 14}, {2, 3, 6, 9, 10}, {2, 3, 5, 10, 14}, {2, 3, 5, 9, 14}, {2, 3, 5, 9, 10}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 10}, {2, 3, 5, 6, 9}, {1, 6, 9, 10, 14}, {1, 5, 9, 10, 14}, {1, 5, 6, 10, 14}, {1, 5, 6, 9, 14}, {1, 5, 6, 9, 10}, {1, 3, 9, 10, 14}, {1, 3, 6, 10, 14}, {1, 3, 6, 9, 14}, {1, 3, 6, 9, 10}, {1, 3, 5, 10, 14}, {1, 3, 5, 9, 14}, {1, 3, 5, 9, 10}, {1, 3, 5, 6, 14}, {1, 3, 5, 6, 10}, {1, 3, 5, 6, 9}, {1, 2, 9, 10, 14}, {1, 2, 6, 10, 14}, {1, 2, 6, 9, 14}, {1, 2, 6, 9, 10}, {1, 2, 5, 10, 14}, {1, 2, 5, 9, 14}, {1, 2, 5, 9, 10}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 10}, {1, 2, 5, 6, 9}, {1, 2, 3, 10, 14}, {1, 2, 3, 9, 14}, {1, 2, 3, 9, 10}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 10}, {1, 2, 3, 6, 9}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 9}, {1, 2, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask18030 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 5, 6, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 9, 10, 14} ∨
        polygon = {3, 6, 9, 10, 14} ∨
        polygon = {3, 5, 9, 10, 14} ∨
        polygon = {3, 5, 6, 10, 14} ∨
        polygon = {3, 5, 6, 9, 14} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {2, 6, 9, 10, 14} ∨
        polygon = {2, 5, 9, 10, 14} ∨
        polygon = {2, 5, 6, 10, 14} ∨
        polygon = {2, 5, 6, 9, 14} ∨
        polygon = {2, 5, 6, 9, 10} ∨
        polygon = {2, 3, 9, 10, 14} ∨
        polygon = {2, 3, 6, 10, 14} ∨
        polygon = {2, 3, 6, 9, 14} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {2, 3, 5, 10, 14} ∨
        polygon = {2, 3, 5, 9, 14} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 5, 6, 14} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {1, 6, 9, 10, 14} ∨
        polygon = {1, 5, 9, 10, 14} ∨
        polygon = {1, 5, 6, 10, 14} ∨
        polygon = {1, 5, 6, 9, 14} ∨
        polygon = {1, 5, 6, 9, 10} ∨
        polygon = {1, 3, 9, 10, 14} ∨
        polygon = {1, 3, 6, 10, 14} ∨
        polygon = {1, 3, 6, 9, 14} ∨
        polygon = {1, 3, 6, 9, 10} ∨
        polygon = {1, 3, 5, 10, 14} ∨
        polygon = {1, 3, 5, 9, 14} ∨
        polygon = {1, 3, 5, 9, 10} ∨
        polygon = {1, 3, 5, 6, 14} ∨
        polygon = {1, 3, 5, 6, 10} ∨
        polygon = {1, 3, 5, 6, 9} ∨
        polygon = {1, 2, 9, 10, 14} ∨
        polygon = {1, 2, 6, 10, 14} ∨
        polygon = {1, 2, 6, 9, 14} ∨
        polygon = {1, 2, 6, 9, 10} ∨
        polygon = {1, 2, 5, 10, 14} ∨
        polygon = {1, 2, 5, 9, 14} ∨
        polygon = {1, 2, 5, 9, 10} ∨
        polygon = {1, 2, 5, 6, 14} ∨
        polygon = {1, 2, 5, 6, 10} ∨
        polygon = {1, 2, 5, 6, 9} ∨
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {1, 2, 3, 6, 9} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {1, 2, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 5, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask18030] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12910 :
    (({1, 2, 3, 5, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 12, 13}, {3, 6, 9, 12, 13}, {3, 5, 9, 12, 13}, {3, 5, 6, 12, 13}, {3, 5, 6, 9, 13}, {3, 5, 6, 9, 12}, {2, 6, 9, 12, 13}, {2, 5, 9, 12, 13}, {2, 5, 6, 12, 13}, {2, 5, 6, 9, 13}, {2, 5, 6, 9, 12}, {2, 3, 9, 12, 13}, {2, 3, 6, 12, 13}, {2, 3, 6, 9, 13}, {2, 3, 6, 9, 12}, {2, 3, 5, 12, 13}, {2, 3, 5, 9, 13}, {2, 3, 5, 9, 12}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 12}, {2, 3, 5, 6, 9}, {1, 6, 9, 12, 13}, {1, 5, 9, 12, 13}, {1, 5, 6, 12, 13}, {1, 5, 6, 9, 13}, {1, 5, 6, 9, 12}, {1, 3, 9, 12, 13}, {1, 3, 6, 12, 13}, {1, 3, 6, 9, 13}, {1, 3, 6, 9, 12}, {1, 3, 5, 12, 13}, {1, 3, 5, 9, 13}, {1, 3, 5, 9, 12}, {1, 3, 5, 6, 13}, {1, 3, 5, 6, 12}, {1, 3, 5, 6, 9}, {1, 2, 9, 12, 13}, {1, 2, 6, 12, 13}, {1, 2, 6, 9, 13}, {1, 2, 6, 9, 12}, {1, 2, 5, 12, 13}, {1, 2, 5, 9, 13}, {1, 2, 5, 9, 12}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 12}, {1, 2, 5, 6, 9}, {1, 2, 3, 12, 13}, {1, 2, 3, 9, 13}, {1, 2, 3, 9, 12}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 12}, {1, 2, 3, 6, 9}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 9}, {1, 2, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12910 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 5, 6, 9, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 9, 12, 13} ∨
        polygon = {3, 6, 9, 12, 13} ∨
        polygon = {3, 5, 9, 12, 13} ∨
        polygon = {3, 5, 6, 12, 13} ∨
        polygon = {3, 5, 6, 9, 13} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {2, 6, 9, 12, 13} ∨
        polygon = {2, 5, 9, 12, 13} ∨
        polygon = {2, 5, 6, 12, 13} ∨
        polygon = {2, 5, 6, 9, 13} ∨
        polygon = {2, 5, 6, 9, 12} ∨
        polygon = {2, 3, 9, 12, 13} ∨
        polygon = {2, 3, 6, 12, 13} ∨
        polygon = {2, 3, 6, 9, 13} ∨
        polygon = {2, 3, 6, 9, 12} ∨
        polygon = {2, 3, 5, 12, 13} ∨
        polygon = {2, 3, 5, 9, 13} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 5, 6, 13} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {1, 6, 9, 12, 13} ∨
        polygon = {1, 5, 9, 12, 13} ∨
        polygon = {1, 5, 6, 12, 13} ∨
        polygon = {1, 5, 6, 9, 13} ∨
        polygon = {1, 5, 6, 9, 12} ∨
        polygon = {1, 3, 9, 12, 13} ∨
        polygon = {1, 3, 6, 12, 13} ∨
        polygon = {1, 3, 6, 9, 13} ∨
        polygon = {1, 3, 6, 9, 12} ∨
        polygon = {1, 3, 5, 12, 13} ∨
        polygon = {1, 3, 5, 9, 13} ∨
        polygon = {1, 3, 5, 9, 12} ∨
        polygon = {1, 3, 5, 6, 13} ∨
        polygon = {1, 3, 5, 6, 12} ∨
        polygon = {1, 3, 5, 6, 9} ∨
        polygon = {1, 2, 9, 12, 13} ∨
        polygon = {1, 2, 6, 12, 13} ∨
        polygon = {1, 2, 6, 9, 13} ∨
        polygon = {1, 2, 6, 9, 12} ∨
        polygon = {1, 2, 5, 12, 13} ∨
        polygon = {1, 2, 5, 9, 13} ∨
        polygon = {1, 2, 5, 9, 12} ∨
        polygon = {1, 2, 5, 6, 13} ∨
        polygon = {1, 2, 5, 6, 12} ∨
        polygon = {1, 2, 5, 6, 9} ∨
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {1, 2, 3, 6, 9} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {1, 2, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 5, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12910] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21102 :
    (({1, 2, 3, 5, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 12, 14}, {3, 6, 9, 12, 14}, {3, 5, 9, 12, 14}, {3, 5, 6, 12, 14}, {3, 5, 6, 9, 14}, {3, 5, 6, 9, 12}, {2, 6, 9, 12, 14}, {2, 5, 9, 12, 14}, {2, 5, 6, 12, 14}, {2, 5, 6, 9, 14}, {2, 5, 6, 9, 12}, {2, 3, 9, 12, 14}, {2, 3, 6, 12, 14}, {2, 3, 6, 9, 14}, {2, 3, 6, 9, 12}, {2, 3, 5, 12, 14}, {2, 3, 5, 9, 14}, {2, 3, 5, 9, 12}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 12}, {2, 3, 5, 6, 9}, {1, 6, 9, 12, 14}, {1, 5, 9, 12, 14}, {1, 5, 6, 12, 14}, {1, 5, 6, 9, 14}, {1, 5, 6, 9, 12}, {1, 3, 9, 12, 14}, {1, 3, 6, 12, 14}, {1, 3, 6, 9, 14}, {1, 3, 6, 9, 12}, {1, 3, 5, 12, 14}, {1, 3, 5, 9, 14}, {1, 3, 5, 9, 12}, {1, 3, 5, 6, 14}, {1, 3, 5, 6, 12}, {1, 3, 5, 6, 9}, {1, 2, 9, 12, 14}, {1, 2, 6, 12, 14}, {1, 2, 6, 9, 14}, {1, 2, 6, 9, 12}, {1, 2, 5, 12, 14}, {1, 2, 5, 9, 14}, {1, 2, 5, 9, 12}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 12}, {1, 2, 5, 6, 9}, {1, 2, 3, 12, 14}, {1, 2, 3, 9, 14}, {1, 2, 3, 9, 12}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 12}, {1, 2, 3, 6, 9}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 9}, {1, 2, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21102 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 5, 6, 9, 12, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 9, 12, 14} ∨
        polygon = {3, 6, 9, 12, 14} ∨
        polygon = {3, 5, 9, 12, 14} ∨
        polygon = {3, 5, 6, 12, 14} ∨
        polygon = {3, 5, 6, 9, 14} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {2, 6, 9, 12, 14} ∨
        polygon = {2, 5, 9, 12, 14} ∨
        polygon = {2, 5, 6, 12, 14} ∨
        polygon = {2, 5, 6, 9, 14} ∨
        polygon = {2, 5, 6, 9, 12} ∨
        polygon = {2, 3, 9, 12, 14} ∨
        polygon = {2, 3, 6, 12, 14} ∨
        polygon = {2, 3, 6, 9, 14} ∨
        polygon = {2, 3, 6, 9, 12} ∨
        polygon = {2, 3, 5, 12, 14} ∨
        polygon = {2, 3, 5, 9, 14} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 5, 6, 14} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {1, 6, 9, 12, 14} ∨
        polygon = {1, 5, 9, 12, 14} ∨
        polygon = {1, 5, 6, 12, 14} ∨
        polygon = {1, 5, 6, 9, 14} ∨
        polygon = {1, 5, 6, 9, 12} ∨
        polygon = {1, 3, 9, 12, 14} ∨
        polygon = {1, 3, 6, 12, 14} ∨
        polygon = {1, 3, 6, 9, 14} ∨
        polygon = {1, 3, 6, 9, 12} ∨
        polygon = {1, 3, 5, 12, 14} ∨
        polygon = {1, 3, 5, 9, 14} ∨
        polygon = {1, 3, 5, 9, 12} ∨
        polygon = {1, 3, 5, 6, 14} ∨
        polygon = {1, 3, 5, 6, 12} ∨
        polygon = {1, 3, 5, 6, 9} ∨
        polygon = {1, 2, 9, 12, 14} ∨
        polygon = {1, 2, 6, 12, 14} ∨
        polygon = {1, 2, 6, 9, 14} ∨
        polygon = {1, 2, 6, 9, 12} ∨
        polygon = {1, 2, 5, 12, 14} ∨
        polygon = {1, 2, 5, 9, 14} ∨
        polygon = {1, 2, 5, 9, 12} ∨
        polygon = {1, 2, 5, 6, 14} ∨
        polygon = {1, 2, 5, 6, 12} ∨
        polygon = {1, 2, 5, 6, 9} ∨
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {1, 2, 3, 6, 9} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {1, 2, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 5, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21102] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25198 :
    (({1, 2, 3, 5, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 13, 14}, {3, 6, 9, 13, 14}, {3, 5, 9, 13, 14}, {3, 5, 6, 13, 14}, {3, 5, 6, 9, 14}, {3, 5, 6, 9, 13}, {2, 6, 9, 13, 14}, {2, 5, 9, 13, 14}, {2, 5, 6, 13, 14}, {2, 5, 6, 9, 14}, {2, 5, 6, 9, 13}, {2, 3, 9, 13, 14}, {2, 3, 6, 13, 14}, {2, 3, 6, 9, 14}, {2, 3, 6, 9, 13}, {2, 3, 5, 13, 14}, {2, 3, 5, 9, 14}, {2, 3, 5, 9, 13}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 9}, {1, 6, 9, 13, 14}, {1, 5, 9, 13, 14}, {1, 5, 6, 13, 14}, {1, 5, 6, 9, 14}, {1, 5, 6, 9, 13}, {1, 3, 9, 13, 14}, {1, 3, 6, 13, 14}, {1, 3, 6, 9, 14}, {1, 3, 6, 9, 13}, {1, 3, 5, 13, 14}, {1, 3, 5, 9, 14}, {1, 3, 5, 9, 13}, {1, 3, 5, 6, 14}, {1, 3, 5, 6, 13}, {1, 3, 5, 6, 9}, {1, 2, 9, 13, 14}, {1, 2, 6, 13, 14}, {1, 2, 6, 9, 14}, {1, 2, 6, 9, 13}, {1, 2, 5, 13, 14}, {1, 2, 5, 9, 14}, {1, 2, 5, 9, 13}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 9}, {1, 2, 3, 13, 14}, {1, 2, 3, 9, 14}, {1, 2, 3, 9, 13}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 9}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 9}, {1, 2, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25198 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 5, 6, 9, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 9, 13, 14} ∨
        polygon = {3, 6, 9, 13, 14} ∨
        polygon = {3, 5, 9, 13, 14} ∨
        polygon = {3, 5, 6, 13, 14} ∨
        polygon = {3, 5, 6, 9, 14} ∨
        polygon = {3, 5, 6, 9, 13} ∨
        polygon = {2, 6, 9, 13, 14} ∨
        polygon = {2, 5, 9, 13, 14} ∨
        polygon = {2, 5, 6, 13, 14} ∨
        polygon = {2, 5, 6, 9, 14} ∨
        polygon = {2, 5, 6, 9, 13} ∨
        polygon = {2, 3, 9, 13, 14} ∨
        polygon = {2, 3, 6, 13, 14} ∨
        polygon = {2, 3, 6, 9, 14} ∨
        polygon = {2, 3, 6, 9, 13} ∨
        polygon = {2, 3, 5, 13, 14} ∨
        polygon = {2, 3, 5, 9, 14} ∨
        polygon = {2, 3, 5, 9, 13} ∨
        polygon = {2, 3, 5, 6, 14} ∨
        polygon = {2, 3, 5, 6, 13} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {1, 6, 9, 13, 14} ∨
        polygon = {1, 5, 9, 13, 14} ∨
        polygon = {1, 5, 6, 13, 14} ∨
        polygon = {1, 5, 6, 9, 14} ∨
        polygon = {1, 5, 6, 9, 13} ∨
        polygon = {1, 3, 9, 13, 14} ∨
        polygon = {1, 3, 6, 13, 14} ∨
        polygon = {1, 3, 6, 9, 14} ∨
        polygon = {1, 3, 6, 9, 13} ∨
        polygon = {1, 3, 5, 13, 14} ∨
        polygon = {1, 3, 5, 9, 14} ∨
        polygon = {1, 3, 5, 9, 13} ∨
        polygon = {1, 3, 5, 6, 14} ∨
        polygon = {1, 3, 5, 6, 13} ∨
        polygon = {1, 3, 5, 6, 9} ∨
        polygon = {1, 2, 9, 13, 14} ∨
        polygon = {1, 2, 6, 13, 14} ∨
        polygon = {1, 2, 6, 9, 14} ∨
        polygon = {1, 2, 6, 9, 13} ∨
        polygon = {1, 2, 5, 13, 14} ∨
        polygon = {1, 2, 5, 9, 14} ∨
        polygon = {1, 2, 5, 9, 13} ∨
        polygon = {1, 2, 5, 6, 14} ∨
        polygon = {1, 2, 5, 6, 13} ∨
        polygon = {1, 2, 5, 6, 9} ∨
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 6, 9} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {1, 2, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 5, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25198] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13422 :
    (({1, 2, 3, 5, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 10, 12, 13}, {3, 6, 10, 12, 13}, {3, 5, 10, 12, 13}, {3, 5, 6, 12, 13}, {3, 5, 6, 10, 13}, {3, 5, 6, 10, 12}, {2, 6, 10, 12, 13}, {2, 5, 10, 12, 13}, {2, 5, 6, 12, 13}, {2, 5, 6, 10, 13}, {2, 5, 6, 10, 12}, {2, 3, 10, 12, 13}, {2, 3, 6, 12, 13}, {2, 3, 6, 10, 13}, {2, 3, 6, 10, 12}, {2, 3, 5, 12, 13}, {2, 3, 5, 10, 13}, {2, 3, 5, 10, 12}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 12}, {2, 3, 5, 6, 10}, {1, 6, 10, 12, 13}, {1, 5, 10, 12, 13}, {1, 5, 6, 12, 13}, {1, 5, 6, 10, 13}, {1, 5, 6, 10, 12}, {1, 3, 10, 12, 13}, {1, 3, 6, 12, 13}, {1, 3, 6, 10, 13}, {1, 3, 6, 10, 12}, {1, 3, 5, 12, 13}, {1, 3, 5, 10, 13}, {1, 3, 5, 10, 12}, {1, 3, 5, 6, 13}, {1, 3, 5, 6, 12}, {1, 3, 5, 6, 10}, {1, 2, 10, 12, 13}, {1, 2, 6, 12, 13}, {1, 2, 6, 10, 13}, {1, 2, 6, 10, 12}, {1, 2, 5, 12, 13}, {1, 2, 5, 10, 13}, {1, 2, 5, 10, 12}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 12}, {1, 2, 5, 6, 10}, {1, 2, 3, 12, 13}, {1, 2, 3, 10, 13}, {1, 2, 3, 10, 12}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 12}, {1, 2, 3, 6, 10}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13422 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 5, 6, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 10, 12, 13} ∨
        polygon = {3, 6, 10, 12, 13} ∨
        polygon = {3, 5, 10, 12, 13} ∨
        polygon = {3, 5, 6, 12, 13} ∨
        polygon = {3, 5, 6, 10, 13} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {2, 6, 10, 12, 13} ∨
        polygon = {2, 5, 10, 12, 13} ∨
        polygon = {2, 5, 6, 12, 13} ∨
        polygon = {2, 5, 6, 10, 13} ∨
        polygon = {2, 5, 6, 10, 12} ∨
        polygon = {2, 3, 10, 12, 13} ∨
        polygon = {2, 3, 6, 12, 13} ∨
        polygon = {2, 3, 6, 10, 13} ∨
        polygon = {2, 3, 6, 10, 12} ∨
        polygon = {2, 3, 5, 12, 13} ∨
        polygon = {2, 3, 5, 10, 13} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 5, 6, 13} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {1, 6, 10, 12, 13} ∨
        polygon = {1, 5, 10, 12, 13} ∨
        polygon = {1, 5, 6, 12, 13} ∨
        polygon = {1, 5, 6, 10, 13} ∨
        polygon = {1, 5, 6, 10, 12} ∨
        polygon = {1, 3, 10, 12, 13} ∨
        polygon = {1, 3, 6, 12, 13} ∨
        polygon = {1, 3, 6, 10, 13} ∨
        polygon = {1, 3, 6, 10, 12} ∨
        polygon = {1, 3, 5, 12, 13} ∨
        polygon = {1, 3, 5, 10, 13} ∨
        polygon = {1, 3, 5, 10, 12} ∨
        polygon = {1, 3, 5, 6, 13} ∨
        polygon = {1, 3, 5, 6, 12} ∨
        polygon = {1, 3, 5, 6, 10} ∨
        polygon = {1, 2, 10, 12, 13} ∨
        polygon = {1, 2, 6, 12, 13} ∨
        polygon = {1, 2, 6, 10, 13} ∨
        polygon = {1, 2, 6, 10, 12} ∨
        polygon = {1, 2, 5, 12, 13} ∨
        polygon = {1, 2, 5, 10, 13} ∨
        polygon = {1, 2, 5, 10, 12} ∨
        polygon = {1, 2, 5, 6, 13} ∨
        polygon = {1, 2, 5, 6, 12} ∨
        polygon = {1, 2, 5, 6, 10} ∨
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 5, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13422] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21614 :
    (({1, 2, 3, 5, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 10, 12, 14}, {3, 6, 10, 12, 14}, {3, 5, 10, 12, 14}, {3, 5, 6, 12, 14}, {3, 5, 6, 10, 14}, {3, 5, 6, 10, 12}, {2, 6, 10, 12, 14}, {2, 5, 10, 12, 14}, {2, 5, 6, 12, 14}, {2, 5, 6, 10, 14}, {2, 5, 6, 10, 12}, {2, 3, 10, 12, 14}, {2, 3, 6, 12, 14}, {2, 3, 6, 10, 14}, {2, 3, 6, 10, 12}, {2, 3, 5, 12, 14}, {2, 3, 5, 10, 14}, {2, 3, 5, 10, 12}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 12}, {2, 3, 5, 6, 10}, {1, 6, 10, 12, 14}, {1, 5, 10, 12, 14}, {1, 5, 6, 12, 14}, {1, 5, 6, 10, 14}, {1, 5, 6, 10, 12}, {1, 3, 10, 12, 14}, {1, 3, 6, 12, 14}, {1, 3, 6, 10, 14}, {1, 3, 6, 10, 12}, {1, 3, 5, 12, 14}, {1, 3, 5, 10, 14}, {1, 3, 5, 10, 12}, {1, 3, 5, 6, 14}, {1, 3, 5, 6, 12}, {1, 3, 5, 6, 10}, {1, 2, 10, 12, 14}, {1, 2, 6, 12, 14}, {1, 2, 6, 10, 14}, {1, 2, 6, 10, 12}, {1, 2, 5, 12, 14}, {1, 2, 5, 10, 14}, {1, 2, 5, 10, 12}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 12}, {1, 2, 5, 6, 10}, {1, 2, 3, 12, 14}, {1, 2, 3, 10, 14}, {1, 2, 3, 10, 12}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 12}, {1, 2, 3, 6, 10}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21614 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 5, 6, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 10, 12, 14} ∨
        polygon = {3, 6, 10, 12, 14} ∨
        polygon = {3, 5, 10, 12, 14} ∨
        polygon = {3, 5, 6, 12, 14} ∨
        polygon = {3, 5, 6, 10, 14} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {2, 6, 10, 12, 14} ∨
        polygon = {2, 5, 10, 12, 14} ∨
        polygon = {2, 5, 6, 12, 14} ∨
        polygon = {2, 5, 6, 10, 14} ∨
        polygon = {2, 5, 6, 10, 12} ∨
        polygon = {2, 3, 10, 12, 14} ∨
        polygon = {2, 3, 6, 12, 14} ∨
        polygon = {2, 3, 6, 10, 14} ∨
        polygon = {2, 3, 6, 10, 12} ∨
        polygon = {2, 3, 5, 12, 14} ∨
        polygon = {2, 3, 5, 10, 14} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 5, 6, 14} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {1, 6, 10, 12, 14} ∨
        polygon = {1, 5, 10, 12, 14} ∨
        polygon = {1, 5, 6, 12, 14} ∨
        polygon = {1, 5, 6, 10, 14} ∨
        polygon = {1, 5, 6, 10, 12} ∨
        polygon = {1, 3, 10, 12, 14} ∨
        polygon = {1, 3, 6, 12, 14} ∨
        polygon = {1, 3, 6, 10, 14} ∨
        polygon = {1, 3, 6, 10, 12} ∨
        polygon = {1, 3, 5, 12, 14} ∨
        polygon = {1, 3, 5, 10, 14} ∨
        polygon = {1, 3, 5, 10, 12} ∨
        polygon = {1, 3, 5, 6, 14} ∨
        polygon = {1, 3, 5, 6, 12} ∨
        polygon = {1, 3, 5, 6, 10} ∨
        polygon = {1, 2, 10, 12, 14} ∨
        polygon = {1, 2, 6, 12, 14} ∨
        polygon = {1, 2, 6, 10, 14} ∨
        polygon = {1, 2, 6, 10, 12} ∨
        polygon = {1, 2, 5, 12, 14} ∨
        polygon = {1, 2, 5, 10, 14} ∨
        polygon = {1, 2, 5, 10, 12} ∨
        polygon = {1, 2, 5, 6, 14} ∨
        polygon = {1, 2, 5, 6, 12} ∨
        polygon = {1, 2, 5, 6, 10} ∨
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 5, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21614] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25710 :
    (({1, 2, 3, 5, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 10, 13, 14}, {3, 6, 10, 13, 14}, {3, 5, 10, 13, 14}, {3, 5, 6, 13, 14}, {3, 5, 6, 10, 14}, {3, 5, 6, 10, 13}, {2, 6, 10, 13, 14}, {2, 5, 10, 13, 14}, {2, 5, 6, 13, 14}, {2, 5, 6, 10, 14}, {2, 5, 6, 10, 13}, {2, 3, 10, 13, 14}, {2, 3, 6, 13, 14}, {2, 3, 6, 10, 14}, {2, 3, 6, 10, 13}, {2, 3, 5, 13, 14}, {2, 3, 5, 10, 14}, {2, 3, 5, 10, 13}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 10}, {1, 6, 10, 13, 14}, {1, 5, 10, 13, 14}, {1, 5, 6, 13, 14}, {1, 5, 6, 10, 14}, {1, 5, 6, 10, 13}, {1, 3, 10, 13, 14}, {1, 3, 6, 13, 14}, {1, 3, 6, 10, 14}, {1, 3, 6, 10, 13}, {1, 3, 5, 13, 14}, {1, 3, 5, 10, 14}, {1, 3, 5, 10, 13}, {1, 3, 5, 6, 14}, {1, 3, 5, 6, 13}, {1, 3, 5, 6, 10}, {1, 2, 10, 13, 14}, {1, 2, 6, 13, 14}, {1, 2, 6, 10, 14}, {1, 2, 6, 10, 13}, {1, 2, 5, 13, 14}, {1, 2, 5, 10, 14}, {1, 2, 5, 10, 13}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 10}, {1, 2, 3, 13, 14}, {1, 2, 3, 10, 14}, {1, 2, 3, 10, 13}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 10}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25710 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 5, 6, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 10, 13, 14} ∨
        polygon = {3, 6, 10, 13, 14} ∨
        polygon = {3, 5, 10, 13, 14} ∨
        polygon = {3, 5, 6, 13, 14} ∨
        polygon = {3, 5, 6, 10, 14} ∨
        polygon = {3, 5, 6, 10, 13} ∨
        polygon = {2, 6, 10, 13, 14} ∨
        polygon = {2, 5, 10, 13, 14} ∨
        polygon = {2, 5, 6, 13, 14} ∨
        polygon = {2, 5, 6, 10, 14} ∨
        polygon = {2, 5, 6, 10, 13} ∨
        polygon = {2, 3, 10, 13, 14} ∨
        polygon = {2, 3, 6, 13, 14} ∨
        polygon = {2, 3, 6, 10, 14} ∨
        polygon = {2, 3, 6, 10, 13} ∨
        polygon = {2, 3, 5, 13, 14} ∨
        polygon = {2, 3, 5, 10, 14} ∨
        polygon = {2, 3, 5, 10, 13} ∨
        polygon = {2, 3, 5, 6, 14} ∨
        polygon = {2, 3, 5, 6, 13} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {1, 6, 10, 13, 14} ∨
        polygon = {1, 5, 10, 13, 14} ∨
        polygon = {1, 5, 6, 13, 14} ∨
        polygon = {1, 5, 6, 10, 14} ∨
        polygon = {1, 5, 6, 10, 13} ∨
        polygon = {1, 3, 10, 13, 14} ∨
        polygon = {1, 3, 6, 13, 14} ∨
        polygon = {1, 3, 6, 10, 14} ∨
        polygon = {1, 3, 6, 10, 13} ∨
        polygon = {1, 3, 5, 13, 14} ∨
        polygon = {1, 3, 5, 10, 14} ∨
        polygon = {1, 3, 5, 10, 13} ∨
        polygon = {1, 3, 5, 6, 14} ∨
        polygon = {1, 3, 5, 6, 13} ∨
        polygon = {1, 3, 5, 6, 10} ∨
        polygon = {1, 2, 10, 13, 14} ∨
        polygon = {1, 2, 6, 13, 14} ∨
        polygon = {1, 2, 6, 10, 14} ∨
        polygon = {1, 2, 6, 10, 13} ∨
        polygon = {1, 2, 5, 13, 14} ∨
        polygon = {1, 2, 5, 10, 14} ∨
        polygon = {1, 2, 5, 10, 13} ∨
        polygon = {1, 2, 5, 6, 14} ∨
        polygon = {1, 2, 5, 6, 13} ∨
        polygon = {1, 2, 5, 6, 10} ∨
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 5, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25710] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask28782 :
    (({1, 2, 3, 5, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 12, 13, 14}, {3, 6, 12, 13, 14}, {3, 5, 12, 13, 14}, {3, 5, 6, 13, 14}, {3, 5, 6, 12, 14}, {3, 5, 6, 12, 13}, {2, 6, 12, 13, 14}, {2, 5, 12, 13, 14}, {2, 5, 6, 13, 14}, {2, 5, 6, 12, 14}, {2, 5, 6, 12, 13}, {2, 3, 12, 13, 14}, {2, 3, 6, 13, 14}, {2, 3, 6, 12, 14}, {2, 3, 6, 12, 13}, {2, 3, 5, 13, 14}, {2, 3, 5, 12, 14}, {2, 3, 5, 12, 13}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 12}, {1, 6, 12, 13, 14}, {1, 5, 12, 13, 14}, {1, 5, 6, 13, 14}, {1, 5, 6, 12, 14}, {1, 5, 6, 12, 13}, {1, 3, 12, 13, 14}, {1, 3, 6, 13, 14}, {1, 3, 6, 12, 14}, {1, 3, 6, 12, 13}, {1, 3, 5, 13, 14}, {1, 3, 5, 12, 14}, {1, 3, 5, 12, 13}, {1, 3, 5, 6, 14}, {1, 3, 5, 6, 13}, {1, 3, 5, 6, 12}, {1, 2, 12, 13, 14}, {1, 2, 6, 13, 14}, {1, 2, 6, 12, 14}, {1, 2, 6, 12, 13}, {1, 2, 5, 13, 14}, {1, 2, 5, 12, 14}, {1, 2, 5, 12, 13}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 12}, {1, 2, 3, 13, 14}, {1, 2, 3, 12, 14}, {1, 2, 3, 12, 13}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 12}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask28782 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 5, 6, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 12, 13, 14} ∨
        polygon = {3, 6, 12, 13, 14} ∨
        polygon = {3, 5, 12, 13, 14} ∨
        polygon = {3, 5, 6, 13, 14} ∨
        polygon = {3, 5, 6, 12, 14} ∨
        polygon = {3, 5, 6, 12, 13} ∨
        polygon = {2, 6, 12, 13, 14} ∨
        polygon = {2, 5, 12, 13, 14} ∨
        polygon = {2, 5, 6, 13, 14} ∨
        polygon = {2, 5, 6, 12, 14} ∨
        polygon = {2, 5, 6, 12, 13} ∨
        polygon = {2, 3, 12, 13, 14} ∨
        polygon = {2, 3, 6, 13, 14} ∨
        polygon = {2, 3, 6, 12, 14} ∨
        polygon = {2, 3, 6, 12, 13} ∨
        polygon = {2, 3, 5, 13, 14} ∨
        polygon = {2, 3, 5, 12, 14} ∨
        polygon = {2, 3, 5, 12, 13} ∨
        polygon = {2, 3, 5, 6, 14} ∨
        polygon = {2, 3, 5, 6, 13} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {1, 6, 12, 13, 14} ∨
        polygon = {1, 5, 12, 13, 14} ∨
        polygon = {1, 5, 6, 13, 14} ∨
        polygon = {1, 5, 6, 12, 14} ∨
        polygon = {1, 5, 6, 12, 13} ∨
        polygon = {1, 3, 12, 13, 14} ∨
        polygon = {1, 3, 6, 13, 14} ∨
        polygon = {1, 3, 6, 12, 14} ∨
        polygon = {1, 3, 6, 12, 13} ∨
        polygon = {1, 3, 5, 13, 14} ∨
        polygon = {1, 3, 5, 12, 14} ∨
        polygon = {1, 3, 5, 12, 13} ∨
        polygon = {1, 3, 5, 6, 14} ∨
        polygon = {1, 3, 5, 6, 13} ∨
        polygon = {1, 3, 5, 6, 12} ∨
        polygon = {1, 2, 12, 13, 14} ∨
        polygon = {1, 2, 6, 13, 14} ∨
        polygon = {1, 2, 6, 12, 14} ∨
        polygon = {1, 2, 6, 12, 13} ∨
        polygon = {1, 2, 5, 13, 14} ∨
        polygon = {1, 2, 5, 12, 14} ∨
        polygon = {1, 2, 5, 12, 13} ∨
        polygon = {1, 2, 5, 6, 14} ∨
        polygon = {1, 2, 5, 6, 13} ∨
        polygon = {1, 2, 5, 6, 12} ∨
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 5, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask28782] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask03758 :
    (({1, 2, 3, 5, 7, 9, 10, 11} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 10, 11}, {3, 7, 9, 10, 11}, {3, 5, 9, 10, 11}, {3, 5, 7, 10, 11}, {3, 5, 7, 9, 11}, {3, 5, 7, 9, 10}, {2, 7, 9, 10, 11}, {2, 5, 9, 10, 11}, {2, 5, 7, 10, 11}, {2, 5, 7, 9, 11}, {2, 5, 7, 9, 10}, {2, 3, 9, 10, 11}, {2, 3, 7, 10, 11}, {2, 3, 7, 9, 11}, {2, 3, 7, 9, 10}, {2, 3, 5, 10, 11}, {2, 3, 5, 9, 11}, {2, 3, 5, 9, 10}, {2, 3, 5, 7, 11}, {2, 3, 5, 7, 10}, {2, 3, 5, 7, 9}, {1, 7, 9, 10, 11}, {1, 5, 9, 10, 11}, {1, 5, 7, 10, 11}, {1, 5, 7, 9, 11}, {1, 5, 7, 9, 10}, {1, 3, 9, 10, 11}, {1, 3, 7, 10, 11}, {1, 3, 7, 9, 11}, {1, 3, 7, 9, 10}, {1, 3, 5, 10, 11}, {1, 3, 5, 9, 11}, {1, 3, 5, 9, 10}, {1, 3, 5, 7, 11}, {1, 3, 5, 7, 10}, {1, 3, 5, 7, 9}, {1, 2, 9, 10, 11}, {1, 2, 7, 10, 11}, {1, 2, 7, 9, 11}, {1, 2, 7, 9, 10}, {1, 2, 5, 10, 11}, {1, 2, 5, 9, 11}, {1, 2, 5, 9, 10}, {1, 2, 5, 7, 11}, {1, 2, 5, 7, 10}, {1, 2, 5, 7, 9}, {1, 2, 3, 10, 11}, {1, 2, 3, 9, 11}, {1, 2, 3, 9, 10}, {1, 2, 3, 7, 11}, {1, 2, 3, 7, 10}, {1, 2, 3, 7, 9}, {1, 2, 3, 5, 11}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 9}, {1, 2, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask03758 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 5, 7, 9, 10, 11} →
      polygon.card = 5 →
        polygon = {5, 7, 9, 10, 11} ∨
        polygon = {3, 7, 9, 10, 11} ∨
        polygon = {3, 5, 9, 10, 11} ∨
        polygon = {3, 5, 7, 10, 11} ∨
        polygon = {3, 5, 7, 9, 11} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {2, 7, 9, 10, 11} ∨
        polygon = {2, 5, 9, 10, 11} ∨
        polygon = {2, 5, 7, 10, 11} ∨
        polygon = {2, 5, 7, 9, 11} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {2, 3, 9, 10, 11} ∨
        polygon = {2, 3, 7, 10, 11} ∨
        polygon = {2, 3, 7, 9, 11} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 3, 5, 10, 11} ∨
        polygon = {2, 3, 5, 9, 11} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 5, 7, 11} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {1, 7, 9, 10, 11} ∨
        polygon = {1, 5, 9, 10, 11} ∨
        polygon = {1, 5, 7, 10, 11} ∨
        polygon = {1, 5, 7, 9, 11} ∨
        polygon = {1, 5, 7, 9, 10} ∨
        polygon = {1, 3, 9, 10, 11} ∨
        polygon = {1, 3, 7, 10, 11} ∨
        polygon = {1, 3, 7, 9, 11} ∨
        polygon = {1, 3, 7, 9, 10} ∨
        polygon = {1, 3, 5, 10, 11} ∨
        polygon = {1, 3, 5, 9, 11} ∨
        polygon = {1, 3, 5, 9, 10} ∨
        polygon = {1, 3, 5, 7, 11} ∨
        polygon = {1, 3, 5, 7, 10} ∨
        polygon = {1, 3, 5, 7, 9} ∨
        polygon = {1, 2, 9, 10, 11} ∨
        polygon = {1, 2, 7, 10, 11} ∨
        polygon = {1, 2, 7, 9, 11} ∨
        polygon = {1, 2, 7, 9, 10} ∨
        polygon = {1, 2, 5, 10, 11} ∨
        polygon = {1, 2, 5, 9, 11} ∨
        polygon = {1, 2, 5, 9, 10} ∨
        polygon = {1, 2, 5, 7, 11} ∨
        polygon = {1, 2, 5, 7, 10} ∨
        polygon = {1, 2, 5, 7, 9} ∨
        polygon = {1, 2, 3, 10, 11} ∨
        polygon = {1, 2, 3, 9, 11} ∨
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {1, 2, 3, 7, 11} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {1, 2, 3, 5, 11} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {1, 2, 3, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 5, 7, 9, 10, 11} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask03758] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05806 :
    (({1, 2, 3, 5, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 10, 12}, {3, 7, 9, 10, 12}, {3, 5, 9, 10, 12}, {3, 5, 7, 10, 12}, {3, 5, 7, 9, 12}, {3, 5, 7, 9, 10}, {2, 7, 9, 10, 12}, {2, 5, 9, 10, 12}, {2, 5, 7, 10, 12}, {2, 5, 7, 9, 12}, {2, 5, 7, 9, 10}, {2, 3, 9, 10, 12}, {2, 3, 7, 10, 12}, {2, 3, 7, 9, 12}, {2, 3, 7, 9, 10}, {2, 3, 5, 10, 12}, {2, 3, 5, 9, 12}, {2, 3, 5, 9, 10}, {2, 3, 5, 7, 12}, {2, 3, 5, 7, 10}, {2, 3, 5, 7, 9}, {1, 7, 9, 10, 12}, {1, 5, 9, 10, 12}, {1, 5, 7, 10, 12}, {1, 5, 7, 9, 12}, {1, 5, 7, 9, 10}, {1, 3, 9, 10, 12}, {1, 3, 7, 10, 12}, {1, 3, 7, 9, 12}, {1, 3, 7, 9, 10}, {1, 3, 5, 10, 12}, {1, 3, 5, 9, 12}, {1, 3, 5, 9, 10}, {1, 3, 5, 7, 12}, {1, 3, 5, 7, 10}, {1, 3, 5, 7, 9}, {1, 2, 9, 10, 12}, {1, 2, 7, 10, 12}, {1, 2, 7, 9, 12}, {1, 2, 7, 9, 10}, {1, 2, 5, 10, 12}, {1, 2, 5, 9, 12}, {1, 2, 5, 9, 10}, {1, 2, 5, 7, 12}, {1, 2, 5, 7, 10}, {1, 2, 5, 7, 9}, {1, 2, 3, 10, 12}, {1, 2, 3, 9, 12}, {1, 2, 3, 9, 10}, {1, 2, 3, 7, 12}, {1, 2, 3, 7, 10}, {1, 2, 3, 7, 9}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 9}, {1, 2, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05806 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 5, 7, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {5, 7, 9, 10, 12} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {2, 7, 9, 10, 12} ∨
        polygon = {2, 5, 9, 10, 12} ∨
        polygon = {2, 5, 7, 10, 12} ∨
        polygon = {2, 5, 7, 9, 12} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {2, 3, 9, 10, 12} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {1, 7, 9, 10, 12} ∨
        polygon = {1, 5, 9, 10, 12} ∨
        polygon = {1, 5, 7, 10, 12} ∨
        polygon = {1, 5, 7, 9, 12} ∨
        polygon = {1, 5, 7, 9, 10} ∨
        polygon = {1, 3, 9, 10, 12} ∨
        polygon = {1, 3, 7, 10, 12} ∨
        polygon = {1, 3, 7, 9, 12} ∨
        polygon = {1, 3, 7, 9, 10} ∨
        polygon = {1, 3, 5, 10, 12} ∨
        polygon = {1, 3, 5, 9, 12} ∨
        polygon = {1, 3, 5, 9, 10} ∨
        polygon = {1, 3, 5, 7, 12} ∨
        polygon = {1, 3, 5, 7, 10} ∨
        polygon = {1, 3, 5, 7, 9} ∨
        polygon = {1, 2, 9, 10, 12} ∨
        polygon = {1, 2, 7, 10, 12} ∨
        polygon = {1, 2, 7, 9, 12} ∨
        polygon = {1, 2, 7, 9, 10} ∨
        polygon = {1, 2, 5, 10, 12} ∨
        polygon = {1, 2, 5, 9, 12} ∨
        polygon = {1, 2, 5, 9, 10} ∨
        polygon = {1, 2, 5, 7, 12} ∨
        polygon = {1, 2, 5, 7, 10} ∨
        polygon = {1, 2, 5, 7, 9} ∨
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {1, 2, 3, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 5, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05806] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09902 :
    (({1, 2, 3, 5, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 10, 13}, {3, 7, 9, 10, 13}, {3, 5, 9, 10, 13}, {3, 5, 7, 10, 13}, {3, 5, 7, 9, 13}, {3, 5, 7, 9, 10}, {2, 7, 9, 10, 13}, {2, 5, 9, 10, 13}, {2, 5, 7, 10, 13}, {2, 5, 7, 9, 13}, {2, 5, 7, 9, 10}, {2, 3, 9, 10, 13}, {2, 3, 7, 10, 13}, {2, 3, 7, 9, 13}, {2, 3, 7, 9, 10}, {2, 3, 5, 10, 13}, {2, 3, 5, 9, 13}, {2, 3, 5, 9, 10}, {2, 3, 5, 7, 13}, {2, 3, 5, 7, 10}, {2, 3, 5, 7, 9}, {1, 7, 9, 10, 13}, {1, 5, 9, 10, 13}, {1, 5, 7, 10, 13}, {1, 5, 7, 9, 13}, {1, 5, 7, 9, 10}, {1, 3, 9, 10, 13}, {1, 3, 7, 10, 13}, {1, 3, 7, 9, 13}, {1, 3, 7, 9, 10}, {1, 3, 5, 10, 13}, {1, 3, 5, 9, 13}, {1, 3, 5, 9, 10}, {1, 3, 5, 7, 13}, {1, 3, 5, 7, 10}, {1, 3, 5, 7, 9}, {1, 2, 9, 10, 13}, {1, 2, 7, 10, 13}, {1, 2, 7, 9, 13}, {1, 2, 7, 9, 10}, {1, 2, 5, 10, 13}, {1, 2, 5, 9, 13}, {1, 2, 5, 9, 10}, {1, 2, 5, 7, 13}, {1, 2, 5, 7, 10}, {1, 2, 5, 7, 9}, {1, 2, 3, 10, 13}, {1, 2, 3, 9, 13}, {1, 2, 3, 9, 10}, {1, 2, 3, 7, 13}, {1, 2, 3, 7, 10}, {1, 2, 3, 7, 9}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 9}, {1, 2, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09902 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 5, 7, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {5, 7, 9, 10, 13} ∨
        polygon = {3, 7, 9, 10, 13} ∨
        polygon = {3, 5, 9, 10, 13} ∨
        polygon = {3, 5, 7, 10, 13} ∨
        polygon = {3, 5, 7, 9, 13} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {2, 7, 9, 10, 13} ∨
        polygon = {2, 5, 9, 10, 13} ∨
        polygon = {2, 5, 7, 10, 13} ∨
        polygon = {2, 5, 7, 9, 13} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {2, 3, 9, 10, 13} ∨
        polygon = {2, 3, 7, 10, 13} ∨
        polygon = {2, 3, 7, 9, 13} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 3, 5, 10, 13} ∨
        polygon = {2, 3, 5, 9, 13} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 5, 7, 13} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {1, 7, 9, 10, 13} ∨
        polygon = {1, 5, 9, 10, 13} ∨
        polygon = {1, 5, 7, 10, 13} ∨
        polygon = {1, 5, 7, 9, 13} ∨
        polygon = {1, 5, 7, 9, 10} ∨
        polygon = {1, 3, 9, 10, 13} ∨
        polygon = {1, 3, 7, 10, 13} ∨
        polygon = {1, 3, 7, 9, 13} ∨
        polygon = {1, 3, 7, 9, 10} ∨
        polygon = {1, 3, 5, 10, 13} ∨
        polygon = {1, 3, 5, 9, 13} ∨
        polygon = {1, 3, 5, 9, 10} ∨
        polygon = {1, 3, 5, 7, 13} ∨
        polygon = {1, 3, 5, 7, 10} ∨
        polygon = {1, 3, 5, 7, 9} ∨
        polygon = {1, 2, 9, 10, 13} ∨
        polygon = {1, 2, 7, 10, 13} ∨
        polygon = {1, 2, 7, 9, 13} ∨
        polygon = {1, 2, 7, 9, 10} ∨
        polygon = {1, 2, 5, 10, 13} ∨
        polygon = {1, 2, 5, 9, 13} ∨
        polygon = {1, 2, 5, 9, 10} ∨
        polygon = {1, 2, 5, 7, 13} ∨
        polygon = {1, 2, 5, 7, 10} ∨
        polygon = {1, 2, 5, 7, 9} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {1, 2, 3, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 5, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09902] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask18094 :
    (({1, 2, 3, 5, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 10, 14}, {3, 7, 9, 10, 14}, {3, 5, 9, 10, 14}, {3, 5, 7, 10, 14}, {3, 5, 7, 9, 14}, {3, 5, 7, 9, 10}, {2, 7, 9, 10, 14}, {2, 5, 9, 10, 14}, {2, 5, 7, 10, 14}, {2, 5, 7, 9, 14}, {2, 5, 7, 9, 10}, {2, 3, 9, 10, 14}, {2, 3, 7, 10, 14}, {2, 3, 7, 9, 14}, {2, 3, 7, 9, 10}, {2, 3, 5, 10, 14}, {2, 3, 5, 9, 14}, {2, 3, 5, 9, 10}, {2, 3, 5, 7, 14}, {2, 3, 5, 7, 10}, {2, 3, 5, 7, 9}, {1, 7, 9, 10, 14}, {1, 5, 9, 10, 14}, {1, 5, 7, 10, 14}, {1, 5, 7, 9, 14}, {1, 5, 7, 9, 10}, {1, 3, 9, 10, 14}, {1, 3, 7, 10, 14}, {1, 3, 7, 9, 14}, {1, 3, 7, 9, 10}, {1, 3, 5, 10, 14}, {1, 3, 5, 9, 14}, {1, 3, 5, 9, 10}, {1, 3, 5, 7, 14}, {1, 3, 5, 7, 10}, {1, 3, 5, 7, 9}, {1, 2, 9, 10, 14}, {1, 2, 7, 10, 14}, {1, 2, 7, 9, 14}, {1, 2, 7, 9, 10}, {1, 2, 5, 10, 14}, {1, 2, 5, 9, 14}, {1, 2, 5, 9, 10}, {1, 2, 5, 7, 14}, {1, 2, 5, 7, 10}, {1, 2, 5, 7, 9}, {1, 2, 3, 10, 14}, {1, 2, 3, 9, 14}, {1, 2, 3, 9, 10}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 10}, {1, 2, 3, 7, 9}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 9}, {1, 2, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask18094 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 5, 7, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 9, 10, 14} ∨
        polygon = {3, 7, 9, 10, 14} ∨
        polygon = {3, 5, 9, 10, 14} ∨
        polygon = {3, 5, 7, 10, 14} ∨
        polygon = {3, 5, 7, 9, 14} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {2, 7, 9, 10, 14} ∨
        polygon = {2, 5, 9, 10, 14} ∨
        polygon = {2, 5, 7, 10, 14} ∨
        polygon = {2, 5, 7, 9, 14} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {2, 3, 9, 10, 14} ∨
        polygon = {2, 3, 7, 10, 14} ∨
        polygon = {2, 3, 7, 9, 14} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 3, 5, 10, 14} ∨
        polygon = {2, 3, 5, 9, 14} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 5, 7, 14} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {1, 7, 9, 10, 14} ∨
        polygon = {1, 5, 9, 10, 14} ∨
        polygon = {1, 5, 7, 10, 14} ∨
        polygon = {1, 5, 7, 9, 14} ∨
        polygon = {1, 5, 7, 9, 10} ∨
        polygon = {1, 3, 9, 10, 14} ∨
        polygon = {1, 3, 7, 10, 14} ∨
        polygon = {1, 3, 7, 9, 14} ∨
        polygon = {1, 3, 7, 9, 10} ∨
        polygon = {1, 3, 5, 10, 14} ∨
        polygon = {1, 3, 5, 9, 14} ∨
        polygon = {1, 3, 5, 9, 10} ∨
        polygon = {1, 3, 5, 7, 14} ∨
        polygon = {1, 3, 5, 7, 10} ∨
        polygon = {1, 3, 5, 7, 9} ∨
        polygon = {1, 2, 9, 10, 14} ∨
        polygon = {1, 2, 7, 10, 14} ∨
        polygon = {1, 2, 7, 9, 14} ∨
        polygon = {1, 2, 7, 9, 10} ∨
        polygon = {1, 2, 5, 10, 14} ∨
        polygon = {1, 2, 5, 9, 14} ∨
        polygon = {1, 2, 5, 9, 10} ∨
        polygon = {1, 2, 5, 7, 14} ∨
        polygon = {1, 2, 5, 7, 10} ∨
        polygon = {1, 2, 5, 7, 9} ∨
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {1, 2, 3, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 5, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask18094] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12974 :
    (({1, 2, 3, 5, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 12, 13}, {3, 7, 9, 12, 13}, {3, 5, 9, 12, 13}, {3, 5, 7, 12, 13}, {3, 5, 7, 9, 13}, {3, 5, 7, 9, 12}, {2, 7, 9, 12, 13}, {2, 5, 9, 12, 13}, {2, 5, 7, 12, 13}, {2, 5, 7, 9, 13}, {2, 5, 7, 9, 12}, {2, 3, 9, 12, 13}, {2, 3, 7, 12, 13}, {2, 3, 7, 9, 13}, {2, 3, 7, 9, 12}, {2, 3, 5, 12, 13}, {2, 3, 5, 9, 13}, {2, 3, 5, 9, 12}, {2, 3, 5, 7, 13}, {2, 3, 5, 7, 12}, {2, 3, 5, 7, 9}, {1, 7, 9, 12, 13}, {1, 5, 9, 12, 13}, {1, 5, 7, 12, 13}, {1, 5, 7, 9, 13}, {1, 5, 7, 9, 12}, {1, 3, 9, 12, 13}, {1, 3, 7, 12, 13}, {1, 3, 7, 9, 13}, {1, 3, 7, 9, 12}, {1, 3, 5, 12, 13}, {1, 3, 5, 9, 13}, {1, 3, 5, 9, 12}, {1, 3, 5, 7, 13}, {1, 3, 5, 7, 12}, {1, 3, 5, 7, 9}, {1, 2, 9, 12, 13}, {1, 2, 7, 12, 13}, {1, 2, 7, 9, 13}, {1, 2, 7, 9, 12}, {1, 2, 5, 12, 13}, {1, 2, 5, 9, 13}, {1, 2, 5, 9, 12}, {1, 2, 5, 7, 13}, {1, 2, 5, 7, 12}, {1, 2, 5, 7, 9}, {1, 2, 3, 12, 13}, {1, 2, 3, 9, 13}, {1, 2, 3, 9, 12}, {1, 2, 3, 7, 13}, {1, 2, 3, 7, 12}, {1, 2, 3, 7, 9}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 9}, {1, 2, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12974 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 5, 7, 9, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 7, 9, 12, 13} ∨
        polygon = {3, 7, 9, 12, 13} ∨
        polygon = {3, 5, 9, 12, 13} ∨
        polygon = {3, 5, 7, 12, 13} ∨
        polygon = {3, 5, 7, 9, 13} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {2, 7, 9, 12, 13} ∨
        polygon = {2, 5, 9, 12, 13} ∨
        polygon = {2, 5, 7, 12, 13} ∨
        polygon = {2, 5, 7, 9, 13} ∨
        polygon = {2, 5, 7, 9, 12} ∨
        polygon = {2, 3, 9, 12, 13} ∨
        polygon = {2, 3, 7, 12, 13} ∨
        polygon = {2, 3, 7, 9, 13} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 3, 5, 12, 13} ∨
        polygon = {2, 3, 5, 9, 13} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 5, 7, 13} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {1, 7, 9, 12, 13} ∨
        polygon = {1, 5, 9, 12, 13} ∨
        polygon = {1, 5, 7, 12, 13} ∨
        polygon = {1, 5, 7, 9, 13} ∨
        polygon = {1, 5, 7, 9, 12} ∨
        polygon = {1, 3, 9, 12, 13} ∨
        polygon = {1, 3, 7, 12, 13} ∨
        polygon = {1, 3, 7, 9, 13} ∨
        polygon = {1, 3, 7, 9, 12} ∨
        polygon = {1, 3, 5, 12, 13} ∨
        polygon = {1, 3, 5, 9, 13} ∨
        polygon = {1, 3, 5, 9, 12} ∨
        polygon = {1, 3, 5, 7, 13} ∨
        polygon = {1, 3, 5, 7, 12} ∨
        polygon = {1, 3, 5, 7, 9} ∨
        polygon = {1, 2, 9, 12, 13} ∨
        polygon = {1, 2, 7, 12, 13} ∨
        polygon = {1, 2, 7, 9, 13} ∨
        polygon = {1, 2, 7, 9, 12} ∨
        polygon = {1, 2, 5, 12, 13} ∨
        polygon = {1, 2, 5, 9, 13} ∨
        polygon = {1, 2, 5, 9, 12} ∨
        polygon = {1, 2, 5, 7, 13} ∨
        polygon = {1, 2, 5, 7, 12} ∨
        polygon = {1, 2, 5, 7, 9} ∨
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {1, 2, 3, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 5, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12974] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21166 :
    (({1, 2, 3, 5, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 12, 14}, {3, 7, 9, 12, 14}, {3, 5, 9, 12, 14}, {3, 5, 7, 12, 14}, {3, 5, 7, 9, 14}, {3, 5, 7, 9, 12}, {2, 7, 9, 12, 14}, {2, 5, 9, 12, 14}, {2, 5, 7, 12, 14}, {2, 5, 7, 9, 14}, {2, 5, 7, 9, 12}, {2, 3, 9, 12, 14}, {2, 3, 7, 12, 14}, {2, 3, 7, 9, 14}, {2, 3, 7, 9, 12}, {2, 3, 5, 12, 14}, {2, 3, 5, 9, 14}, {2, 3, 5, 9, 12}, {2, 3, 5, 7, 14}, {2, 3, 5, 7, 12}, {2, 3, 5, 7, 9}, {1, 7, 9, 12, 14}, {1, 5, 9, 12, 14}, {1, 5, 7, 12, 14}, {1, 5, 7, 9, 14}, {1, 5, 7, 9, 12}, {1, 3, 9, 12, 14}, {1, 3, 7, 12, 14}, {1, 3, 7, 9, 14}, {1, 3, 7, 9, 12}, {1, 3, 5, 12, 14}, {1, 3, 5, 9, 14}, {1, 3, 5, 9, 12}, {1, 3, 5, 7, 14}, {1, 3, 5, 7, 12}, {1, 3, 5, 7, 9}, {1, 2, 9, 12, 14}, {1, 2, 7, 12, 14}, {1, 2, 7, 9, 14}, {1, 2, 7, 9, 12}, {1, 2, 5, 12, 14}, {1, 2, 5, 9, 14}, {1, 2, 5, 9, 12}, {1, 2, 5, 7, 14}, {1, 2, 5, 7, 12}, {1, 2, 5, 7, 9}, {1, 2, 3, 12, 14}, {1, 2, 3, 9, 14}, {1, 2, 3, 9, 12}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 12}, {1, 2, 3, 7, 9}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 9}, {1, 2, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21166 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 5, 7, 9, 12, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 9, 12, 14} ∨
        polygon = {3, 7, 9, 12, 14} ∨
        polygon = {3, 5, 9, 12, 14} ∨
        polygon = {3, 5, 7, 12, 14} ∨
        polygon = {3, 5, 7, 9, 14} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {2, 7, 9, 12, 14} ∨
        polygon = {2, 5, 9, 12, 14} ∨
        polygon = {2, 5, 7, 12, 14} ∨
        polygon = {2, 5, 7, 9, 14} ∨
        polygon = {2, 5, 7, 9, 12} ∨
        polygon = {2, 3, 9, 12, 14} ∨
        polygon = {2, 3, 7, 12, 14} ∨
        polygon = {2, 3, 7, 9, 14} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 3, 5, 12, 14} ∨
        polygon = {2, 3, 5, 9, 14} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 5, 7, 14} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {1, 7, 9, 12, 14} ∨
        polygon = {1, 5, 9, 12, 14} ∨
        polygon = {1, 5, 7, 12, 14} ∨
        polygon = {1, 5, 7, 9, 14} ∨
        polygon = {1, 5, 7, 9, 12} ∨
        polygon = {1, 3, 9, 12, 14} ∨
        polygon = {1, 3, 7, 12, 14} ∨
        polygon = {1, 3, 7, 9, 14} ∨
        polygon = {1, 3, 7, 9, 12} ∨
        polygon = {1, 3, 5, 12, 14} ∨
        polygon = {1, 3, 5, 9, 14} ∨
        polygon = {1, 3, 5, 9, 12} ∨
        polygon = {1, 3, 5, 7, 14} ∨
        polygon = {1, 3, 5, 7, 12} ∨
        polygon = {1, 3, 5, 7, 9} ∨
        polygon = {1, 2, 9, 12, 14} ∨
        polygon = {1, 2, 7, 12, 14} ∨
        polygon = {1, 2, 7, 9, 14} ∨
        polygon = {1, 2, 7, 9, 12} ∨
        polygon = {1, 2, 5, 12, 14} ∨
        polygon = {1, 2, 5, 9, 14} ∨
        polygon = {1, 2, 5, 9, 12} ∨
        polygon = {1, 2, 5, 7, 14} ∨
        polygon = {1, 2, 5, 7, 12} ∨
        polygon = {1, 2, 5, 7, 9} ∨
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {1, 2, 3, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 5, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21166] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25262 :
    (({1, 2, 3, 5, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 13, 14}, {3, 7, 9, 13, 14}, {3, 5, 9, 13, 14}, {3, 5, 7, 13, 14}, {3, 5, 7, 9, 14}, {3, 5, 7, 9, 13}, {2, 7, 9, 13, 14}, {2, 5, 9, 13, 14}, {2, 5, 7, 13, 14}, {2, 5, 7, 9, 14}, {2, 5, 7, 9, 13}, {2, 3, 9, 13, 14}, {2, 3, 7, 13, 14}, {2, 3, 7, 9, 14}, {2, 3, 7, 9, 13}, {2, 3, 5, 13, 14}, {2, 3, 5, 9, 14}, {2, 3, 5, 9, 13}, {2, 3, 5, 7, 14}, {2, 3, 5, 7, 13}, {2, 3, 5, 7, 9}, {1, 7, 9, 13, 14}, {1, 5, 9, 13, 14}, {1, 5, 7, 13, 14}, {1, 5, 7, 9, 14}, {1, 5, 7, 9, 13}, {1, 3, 9, 13, 14}, {1, 3, 7, 13, 14}, {1, 3, 7, 9, 14}, {1, 3, 7, 9, 13}, {1, 3, 5, 13, 14}, {1, 3, 5, 9, 14}, {1, 3, 5, 9, 13}, {1, 3, 5, 7, 14}, {1, 3, 5, 7, 13}, {1, 3, 5, 7, 9}, {1, 2, 9, 13, 14}, {1, 2, 7, 13, 14}, {1, 2, 7, 9, 14}, {1, 2, 7, 9, 13}, {1, 2, 5, 13, 14}, {1, 2, 5, 9, 14}, {1, 2, 5, 9, 13}, {1, 2, 5, 7, 14}, {1, 2, 5, 7, 13}, {1, 2, 5, 7, 9}, {1, 2, 3, 13, 14}, {1, 2, 3, 9, 14}, {1, 2, 3, 9, 13}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 13}, {1, 2, 3, 7, 9}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 9}, {1, 2, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25262 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 5, 7, 9, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 9, 13, 14} ∨
        polygon = {3, 7, 9, 13, 14} ∨
        polygon = {3, 5, 9, 13, 14} ∨
        polygon = {3, 5, 7, 13, 14} ∨
        polygon = {3, 5, 7, 9, 14} ∨
        polygon = {3, 5, 7, 9, 13} ∨
        polygon = {2, 7, 9, 13, 14} ∨
        polygon = {2, 5, 9, 13, 14} ∨
        polygon = {2, 5, 7, 13, 14} ∨
        polygon = {2, 5, 7, 9, 14} ∨
        polygon = {2, 5, 7, 9, 13} ∨
        polygon = {2, 3, 9, 13, 14} ∨
        polygon = {2, 3, 7, 13, 14} ∨
        polygon = {2, 3, 7, 9, 14} ∨
        polygon = {2, 3, 7, 9, 13} ∨
        polygon = {2, 3, 5, 13, 14} ∨
        polygon = {2, 3, 5, 9, 14} ∨
        polygon = {2, 3, 5, 9, 13} ∨
        polygon = {2, 3, 5, 7, 14} ∨
        polygon = {2, 3, 5, 7, 13} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {1, 7, 9, 13, 14} ∨
        polygon = {1, 5, 9, 13, 14} ∨
        polygon = {1, 5, 7, 13, 14} ∨
        polygon = {1, 5, 7, 9, 14} ∨
        polygon = {1, 5, 7, 9, 13} ∨
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
        polygon = {1, 2, 9, 13, 14} ∨
        polygon = {1, 2, 7, 13, 14} ∨
        polygon = {1, 2, 7, 9, 14} ∨
        polygon = {1, 2, 7, 9, 13} ∨
        polygon = {1, 2, 5, 13, 14} ∨
        polygon = {1, 2, 5, 9, 14} ∨
        polygon = {1, 2, 5, 9, 13} ∨
        polygon = {1, 2, 5, 7, 14} ∨
        polygon = {1, 2, 5, 7, 13} ∨
        polygon = {1, 2, 5, 7, 9} ∨
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {1, 2, 3, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 5, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25262] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13486 :
    (({1, 2, 3, 5, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 10, 12, 13}, {3, 7, 10, 12, 13}, {3, 5, 10, 12, 13}, {3, 5, 7, 12, 13}, {3, 5, 7, 10, 13}, {3, 5, 7, 10, 12}, {2, 7, 10, 12, 13}, {2, 5, 10, 12, 13}, {2, 5, 7, 12, 13}, {2, 5, 7, 10, 13}, {2, 5, 7, 10, 12}, {2, 3, 10, 12, 13}, {2, 3, 7, 12, 13}, {2, 3, 7, 10, 13}, {2, 3, 7, 10, 12}, {2, 3, 5, 12, 13}, {2, 3, 5, 10, 13}, {2, 3, 5, 10, 12}, {2, 3, 5, 7, 13}, {2, 3, 5, 7, 12}, {2, 3, 5, 7, 10}, {1, 7, 10, 12, 13}, {1, 5, 10, 12, 13}, {1, 5, 7, 12, 13}, {1, 5, 7, 10, 13}, {1, 5, 7, 10, 12}, {1, 3, 10, 12, 13}, {1, 3, 7, 12, 13}, {1, 3, 7, 10, 13}, {1, 3, 7, 10, 12}, {1, 3, 5, 12, 13}, {1, 3, 5, 10, 13}, {1, 3, 5, 10, 12}, {1, 3, 5, 7, 13}, {1, 3, 5, 7, 12}, {1, 3, 5, 7, 10}, {1, 2, 10, 12, 13}, {1, 2, 7, 12, 13}, {1, 2, 7, 10, 13}, {1, 2, 7, 10, 12}, {1, 2, 5, 12, 13}, {1, 2, 5, 10, 13}, {1, 2, 5, 10, 12}, {1, 2, 5, 7, 13}, {1, 2, 5, 7, 12}, {1, 2, 5, 7, 10}, {1, 2, 3, 12, 13}, {1, 2, 3, 10, 13}, {1, 2, 3, 10, 12}, {1, 2, 3, 7, 13}, {1, 2, 3, 7, 12}, {1, 2, 3, 7, 10}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13486 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 5, 7, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 7, 10, 12, 13} ∨
        polygon = {3, 7, 10, 12, 13} ∨
        polygon = {3, 5, 10, 12, 13} ∨
        polygon = {3, 5, 7, 12, 13} ∨
        polygon = {3, 5, 7, 10, 13} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {2, 7, 10, 12, 13} ∨
        polygon = {2, 5, 10, 12, 13} ∨
        polygon = {2, 5, 7, 12, 13} ∨
        polygon = {2, 5, 7, 10, 13} ∨
        polygon = {2, 5, 7, 10, 12} ∨
        polygon = {2, 3, 10, 12, 13} ∨
        polygon = {2, 3, 7, 12, 13} ∨
        polygon = {2, 3, 7, 10, 13} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {2, 3, 5, 12, 13} ∨
        polygon = {2, 3, 5, 10, 13} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 5, 7, 13} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {1, 7, 10, 12, 13} ∨
        polygon = {1, 5, 10, 12, 13} ∨
        polygon = {1, 5, 7, 12, 13} ∨
        polygon = {1, 5, 7, 10, 13} ∨
        polygon = {1, 5, 7, 10, 12} ∨
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
        polygon = {1, 2, 10, 12, 13} ∨
        polygon = {1, 2, 7, 12, 13} ∨
        polygon = {1, 2, 7, 10, 13} ∨
        polygon = {1, 2, 7, 10, 12} ∨
        polygon = {1, 2, 5, 12, 13} ∨
        polygon = {1, 2, 5, 10, 13} ∨
        polygon = {1, 2, 5, 10, 12} ∨
        polygon = {1, 2, 5, 7, 13} ∨
        polygon = {1, 2, 5, 7, 12} ∨
        polygon = {1, 2, 5, 7, 10} ∨
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 5, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13486] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21678 :
    (({1, 2, 3, 5, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 10, 12, 14}, {3, 7, 10, 12, 14}, {3, 5, 10, 12, 14}, {3, 5, 7, 12, 14}, {3, 5, 7, 10, 14}, {3, 5, 7, 10, 12}, {2, 7, 10, 12, 14}, {2, 5, 10, 12, 14}, {2, 5, 7, 12, 14}, {2, 5, 7, 10, 14}, {2, 5, 7, 10, 12}, {2, 3, 10, 12, 14}, {2, 3, 7, 12, 14}, {2, 3, 7, 10, 14}, {2, 3, 7, 10, 12}, {2, 3, 5, 12, 14}, {2, 3, 5, 10, 14}, {2, 3, 5, 10, 12}, {2, 3, 5, 7, 14}, {2, 3, 5, 7, 12}, {2, 3, 5, 7, 10}, {1, 7, 10, 12, 14}, {1, 5, 10, 12, 14}, {1, 5, 7, 12, 14}, {1, 5, 7, 10, 14}, {1, 5, 7, 10, 12}, {1, 3, 10, 12, 14}, {1, 3, 7, 12, 14}, {1, 3, 7, 10, 14}, {1, 3, 7, 10, 12}, {1, 3, 5, 12, 14}, {1, 3, 5, 10, 14}, {1, 3, 5, 10, 12}, {1, 3, 5, 7, 14}, {1, 3, 5, 7, 12}, {1, 3, 5, 7, 10}, {1, 2, 10, 12, 14}, {1, 2, 7, 12, 14}, {1, 2, 7, 10, 14}, {1, 2, 7, 10, 12}, {1, 2, 5, 12, 14}, {1, 2, 5, 10, 14}, {1, 2, 5, 10, 12}, {1, 2, 5, 7, 14}, {1, 2, 5, 7, 12}, {1, 2, 5, 7, 10}, {1, 2, 3, 12, 14}, {1, 2, 3, 10, 14}, {1, 2, 3, 10, 12}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 12}, {1, 2, 3, 7, 10}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21678 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 5, 7, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 10, 12, 14} ∨
        polygon = {3, 7, 10, 12, 14} ∨
        polygon = {3, 5, 10, 12, 14} ∨
        polygon = {3, 5, 7, 12, 14} ∨
        polygon = {3, 5, 7, 10, 14} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {2, 7, 10, 12, 14} ∨
        polygon = {2, 5, 10, 12, 14} ∨
        polygon = {2, 5, 7, 12, 14} ∨
        polygon = {2, 5, 7, 10, 14} ∨
        polygon = {2, 5, 7, 10, 12} ∨
        polygon = {2, 3, 10, 12, 14} ∨
        polygon = {2, 3, 7, 12, 14} ∨
        polygon = {2, 3, 7, 10, 14} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {2, 3, 5, 12, 14} ∨
        polygon = {2, 3, 5, 10, 14} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 5, 7, 14} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {1, 7, 10, 12, 14} ∨
        polygon = {1, 5, 10, 12, 14} ∨
        polygon = {1, 5, 7, 12, 14} ∨
        polygon = {1, 5, 7, 10, 14} ∨
        polygon = {1, 5, 7, 10, 12} ∨
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
        polygon = {1, 2, 10, 12, 14} ∨
        polygon = {1, 2, 7, 12, 14} ∨
        polygon = {1, 2, 7, 10, 14} ∨
        polygon = {1, 2, 7, 10, 12} ∨
        polygon = {1, 2, 5, 12, 14} ∨
        polygon = {1, 2, 5, 10, 14} ∨
        polygon = {1, 2, 5, 10, 12} ∨
        polygon = {1, 2, 5, 7, 14} ∨
        polygon = {1, 2, 5, 7, 12} ∨
        polygon = {1, 2, 5, 7, 10} ∨
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 5, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21678] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25774 :
    (({1, 2, 3, 5, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 10, 13, 14}, {3, 7, 10, 13, 14}, {3, 5, 10, 13, 14}, {3, 5, 7, 13, 14}, {3, 5, 7, 10, 14}, {3, 5, 7, 10, 13}, {2, 7, 10, 13, 14}, {2, 5, 10, 13, 14}, {2, 5, 7, 13, 14}, {2, 5, 7, 10, 14}, {2, 5, 7, 10, 13}, {2, 3, 10, 13, 14}, {2, 3, 7, 13, 14}, {2, 3, 7, 10, 14}, {2, 3, 7, 10, 13}, {2, 3, 5, 13, 14}, {2, 3, 5, 10, 14}, {2, 3, 5, 10, 13}, {2, 3, 5, 7, 14}, {2, 3, 5, 7, 13}, {2, 3, 5, 7, 10}, {1, 7, 10, 13, 14}, {1, 5, 10, 13, 14}, {1, 5, 7, 13, 14}, {1, 5, 7, 10, 14}, {1, 5, 7, 10, 13}, {1, 3, 10, 13, 14}, {1, 3, 7, 13, 14}, {1, 3, 7, 10, 14}, {1, 3, 7, 10, 13}, {1, 3, 5, 13, 14}, {1, 3, 5, 10, 14}, {1, 3, 5, 10, 13}, {1, 3, 5, 7, 14}, {1, 3, 5, 7, 13}, {1, 3, 5, 7, 10}, {1, 2, 10, 13, 14}, {1, 2, 7, 13, 14}, {1, 2, 7, 10, 14}, {1, 2, 7, 10, 13}, {1, 2, 5, 13, 14}, {1, 2, 5, 10, 14}, {1, 2, 5, 10, 13}, {1, 2, 5, 7, 14}, {1, 2, 5, 7, 13}, {1, 2, 5, 7, 10}, {1, 2, 3, 13, 14}, {1, 2, 3, 10, 14}, {1, 2, 3, 10, 13}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 13}, {1, 2, 3, 7, 10}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25774 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 5, 7, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 10, 13, 14} ∨
        polygon = {3, 7, 10, 13, 14} ∨
        polygon = {3, 5, 10, 13, 14} ∨
        polygon = {3, 5, 7, 13, 14} ∨
        polygon = {3, 5, 7, 10, 14} ∨
        polygon = {3, 5, 7, 10, 13} ∨
        polygon = {2, 7, 10, 13, 14} ∨
        polygon = {2, 5, 10, 13, 14} ∨
        polygon = {2, 5, 7, 13, 14} ∨
        polygon = {2, 5, 7, 10, 14} ∨
        polygon = {2, 5, 7, 10, 13} ∨
        polygon = {2, 3, 10, 13, 14} ∨
        polygon = {2, 3, 7, 13, 14} ∨
        polygon = {2, 3, 7, 10, 14} ∨
        polygon = {2, 3, 7, 10, 13} ∨
        polygon = {2, 3, 5, 13, 14} ∨
        polygon = {2, 3, 5, 10, 14} ∨
        polygon = {2, 3, 5, 10, 13} ∨
        polygon = {2, 3, 5, 7, 14} ∨
        polygon = {2, 3, 5, 7, 13} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {1, 7, 10, 13, 14} ∨
        polygon = {1, 5, 10, 13, 14} ∨
        polygon = {1, 5, 7, 13, 14} ∨
        polygon = {1, 5, 7, 10, 14} ∨
        polygon = {1, 5, 7, 10, 13} ∨
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
        polygon = {1, 2, 10, 13, 14} ∨
        polygon = {1, 2, 7, 13, 14} ∨
        polygon = {1, 2, 7, 10, 14} ∨
        polygon = {1, 2, 7, 10, 13} ∨
        polygon = {1, 2, 5, 13, 14} ∨
        polygon = {1, 2, 5, 10, 14} ∨
        polygon = {1, 2, 5, 10, 13} ∨
        polygon = {1, 2, 5, 7, 14} ∨
        polygon = {1, 2, 5, 7, 13} ∨
        polygon = {1, 2, 5, 7, 10} ∨
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 5, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25774] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask28846 :
    (({1, 2, 3, 5, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 12, 13, 14}, {3, 7, 12, 13, 14}, {3, 5, 12, 13, 14}, {3, 5, 7, 13, 14}, {3, 5, 7, 12, 14}, {3, 5, 7, 12, 13}, {2, 7, 12, 13, 14}, {2, 5, 12, 13, 14}, {2, 5, 7, 13, 14}, {2, 5, 7, 12, 14}, {2, 5, 7, 12, 13}, {2, 3, 12, 13, 14}, {2, 3, 7, 13, 14}, {2, 3, 7, 12, 14}, {2, 3, 7, 12, 13}, {2, 3, 5, 13, 14}, {2, 3, 5, 12, 14}, {2, 3, 5, 12, 13}, {2, 3, 5, 7, 14}, {2, 3, 5, 7, 13}, {2, 3, 5, 7, 12}, {1, 7, 12, 13, 14}, {1, 5, 12, 13, 14}, {1, 5, 7, 13, 14}, {1, 5, 7, 12, 14}, {1, 5, 7, 12, 13}, {1, 3, 12, 13, 14}, {1, 3, 7, 13, 14}, {1, 3, 7, 12, 14}, {1, 3, 7, 12, 13}, {1, 3, 5, 13, 14}, {1, 3, 5, 12, 14}, {1, 3, 5, 12, 13}, {1, 3, 5, 7, 14}, {1, 3, 5, 7, 13}, {1, 3, 5, 7, 12}, {1, 2, 12, 13, 14}, {1, 2, 7, 13, 14}, {1, 2, 7, 12, 14}, {1, 2, 7, 12, 13}, {1, 2, 5, 13, 14}, {1, 2, 5, 12, 14}, {1, 2, 5, 12, 13}, {1, 2, 5, 7, 14}, {1, 2, 5, 7, 13}, {1, 2, 5, 7, 12}, {1, 2, 3, 13, 14}, {1, 2, 3, 12, 14}, {1, 2, 3, 12, 13}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 13}, {1, 2, 3, 7, 12}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask28846 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 5, 7, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 12, 13, 14} ∨
        polygon = {3, 7, 12, 13, 14} ∨
        polygon = {3, 5, 12, 13, 14} ∨
        polygon = {3, 5, 7, 13, 14} ∨
        polygon = {3, 5, 7, 12, 14} ∨
        polygon = {3, 5, 7, 12, 13} ∨
        polygon = {2, 7, 12, 13, 14} ∨
        polygon = {2, 5, 12, 13, 14} ∨
        polygon = {2, 5, 7, 13, 14} ∨
        polygon = {2, 5, 7, 12, 14} ∨
        polygon = {2, 5, 7, 12, 13} ∨
        polygon = {2, 3, 12, 13, 14} ∨
        polygon = {2, 3, 7, 13, 14} ∨
        polygon = {2, 3, 7, 12, 14} ∨
        polygon = {2, 3, 7, 12, 13} ∨
        polygon = {2, 3, 5, 13, 14} ∨
        polygon = {2, 3, 5, 12, 14} ∨
        polygon = {2, 3, 5, 12, 13} ∨
        polygon = {2, 3, 5, 7, 14} ∨
        polygon = {2, 3, 5, 7, 13} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {1, 7, 12, 13, 14} ∨
        polygon = {1, 5, 12, 13, 14} ∨
        polygon = {1, 5, 7, 13, 14} ∨
        polygon = {1, 5, 7, 12, 14} ∨
        polygon = {1, 5, 7, 12, 13} ∨
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
        polygon = {1, 2, 12, 13, 14} ∨
        polygon = {1, 2, 7, 13, 14} ∨
        polygon = {1, 2, 7, 12, 14} ∨
        polygon = {1, 2, 7, 12, 13} ∨
        polygon = {1, 2, 5, 13, 14} ∨
        polygon = {1, 2, 5, 12, 14} ∨
        polygon = {1, 2, 5, 12, 13} ∨
        polygon = {1, 2, 5, 7, 14} ∨
        polygon = {1, 2, 5, 7, 13} ∨
        polygon = {1, 2, 5, 7, 12} ∨
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 5, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask28846] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13614 :
    (({1, 2, 3, 5, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 8, 10, 12, 13}, {3, 8, 10, 12, 13}, {3, 5, 10, 12, 13}, {3, 5, 8, 12, 13}, {3, 5, 8, 10, 13}, {3, 5, 8, 10, 12}, {2, 8, 10, 12, 13}, {2, 5, 10, 12, 13}, {2, 5, 8, 12, 13}, {2, 5, 8, 10, 13}, {2, 5, 8, 10, 12}, {2, 3, 10, 12, 13}, {2, 3, 8, 12, 13}, {2, 3, 8, 10, 13}, {2, 3, 8, 10, 12}, {2, 3, 5, 12, 13}, {2, 3, 5, 10, 13}, {2, 3, 5, 10, 12}, {2, 3, 5, 8, 13}, {2, 3, 5, 8, 12}, {2, 3, 5, 8, 10}, {1, 8, 10, 12, 13}, {1, 5, 10, 12, 13}, {1, 5, 8, 12, 13}, {1, 5, 8, 10, 13}, {1, 5, 8, 10, 12}, {1, 3, 10, 12, 13}, {1, 3, 8, 12, 13}, {1, 3, 8, 10, 13}, {1, 3, 8, 10, 12}, {1, 3, 5, 12, 13}, {1, 3, 5, 10, 13}, {1, 3, 5, 10, 12}, {1, 3, 5, 8, 13}, {1, 3, 5, 8, 12}, {1, 3, 5, 8, 10}, {1, 2, 10, 12, 13}, {1, 2, 8, 12, 13}, {1, 2, 8, 10, 13}, {1, 2, 8, 10, 12}, {1, 2, 5, 12, 13}, {1, 2, 5, 10, 13}, {1, 2, 5, 10, 12}, {1, 2, 5, 8, 13}, {1, 2, 5, 8, 12}, {1, 2, 5, 8, 10}, {1, 2, 3, 12, 13}, {1, 2, 3, 10, 13}, {1, 2, 3, 10, 12}, {1, 2, 3, 8, 13}, {1, 2, 3, 8, 12}, {1, 2, 3, 8, 10}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13614 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 5, 8, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 8, 10, 12, 13} ∨
        polygon = {3, 8, 10, 12, 13} ∨
        polygon = {3, 5, 10, 12, 13} ∨
        polygon = {3, 5, 8, 12, 13} ∨
        polygon = {3, 5, 8, 10, 13} ∨
        polygon = {3, 5, 8, 10, 12} ∨
        polygon = {2, 8, 10, 12, 13} ∨
        polygon = {2, 5, 10, 12, 13} ∨
        polygon = {2, 5, 8, 12, 13} ∨
        polygon = {2, 5, 8, 10, 13} ∨
        polygon = {2, 5, 8, 10, 12} ∨
        polygon = {2, 3, 10, 12, 13} ∨
        polygon = {2, 3, 8, 12, 13} ∨
        polygon = {2, 3, 8, 10, 13} ∨
        polygon = {2, 3, 8, 10, 12} ∨
        polygon = {2, 3, 5, 12, 13} ∨
        polygon = {2, 3, 5, 10, 13} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 5, 8, 13} ∨
        polygon = {2, 3, 5, 8, 12} ∨
        polygon = {2, 3, 5, 8, 10} ∨
        polygon = {1, 8, 10, 12, 13} ∨
        polygon = {1, 5, 10, 12, 13} ∨
        polygon = {1, 5, 8, 12, 13} ∨
        polygon = {1, 5, 8, 10, 13} ∨
        polygon = {1, 5, 8, 10, 12} ∨
        polygon = {1, 3, 10, 12, 13} ∨
        polygon = {1, 3, 8, 12, 13} ∨
        polygon = {1, 3, 8, 10, 13} ∨
        polygon = {1, 3, 8, 10, 12} ∨
        polygon = {1, 3, 5, 12, 13} ∨
        polygon = {1, 3, 5, 10, 13} ∨
        polygon = {1, 3, 5, 10, 12} ∨
        polygon = {1, 3, 5, 8, 13} ∨
        polygon = {1, 3, 5, 8, 12} ∨
        polygon = {1, 3, 5, 8, 10} ∨
        polygon = {1, 2, 10, 12, 13} ∨
        polygon = {1, 2, 8, 12, 13} ∨
        polygon = {1, 2, 8, 10, 13} ∨
        polygon = {1, 2, 8, 10, 12} ∨
        polygon = {1, 2, 5, 12, 13} ∨
        polygon = {1, 2, 5, 10, 13} ∨
        polygon = {1, 2, 5, 10, 12} ∨
        polygon = {1, 2, 5, 8, 13} ∨
        polygon = {1, 2, 5, 8, 12} ∨
        polygon = {1, 2, 5, 8, 10} ∨
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 8, 13} ∨
        polygon = {1, 2, 3, 8, 12} ∨
        polygon = {1, 2, 3, 8, 10} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 5, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13614] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13870 :
    (({1, 2, 3, 5, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 10, 12, 13}, {3, 9, 10, 12, 13}, {3, 5, 10, 12, 13}, {3, 5, 9, 12, 13}, {3, 5, 9, 10, 13}, {3, 5, 9, 10, 12}, {2, 9, 10, 12, 13}, {2, 5, 10, 12, 13}, {2, 5, 9, 12, 13}, {2, 5, 9, 10, 13}, {2, 5, 9, 10, 12}, {2, 3, 10, 12, 13}, {2, 3, 9, 12, 13}, {2, 3, 9, 10, 13}, {2, 3, 9, 10, 12}, {2, 3, 5, 12, 13}, {2, 3, 5, 10, 13}, {2, 3, 5, 10, 12}, {2, 3, 5, 9, 13}, {2, 3, 5, 9, 12}, {2, 3, 5, 9, 10}, {1, 9, 10, 12, 13}, {1, 5, 10, 12, 13}, {1, 5, 9, 12, 13}, {1, 5, 9, 10, 13}, {1, 5, 9, 10, 12}, {1, 3, 10, 12, 13}, {1, 3, 9, 12, 13}, {1, 3, 9, 10, 13}, {1, 3, 9, 10, 12}, {1, 3, 5, 12, 13}, {1, 3, 5, 10, 13}, {1, 3, 5, 10, 12}, {1, 3, 5, 9, 13}, {1, 3, 5, 9, 12}, {1, 3, 5, 9, 10}, {1, 2, 10, 12, 13}, {1, 2, 9, 12, 13}, {1, 2, 9, 10, 13}, {1, 2, 9, 10, 12}, {1, 2, 5, 12, 13}, {1, 2, 5, 10, 13}, {1, 2, 5, 10, 12}, {1, 2, 5, 9, 13}, {1, 2, 5, 9, 12}, {1, 2, 5, 9, 10}, {1, 2, 3, 12, 13}, {1, 2, 3, 10, 13}, {1, 2, 3, 10, 12}, {1, 2, 3, 9, 13}, {1, 2, 3, 9, 12}, {1, 2, 3, 9, 10}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13870 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 5, 9, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 9, 10, 12, 13} ∨
        polygon = {3, 9, 10, 12, 13} ∨
        polygon = {3, 5, 10, 12, 13} ∨
        polygon = {3, 5, 9, 12, 13} ∨
        polygon = {3, 5, 9, 10, 13} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {2, 9, 10, 12, 13} ∨
        polygon = {2, 5, 10, 12, 13} ∨
        polygon = {2, 5, 9, 12, 13} ∨
        polygon = {2, 5, 9, 10, 13} ∨
        polygon = {2, 5, 9, 10, 12} ∨
        polygon = {2, 3, 10, 12, 13} ∨
        polygon = {2, 3, 9, 12, 13} ∨
        polygon = {2, 3, 9, 10, 13} ∨
        polygon = {2, 3, 9, 10, 12} ∨
        polygon = {2, 3, 5, 12, 13} ∨
        polygon = {2, 3, 5, 10, 13} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 5, 9, 13} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {1, 9, 10, 12, 13} ∨
        polygon = {1, 5, 10, 12, 13} ∨
        polygon = {1, 5, 9, 12, 13} ∨
        polygon = {1, 5, 9, 10, 13} ∨
        polygon = {1, 5, 9, 10, 12} ∨
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
        polygon = {1, 2, 10, 12, 13} ∨
        polygon = {1, 2, 9, 12, 13} ∨
        polygon = {1, 2, 9, 10, 13} ∨
        polygon = {1, 2, 9, 10, 12} ∨
        polygon = {1, 2, 5, 12, 13} ∨
        polygon = {1, 2, 5, 10, 13} ∨
        polygon = {1, 2, 5, 10, 12} ∨
        polygon = {1, 2, 5, 9, 13} ∨
        polygon = {1, 2, 5, 9, 12} ∨
        polygon = {1, 2, 5, 9, 10} ∨
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 5, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13870] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask22062 :
    (({1, 2, 3, 5, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 10, 12, 14}, {3, 9, 10, 12, 14}, {3, 5, 10, 12, 14}, {3, 5, 9, 12, 14}, {3, 5, 9, 10, 14}, {3, 5, 9, 10, 12}, {2, 9, 10, 12, 14}, {2, 5, 10, 12, 14}, {2, 5, 9, 12, 14}, {2, 5, 9, 10, 14}, {2, 5, 9, 10, 12}, {2, 3, 10, 12, 14}, {2, 3, 9, 12, 14}, {2, 3, 9, 10, 14}, {2, 3, 9, 10, 12}, {2, 3, 5, 12, 14}, {2, 3, 5, 10, 14}, {2, 3, 5, 10, 12}, {2, 3, 5, 9, 14}, {2, 3, 5, 9, 12}, {2, 3, 5, 9, 10}, {1, 9, 10, 12, 14}, {1, 5, 10, 12, 14}, {1, 5, 9, 12, 14}, {1, 5, 9, 10, 14}, {1, 5, 9, 10, 12}, {1, 3, 10, 12, 14}, {1, 3, 9, 12, 14}, {1, 3, 9, 10, 14}, {1, 3, 9, 10, 12}, {1, 3, 5, 12, 14}, {1, 3, 5, 10, 14}, {1, 3, 5, 10, 12}, {1, 3, 5, 9, 14}, {1, 3, 5, 9, 12}, {1, 3, 5, 9, 10}, {1, 2, 10, 12, 14}, {1, 2, 9, 12, 14}, {1, 2, 9, 10, 14}, {1, 2, 9, 10, 12}, {1, 2, 5, 12, 14}, {1, 2, 5, 10, 14}, {1, 2, 5, 10, 12}, {1, 2, 5, 9, 14}, {1, 2, 5, 9, 12}, {1, 2, 5, 9, 10}, {1, 2, 3, 12, 14}, {1, 2, 3, 10, 14}, {1, 2, 3, 10, 12}, {1, 2, 3, 9, 14}, {1, 2, 3, 9, 12}, {1, 2, 3, 9, 10}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask22062 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 5, 9, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {5, 9, 10, 12, 14} ∨
        polygon = {3, 9, 10, 12, 14} ∨
        polygon = {3, 5, 10, 12, 14} ∨
        polygon = {3, 5, 9, 12, 14} ∨
        polygon = {3, 5, 9, 10, 14} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {2, 9, 10, 12, 14} ∨
        polygon = {2, 5, 10, 12, 14} ∨
        polygon = {2, 5, 9, 12, 14} ∨
        polygon = {2, 5, 9, 10, 14} ∨
        polygon = {2, 5, 9, 10, 12} ∨
        polygon = {2, 3, 10, 12, 14} ∨
        polygon = {2, 3, 9, 12, 14} ∨
        polygon = {2, 3, 9, 10, 14} ∨
        polygon = {2, 3, 9, 10, 12} ∨
        polygon = {2, 3, 5, 12, 14} ∨
        polygon = {2, 3, 5, 10, 14} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 5, 9, 14} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {1, 9, 10, 12, 14} ∨
        polygon = {1, 5, 10, 12, 14} ∨
        polygon = {1, 5, 9, 12, 14} ∨
        polygon = {1, 5, 9, 10, 14} ∨
        polygon = {1, 5, 9, 10, 12} ∨
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
        polygon = {1, 2, 10, 12, 14} ∨
        polygon = {1, 2, 9, 12, 14} ∨
        polygon = {1, 2, 9, 10, 14} ∨
        polygon = {1, 2, 9, 10, 12} ∨
        polygon = {1, 2, 5, 12, 14} ∨
        polygon = {1, 2, 5, 10, 14} ∨
        polygon = {1, 2, 5, 10, 12} ∨
        polygon = {1, 2, 5, 9, 14} ∨
        polygon = {1, 2, 5, 9, 12} ∨
        polygon = {1, 2, 5, 9, 10} ∨
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 5, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask22062] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask26158 :
    (({1, 2, 3, 5, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 10, 13, 14}, {3, 9, 10, 13, 14}, {3, 5, 10, 13, 14}, {3, 5, 9, 13, 14}, {3, 5, 9, 10, 14}, {3, 5, 9, 10, 13}, {2, 9, 10, 13, 14}, {2, 5, 10, 13, 14}, {2, 5, 9, 13, 14}, {2, 5, 9, 10, 14}, {2, 5, 9, 10, 13}, {2, 3, 10, 13, 14}, {2, 3, 9, 13, 14}, {2, 3, 9, 10, 14}, {2, 3, 9, 10, 13}, {2, 3, 5, 13, 14}, {2, 3, 5, 10, 14}, {2, 3, 5, 10, 13}, {2, 3, 5, 9, 14}, {2, 3, 5, 9, 13}, {2, 3, 5, 9, 10}, {1, 9, 10, 13, 14}, {1, 5, 10, 13, 14}, {1, 5, 9, 13, 14}, {1, 5, 9, 10, 14}, {1, 5, 9, 10, 13}, {1, 3, 10, 13, 14}, {1, 3, 9, 13, 14}, {1, 3, 9, 10, 14}, {1, 3, 9, 10, 13}, {1, 3, 5, 13, 14}, {1, 3, 5, 10, 14}, {1, 3, 5, 10, 13}, {1, 3, 5, 9, 14}, {1, 3, 5, 9, 13}, {1, 3, 5, 9, 10}, {1, 2, 10, 13, 14}, {1, 2, 9, 13, 14}, {1, 2, 9, 10, 14}, {1, 2, 9, 10, 13}, {1, 2, 5, 13, 14}, {1, 2, 5, 10, 14}, {1, 2, 5, 10, 13}, {1, 2, 5, 9, 14}, {1, 2, 5, 9, 13}, {1, 2, 5, 9, 10}, {1, 2, 3, 13, 14}, {1, 2, 3, 10, 14}, {1, 2, 3, 10, 13}, {1, 2, 3, 9, 14}, {1, 2, 3, 9, 13}, {1, 2, 3, 9, 10}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26158 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 5, 9, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 9, 10, 13, 14} ∨
        polygon = {3, 9, 10, 13, 14} ∨
        polygon = {3, 5, 10, 13, 14} ∨
        polygon = {3, 5, 9, 13, 14} ∨
        polygon = {3, 5, 9, 10, 14} ∨
        polygon = {3, 5, 9, 10, 13} ∨
        polygon = {2, 9, 10, 13, 14} ∨
        polygon = {2, 5, 10, 13, 14} ∨
        polygon = {2, 5, 9, 13, 14} ∨
        polygon = {2, 5, 9, 10, 14} ∨
        polygon = {2, 5, 9, 10, 13} ∨
        polygon = {2, 3, 10, 13, 14} ∨
        polygon = {2, 3, 9, 13, 14} ∨
        polygon = {2, 3, 9, 10, 14} ∨
        polygon = {2, 3, 9, 10, 13} ∨
        polygon = {2, 3, 5, 13, 14} ∨
        polygon = {2, 3, 5, 10, 14} ∨
        polygon = {2, 3, 5, 10, 13} ∨
        polygon = {2, 3, 5, 9, 14} ∨
        polygon = {2, 3, 5, 9, 13} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {1, 9, 10, 13, 14} ∨
        polygon = {1, 5, 10, 13, 14} ∨
        polygon = {1, 5, 9, 13, 14} ∨
        polygon = {1, 5, 9, 10, 14} ∨
        polygon = {1, 5, 9, 10, 13} ∨
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
        polygon = {1, 2, 10, 13, 14} ∨
        polygon = {1, 2, 9, 13, 14} ∨
        polygon = {1, 2, 9, 10, 14} ∨
        polygon = {1, 2, 9, 10, 13} ∨
        polygon = {1, 2, 5, 13, 14} ∨
        polygon = {1, 2, 5, 10, 14} ∨
        polygon = {1, 2, 5, 10, 13} ∨
        polygon = {1, 2, 5, 9, 14} ∨
        polygon = {1, 2, 5, 9, 13} ∨
        polygon = {1, 2, 5, 9, 10} ∨
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 5, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26158] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29230 :
    (({1, 2, 3, 5, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 12, 13, 14}, {3, 9, 12, 13, 14}, {3, 5, 12, 13, 14}, {3, 5, 9, 13, 14}, {3, 5, 9, 12, 14}, {3, 5, 9, 12, 13}, {2, 9, 12, 13, 14}, {2, 5, 12, 13, 14}, {2, 5, 9, 13, 14}, {2, 5, 9, 12, 14}, {2, 5, 9, 12, 13}, {2, 3, 12, 13, 14}, {2, 3, 9, 13, 14}, {2, 3, 9, 12, 14}, {2, 3, 9, 12, 13}, {2, 3, 5, 13, 14}, {2, 3, 5, 12, 14}, {2, 3, 5, 12, 13}, {2, 3, 5, 9, 14}, {2, 3, 5, 9, 13}, {2, 3, 5, 9, 12}, {1, 9, 12, 13, 14}, {1, 5, 12, 13, 14}, {1, 5, 9, 13, 14}, {1, 5, 9, 12, 14}, {1, 5, 9, 12, 13}, {1, 3, 12, 13, 14}, {1, 3, 9, 13, 14}, {1, 3, 9, 12, 14}, {1, 3, 9, 12, 13}, {1, 3, 5, 13, 14}, {1, 3, 5, 12, 14}, {1, 3, 5, 12, 13}, {1, 3, 5, 9, 14}, {1, 3, 5, 9, 13}, {1, 3, 5, 9, 12}, {1, 2, 12, 13, 14}, {1, 2, 9, 13, 14}, {1, 2, 9, 12, 14}, {1, 2, 9, 12, 13}, {1, 2, 5, 13, 14}, {1, 2, 5, 12, 14}, {1, 2, 5, 12, 13}, {1, 2, 5, 9, 14}, {1, 2, 5, 9, 13}, {1, 2, 5, 9, 12}, {1, 2, 3, 13, 14}, {1, 2, 3, 12, 14}, {1, 2, 3, 12, 13}, {1, 2, 3, 9, 14}, {1, 2, 3, 9, 13}, {1, 2, 3, 9, 12}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29230 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 5, 9, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 9, 12, 13, 14} ∨
        polygon = {3, 9, 12, 13, 14} ∨
        polygon = {3, 5, 12, 13, 14} ∨
        polygon = {3, 5, 9, 13, 14} ∨
        polygon = {3, 5, 9, 12, 14} ∨
        polygon = {3, 5, 9, 12, 13} ∨
        polygon = {2, 9, 12, 13, 14} ∨
        polygon = {2, 5, 12, 13, 14} ∨
        polygon = {2, 5, 9, 13, 14} ∨
        polygon = {2, 5, 9, 12, 14} ∨
        polygon = {2, 5, 9, 12, 13} ∨
        polygon = {2, 3, 12, 13, 14} ∨
        polygon = {2, 3, 9, 13, 14} ∨
        polygon = {2, 3, 9, 12, 14} ∨
        polygon = {2, 3, 9, 12, 13} ∨
        polygon = {2, 3, 5, 13, 14} ∨
        polygon = {2, 3, 5, 12, 14} ∨
        polygon = {2, 3, 5, 12, 13} ∨
        polygon = {2, 3, 5, 9, 14} ∨
        polygon = {2, 3, 5, 9, 13} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {1, 9, 12, 13, 14} ∨
        polygon = {1, 5, 12, 13, 14} ∨
        polygon = {1, 5, 9, 13, 14} ∨
        polygon = {1, 5, 9, 12, 14} ∨
        polygon = {1, 5, 9, 12, 13} ∨
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
        polygon = {1, 2, 12, 13, 14} ∨
        polygon = {1, 2, 9, 13, 14} ∨
        polygon = {1, 2, 9, 12, 14} ∨
        polygon = {1, 2, 9, 12, 13} ∨
        polygon = {1, 2, 5, 13, 14} ∨
        polygon = {1, 2, 5, 12, 14} ∨
        polygon = {1, 2, 5, 12, 13} ∨
        polygon = {1, 2, 5, 9, 14} ∨
        polygon = {1, 2, 5, 9, 13} ∨
        polygon = {1, 2, 5, 9, 12} ∨
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 5, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29230] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29742 :
    (({1, 2, 3, 5, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 10, 12, 13, 14}, {3, 10, 12, 13, 14}, {3, 5, 12, 13, 14}, {3, 5, 10, 13, 14}, {3, 5, 10, 12, 14}, {3, 5, 10, 12, 13}, {2, 10, 12, 13, 14}, {2, 5, 12, 13, 14}, {2, 5, 10, 13, 14}, {2, 5, 10, 12, 14}, {2, 5, 10, 12, 13}, {2, 3, 12, 13, 14}, {2, 3, 10, 13, 14}, {2, 3, 10, 12, 14}, {2, 3, 10, 12, 13}, {2, 3, 5, 13, 14}, {2, 3, 5, 12, 14}, {2, 3, 5, 12, 13}, {2, 3, 5, 10, 14}, {2, 3, 5, 10, 13}, {2, 3, 5, 10, 12}, {1, 10, 12, 13, 14}, {1, 5, 12, 13, 14}, {1, 5, 10, 13, 14}, {1, 5, 10, 12, 14}, {1, 5, 10, 12, 13}, {1, 3, 12, 13, 14}, {1, 3, 10, 13, 14}, {1, 3, 10, 12, 14}, {1, 3, 10, 12, 13}, {1, 3, 5, 13, 14}, {1, 3, 5, 12, 14}, {1, 3, 5, 12, 13}, {1, 3, 5, 10, 14}, {1, 3, 5, 10, 13}, {1, 3, 5, 10, 12}, {1, 2, 12, 13, 14}, {1, 2, 10, 13, 14}, {1, 2, 10, 12, 14}, {1, 2, 10, 12, 13}, {1, 2, 5, 13, 14}, {1, 2, 5, 12, 14}, {1, 2, 5, 12, 13}, {1, 2, 5, 10, 14}, {1, 2, 5, 10, 13}, {1, 2, 5, 10, 12}, {1, 2, 3, 13, 14}, {1, 2, 3, 12, 14}, {1, 2, 3, 12, 13}, {1, 2, 3, 10, 14}, {1, 2, 3, 10, 13}, {1, 2, 3, 10, 12}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29742 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 5, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 10, 12, 13, 14} ∨
        polygon = {3, 10, 12, 13, 14} ∨
        polygon = {3, 5, 12, 13, 14} ∨
        polygon = {3, 5, 10, 13, 14} ∨
        polygon = {3, 5, 10, 12, 14} ∨
        polygon = {3, 5, 10, 12, 13} ∨
        polygon = {2, 10, 12, 13, 14} ∨
        polygon = {2, 5, 12, 13, 14} ∨
        polygon = {2, 5, 10, 13, 14} ∨
        polygon = {2, 5, 10, 12, 14} ∨
        polygon = {2, 5, 10, 12, 13} ∨
        polygon = {2, 3, 12, 13, 14} ∨
        polygon = {2, 3, 10, 13, 14} ∨
        polygon = {2, 3, 10, 12, 14} ∨
        polygon = {2, 3, 10, 12, 13} ∨
        polygon = {2, 3, 5, 13, 14} ∨
        polygon = {2, 3, 5, 12, 14} ∨
        polygon = {2, 3, 5, 12, 13} ∨
        polygon = {2, 3, 5, 10, 14} ∨
        polygon = {2, 3, 5, 10, 13} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {1, 10, 12, 13, 14} ∨
        polygon = {1, 5, 12, 13, 14} ∨
        polygon = {1, 5, 10, 13, 14} ∨
        polygon = {1, 5, 10, 12, 14} ∨
        polygon = {1, 5, 10, 12, 13} ∨
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
        polygon = {1, 2, 12, 13, 14} ∨
        polygon = {1, 2, 10, 13, 14} ∨
        polygon = {1, 2, 10, 12, 14} ∨
        polygon = {1, 2, 10, 12, 13} ∨
        polygon = {1, 2, 5, 13, 14} ∨
        polygon = {1, 2, 5, 12, 14} ∨
        polygon = {1, 2, 5, 12, 13} ∨
        polygon = {1, 2, 5, 10, 14} ∨
        polygon = {1, 2, 5, 10, 13} ∨
        polygon = {1, 2, 5, 10, 12} ∨
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 5, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29742] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05838 :
    (({1, 2, 3, 6, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 12}, {3, 7, 9, 10, 12}, {3, 6, 9, 10, 12}, {3, 6, 7, 10, 12}, {3, 6, 7, 9, 12}, {3, 6, 7, 9, 10}, {2, 7, 9, 10, 12}, {2, 6, 9, 10, 12}, {2, 6, 7, 10, 12}, {2, 6, 7, 9, 12}, {2, 6, 7, 9, 10}, {2, 3, 9, 10, 12}, {2, 3, 7, 10, 12}, {2, 3, 7, 9, 12}, {2, 3, 7, 9, 10}, {2, 3, 6, 10, 12}, {2, 3, 6, 9, 12}, {2, 3, 6, 9, 10}, {2, 3, 6, 7, 12}, {2, 3, 6, 7, 10}, {2, 3, 6, 7, 9}, {1, 7, 9, 10, 12}, {1, 6, 9, 10, 12}, {1, 6, 7, 10, 12}, {1, 6, 7, 9, 12}, {1, 6, 7, 9, 10}, {1, 3, 9, 10, 12}, {1, 3, 7, 10, 12}, {1, 3, 7, 9, 12}, {1, 3, 7, 9, 10}, {1, 3, 6, 10, 12}, {1, 3, 6, 9, 12}, {1, 3, 6, 9, 10}, {1, 3, 6, 7, 12}, {1, 3, 6, 7, 10}, {1, 3, 6, 7, 9}, {1, 2, 9, 10, 12}, {1, 2, 7, 10, 12}, {1, 2, 7, 9, 12}, {1, 2, 7, 9, 10}, {1, 2, 6, 10, 12}, {1, 2, 6, 9, 12}, {1, 2, 6, 9, 10}, {1, 2, 6, 7, 12}, {1, 2, 6, 7, 10}, {1, 2, 6, 7, 9}, {1, 2, 3, 10, 12}, {1, 2, 3, 9, 12}, {1, 2, 3, 9, 10}, {1, 2, 3, 7, 12}, {1, 2, 3, 7, 10}, {1, 2, 3, 7, 9}, {1, 2, 3, 6, 12}, {1, 2, 3, 6, 10}, {1, 2, 3, 6, 9}, {1, 2, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05838 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 6, 7, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 10, 12} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {2, 7, 9, 10, 12} ∨
        polygon = {2, 6, 9, 10, 12} ∨
        polygon = {2, 6, 7, 10, 12} ∨
        polygon = {2, 6, 7, 9, 12} ∨
        polygon = {2, 6, 7, 9, 10} ∨
        polygon = {2, 3, 9, 10, 12} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 3, 6, 10, 12} ∨
        polygon = {2, 3, 6, 9, 12} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {2, 3, 6, 7, 12} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {1, 7, 9, 10, 12} ∨
        polygon = {1, 6, 9, 10, 12} ∨
        polygon = {1, 6, 7, 10, 12} ∨
        polygon = {1, 6, 7, 9, 12} ∨
        polygon = {1, 6, 7, 9, 10} ∨
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
        polygon = {1, 2, 9, 10, 12} ∨
        polygon = {1, 2, 7, 10, 12} ∨
        polygon = {1, 2, 7, 9, 12} ∨
        polygon = {1, 2, 7, 9, 10} ∨
        polygon = {1, 2, 6, 10, 12} ∨
        polygon = {1, 2, 6, 9, 12} ∨
        polygon = {1, 2, 6, 9, 10} ∨
        polygon = {1, 2, 6, 7, 12} ∨
        polygon = {1, 2, 6, 7, 10} ∨
        polygon = {1, 2, 6, 7, 9} ∨
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {1, 2, 3, 6, 9} ∨
        polygon = {1, 2, 3, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 6, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05838] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09934 :
    (({1, 2, 3, 6, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 13}, {3, 7, 9, 10, 13}, {3, 6, 9, 10, 13}, {3, 6, 7, 10, 13}, {3, 6, 7, 9, 13}, {3, 6, 7, 9, 10}, {2, 7, 9, 10, 13}, {2, 6, 9, 10, 13}, {2, 6, 7, 10, 13}, {2, 6, 7, 9, 13}, {2, 6, 7, 9, 10}, {2, 3, 9, 10, 13}, {2, 3, 7, 10, 13}, {2, 3, 7, 9, 13}, {2, 3, 7, 9, 10}, {2, 3, 6, 10, 13}, {2, 3, 6, 9, 13}, {2, 3, 6, 9, 10}, {2, 3, 6, 7, 13}, {2, 3, 6, 7, 10}, {2, 3, 6, 7, 9}, {1, 7, 9, 10, 13}, {1, 6, 9, 10, 13}, {1, 6, 7, 10, 13}, {1, 6, 7, 9, 13}, {1, 6, 7, 9, 10}, {1, 3, 9, 10, 13}, {1, 3, 7, 10, 13}, {1, 3, 7, 9, 13}, {1, 3, 7, 9, 10}, {1, 3, 6, 10, 13}, {1, 3, 6, 9, 13}, {1, 3, 6, 9, 10}, {1, 3, 6, 7, 13}, {1, 3, 6, 7, 10}, {1, 3, 6, 7, 9}, {1, 2, 9, 10, 13}, {1, 2, 7, 10, 13}, {1, 2, 7, 9, 13}, {1, 2, 7, 9, 10}, {1, 2, 6, 10, 13}, {1, 2, 6, 9, 13}, {1, 2, 6, 9, 10}, {1, 2, 6, 7, 13}, {1, 2, 6, 7, 10}, {1, 2, 6, 7, 9}, {1, 2, 3, 10, 13}, {1, 2, 3, 9, 13}, {1, 2, 3, 9, 10}, {1, 2, 3, 7, 13}, {1, 2, 3, 7, 10}, {1, 2, 3, 7, 9}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 10}, {1, 2, 3, 6, 9}, {1, 2, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09934 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 6, 7, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 10, 13} ∨
        polygon = {3, 7, 9, 10, 13} ∨
        polygon = {3, 6, 9, 10, 13} ∨
        polygon = {3, 6, 7, 10, 13} ∨
        polygon = {3, 6, 7, 9, 13} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {2, 7, 9, 10, 13} ∨
        polygon = {2, 6, 9, 10, 13} ∨
        polygon = {2, 6, 7, 10, 13} ∨
        polygon = {2, 6, 7, 9, 13} ∨
        polygon = {2, 6, 7, 9, 10} ∨
        polygon = {2, 3, 9, 10, 13} ∨
        polygon = {2, 3, 7, 10, 13} ∨
        polygon = {2, 3, 7, 9, 13} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 3, 6, 10, 13} ∨
        polygon = {2, 3, 6, 9, 13} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {2, 3, 6, 7, 13} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {1, 7, 9, 10, 13} ∨
        polygon = {1, 6, 9, 10, 13} ∨
        polygon = {1, 6, 7, 10, 13} ∨
        polygon = {1, 6, 7, 9, 13} ∨
        polygon = {1, 6, 7, 9, 10} ∨
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
        polygon = {1, 2, 9, 10, 13} ∨
        polygon = {1, 2, 7, 10, 13} ∨
        polygon = {1, 2, 7, 9, 13} ∨
        polygon = {1, 2, 7, 9, 10} ∨
        polygon = {1, 2, 6, 10, 13} ∨
        polygon = {1, 2, 6, 9, 13} ∨
        polygon = {1, 2, 6, 9, 10} ∨
        polygon = {1, 2, 6, 7, 13} ∨
        polygon = {1, 2, 6, 7, 10} ∨
        polygon = {1, 2, 6, 7, 9} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {1, 2, 3, 6, 9} ∨
        polygon = {1, 2, 3, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 6, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09934] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask18126 :
    (({1, 2, 3, 6, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 14}, {3, 7, 9, 10, 14}, {3, 6, 9, 10, 14}, {3, 6, 7, 10, 14}, {3, 6, 7, 9, 14}, {3, 6, 7, 9, 10}, {2, 7, 9, 10, 14}, {2, 6, 9, 10, 14}, {2, 6, 7, 10, 14}, {2, 6, 7, 9, 14}, {2, 6, 7, 9, 10}, {2, 3, 9, 10, 14}, {2, 3, 7, 10, 14}, {2, 3, 7, 9, 14}, {2, 3, 7, 9, 10}, {2, 3, 6, 10, 14}, {2, 3, 6, 9, 14}, {2, 3, 6, 9, 10}, {2, 3, 6, 7, 14}, {2, 3, 6, 7, 10}, {2, 3, 6, 7, 9}, {1, 7, 9, 10, 14}, {1, 6, 9, 10, 14}, {1, 6, 7, 10, 14}, {1, 6, 7, 9, 14}, {1, 6, 7, 9, 10}, {1, 3, 9, 10, 14}, {1, 3, 7, 10, 14}, {1, 3, 7, 9, 14}, {1, 3, 7, 9, 10}, {1, 3, 6, 10, 14}, {1, 3, 6, 9, 14}, {1, 3, 6, 9, 10}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 10}, {1, 3, 6, 7, 9}, {1, 2, 9, 10, 14}, {1, 2, 7, 10, 14}, {1, 2, 7, 9, 14}, {1, 2, 7, 9, 10}, {1, 2, 6, 10, 14}, {1, 2, 6, 9, 14}, {1, 2, 6, 9, 10}, {1, 2, 6, 7, 14}, {1, 2, 6, 7, 10}, {1, 2, 6, 7, 9}, {1, 2, 3, 10, 14}, {1, 2, 3, 9, 14}, {1, 2, 3, 9, 10}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 10}, {1, 2, 3, 7, 9}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 10}, {1, 2, 3, 6, 9}, {1, 2, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask18126 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 6, 7, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 10, 14} ∨
        polygon = {3, 7, 9, 10, 14} ∨
        polygon = {3, 6, 9, 10, 14} ∨
        polygon = {3, 6, 7, 10, 14} ∨
        polygon = {3, 6, 7, 9, 14} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {2, 7, 9, 10, 14} ∨
        polygon = {2, 6, 9, 10, 14} ∨
        polygon = {2, 6, 7, 10, 14} ∨
        polygon = {2, 6, 7, 9, 14} ∨
        polygon = {2, 6, 7, 9, 10} ∨
        polygon = {2, 3, 9, 10, 14} ∨
        polygon = {2, 3, 7, 10, 14} ∨
        polygon = {2, 3, 7, 9, 14} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 3, 6, 10, 14} ∨
        polygon = {2, 3, 6, 9, 14} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {2, 3, 6, 7, 14} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {1, 7, 9, 10, 14} ∨
        polygon = {1, 6, 9, 10, 14} ∨
        polygon = {1, 6, 7, 10, 14} ∨
        polygon = {1, 6, 7, 9, 14} ∨
        polygon = {1, 6, 7, 9, 10} ∨
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
        polygon = {1, 2, 9, 10, 14} ∨
        polygon = {1, 2, 7, 10, 14} ∨
        polygon = {1, 2, 7, 9, 14} ∨
        polygon = {1, 2, 7, 9, 10} ∨
        polygon = {1, 2, 6, 10, 14} ∨
        polygon = {1, 2, 6, 9, 14} ∨
        polygon = {1, 2, 6, 9, 10} ∨
        polygon = {1, 2, 6, 7, 14} ∨
        polygon = {1, 2, 6, 7, 10} ∨
        polygon = {1, 2, 6, 7, 9} ∨
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {1, 2, 3, 6, 9} ∨
        polygon = {1, 2, 3, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 6, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask18126] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13006 :
    (({1, 2, 3, 6, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 12, 13}, {3, 7, 9, 12, 13}, {3, 6, 9, 12, 13}, {3, 6, 7, 12, 13}, {3, 6, 7, 9, 13}, {3, 6, 7, 9, 12}, {2, 7, 9, 12, 13}, {2, 6, 9, 12, 13}, {2, 6, 7, 12, 13}, {2, 6, 7, 9, 13}, {2, 6, 7, 9, 12}, {2, 3, 9, 12, 13}, {2, 3, 7, 12, 13}, {2, 3, 7, 9, 13}, {2, 3, 7, 9, 12}, {2, 3, 6, 12, 13}, {2, 3, 6, 9, 13}, {2, 3, 6, 9, 12}, {2, 3, 6, 7, 13}, {2, 3, 6, 7, 12}, {2, 3, 6, 7, 9}, {1, 7, 9, 12, 13}, {1, 6, 9, 12, 13}, {1, 6, 7, 12, 13}, {1, 6, 7, 9, 13}, {1, 6, 7, 9, 12}, {1, 3, 9, 12, 13}, {1, 3, 7, 12, 13}, {1, 3, 7, 9, 13}, {1, 3, 7, 9, 12}, {1, 3, 6, 12, 13}, {1, 3, 6, 9, 13}, {1, 3, 6, 9, 12}, {1, 3, 6, 7, 13}, {1, 3, 6, 7, 12}, {1, 3, 6, 7, 9}, {1, 2, 9, 12, 13}, {1, 2, 7, 12, 13}, {1, 2, 7, 9, 13}, {1, 2, 7, 9, 12}, {1, 2, 6, 12, 13}, {1, 2, 6, 9, 13}, {1, 2, 6, 9, 12}, {1, 2, 6, 7, 13}, {1, 2, 6, 7, 12}, {1, 2, 6, 7, 9}, {1, 2, 3, 12, 13}, {1, 2, 3, 9, 13}, {1, 2, 3, 9, 12}, {1, 2, 3, 7, 13}, {1, 2, 3, 7, 12}, {1, 2, 3, 7, 9}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 12}, {1, 2, 3, 6, 9}, {1, 2, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13006 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 6, 7, 9, 12, 13} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 12, 13} ∨
        polygon = {3, 7, 9, 12, 13} ∨
        polygon = {3, 6, 9, 12, 13} ∨
        polygon = {3, 6, 7, 12, 13} ∨
        polygon = {3, 6, 7, 9, 13} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {2, 7, 9, 12, 13} ∨
        polygon = {2, 6, 9, 12, 13} ∨
        polygon = {2, 6, 7, 12, 13} ∨
        polygon = {2, 6, 7, 9, 13} ∨
        polygon = {2, 6, 7, 9, 12} ∨
        polygon = {2, 3, 9, 12, 13} ∨
        polygon = {2, 3, 7, 12, 13} ∨
        polygon = {2, 3, 7, 9, 13} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 3, 6, 12, 13} ∨
        polygon = {2, 3, 6, 9, 13} ∨
        polygon = {2, 3, 6, 9, 12} ∨
        polygon = {2, 3, 6, 7, 13} ∨
        polygon = {2, 3, 6, 7, 12} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {1, 7, 9, 12, 13} ∨
        polygon = {1, 6, 9, 12, 13} ∨
        polygon = {1, 6, 7, 12, 13} ∨
        polygon = {1, 6, 7, 9, 13} ∨
        polygon = {1, 6, 7, 9, 12} ∨
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
        polygon = {1, 2, 9, 12, 13} ∨
        polygon = {1, 2, 7, 12, 13} ∨
        polygon = {1, 2, 7, 9, 13} ∨
        polygon = {1, 2, 7, 9, 12} ∨
        polygon = {1, 2, 6, 12, 13} ∨
        polygon = {1, 2, 6, 9, 13} ∨
        polygon = {1, 2, 6, 9, 12} ∨
        polygon = {1, 2, 6, 7, 13} ∨
        polygon = {1, 2, 6, 7, 12} ∨
        polygon = {1, 2, 6, 7, 9} ∨
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {1, 2, 3, 6, 9} ∨
        polygon = {1, 2, 3, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 6, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13006] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21198 :
    (({1, 2, 3, 6, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 12, 14}, {3, 7, 9, 12, 14}, {3, 6, 9, 12, 14}, {3, 6, 7, 12, 14}, {3, 6, 7, 9, 14}, {3, 6, 7, 9, 12}, {2, 7, 9, 12, 14}, {2, 6, 9, 12, 14}, {2, 6, 7, 12, 14}, {2, 6, 7, 9, 14}, {2, 6, 7, 9, 12}, {2, 3, 9, 12, 14}, {2, 3, 7, 12, 14}, {2, 3, 7, 9, 14}, {2, 3, 7, 9, 12}, {2, 3, 6, 12, 14}, {2, 3, 6, 9, 14}, {2, 3, 6, 9, 12}, {2, 3, 6, 7, 14}, {2, 3, 6, 7, 12}, {2, 3, 6, 7, 9}, {1, 7, 9, 12, 14}, {1, 6, 9, 12, 14}, {1, 6, 7, 12, 14}, {1, 6, 7, 9, 14}, {1, 6, 7, 9, 12}, {1, 3, 9, 12, 14}, {1, 3, 7, 12, 14}, {1, 3, 7, 9, 14}, {1, 3, 7, 9, 12}, {1, 3, 6, 12, 14}, {1, 3, 6, 9, 14}, {1, 3, 6, 9, 12}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 12}, {1, 3, 6, 7, 9}, {1, 2, 9, 12, 14}, {1, 2, 7, 12, 14}, {1, 2, 7, 9, 14}, {1, 2, 7, 9, 12}, {1, 2, 6, 12, 14}, {1, 2, 6, 9, 14}, {1, 2, 6, 9, 12}, {1, 2, 6, 7, 14}, {1, 2, 6, 7, 12}, {1, 2, 6, 7, 9}, {1, 2, 3, 12, 14}, {1, 2, 3, 9, 14}, {1, 2, 3, 9, 12}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 12}, {1, 2, 3, 7, 9}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 12}, {1, 2, 3, 6, 9}, {1, 2, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21198 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 6, 7, 9, 12, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 12, 14} ∨
        polygon = {3, 7, 9, 12, 14} ∨
        polygon = {3, 6, 9, 12, 14} ∨
        polygon = {3, 6, 7, 12, 14} ∨
        polygon = {3, 6, 7, 9, 14} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {2, 7, 9, 12, 14} ∨
        polygon = {2, 6, 9, 12, 14} ∨
        polygon = {2, 6, 7, 12, 14} ∨
        polygon = {2, 6, 7, 9, 14} ∨
        polygon = {2, 6, 7, 9, 12} ∨
        polygon = {2, 3, 9, 12, 14} ∨
        polygon = {2, 3, 7, 12, 14} ∨
        polygon = {2, 3, 7, 9, 14} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 3, 6, 12, 14} ∨
        polygon = {2, 3, 6, 9, 14} ∨
        polygon = {2, 3, 6, 9, 12} ∨
        polygon = {2, 3, 6, 7, 14} ∨
        polygon = {2, 3, 6, 7, 12} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {1, 7, 9, 12, 14} ∨
        polygon = {1, 6, 9, 12, 14} ∨
        polygon = {1, 6, 7, 12, 14} ∨
        polygon = {1, 6, 7, 9, 14} ∨
        polygon = {1, 6, 7, 9, 12} ∨
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
        polygon = {1, 2, 9, 12, 14} ∨
        polygon = {1, 2, 7, 12, 14} ∨
        polygon = {1, 2, 7, 9, 14} ∨
        polygon = {1, 2, 7, 9, 12} ∨
        polygon = {1, 2, 6, 12, 14} ∨
        polygon = {1, 2, 6, 9, 14} ∨
        polygon = {1, 2, 6, 9, 12} ∨
        polygon = {1, 2, 6, 7, 14} ∨
        polygon = {1, 2, 6, 7, 12} ∨
        polygon = {1, 2, 6, 7, 9} ∨
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {1, 2, 3, 6, 9} ∨
        polygon = {1, 2, 3, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 6, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21198] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25294 :
    (({1, 2, 3, 6, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 13, 14}, {3, 7, 9, 13, 14}, {3, 6, 9, 13, 14}, {3, 6, 7, 13, 14}, {3, 6, 7, 9, 14}, {3, 6, 7, 9, 13}, {2, 7, 9, 13, 14}, {2, 6, 9, 13, 14}, {2, 6, 7, 13, 14}, {2, 6, 7, 9, 14}, {2, 6, 7, 9, 13}, {2, 3, 9, 13, 14}, {2, 3, 7, 13, 14}, {2, 3, 7, 9, 14}, {2, 3, 7, 9, 13}, {2, 3, 6, 13, 14}, {2, 3, 6, 9, 14}, {2, 3, 6, 9, 13}, {2, 3, 6, 7, 14}, {2, 3, 6, 7, 13}, {2, 3, 6, 7, 9}, {1, 7, 9, 13, 14}, {1, 6, 9, 13, 14}, {1, 6, 7, 13, 14}, {1, 6, 7, 9, 14}, {1, 6, 7, 9, 13}, {1, 3, 9, 13, 14}, {1, 3, 7, 13, 14}, {1, 3, 7, 9, 14}, {1, 3, 7, 9, 13}, {1, 3, 6, 13, 14}, {1, 3, 6, 9, 14}, {1, 3, 6, 9, 13}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 13}, {1, 3, 6, 7, 9}, {1, 2, 9, 13, 14}, {1, 2, 7, 13, 14}, {1, 2, 7, 9, 14}, {1, 2, 7, 9, 13}, {1, 2, 6, 13, 14}, {1, 2, 6, 9, 14}, {1, 2, 6, 9, 13}, {1, 2, 6, 7, 14}, {1, 2, 6, 7, 13}, {1, 2, 6, 7, 9}, {1, 2, 3, 13, 14}, {1, 2, 3, 9, 14}, {1, 2, 3, 9, 13}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 13}, {1, 2, 3, 7, 9}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 9}, {1, 2, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25294 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 6, 7, 9, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 13, 14} ∨
        polygon = {3, 7, 9, 13, 14} ∨
        polygon = {3, 6, 9, 13, 14} ∨
        polygon = {3, 6, 7, 13, 14} ∨
        polygon = {3, 6, 7, 9, 14} ∨
        polygon = {3, 6, 7, 9, 13} ∨
        polygon = {2, 7, 9, 13, 14} ∨
        polygon = {2, 6, 9, 13, 14} ∨
        polygon = {2, 6, 7, 13, 14} ∨
        polygon = {2, 6, 7, 9, 14} ∨
        polygon = {2, 6, 7, 9, 13} ∨
        polygon = {2, 3, 9, 13, 14} ∨
        polygon = {2, 3, 7, 13, 14} ∨
        polygon = {2, 3, 7, 9, 14} ∨
        polygon = {2, 3, 7, 9, 13} ∨
        polygon = {2, 3, 6, 13, 14} ∨
        polygon = {2, 3, 6, 9, 14} ∨
        polygon = {2, 3, 6, 9, 13} ∨
        polygon = {2, 3, 6, 7, 14} ∨
        polygon = {2, 3, 6, 7, 13} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {1, 7, 9, 13, 14} ∨
        polygon = {1, 6, 9, 13, 14} ∨
        polygon = {1, 6, 7, 13, 14} ∨
        polygon = {1, 6, 7, 9, 14} ∨
        polygon = {1, 6, 7, 9, 13} ∨
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
        polygon = {1, 2, 9, 13, 14} ∨
        polygon = {1, 2, 7, 13, 14} ∨
        polygon = {1, 2, 7, 9, 14} ∨
        polygon = {1, 2, 7, 9, 13} ∨
        polygon = {1, 2, 6, 13, 14} ∨
        polygon = {1, 2, 6, 9, 14} ∨
        polygon = {1, 2, 6, 9, 13} ∨
        polygon = {1, 2, 6, 7, 14} ∨
        polygon = {1, 2, 6, 7, 13} ∨
        polygon = {1, 2, 6, 7, 9} ∨
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 6, 9} ∨
        polygon = {1, 2, 3, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 6, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25294] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13518 :
    (({1, 2, 3, 6, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 12, 13}, {3, 7, 10, 12, 13}, {3, 6, 10, 12, 13}, {3, 6, 7, 12, 13}, {3, 6, 7, 10, 13}, {3, 6, 7, 10, 12}, {2, 7, 10, 12, 13}, {2, 6, 10, 12, 13}, {2, 6, 7, 12, 13}, {2, 6, 7, 10, 13}, {2, 6, 7, 10, 12}, {2, 3, 10, 12, 13}, {2, 3, 7, 12, 13}, {2, 3, 7, 10, 13}, {2, 3, 7, 10, 12}, {2, 3, 6, 12, 13}, {2, 3, 6, 10, 13}, {2, 3, 6, 10, 12}, {2, 3, 6, 7, 13}, {2, 3, 6, 7, 12}, {2, 3, 6, 7, 10}, {1, 7, 10, 12, 13}, {1, 6, 10, 12, 13}, {1, 6, 7, 12, 13}, {1, 6, 7, 10, 13}, {1, 6, 7, 10, 12}, {1, 3, 10, 12, 13}, {1, 3, 7, 12, 13}, {1, 3, 7, 10, 13}, {1, 3, 7, 10, 12}, {1, 3, 6, 12, 13}, {1, 3, 6, 10, 13}, {1, 3, 6, 10, 12}, {1, 3, 6, 7, 13}, {1, 3, 6, 7, 12}, {1, 3, 6, 7, 10}, {1, 2, 10, 12, 13}, {1, 2, 7, 12, 13}, {1, 2, 7, 10, 13}, {1, 2, 7, 10, 12}, {1, 2, 6, 12, 13}, {1, 2, 6, 10, 13}, {1, 2, 6, 10, 12}, {1, 2, 6, 7, 13}, {1, 2, 6, 7, 12}, {1, 2, 6, 7, 10}, {1, 2, 3, 12, 13}, {1, 2, 3, 10, 13}, {1, 2, 3, 10, 12}, {1, 2, 3, 7, 13}, {1, 2, 3, 7, 12}, {1, 2, 3, 7, 10}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 12}, {1, 2, 3, 6, 10}, {1, 2, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13518 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 6, 7, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {6, 7, 10, 12, 13} ∨
        polygon = {3, 7, 10, 12, 13} ∨
        polygon = {3, 6, 10, 12, 13} ∨
        polygon = {3, 6, 7, 12, 13} ∨
        polygon = {3, 6, 7, 10, 13} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {2, 7, 10, 12, 13} ∨
        polygon = {2, 6, 10, 12, 13} ∨
        polygon = {2, 6, 7, 12, 13} ∨
        polygon = {2, 6, 7, 10, 13} ∨
        polygon = {2, 6, 7, 10, 12} ∨
        polygon = {2, 3, 10, 12, 13} ∨
        polygon = {2, 3, 7, 12, 13} ∨
        polygon = {2, 3, 7, 10, 13} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {2, 3, 6, 12, 13} ∨
        polygon = {2, 3, 6, 10, 13} ∨
        polygon = {2, 3, 6, 10, 12} ∨
        polygon = {2, 3, 6, 7, 13} ∨
        polygon = {2, 3, 6, 7, 12} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {1, 7, 10, 12, 13} ∨
        polygon = {1, 6, 10, 12, 13} ∨
        polygon = {1, 6, 7, 12, 13} ∨
        polygon = {1, 6, 7, 10, 13} ∨
        polygon = {1, 6, 7, 10, 12} ∨
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
        polygon = {1, 2, 10, 12, 13} ∨
        polygon = {1, 2, 7, 12, 13} ∨
        polygon = {1, 2, 7, 10, 13} ∨
        polygon = {1, 2, 7, 10, 12} ∨
        polygon = {1, 2, 6, 12, 13} ∨
        polygon = {1, 2, 6, 10, 13} ∨
        polygon = {1, 2, 6, 10, 12} ∨
        polygon = {1, 2, 6, 7, 13} ∨
        polygon = {1, 2, 6, 7, 12} ∨
        polygon = {1, 2, 6, 7, 10} ∨
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {1, 2, 3, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 6, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13518] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21710 :
    (({1, 2, 3, 6, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 12, 14}, {3, 7, 10, 12, 14}, {3, 6, 10, 12, 14}, {3, 6, 7, 12, 14}, {3, 6, 7, 10, 14}, {3, 6, 7, 10, 12}, {2, 7, 10, 12, 14}, {2, 6, 10, 12, 14}, {2, 6, 7, 12, 14}, {2, 6, 7, 10, 14}, {2, 6, 7, 10, 12}, {2, 3, 10, 12, 14}, {2, 3, 7, 12, 14}, {2, 3, 7, 10, 14}, {2, 3, 7, 10, 12}, {2, 3, 6, 12, 14}, {2, 3, 6, 10, 14}, {2, 3, 6, 10, 12}, {2, 3, 6, 7, 14}, {2, 3, 6, 7, 12}, {2, 3, 6, 7, 10}, {1, 7, 10, 12, 14}, {1, 6, 10, 12, 14}, {1, 6, 7, 12, 14}, {1, 6, 7, 10, 14}, {1, 6, 7, 10, 12}, {1, 3, 10, 12, 14}, {1, 3, 7, 12, 14}, {1, 3, 7, 10, 14}, {1, 3, 7, 10, 12}, {1, 3, 6, 12, 14}, {1, 3, 6, 10, 14}, {1, 3, 6, 10, 12}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 12}, {1, 3, 6, 7, 10}, {1, 2, 10, 12, 14}, {1, 2, 7, 12, 14}, {1, 2, 7, 10, 14}, {1, 2, 7, 10, 12}, {1, 2, 6, 12, 14}, {1, 2, 6, 10, 14}, {1, 2, 6, 10, 12}, {1, 2, 6, 7, 14}, {1, 2, 6, 7, 12}, {1, 2, 6, 7, 10}, {1, 2, 3, 12, 14}, {1, 2, 3, 10, 14}, {1, 2, 3, 10, 12}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 12}, {1, 2, 3, 7, 10}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 12}, {1, 2, 3, 6, 10}, {1, 2, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21710 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 6, 7, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 10, 12, 14} ∨
        polygon = {3, 7, 10, 12, 14} ∨
        polygon = {3, 6, 10, 12, 14} ∨
        polygon = {3, 6, 7, 12, 14} ∨
        polygon = {3, 6, 7, 10, 14} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {2, 7, 10, 12, 14} ∨
        polygon = {2, 6, 10, 12, 14} ∨
        polygon = {2, 6, 7, 12, 14} ∨
        polygon = {2, 6, 7, 10, 14} ∨
        polygon = {2, 6, 7, 10, 12} ∨
        polygon = {2, 3, 10, 12, 14} ∨
        polygon = {2, 3, 7, 12, 14} ∨
        polygon = {2, 3, 7, 10, 14} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {2, 3, 6, 12, 14} ∨
        polygon = {2, 3, 6, 10, 14} ∨
        polygon = {2, 3, 6, 10, 12} ∨
        polygon = {2, 3, 6, 7, 14} ∨
        polygon = {2, 3, 6, 7, 12} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {1, 7, 10, 12, 14} ∨
        polygon = {1, 6, 10, 12, 14} ∨
        polygon = {1, 6, 7, 12, 14} ∨
        polygon = {1, 6, 7, 10, 14} ∨
        polygon = {1, 6, 7, 10, 12} ∨
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
        polygon = {1, 2, 10, 12, 14} ∨
        polygon = {1, 2, 7, 12, 14} ∨
        polygon = {1, 2, 7, 10, 14} ∨
        polygon = {1, 2, 7, 10, 12} ∨
        polygon = {1, 2, 6, 12, 14} ∨
        polygon = {1, 2, 6, 10, 14} ∨
        polygon = {1, 2, 6, 10, 12} ∨
        polygon = {1, 2, 6, 7, 14} ∨
        polygon = {1, 2, 6, 7, 12} ∨
        polygon = {1, 2, 6, 7, 10} ∨
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {1, 2, 3, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 6, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21710] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25806 :
    (({1, 2, 3, 6, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 13, 14}, {3, 7, 10, 13, 14}, {3, 6, 10, 13, 14}, {3, 6, 7, 13, 14}, {3, 6, 7, 10, 14}, {3, 6, 7, 10, 13}, {2, 7, 10, 13, 14}, {2, 6, 10, 13, 14}, {2, 6, 7, 13, 14}, {2, 6, 7, 10, 14}, {2, 6, 7, 10, 13}, {2, 3, 10, 13, 14}, {2, 3, 7, 13, 14}, {2, 3, 7, 10, 14}, {2, 3, 7, 10, 13}, {2, 3, 6, 13, 14}, {2, 3, 6, 10, 14}, {2, 3, 6, 10, 13}, {2, 3, 6, 7, 14}, {2, 3, 6, 7, 13}, {2, 3, 6, 7, 10}, {1, 7, 10, 13, 14}, {1, 6, 10, 13, 14}, {1, 6, 7, 13, 14}, {1, 6, 7, 10, 14}, {1, 6, 7, 10, 13}, {1, 3, 10, 13, 14}, {1, 3, 7, 13, 14}, {1, 3, 7, 10, 14}, {1, 3, 7, 10, 13}, {1, 3, 6, 13, 14}, {1, 3, 6, 10, 14}, {1, 3, 6, 10, 13}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 13}, {1, 3, 6, 7, 10}, {1, 2, 10, 13, 14}, {1, 2, 7, 13, 14}, {1, 2, 7, 10, 14}, {1, 2, 7, 10, 13}, {1, 2, 6, 13, 14}, {1, 2, 6, 10, 14}, {1, 2, 6, 10, 13}, {1, 2, 6, 7, 14}, {1, 2, 6, 7, 13}, {1, 2, 6, 7, 10}, {1, 2, 3, 13, 14}, {1, 2, 3, 10, 14}, {1, 2, 3, 10, 13}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 13}, {1, 2, 3, 7, 10}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 10}, {1, 2, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25806 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 6, 7, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 10, 13, 14} ∨
        polygon = {3, 7, 10, 13, 14} ∨
        polygon = {3, 6, 10, 13, 14} ∨
        polygon = {3, 6, 7, 13, 14} ∨
        polygon = {3, 6, 7, 10, 14} ∨
        polygon = {3, 6, 7, 10, 13} ∨
        polygon = {2, 7, 10, 13, 14} ∨
        polygon = {2, 6, 10, 13, 14} ∨
        polygon = {2, 6, 7, 13, 14} ∨
        polygon = {2, 6, 7, 10, 14} ∨
        polygon = {2, 6, 7, 10, 13} ∨
        polygon = {2, 3, 10, 13, 14} ∨
        polygon = {2, 3, 7, 13, 14} ∨
        polygon = {2, 3, 7, 10, 14} ∨
        polygon = {2, 3, 7, 10, 13} ∨
        polygon = {2, 3, 6, 13, 14} ∨
        polygon = {2, 3, 6, 10, 14} ∨
        polygon = {2, 3, 6, 10, 13} ∨
        polygon = {2, 3, 6, 7, 14} ∨
        polygon = {2, 3, 6, 7, 13} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {1, 7, 10, 13, 14} ∨
        polygon = {1, 6, 10, 13, 14} ∨
        polygon = {1, 6, 7, 13, 14} ∨
        polygon = {1, 6, 7, 10, 14} ∨
        polygon = {1, 6, 7, 10, 13} ∨
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
        polygon = {1, 2, 10, 13, 14} ∨
        polygon = {1, 2, 7, 13, 14} ∨
        polygon = {1, 2, 7, 10, 14} ∨
        polygon = {1, 2, 7, 10, 13} ∨
        polygon = {1, 2, 6, 13, 14} ∨
        polygon = {1, 2, 6, 10, 14} ∨
        polygon = {1, 2, 6, 10, 13} ∨
        polygon = {1, 2, 6, 7, 14} ∨
        polygon = {1, 2, 6, 7, 13} ∨
        polygon = {1, 2, 6, 7, 10} ∨
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {1, 2, 3, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 6, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25806] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask28878 :
    (({1, 2, 3, 6, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 12, 13, 14}, {3, 7, 12, 13, 14}, {3, 6, 12, 13, 14}, {3, 6, 7, 13, 14}, {3, 6, 7, 12, 14}, {3, 6, 7, 12, 13}, {2, 7, 12, 13, 14}, {2, 6, 12, 13, 14}, {2, 6, 7, 13, 14}, {2, 6, 7, 12, 14}, {2, 6, 7, 12, 13}, {2, 3, 12, 13, 14}, {2, 3, 7, 13, 14}, {2, 3, 7, 12, 14}, {2, 3, 7, 12, 13}, {2, 3, 6, 13, 14}, {2, 3, 6, 12, 14}, {2, 3, 6, 12, 13}, {2, 3, 6, 7, 14}, {2, 3, 6, 7, 13}, {2, 3, 6, 7, 12}, {1, 7, 12, 13, 14}, {1, 6, 12, 13, 14}, {1, 6, 7, 13, 14}, {1, 6, 7, 12, 14}, {1, 6, 7, 12, 13}, {1, 3, 12, 13, 14}, {1, 3, 7, 13, 14}, {1, 3, 7, 12, 14}, {1, 3, 7, 12, 13}, {1, 3, 6, 13, 14}, {1, 3, 6, 12, 14}, {1, 3, 6, 12, 13}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 13}, {1, 3, 6, 7, 12}, {1, 2, 12, 13, 14}, {1, 2, 7, 13, 14}, {1, 2, 7, 12, 14}, {1, 2, 7, 12, 13}, {1, 2, 6, 13, 14}, {1, 2, 6, 12, 14}, {1, 2, 6, 12, 13}, {1, 2, 6, 7, 14}, {1, 2, 6, 7, 13}, {1, 2, 6, 7, 12}, {1, 2, 3, 13, 14}, {1, 2, 3, 12, 14}, {1, 2, 3, 12, 13}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 13}, {1, 2, 3, 7, 12}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 12}, {1, 2, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask28878 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 6, 7, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 12, 13, 14} ∨
        polygon = {3, 7, 12, 13, 14} ∨
        polygon = {3, 6, 12, 13, 14} ∨
        polygon = {3, 6, 7, 13, 14} ∨
        polygon = {3, 6, 7, 12, 14} ∨
        polygon = {3, 6, 7, 12, 13} ∨
        polygon = {2, 7, 12, 13, 14} ∨
        polygon = {2, 6, 12, 13, 14} ∨
        polygon = {2, 6, 7, 13, 14} ∨
        polygon = {2, 6, 7, 12, 14} ∨
        polygon = {2, 6, 7, 12, 13} ∨
        polygon = {2, 3, 12, 13, 14} ∨
        polygon = {2, 3, 7, 13, 14} ∨
        polygon = {2, 3, 7, 12, 14} ∨
        polygon = {2, 3, 7, 12, 13} ∨
        polygon = {2, 3, 6, 13, 14} ∨
        polygon = {2, 3, 6, 12, 14} ∨
        polygon = {2, 3, 6, 12, 13} ∨
        polygon = {2, 3, 6, 7, 14} ∨
        polygon = {2, 3, 6, 7, 13} ∨
        polygon = {2, 3, 6, 7, 12} ∨
        polygon = {1, 7, 12, 13, 14} ∨
        polygon = {1, 6, 12, 13, 14} ∨
        polygon = {1, 6, 7, 13, 14} ∨
        polygon = {1, 6, 7, 12, 14} ∨
        polygon = {1, 6, 7, 12, 13} ∨
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
        polygon = {1, 2, 12, 13, 14} ∨
        polygon = {1, 2, 7, 13, 14} ∨
        polygon = {1, 2, 7, 12, 14} ∨
        polygon = {1, 2, 7, 12, 13} ∨
        polygon = {1, 2, 6, 13, 14} ∨
        polygon = {1, 2, 6, 12, 14} ∨
        polygon = {1, 2, 6, 12, 13} ∨
        polygon = {1, 2, 6, 7, 14} ∨
        polygon = {1, 2, 6, 7, 13} ∨
        polygon = {1, 2, 6, 7, 12} ∨
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {1, 2, 3, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 6, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask28878] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13902 :
    (({1, 2, 3, 6, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 12, 13}, {3, 9, 10, 12, 13}, {3, 6, 10, 12, 13}, {3, 6, 9, 12, 13}, {3, 6, 9, 10, 13}, {3, 6, 9, 10, 12}, {2, 9, 10, 12, 13}, {2, 6, 10, 12, 13}, {2, 6, 9, 12, 13}, {2, 6, 9, 10, 13}, {2, 6, 9, 10, 12}, {2, 3, 10, 12, 13}, {2, 3, 9, 12, 13}, {2, 3, 9, 10, 13}, {2, 3, 9, 10, 12}, {2, 3, 6, 12, 13}, {2, 3, 6, 10, 13}, {2, 3, 6, 10, 12}, {2, 3, 6, 9, 13}, {2, 3, 6, 9, 12}, {2, 3, 6, 9, 10}, {1, 9, 10, 12, 13}, {1, 6, 10, 12, 13}, {1, 6, 9, 12, 13}, {1, 6, 9, 10, 13}, {1, 6, 9, 10, 12}, {1, 3, 10, 12, 13}, {1, 3, 9, 12, 13}, {1, 3, 9, 10, 13}, {1, 3, 9, 10, 12}, {1, 3, 6, 12, 13}, {1, 3, 6, 10, 13}, {1, 3, 6, 10, 12}, {1, 3, 6, 9, 13}, {1, 3, 6, 9, 12}, {1, 3, 6, 9, 10}, {1, 2, 10, 12, 13}, {1, 2, 9, 12, 13}, {1, 2, 9, 10, 13}, {1, 2, 9, 10, 12}, {1, 2, 6, 12, 13}, {1, 2, 6, 10, 13}, {1, 2, 6, 10, 12}, {1, 2, 6, 9, 13}, {1, 2, 6, 9, 12}, {1, 2, 6, 9, 10}, {1, 2, 3, 12, 13}, {1, 2, 3, 10, 13}, {1, 2, 3, 10, 12}, {1, 2, 3, 9, 13}, {1, 2, 3, 9, 12}, {1, 2, 3, 9, 10}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 12}, {1, 2, 3, 6, 10}, {1, 2, 3, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13902 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 6, 9, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {6, 9, 10, 12, 13} ∨
        polygon = {3, 9, 10, 12, 13} ∨
        polygon = {3, 6, 10, 12, 13} ∨
        polygon = {3, 6, 9, 12, 13} ∨
        polygon = {3, 6, 9, 10, 13} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {2, 9, 10, 12, 13} ∨
        polygon = {2, 6, 10, 12, 13} ∨
        polygon = {2, 6, 9, 12, 13} ∨
        polygon = {2, 6, 9, 10, 13} ∨
        polygon = {2, 6, 9, 10, 12} ∨
        polygon = {2, 3, 10, 12, 13} ∨
        polygon = {2, 3, 9, 12, 13} ∨
        polygon = {2, 3, 9, 10, 13} ∨
        polygon = {2, 3, 9, 10, 12} ∨
        polygon = {2, 3, 6, 12, 13} ∨
        polygon = {2, 3, 6, 10, 13} ∨
        polygon = {2, 3, 6, 10, 12} ∨
        polygon = {2, 3, 6, 9, 13} ∨
        polygon = {2, 3, 6, 9, 12} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {1, 9, 10, 12, 13} ∨
        polygon = {1, 6, 10, 12, 13} ∨
        polygon = {1, 6, 9, 12, 13} ∨
        polygon = {1, 6, 9, 10, 13} ∨
        polygon = {1, 6, 9, 10, 12} ∨
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
        polygon = {1, 2, 10, 12, 13} ∨
        polygon = {1, 2, 9, 12, 13} ∨
        polygon = {1, 2, 9, 10, 13} ∨
        polygon = {1, 2, 9, 10, 12} ∨
        polygon = {1, 2, 6, 12, 13} ∨
        polygon = {1, 2, 6, 10, 13} ∨
        polygon = {1, 2, 6, 10, 12} ∨
        polygon = {1, 2, 6, 9, 13} ∨
        polygon = {1, 2, 6, 9, 12} ∨
        polygon = {1, 2, 6, 9, 10} ∨
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {1, 2, 3, 6, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 6, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13902] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask22094 :
    (({1, 2, 3, 6, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 12, 14}, {3, 9, 10, 12, 14}, {3, 6, 10, 12, 14}, {3, 6, 9, 12, 14}, {3, 6, 9, 10, 14}, {3, 6, 9, 10, 12}, {2, 9, 10, 12, 14}, {2, 6, 10, 12, 14}, {2, 6, 9, 12, 14}, {2, 6, 9, 10, 14}, {2, 6, 9, 10, 12}, {2, 3, 10, 12, 14}, {2, 3, 9, 12, 14}, {2, 3, 9, 10, 14}, {2, 3, 9, 10, 12}, {2, 3, 6, 12, 14}, {2, 3, 6, 10, 14}, {2, 3, 6, 10, 12}, {2, 3, 6, 9, 14}, {2, 3, 6, 9, 12}, {2, 3, 6, 9, 10}, {1, 9, 10, 12, 14}, {1, 6, 10, 12, 14}, {1, 6, 9, 12, 14}, {1, 6, 9, 10, 14}, {1, 6, 9, 10, 12}, {1, 3, 10, 12, 14}, {1, 3, 9, 12, 14}, {1, 3, 9, 10, 14}, {1, 3, 9, 10, 12}, {1, 3, 6, 12, 14}, {1, 3, 6, 10, 14}, {1, 3, 6, 10, 12}, {1, 3, 6, 9, 14}, {1, 3, 6, 9, 12}, {1, 3, 6, 9, 10}, {1, 2, 10, 12, 14}, {1, 2, 9, 12, 14}, {1, 2, 9, 10, 14}, {1, 2, 9, 10, 12}, {1, 2, 6, 12, 14}, {1, 2, 6, 10, 14}, {1, 2, 6, 10, 12}, {1, 2, 6, 9, 14}, {1, 2, 6, 9, 12}, {1, 2, 6, 9, 10}, {1, 2, 3, 12, 14}, {1, 2, 3, 10, 14}, {1, 2, 3, 10, 12}, {1, 2, 3, 9, 14}, {1, 2, 3, 9, 12}, {1, 2, 3, 9, 10}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 12}, {1, 2, 3, 6, 10}, {1, 2, 3, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask22094 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 6, 9, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {6, 9, 10, 12, 14} ∨
        polygon = {3, 9, 10, 12, 14} ∨
        polygon = {3, 6, 10, 12, 14} ∨
        polygon = {3, 6, 9, 12, 14} ∨
        polygon = {3, 6, 9, 10, 14} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {2, 9, 10, 12, 14} ∨
        polygon = {2, 6, 10, 12, 14} ∨
        polygon = {2, 6, 9, 12, 14} ∨
        polygon = {2, 6, 9, 10, 14} ∨
        polygon = {2, 6, 9, 10, 12} ∨
        polygon = {2, 3, 10, 12, 14} ∨
        polygon = {2, 3, 9, 12, 14} ∨
        polygon = {2, 3, 9, 10, 14} ∨
        polygon = {2, 3, 9, 10, 12} ∨
        polygon = {2, 3, 6, 12, 14} ∨
        polygon = {2, 3, 6, 10, 14} ∨
        polygon = {2, 3, 6, 10, 12} ∨
        polygon = {2, 3, 6, 9, 14} ∨
        polygon = {2, 3, 6, 9, 12} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {1, 9, 10, 12, 14} ∨
        polygon = {1, 6, 10, 12, 14} ∨
        polygon = {1, 6, 9, 12, 14} ∨
        polygon = {1, 6, 9, 10, 14} ∨
        polygon = {1, 6, 9, 10, 12} ∨
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
        polygon = {1, 2, 10, 12, 14} ∨
        polygon = {1, 2, 9, 12, 14} ∨
        polygon = {1, 2, 9, 10, 14} ∨
        polygon = {1, 2, 9, 10, 12} ∨
        polygon = {1, 2, 6, 12, 14} ∨
        polygon = {1, 2, 6, 10, 14} ∨
        polygon = {1, 2, 6, 10, 12} ∨
        polygon = {1, 2, 6, 9, 14} ∨
        polygon = {1, 2, 6, 9, 12} ∨
        polygon = {1, 2, 6, 9, 10} ∨
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {1, 2, 3, 6, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 6, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask22094] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask26190 :
    (({1, 2, 3, 6, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 13, 14}, {3, 9, 10, 13, 14}, {3, 6, 10, 13, 14}, {3, 6, 9, 13, 14}, {3, 6, 9, 10, 14}, {3, 6, 9, 10, 13}, {2, 9, 10, 13, 14}, {2, 6, 10, 13, 14}, {2, 6, 9, 13, 14}, {2, 6, 9, 10, 14}, {2, 6, 9, 10, 13}, {2, 3, 10, 13, 14}, {2, 3, 9, 13, 14}, {2, 3, 9, 10, 14}, {2, 3, 9, 10, 13}, {2, 3, 6, 13, 14}, {2, 3, 6, 10, 14}, {2, 3, 6, 10, 13}, {2, 3, 6, 9, 14}, {2, 3, 6, 9, 13}, {2, 3, 6, 9, 10}, {1, 9, 10, 13, 14}, {1, 6, 10, 13, 14}, {1, 6, 9, 13, 14}, {1, 6, 9, 10, 14}, {1, 6, 9, 10, 13}, {1, 3, 10, 13, 14}, {1, 3, 9, 13, 14}, {1, 3, 9, 10, 14}, {1, 3, 9, 10, 13}, {1, 3, 6, 13, 14}, {1, 3, 6, 10, 14}, {1, 3, 6, 10, 13}, {1, 3, 6, 9, 14}, {1, 3, 6, 9, 13}, {1, 3, 6, 9, 10}, {1, 2, 10, 13, 14}, {1, 2, 9, 13, 14}, {1, 2, 9, 10, 14}, {1, 2, 9, 10, 13}, {1, 2, 6, 13, 14}, {1, 2, 6, 10, 14}, {1, 2, 6, 10, 13}, {1, 2, 6, 9, 14}, {1, 2, 6, 9, 13}, {1, 2, 6, 9, 10}, {1, 2, 3, 13, 14}, {1, 2, 3, 10, 14}, {1, 2, 3, 10, 13}, {1, 2, 3, 9, 14}, {1, 2, 3, 9, 13}, {1, 2, 3, 9, 10}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 10}, {1, 2, 3, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26190 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 6, 9, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 9, 10, 13, 14} ∨
        polygon = {3, 9, 10, 13, 14} ∨
        polygon = {3, 6, 10, 13, 14} ∨
        polygon = {3, 6, 9, 13, 14} ∨
        polygon = {3, 6, 9, 10, 14} ∨
        polygon = {3, 6, 9, 10, 13} ∨
        polygon = {2, 9, 10, 13, 14} ∨
        polygon = {2, 6, 10, 13, 14} ∨
        polygon = {2, 6, 9, 13, 14} ∨
        polygon = {2, 6, 9, 10, 14} ∨
        polygon = {2, 6, 9, 10, 13} ∨
        polygon = {2, 3, 10, 13, 14} ∨
        polygon = {2, 3, 9, 13, 14} ∨
        polygon = {2, 3, 9, 10, 14} ∨
        polygon = {2, 3, 9, 10, 13} ∨
        polygon = {2, 3, 6, 13, 14} ∨
        polygon = {2, 3, 6, 10, 14} ∨
        polygon = {2, 3, 6, 10, 13} ∨
        polygon = {2, 3, 6, 9, 14} ∨
        polygon = {2, 3, 6, 9, 13} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {1, 9, 10, 13, 14} ∨
        polygon = {1, 6, 10, 13, 14} ∨
        polygon = {1, 6, 9, 13, 14} ∨
        polygon = {1, 6, 9, 10, 14} ∨
        polygon = {1, 6, 9, 10, 13} ∨
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
        polygon = {1, 2, 10, 13, 14} ∨
        polygon = {1, 2, 9, 13, 14} ∨
        polygon = {1, 2, 9, 10, 14} ∨
        polygon = {1, 2, 9, 10, 13} ∨
        polygon = {1, 2, 6, 13, 14} ∨
        polygon = {1, 2, 6, 10, 14} ∨
        polygon = {1, 2, 6, 10, 13} ∨
        polygon = {1, 2, 6, 9, 14} ∨
        polygon = {1, 2, 6, 9, 13} ∨
        polygon = {1, 2, 6, 9, 10} ∨
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {1, 2, 3, 6, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 6, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26190] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29262 :
    (({1, 2, 3, 6, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 12, 13, 14}, {3, 9, 12, 13, 14}, {3, 6, 12, 13, 14}, {3, 6, 9, 13, 14}, {3, 6, 9, 12, 14}, {3, 6, 9, 12, 13}, {2, 9, 12, 13, 14}, {2, 6, 12, 13, 14}, {2, 6, 9, 13, 14}, {2, 6, 9, 12, 14}, {2, 6, 9, 12, 13}, {2, 3, 12, 13, 14}, {2, 3, 9, 13, 14}, {2, 3, 9, 12, 14}, {2, 3, 9, 12, 13}, {2, 3, 6, 13, 14}, {2, 3, 6, 12, 14}, {2, 3, 6, 12, 13}, {2, 3, 6, 9, 14}, {2, 3, 6, 9, 13}, {2, 3, 6, 9, 12}, {1, 9, 12, 13, 14}, {1, 6, 12, 13, 14}, {1, 6, 9, 13, 14}, {1, 6, 9, 12, 14}, {1, 6, 9, 12, 13}, {1, 3, 12, 13, 14}, {1, 3, 9, 13, 14}, {1, 3, 9, 12, 14}, {1, 3, 9, 12, 13}, {1, 3, 6, 13, 14}, {1, 3, 6, 12, 14}, {1, 3, 6, 12, 13}, {1, 3, 6, 9, 14}, {1, 3, 6, 9, 13}, {1, 3, 6, 9, 12}, {1, 2, 12, 13, 14}, {1, 2, 9, 13, 14}, {1, 2, 9, 12, 14}, {1, 2, 9, 12, 13}, {1, 2, 6, 13, 14}, {1, 2, 6, 12, 14}, {1, 2, 6, 12, 13}, {1, 2, 6, 9, 14}, {1, 2, 6, 9, 13}, {1, 2, 6, 9, 12}, {1, 2, 3, 13, 14}, {1, 2, 3, 12, 14}, {1, 2, 3, 12, 13}, {1, 2, 3, 9, 14}, {1, 2, 3, 9, 13}, {1, 2, 3, 9, 12}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 12}, {1, 2, 3, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29262 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 6, 9, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 9, 12, 13, 14} ∨
        polygon = {3, 9, 12, 13, 14} ∨
        polygon = {3, 6, 12, 13, 14} ∨
        polygon = {3, 6, 9, 13, 14} ∨
        polygon = {3, 6, 9, 12, 14} ∨
        polygon = {3, 6, 9, 12, 13} ∨
        polygon = {2, 9, 12, 13, 14} ∨
        polygon = {2, 6, 12, 13, 14} ∨
        polygon = {2, 6, 9, 13, 14} ∨
        polygon = {2, 6, 9, 12, 14} ∨
        polygon = {2, 6, 9, 12, 13} ∨
        polygon = {2, 3, 12, 13, 14} ∨
        polygon = {2, 3, 9, 13, 14} ∨
        polygon = {2, 3, 9, 12, 14} ∨
        polygon = {2, 3, 9, 12, 13} ∨
        polygon = {2, 3, 6, 13, 14} ∨
        polygon = {2, 3, 6, 12, 14} ∨
        polygon = {2, 3, 6, 12, 13} ∨
        polygon = {2, 3, 6, 9, 14} ∨
        polygon = {2, 3, 6, 9, 13} ∨
        polygon = {2, 3, 6, 9, 12} ∨
        polygon = {1, 9, 12, 13, 14} ∨
        polygon = {1, 6, 12, 13, 14} ∨
        polygon = {1, 6, 9, 13, 14} ∨
        polygon = {1, 6, 9, 12, 14} ∨
        polygon = {1, 6, 9, 12, 13} ∨
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
        polygon = {1, 2, 12, 13, 14} ∨
        polygon = {1, 2, 9, 13, 14} ∨
        polygon = {1, 2, 9, 12, 14} ∨
        polygon = {1, 2, 9, 12, 13} ∨
        polygon = {1, 2, 6, 13, 14} ∨
        polygon = {1, 2, 6, 12, 14} ∨
        polygon = {1, 2, 6, 12, 13} ∨
        polygon = {1, 2, 6, 9, 14} ∨
        polygon = {1, 2, 6, 9, 13} ∨
        polygon = {1, 2, 6, 9, 12} ∨
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {1, 2, 3, 6, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 6, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29262] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

end ErdosSzekeres

end
