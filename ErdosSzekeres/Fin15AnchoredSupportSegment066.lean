module

public import ErdosSzekeres.Fin15AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 066. -/

theorem fin15Anchored_fiveFamily_mask21535 :
    (({0, 1, 2, 3, 4, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 10, 12, 14}, {2, 4, 10, 12, 14}, {2, 3, 10, 12, 14}, {2, 3, 4, 12, 14}, {2, 3, 4, 10, 14}, {2, 3, 4, 10, 12}, {1, 4, 10, 12, 14}, {1, 3, 10, 12, 14}, {1, 3, 4, 12, 14}, {1, 3, 4, 10, 14}, {1, 3, 4, 10, 12}, {1, 2, 10, 12, 14}, {1, 2, 4, 12, 14}, {1, 2, 4, 10, 14}, {1, 2, 4, 10, 12}, {1, 2, 3, 12, 14}, {1, 2, 3, 10, 14}, {1, 2, 3, 10, 12}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 12}, {1, 2, 3, 4, 10}, {0, 4, 10, 12, 14}, {0, 3, 10, 12, 14}, {0, 3, 4, 12, 14}, {0, 3, 4, 10, 14}, {0, 3, 4, 10, 12}, {0, 2, 10, 12, 14}, {0, 2, 4, 12, 14}, {0, 2, 4, 10, 14}, {0, 2, 4, 10, 12}, {0, 2, 3, 12, 14}, {0, 2, 3, 10, 14}, {0, 2, 3, 10, 12}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 10}, {0, 1, 10, 12, 14}, {0, 1, 4, 12, 14}, {0, 1, 4, 10, 14}, {0, 1, 4, 10, 12}, {0, 1, 3, 12, 14}, {0, 1, 3, 10, 14}, {0, 1, 3, 10, 12}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 10}, {0, 1, 2, 12, 14}, {0, 1, 2, 10, 14}, {0, 1, 2, 10, 12}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 10}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21535 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {3, 4, 10, 12, 14} ∨
        polygon = {2, 4, 10, 12, 14} ∨
        polygon = {2, 3, 10, 12, 14} ∨
        polygon = {2, 3, 4, 12, 14} ∨
        polygon = {2, 3, 4, 10, 14} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {1, 4, 10, 12, 14} ∨
        polygon = {1, 3, 10, 12, 14} ∨
        polygon = {1, 3, 4, 12, 14} ∨
        polygon = {1, 3, 4, 10, 14} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 2, 10, 12, 14} ∨
        polygon = {1, 2, 4, 12, 14} ∨
        polygon = {1, 2, 4, 10, 14} ∨
        polygon = {1, 2, 4, 10, 12} ∨
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 4, 14} ∨
        polygon = {1, 2, 3, 4, 12} ∨
        polygon = {1, 2, 3, 4, 10} ∨
        polygon = {0, 4, 10, 12, 14} ∨
        polygon = {0, 3, 10, 12, 14} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 2, 10, 12, 14} ∨
        polygon = {0, 2, 4, 12, 14} ∨
        polygon = {0, 2, 4, 10, 14} ∨
        polygon = {0, 2, 4, 10, 12} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 1, 10, 12, 14} ∨
        polygon = {0, 1, 4, 12, 14} ∨
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 2, 12, 14} ∨
        polygon = {0, 1, 2, 10, 14} ∨
        polygon = {0, 1, 2, 10, 12} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21535] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25631 :
    (({0, 1, 2, 3, 4, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 10, 13, 14}, {2, 4, 10, 13, 14}, {2, 3, 10, 13, 14}, {2, 3, 4, 13, 14}, {2, 3, 4, 10, 14}, {2, 3, 4, 10, 13}, {1, 4, 10, 13, 14}, {1, 3, 10, 13, 14}, {1, 3, 4, 13, 14}, {1, 3, 4, 10, 14}, {1, 3, 4, 10, 13}, {1, 2, 10, 13, 14}, {1, 2, 4, 13, 14}, {1, 2, 4, 10, 14}, {1, 2, 4, 10, 13}, {1, 2, 3, 13, 14}, {1, 2, 3, 10, 14}, {1, 2, 3, 10, 13}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 10}, {0, 4, 10, 13, 14}, {0, 3, 10, 13, 14}, {0, 3, 4, 13, 14}, {0, 3, 4, 10, 14}, {0, 3, 4, 10, 13}, {0, 2, 10, 13, 14}, {0, 2, 4, 13, 14}, {0, 2, 4, 10, 14}, {0, 2, 4, 10, 13}, {0, 2, 3, 13, 14}, {0, 2, 3, 10, 14}, {0, 2, 3, 10, 13}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 10}, {0, 1, 10, 13, 14}, {0, 1, 4, 13, 14}, {0, 1, 4, 10, 14}, {0, 1, 4, 10, 13}, {0, 1, 3, 13, 14}, {0, 1, 3, 10, 14}, {0, 1, 3, 10, 13}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 10}, {0, 1, 2, 13, 14}, {0, 1, 2, 10, 14}, {0, 1, 2, 10, 13}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 10}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25631 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {3, 4, 10, 13, 14} ∨
        polygon = {2, 4, 10, 13, 14} ∨
        polygon = {2, 3, 10, 13, 14} ∨
        polygon = {2, 3, 4, 13, 14} ∨
        polygon = {2, 3, 4, 10, 14} ∨
        polygon = {2, 3, 4, 10, 13} ∨
        polygon = {1, 4, 10, 13, 14} ∨
        polygon = {1, 3, 10, 13, 14} ∨
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 10, 14} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 2, 10, 13, 14} ∨
        polygon = {1, 2, 4, 13, 14} ∨
        polygon = {1, 2, 4, 10, 14} ∨
        polygon = {1, 2, 4, 10, 13} ∨
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 4, 14} ∨
        polygon = {1, 2, 3, 4, 13} ∨
        polygon = {1, 2, 3, 4, 10} ∨
        polygon = {0, 4, 10, 13, 14} ∨
        polygon = {0, 3, 10, 13, 14} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 2, 10, 13, 14} ∨
        polygon = {0, 2, 4, 13, 14} ∨
        polygon = {0, 2, 4, 10, 14} ∨
        polygon = {0, 2, 4, 10, 13} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 1, 10, 13, 14} ∨
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 2, 13, 14} ∨
        polygon = {0, 1, 2, 10, 14} ∨
        polygon = {0, 1, 2, 10, 13} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25631] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask28703 :
    (({0, 1, 2, 3, 4, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 12, 13, 14}, {2, 4, 12, 13, 14}, {2, 3, 12, 13, 14}, {2, 3, 4, 13, 14}, {2, 3, 4, 12, 14}, {2, 3, 4, 12, 13}, {1, 4, 12, 13, 14}, {1, 3, 12, 13, 14}, {1, 3, 4, 13, 14}, {1, 3, 4, 12, 14}, {1, 3, 4, 12, 13}, {1, 2, 12, 13, 14}, {1, 2, 4, 13, 14}, {1, 2, 4, 12, 14}, {1, 2, 4, 12, 13}, {1, 2, 3, 13, 14}, {1, 2, 3, 12, 14}, {1, 2, 3, 12, 13}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 12}, {0, 4, 12, 13, 14}, {0, 3, 12, 13, 14}, {0, 3, 4, 13, 14}, {0, 3, 4, 12, 14}, {0, 3, 4, 12, 13}, {0, 2, 12, 13, 14}, {0, 2, 4, 13, 14}, {0, 2, 4, 12, 14}, {0, 2, 4, 12, 13}, {0, 2, 3, 13, 14}, {0, 2, 3, 12, 14}, {0, 2, 3, 12, 13}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 12}, {0, 1, 12, 13, 14}, {0, 1, 4, 13, 14}, {0, 1, 4, 12, 14}, {0, 1, 4, 12, 13}, {0, 1, 3, 13, 14}, {0, 1, 3, 12, 14}, {0, 1, 3, 12, 13}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 12}, {0, 1, 2, 13, 14}, {0, 1, 2, 12, 14}, {0, 1, 2, 12, 13}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 12}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask28703 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {3, 4, 12, 13, 14} ∨
        polygon = {2, 4, 12, 13, 14} ∨
        polygon = {2, 3, 12, 13, 14} ∨
        polygon = {2, 3, 4, 13, 14} ∨
        polygon = {2, 3, 4, 12, 14} ∨
        polygon = {2, 3, 4, 12, 13} ∨
        polygon = {1, 4, 12, 13, 14} ∨
        polygon = {1, 3, 12, 13, 14} ∨
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 12, 14} ∨
        polygon = {1, 3, 4, 12, 13} ∨
        polygon = {1, 2, 12, 13, 14} ∨
        polygon = {1, 2, 4, 13, 14} ∨
        polygon = {1, 2, 4, 12, 14} ∨
        polygon = {1, 2, 4, 12, 13} ∨
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 4, 14} ∨
        polygon = {1, 2, 3, 4, 13} ∨
        polygon = {1, 2, 3, 4, 12} ∨
        polygon = {0, 4, 12, 13, 14} ∨
        polygon = {0, 3, 12, 13, 14} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 2, 12, 13, 14} ∨
        polygon = {0, 2, 4, 13, 14} ∨
        polygon = {0, 2, 4, 12, 14} ∨
        polygon = {0, 2, 4, 12, 13} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 1, 12, 13, 14} ∨
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 12, 14} ∨
        polygon = {0, 1, 4, 12, 13} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 2, 13, 14} ∨
        polygon = {0, 1, 2, 12, 14} ∨
        polygon = {0, 1, 2, 12, 13} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask28703] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask00751 :
    (({0, 1, 2, 3, 5, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 7, 9}, {2, 5, 6, 7, 9}, {2, 3, 6, 7, 9}, {2, 3, 5, 7, 9}, {2, 3, 5, 6, 9}, {2, 3, 5, 6, 7}, {1, 5, 6, 7, 9}, {1, 3, 6, 7, 9}, {1, 3, 5, 7, 9}, {1, 3, 5, 6, 9}, {1, 3, 5, 6, 7}, {1, 2, 6, 7, 9}, {1, 2, 5, 7, 9}, {1, 2, 5, 6, 9}, {1, 2, 5, 6, 7}, {1, 2, 3, 7, 9}, {1, 2, 3, 6, 9}, {1, 2, 3, 6, 7}, {1, 2, 3, 5, 9}, {1, 2, 3, 5, 7}, {1, 2, 3, 5, 6}, {0, 5, 6, 7, 9}, {0, 3, 6, 7, 9}, {0, 3, 5, 7, 9}, {0, 3, 5, 6, 9}, {0, 3, 5, 6, 7}, {0, 2, 6, 7, 9}, {0, 2, 5, 7, 9}, {0, 2, 5, 6, 9}, {0, 2, 5, 6, 7}, {0, 2, 3, 7, 9}, {0, 2, 3, 6, 9}, {0, 2, 3, 6, 7}, {0, 2, 3, 5, 9}, {0, 2, 3, 5, 7}, {0, 2, 3, 5, 6}, {0, 1, 6, 7, 9}, {0, 1, 5, 7, 9}, {0, 1, 5, 6, 9}, {0, 1, 5, 6, 7}, {0, 1, 3, 7, 9}, {0, 1, 3, 6, 9}, {0, 1, 3, 6, 7}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 7}, {0, 1, 3, 5, 6}, {0, 1, 2, 7, 9}, {0, 1, 2, 6, 9}, {0, 1, 2, 6, 7}, {0, 1, 2, 5, 9}, {0, 1, 2, 5, 7}, {0, 1, 2, 5, 6}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 6}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask00751 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 5, 6, 7, 9} →
      polygon.card = 5 →
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {2, 5, 6, 7, 9} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {2, 3, 5, 6, 7} ∨
        polygon = {1, 5, 6, 7, 9} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {1, 3, 5, 7, 9} ∨
        polygon = {1, 3, 5, 6, 9} ∨
        polygon = {1, 3, 5, 6, 7} ∨
        polygon = {1, 2, 6, 7, 9} ∨
        polygon = {1, 2, 5, 7, 9} ∨
        polygon = {1, 2, 5, 6, 9} ∨
        polygon = {1, 2, 5, 6, 7} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {1, 2, 3, 6, 9} ∨
        polygon = {1, 2, 3, 6, 7} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {1, 2, 3, 5, 7} ∨
        polygon = {1, 2, 3, 5, 6} ∨
        polygon = {0, 5, 6, 7, 9} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 3, 5, 6, 7} ∨
        polygon = {0, 2, 6, 7, 9} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 5, 6, 9} ∨
        polygon = {0, 2, 5, 6, 7} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 2, 3, 5, 6} ∨
        polygon = {0, 1, 6, 7, 9} ∨
        polygon = {0, 1, 5, 7, 9} ∨
        polygon = {0, 1, 5, 6, 9} ∨
        polygon = {0, 1, 5, 6, 7} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 5, 6} ∨
        polygon = {0, 1, 2, 7, 9} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 5, 9} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 5, 6} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 6} ∨
        polygon = {0, 1, 2, 3, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 5, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask00751] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01263 :
    (({0, 1, 2, 3, 5, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 7, 10}, {2, 5, 6, 7, 10}, {2, 3, 6, 7, 10}, {2, 3, 5, 7, 10}, {2, 3, 5, 6, 10}, {2, 3, 5, 6, 7}, {1, 5, 6, 7, 10}, {1, 3, 6, 7, 10}, {1, 3, 5, 7, 10}, {1, 3, 5, 6, 10}, {1, 3, 5, 6, 7}, {1, 2, 6, 7, 10}, {1, 2, 5, 7, 10}, {1, 2, 5, 6, 10}, {1, 2, 5, 6, 7}, {1, 2, 3, 7, 10}, {1, 2, 3, 6, 10}, {1, 2, 3, 6, 7}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 7}, {1, 2, 3, 5, 6}, {0, 5, 6, 7, 10}, {0, 3, 6, 7, 10}, {0, 3, 5, 7, 10}, {0, 3, 5, 6, 10}, {0, 3, 5, 6, 7}, {0, 2, 6, 7, 10}, {0, 2, 5, 7, 10}, {0, 2, 5, 6, 10}, {0, 2, 5, 6, 7}, {0, 2, 3, 7, 10}, {0, 2, 3, 6, 10}, {0, 2, 3, 6, 7}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 7}, {0, 2, 3, 5, 6}, {0, 1, 6, 7, 10}, {0, 1, 5, 7, 10}, {0, 1, 5, 6, 10}, {0, 1, 5, 6, 7}, {0, 1, 3, 7, 10}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 7}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 7}, {0, 1, 3, 5, 6}, {0, 1, 2, 7, 10}, {0, 1, 2, 6, 10}, {0, 1, 2, 6, 7}, {0, 1, 2, 5, 10}, {0, 1, 2, 5, 7}, {0, 1, 2, 5, 6}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 6}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01263 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 5, 6, 7, 10} →
      polygon.card = 5 →
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {2, 5, 6, 7, 10} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {2, 3, 5, 6, 7} ∨
        polygon = {1, 5, 6, 7, 10} ∨
        polygon = {1, 3, 6, 7, 10} ∨
        polygon = {1, 3, 5, 7, 10} ∨
        polygon = {1, 3, 5, 6, 10} ∨
        polygon = {1, 3, 5, 6, 7} ∨
        polygon = {1, 2, 6, 7, 10} ∨
        polygon = {1, 2, 5, 7, 10} ∨
        polygon = {1, 2, 5, 6, 10} ∨
        polygon = {1, 2, 5, 6, 7} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {1, 2, 3, 6, 7} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 7} ∨
        polygon = {1, 2, 3, 5, 6} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 3, 5, 6, 7} ∨
        polygon = {0, 2, 6, 7, 10} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 5, 6, 7} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 2, 3, 5, 6} ∨
        polygon = {0, 1, 6, 7, 10} ∨
        polygon = {0, 1, 5, 7, 10} ∨
        polygon = {0, 1, 5, 6, 10} ∨
        polygon = {0, 1, 5, 6, 7} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 5, 6} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 5, 6} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 6} ∨
        polygon = {0, 1, 2, 3, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 5, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01263] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask04335 :
    (({0, 1, 2, 3, 5, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 7, 12}, {2, 5, 6, 7, 12}, {2, 3, 6, 7, 12}, {2, 3, 5, 7, 12}, {2, 3, 5, 6, 12}, {2, 3, 5, 6, 7}, {1, 5, 6, 7, 12}, {1, 3, 6, 7, 12}, {1, 3, 5, 7, 12}, {1, 3, 5, 6, 12}, {1, 3, 5, 6, 7}, {1, 2, 6, 7, 12}, {1, 2, 5, 7, 12}, {1, 2, 5, 6, 12}, {1, 2, 5, 6, 7}, {1, 2, 3, 7, 12}, {1, 2, 3, 6, 12}, {1, 2, 3, 6, 7}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 7}, {1, 2, 3, 5, 6}, {0, 5, 6, 7, 12}, {0, 3, 6, 7, 12}, {0, 3, 5, 7, 12}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 7}, {0, 2, 6, 7, 12}, {0, 2, 5, 7, 12}, {0, 2, 5, 6, 12}, {0, 2, 5, 6, 7}, {0, 2, 3, 7, 12}, {0, 2, 3, 6, 12}, {0, 2, 3, 6, 7}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 7}, {0, 2, 3, 5, 6}, {0, 1, 6, 7, 12}, {0, 1, 5, 7, 12}, {0, 1, 5, 6, 12}, {0, 1, 5, 6, 7}, {0, 1, 3, 7, 12}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 7}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 7}, {0, 1, 3, 5, 6}, {0, 1, 2, 7, 12}, {0, 1, 2, 6, 12}, {0, 1, 2, 6, 7}, {0, 1, 2, 5, 12}, {0, 1, 2, 5, 7}, {0, 1, 2, 5, 6}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 6}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask04335 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 5, 6, 7, 12} →
      polygon.card = 5 →
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {2, 5, 6, 7, 12} ∨
        polygon = {2, 3, 6, 7, 12} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {2, 3, 5, 6, 7} ∨
        polygon = {1, 5, 6, 7, 12} ∨
        polygon = {1, 3, 6, 7, 12} ∨
        polygon = {1, 3, 5, 7, 12} ∨
        polygon = {1, 3, 5, 6, 12} ∨
        polygon = {1, 3, 5, 6, 7} ∨
        polygon = {1, 2, 6, 7, 12} ∨
        polygon = {1, 2, 5, 7, 12} ∨
        polygon = {1, 2, 5, 6, 12} ∨
        polygon = {1, 2, 5, 6, 7} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {1, 2, 3, 6, 7} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 7} ∨
        polygon = {1, 2, 3, 5, 6} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 5, 6, 7} ∨
        polygon = {0, 2, 6, 7, 12} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 5, 6, 7} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 2, 3, 5, 6} ∨
        polygon = {0, 1, 6, 7, 12} ∨
        polygon = {0, 1, 5, 7, 12} ∨
        polygon = {0, 1, 5, 6, 12} ∨
        polygon = {0, 1, 5, 6, 7} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 5, 6} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 6, 12} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 5, 12} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 5, 6} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 6} ∨
        polygon = {0, 1, 2, 3, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 5, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask04335] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask08431 :
    (({0, 1, 2, 3, 5, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 7, 13}, {2, 5, 6, 7, 13}, {2, 3, 6, 7, 13}, {2, 3, 5, 7, 13}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 7}, {1, 5, 6, 7, 13}, {1, 3, 6, 7, 13}, {1, 3, 5, 7, 13}, {1, 3, 5, 6, 13}, {1, 3, 5, 6, 7}, {1, 2, 6, 7, 13}, {1, 2, 5, 7, 13}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 7}, {1, 2, 3, 7, 13}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 7}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 7}, {1, 2, 3, 5, 6}, {0, 5, 6, 7, 13}, {0, 3, 6, 7, 13}, {0, 3, 5, 7, 13}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 7}, {0, 2, 6, 7, 13}, {0, 2, 5, 7, 13}, {0, 2, 5, 6, 13}, {0, 2, 5, 6, 7}, {0, 2, 3, 7, 13}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 7}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 7}, {0, 2, 3, 5, 6}, {0, 1, 6, 7, 13}, {0, 1, 5, 7, 13}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 7}, {0, 1, 3, 7, 13}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 7}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 7}, {0, 1, 3, 5, 6}, {0, 1, 2, 7, 13}, {0, 1, 2, 6, 13}, {0, 1, 2, 6, 7}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 7}, {0, 1, 2, 5, 6}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 6}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask08431 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 5, 6, 7, 13} →
      polygon.card = 5 →
        polygon = {3, 5, 6, 7, 13} ∨
        polygon = {2, 5, 6, 7, 13} ∨
        polygon = {2, 3, 6, 7, 13} ∨
        polygon = {2, 3, 5, 7, 13} ∨
        polygon = {2, 3, 5, 6, 13} ∨
        polygon = {2, 3, 5, 6, 7} ∨
        polygon = {1, 5, 6, 7, 13} ∨
        polygon = {1, 3, 6, 7, 13} ∨
        polygon = {1, 3, 5, 7, 13} ∨
        polygon = {1, 3, 5, 6, 13} ∨
        polygon = {1, 3, 5, 6, 7} ∨
        polygon = {1, 2, 6, 7, 13} ∨
        polygon = {1, 2, 5, 7, 13} ∨
        polygon = {1, 2, 5, 6, 13} ∨
        polygon = {1, 2, 5, 6, 7} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 6, 7} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 7} ∨
        polygon = {1, 2, 3, 5, 6} ∨
        polygon = {0, 5, 6, 7, 13} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 6, 13} ∨
        polygon = {0, 3, 5, 6, 7} ∨
        polygon = {0, 2, 6, 7, 13} ∨
        polygon = {0, 2, 5, 7, 13} ∨
        polygon = {0, 2, 5, 6, 13} ∨
        polygon = {0, 2, 5, 6, 7} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 2, 3, 5, 6} ∨
        polygon = {0, 1, 6, 7, 13} ∨
        polygon = {0, 1, 5, 7, 13} ∨
        polygon = {0, 1, 5, 6, 13} ∨
        polygon = {0, 1, 5, 6, 7} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 5, 6} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 6, 13} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 5, 13} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 5, 6} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 6} ∨
        polygon = {0, 1, 2, 3, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 5, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask08431] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask16623 :
    (({0, 1, 2, 3, 5, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 7, 14}, {2, 5, 6, 7, 14}, {2, 3, 6, 7, 14}, {2, 3, 5, 7, 14}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 7}, {1, 5, 6, 7, 14}, {1, 3, 6, 7, 14}, {1, 3, 5, 7, 14}, {1, 3, 5, 6, 14}, {1, 3, 5, 6, 7}, {1, 2, 6, 7, 14}, {1, 2, 5, 7, 14}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 7}, {1, 2, 3, 7, 14}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 7}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 7}, {1, 2, 3, 5, 6}, {0, 5, 6, 7, 14}, {0, 3, 6, 7, 14}, {0, 3, 5, 7, 14}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 7}, {0, 2, 6, 7, 14}, {0, 2, 5, 7, 14}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 7}, {0, 2, 3, 7, 14}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 7}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 7}, {0, 2, 3, 5, 6}, {0, 1, 6, 7, 14}, {0, 1, 5, 7, 14}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 7}, {0, 1, 3, 7, 14}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 7}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 7}, {0, 1, 3, 5, 6}, {0, 1, 2, 7, 14}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 7}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 7}, {0, 1, 2, 5, 6}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 6}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask16623 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 5, 6, 7, 14} →
      polygon.card = 5 →
        polygon = {3, 5, 6, 7, 14} ∨
        polygon = {2, 5, 6, 7, 14} ∨
        polygon = {2, 3, 6, 7, 14} ∨
        polygon = {2, 3, 5, 7, 14} ∨
        polygon = {2, 3, 5, 6, 14} ∨
        polygon = {2, 3, 5, 6, 7} ∨
        polygon = {1, 5, 6, 7, 14} ∨
        polygon = {1, 3, 6, 7, 14} ∨
        polygon = {1, 3, 5, 7, 14} ∨
        polygon = {1, 3, 5, 6, 14} ∨
        polygon = {1, 3, 5, 6, 7} ∨
        polygon = {1, 2, 6, 7, 14} ∨
        polygon = {1, 2, 5, 7, 14} ∨
        polygon = {1, 2, 5, 6, 14} ∨
        polygon = {1, 2, 5, 6, 7} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 7} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 7} ∨
        polygon = {1, 2, 3, 5, 6} ∨
        polygon = {0, 5, 6, 7, 14} ∨
        polygon = {0, 3, 6, 7, 14} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 6, 14} ∨
        polygon = {0, 3, 5, 6, 7} ∨
        polygon = {0, 2, 6, 7, 14} ∨
        polygon = {0, 2, 5, 7, 14} ∨
        polygon = {0, 2, 5, 6, 14} ∨
        polygon = {0, 2, 5, 6, 7} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 2, 3, 5, 6} ∨
        polygon = {0, 1, 6, 7, 14} ∨
        polygon = {0, 1, 5, 7, 14} ∨
        polygon = {0, 1, 5, 6, 14} ∨
        polygon = {0, 1, 5, 6, 7} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 5, 6} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 6, 14} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 5, 14} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 5, 6} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 6} ∨
        polygon = {0, 1, 2, 3, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 5, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask16623] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01647 :
    (({0, 1, 2, 3, 5, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 9, 10}, {2, 5, 6, 9, 10}, {2, 3, 6, 9, 10}, {2, 3, 5, 9, 10}, {2, 3, 5, 6, 10}, {2, 3, 5, 6, 9}, {1, 5, 6, 9, 10}, {1, 3, 6, 9, 10}, {1, 3, 5, 9, 10}, {1, 3, 5, 6, 10}, {1, 3, 5, 6, 9}, {1, 2, 6, 9, 10}, {1, 2, 5, 9, 10}, {1, 2, 5, 6, 10}, {1, 2, 5, 6, 9}, {1, 2, 3, 9, 10}, {1, 2, 3, 6, 10}, {1, 2, 3, 6, 9}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 9}, {1, 2, 3, 5, 6}, {0, 5, 6, 9, 10}, {0, 3, 6, 9, 10}, {0, 3, 5, 9, 10}, {0, 3, 5, 6, 10}, {0, 3, 5, 6, 9}, {0, 2, 6, 9, 10}, {0, 2, 5, 9, 10}, {0, 2, 5, 6, 10}, {0, 2, 5, 6, 9}, {0, 2, 3, 9, 10}, {0, 2, 3, 6, 10}, {0, 2, 3, 6, 9}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 9}, {0, 2, 3, 5, 6}, {0, 1, 6, 9, 10}, {0, 1, 5, 9, 10}, {0, 1, 5, 6, 10}, {0, 1, 5, 6, 9}, {0, 1, 3, 9, 10}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 9}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 6}, {0, 1, 2, 9, 10}, {0, 1, 2, 6, 10}, {0, 1, 2, 6, 9}, {0, 1, 2, 5, 10}, {0, 1, 2, 5, 9}, {0, 1, 2, 5, 6}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 6}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01647 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 5, 6, 9, 10} →
      polygon.card = 5 →
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {2, 5, 6, 9, 10} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {1, 5, 6, 9, 10} ∨
        polygon = {1, 3, 6, 9, 10} ∨
        polygon = {1, 3, 5, 9, 10} ∨
        polygon = {1, 3, 5, 6, 10} ∨
        polygon = {1, 3, 5, 6, 9} ∨
        polygon = {1, 2, 6, 9, 10} ∨
        polygon = {1, 2, 5, 9, 10} ∨
        polygon = {1, 2, 5, 6, 10} ∨
        polygon = {1, 2, 5, 6, 9} ∨
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {1, 2, 3, 6, 9} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {1, 2, 3, 5, 6} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 2, 6, 9, 10} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 5, 6, 9} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 5, 6} ∨
        polygon = {0, 1, 6, 9, 10} ∨
        polygon = {0, 1, 5, 9, 10} ∨
        polygon = {0, 1, 5, 6, 10} ∨
        polygon = {0, 1, 5, 6, 9} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 6} ∨
        polygon = {0, 1, 2, 9, 10} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 5, 9} ∨
        polygon = {0, 1, 2, 5, 6} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 6} ∨
        polygon = {0, 1, 2, 3, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 5, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01647] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask04719 :
    (({0, 1, 2, 3, 5, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 9, 12}, {2, 5, 6, 9, 12}, {2, 3, 6, 9, 12}, {2, 3, 5, 9, 12}, {2, 3, 5, 6, 12}, {2, 3, 5, 6, 9}, {1, 5, 6, 9, 12}, {1, 3, 6, 9, 12}, {1, 3, 5, 9, 12}, {1, 3, 5, 6, 12}, {1, 3, 5, 6, 9}, {1, 2, 6, 9, 12}, {1, 2, 5, 9, 12}, {1, 2, 5, 6, 12}, {1, 2, 5, 6, 9}, {1, 2, 3, 9, 12}, {1, 2, 3, 6, 12}, {1, 2, 3, 6, 9}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 9}, {1, 2, 3, 5, 6}, {0, 5, 6, 9, 12}, {0, 3, 6, 9, 12}, {0, 3, 5, 9, 12}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 9}, {0, 2, 6, 9, 12}, {0, 2, 5, 9, 12}, {0, 2, 5, 6, 12}, {0, 2, 5, 6, 9}, {0, 2, 3, 9, 12}, {0, 2, 3, 6, 12}, {0, 2, 3, 6, 9}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 9}, {0, 2, 3, 5, 6}, {0, 1, 6, 9, 12}, {0, 1, 5, 9, 12}, {0, 1, 5, 6, 12}, {0, 1, 5, 6, 9}, {0, 1, 3, 9, 12}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 9}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 6}, {0, 1, 2, 9, 12}, {0, 1, 2, 6, 12}, {0, 1, 2, 6, 9}, {0, 1, 2, 5, 12}, {0, 1, 2, 5, 9}, {0, 1, 2, 5, 6}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 6}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask04719 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 5, 6, 9, 12} →
      polygon.card = 5 →
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {2, 5, 6, 9, 12} ∨
        polygon = {2, 3, 6, 9, 12} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {1, 5, 6, 9, 12} ∨
        polygon = {1, 3, 6, 9, 12} ∨
        polygon = {1, 3, 5, 9, 12} ∨
        polygon = {1, 3, 5, 6, 12} ∨
        polygon = {1, 3, 5, 6, 9} ∨
        polygon = {1, 2, 6, 9, 12} ∨
        polygon = {1, 2, 5, 9, 12} ∨
        polygon = {1, 2, 5, 6, 12} ∨
        polygon = {1, 2, 5, 6, 9} ∨
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {1, 2, 3, 6, 9} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {1, 2, 3, 5, 6} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 2, 6, 9, 12} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 5, 6, 9} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 5, 6} ∨
        polygon = {0, 1, 6, 9, 12} ∨
        polygon = {0, 1, 5, 9, 12} ∨
        polygon = {0, 1, 5, 6, 12} ∨
        polygon = {0, 1, 5, 6, 9} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 6} ∨
        polygon = {0, 1, 2, 9, 12} ∨
        polygon = {0, 1, 2, 6, 12} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 5, 12} ∨
        polygon = {0, 1, 2, 5, 9} ∨
        polygon = {0, 1, 2, 5, 6} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 6} ∨
        polygon = {0, 1, 2, 3, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 5, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask04719] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask08815 :
    (({0, 1, 2, 3, 5, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 9, 13}, {2, 5, 6, 9, 13}, {2, 3, 6, 9, 13}, {2, 3, 5, 9, 13}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 9}, {1, 5, 6, 9, 13}, {1, 3, 6, 9, 13}, {1, 3, 5, 9, 13}, {1, 3, 5, 6, 13}, {1, 3, 5, 6, 9}, {1, 2, 6, 9, 13}, {1, 2, 5, 9, 13}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 9}, {1, 2, 3, 9, 13}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 9}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 9}, {1, 2, 3, 5, 6}, {0, 5, 6, 9, 13}, {0, 3, 6, 9, 13}, {0, 3, 5, 9, 13}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 9}, {0, 2, 6, 9, 13}, {0, 2, 5, 9, 13}, {0, 2, 5, 6, 13}, {0, 2, 5, 6, 9}, {0, 2, 3, 9, 13}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 9}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 9}, {0, 2, 3, 5, 6}, {0, 1, 6, 9, 13}, {0, 1, 5, 9, 13}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 9}, {0, 1, 3, 9, 13}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 9}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 6}, {0, 1, 2, 9, 13}, {0, 1, 2, 6, 13}, {0, 1, 2, 6, 9}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 9}, {0, 1, 2, 5, 6}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 6}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask08815 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 5, 6, 9, 13} →
      polygon.card = 5 →
        polygon = {3, 5, 6, 9, 13} ∨
        polygon = {2, 5, 6, 9, 13} ∨
        polygon = {2, 3, 6, 9, 13} ∨
        polygon = {2, 3, 5, 9, 13} ∨
        polygon = {2, 3, 5, 6, 13} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {1, 5, 6, 9, 13} ∨
        polygon = {1, 3, 6, 9, 13} ∨
        polygon = {1, 3, 5, 9, 13} ∨
        polygon = {1, 3, 5, 6, 13} ∨
        polygon = {1, 3, 5, 6, 9} ∨
        polygon = {1, 2, 6, 9, 13} ∨
        polygon = {1, 2, 5, 9, 13} ∨
        polygon = {1, 2, 5, 6, 13} ∨
        polygon = {1, 2, 5, 6, 9} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 6, 9} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {1, 2, 3, 5, 6} ∨
        polygon = {0, 5, 6, 9, 13} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 6, 13} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 2, 6, 9, 13} ∨
        polygon = {0, 2, 5, 9, 13} ∨
        polygon = {0, 2, 5, 6, 13} ∨
        polygon = {0, 2, 5, 6, 9} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 5, 6} ∨
        polygon = {0, 1, 6, 9, 13} ∨
        polygon = {0, 1, 5, 9, 13} ∨
        polygon = {0, 1, 5, 6, 13} ∨
        polygon = {0, 1, 5, 6, 9} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 6} ∨
        polygon = {0, 1, 2, 9, 13} ∨
        polygon = {0, 1, 2, 6, 13} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 5, 13} ∨
        polygon = {0, 1, 2, 5, 9} ∨
        polygon = {0, 1, 2, 5, 6} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 6} ∨
        polygon = {0, 1, 2, 3, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 5, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask08815] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17007 :
    (({0, 1, 2, 3, 5, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 9, 14}, {2, 5, 6, 9, 14}, {2, 3, 6, 9, 14}, {2, 3, 5, 9, 14}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 9}, {1, 5, 6, 9, 14}, {1, 3, 6, 9, 14}, {1, 3, 5, 9, 14}, {1, 3, 5, 6, 14}, {1, 3, 5, 6, 9}, {1, 2, 6, 9, 14}, {1, 2, 5, 9, 14}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 9}, {1, 2, 3, 9, 14}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 9}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 9}, {1, 2, 3, 5, 6}, {0, 5, 6, 9, 14}, {0, 3, 6, 9, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 9}, {0, 2, 6, 9, 14}, {0, 2, 5, 9, 14}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 9}, {0, 2, 3, 9, 14}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 9}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 9}, {0, 2, 3, 5, 6}, {0, 1, 6, 9, 14}, {0, 1, 5, 9, 14}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 9}, {0, 1, 3, 9, 14}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 9}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 6}, {0, 1, 2, 9, 14}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 9}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 9}, {0, 1, 2, 5, 6}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 6}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17007 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 5, 6, 9, 14} →
      polygon.card = 5 →
        polygon = {3, 5, 6, 9, 14} ∨
        polygon = {2, 5, 6, 9, 14} ∨
        polygon = {2, 3, 6, 9, 14} ∨
        polygon = {2, 3, 5, 9, 14} ∨
        polygon = {2, 3, 5, 6, 14} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {1, 5, 6, 9, 14} ∨
        polygon = {1, 3, 6, 9, 14} ∨
        polygon = {1, 3, 5, 9, 14} ∨
        polygon = {1, 3, 5, 6, 14} ∨
        polygon = {1, 3, 5, 6, 9} ∨
        polygon = {1, 2, 6, 9, 14} ∨
        polygon = {1, 2, 5, 9, 14} ∨
        polygon = {1, 2, 5, 6, 14} ∨
        polygon = {1, 2, 5, 6, 9} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 9} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {1, 2, 3, 5, 6} ∨
        polygon = {0, 5, 6, 9, 14} ∨
        polygon = {0, 3, 6, 9, 14} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 6, 14} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 2, 6, 9, 14} ∨
        polygon = {0, 2, 5, 9, 14} ∨
        polygon = {0, 2, 5, 6, 14} ∨
        polygon = {0, 2, 5, 6, 9} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 5, 6} ∨
        polygon = {0, 1, 6, 9, 14} ∨
        polygon = {0, 1, 5, 9, 14} ∨
        polygon = {0, 1, 5, 6, 14} ∨
        polygon = {0, 1, 5, 6, 9} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 6} ∨
        polygon = {0, 1, 2, 9, 14} ∨
        polygon = {0, 1, 2, 6, 14} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 5, 14} ∨
        polygon = {0, 1, 2, 5, 9} ∨
        polygon = {0, 1, 2, 5, 6} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 6} ∨
        polygon = {0, 1, 2, 3, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 5, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17007] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05231 :
    (({0, 1, 2, 3, 5, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 10, 12}, {2, 5, 6, 10, 12}, {2, 3, 6, 10, 12}, {2, 3, 5, 10, 12}, {2, 3, 5, 6, 12}, {2, 3, 5, 6, 10}, {1, 5, 6, 10, 12}, {1, 3, 6, 10, 12}, {1, 3, 5, 10, 12}, {1, 3, 5, 6, 12}, {1, 3, 5, 6, 10}, {1, 2, 6, 10, 12}, {1, 2, 5, 10, 12}, {1, 2, 5, 6, 12}, {1, 2, 5, 6, 10}, {1, 2, 3, 10, 12}, {1, 2, 3, 6, 12}, {1, 2, 3, 6, 10}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 6}, {0, 5, 6, 10, 12}, {0, 3, 6, 10, 12}, {0, 3, 5, 10, 12}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 10}, {0, 2, 6, 10, 12}, {0, 2, 5, 10, 12}, {0, 2, 5, 6, 12}, {0, 2, 5, 6, 10}, {0, 2, 3, 10, 12}, {0, 2, 3, 6, 12}, {0, 2, 3, 6, 10}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 6}, {0, 1, 6, 10, 12}, {0, 1, 5, 10, 12}, {0, 1, 5, 6, 12}, {0, 1, 5, 6, 10}, {0, 1, 3, 10, 12}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 10}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 6}, {0, 1, 2, 10, 12}, {0, 1, 2, 6, 12}, {0, 1, 2, 6, 10}, {0, 1, 2, 5, 12}, {0, 1, 2, 5, 10}, {0, 1, 2, 5, 6}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 6}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05231 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 5, 6, 10, 12} →
      polygon.card = 5 →
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {2, 5, 6, 10, 12} ∨
        polygon = {2, 3, 6, 10, 12} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {1, 5, 6, 10, 12} ∨
        polygon = {1, 3, 6, 10, 12} ∨
        polygon = {1, 3, 5, 10, 12} ∨
        polygon = {1, 3, 5, 6, 12} ∨
        polygon = {1, 3, 5, 6, 10} ∨
        polygon = {1, 2, 6, 10, 12} ∨
        polygon = {1, 2, 5, 10, 12} ∨
        polygon = {1, 2, 5, 6, 12} ∨
        polygon = {1, 2, 5, 6, 10} ∨
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 6} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 2, 6, 10, 12} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 6} ∨
        polygon = {0, 1, 6, 10, 12} ∨
        polygon = {0, 1, 5, 10, 12} ∨
        polygon = {0, 1, 5, 6, 12} ∨
        polygon = {0, 1, 5, 6, 10} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 6} ∨
        polygon = {0, 1, 2, 10, 12} ∨
        polygon = {0, 1, 2, 6, 12} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 5, 12} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 5, 6} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 6} ∨
        polygon = {0, 1, 2, 3, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 5, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05231] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09327 :
    (({0, 1, 2, 3, 5, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 10, 13}, {2, 5, 6, 10, 13}, {2, 3, 6, 10, 13}, {2, 3, 5, 10, 13}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 10}, {1, 5, 6, 10, 13}, {1, 3, 6, 10, 13}, {1, 3, 5, 10, 13}, {1, 3, 5, 6, 13}, {1, 3, 5, 6, 10}, {1, 2, 6, 10, 13}, {1, 2, 5, 10, 13}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 10}, {1, 2, 3, 10, 13}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 10}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 6}, {0, 5, 6, 10, 13}, {0, 3, 6, 10, 13}, {0, 3, 5, 10, 13}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 10}, {0, 2, 6, 10, 13}, {0, 2, 5, 10, 13}, {0, 2, 5, 6, 13}, {0, 2, 5, 6, 10}, {0, 2, 3, 10, 13}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 10}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 6}, {0, 1, 6, 10, 13}, {0, 1, 5, 10, 13}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 10}, {0, 1, 3, 10, 13}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 10}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 6}, {0, 1, 2, 10, 13}, {0, 1, 2, 6, 13}, {0, 1, 2, 6, 10}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 10}, {0, 1, 2, 5, 6}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 6}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09327 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 5, 6, 10, 13} →
      polygon.card = 5 →
        polygon = {3, 5, 6, 10, 13} ∨
        polygon = {2, 5, 6, 10, 13} ∨
        polygon = {2, 3, 6, 10, 13} ∨
        polygon = {2, 3, 5, 10, 13} ∨
        polygon = {2, 3, 5, 6, 13} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {1, 5, 6, 10, 13} ∨
        polygon = {1, 3, 6, 10, 13} ∨
        polygon = {1, 3, 5, 10, 13} ∨
        polygon = {1, 3, 5, 6, 13} ∨
        polygon = {1, 3, 5, 6, 10} ∨
        polygon = {1, 2, 6, 10, 13} ∨
        polygon = {1, 2, 5, 10, 13} ∨
        polygon = {1, 2, 5, 6, 13} ∨
        polygon = {1, 2, 5, 6, 10} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 6} ∨
        polygon = {0, 5, 6, 10, 13} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 6, 13} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 2, 6, 10, 13} ∨
        polygon = {0, 2, 5, 10, 13} ∨
        polygon = {0, 2, 5, 6, 13} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 6} ∨
        polygon = {0, 1, 6, 10, 13} ∨
        polygon = {0, 1, 5, 10, 13} ∨
        polygon = {0, 1, 5, 6, 13} ∨
        polygon = {0, 1, 5, 6, 10} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 6} ∨
        polygon = {0, 1, 2, 10, 13} ∨
        polygon = {0, 1, 2, 6, 13} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 5, 13} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 5, 6} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 6} ∨
        polygon = {0, 1, 2, 3, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 5, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09327] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17519 :
    (({0, 1, 2, 3, 5, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 10, 14}, {2, 5, 6, 10, 14}, {2, 3, 6, 10, 14}, {2, 3, 5, 10, 14}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 10}, {1, 5, 6, 10, 14}, {1, 3, 6, 10, 14}, {1, 3, 5, 10, 14}, {1, 3, 5, 6, 14}, {1, 3, 5, 6, 10}, {1, 2, 6, 10, 14}, {1, 2, 5, 10, 14}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 10}, {1, 2, 3, 10, 14}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 10}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 6}, {0, 5, 6, 10, 14}, {0, 3, 6, 10, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 10}, {0, 2, 6, 10, 14}, {0, 2, 5, 10, 14}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 10}, {0, 2, 3, 10, 14}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 10}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 6}, {0, 1, 6, 10, 14}, {0, 1, 5, 10, 14}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 10}, {0, 1, 3, 10, 14}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 10}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 6}, {0, 1, 2, 10, 14}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 10}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 10}, {0, 1, 2, 5, 6}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 6}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17519 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 5, 6, 10, 14} →
      polygon.card = 5 →
        polygon = {3, 5, 6, 10, 14} ∨
        polygon = {2, 5, 6, 10, 14} ∨
        polygon = {2, 3, 6, 10, 14} ∨
        polygon = {2, 3, 5, 10, 14} ∨
        polygon = {2, 3, 5, 6, 14} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {1, 5, 6, 10, 14} ∨
        polygon = {1, 3, 6, 10, 14} ∨
        polygon = {1, 3, 5, 10, 14} ∨
        polygon = {1, 3, 5, 6, 14} ∨
        polygon = {1, 3, 5, 6, 10} ∨
        polygon = {1, 2, 6, 10, 14} ∨
        polygon = {1, 2, 5, 10, 14} ∨
        polygon = {1, 2, 5, 6, 14} ∨
        polygon = {1, 2, 5, 6, 10} ∨
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 6} ∨
        polygon = {0, 5, 6, 10, 14} ∨
        polygon = {0, 3, 6, 10, 14} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 6, 14} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 2, 6, 10, 14} ∨
        polygon = {0, 2, 5, 10, 14} ∨
        polygon = {0, 2, 5, 6, 14} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 6} ∨
        polygon = {0, 1, 6, 10, 14} ∨
        polygon = {0, 1, 5, 10, 14} ∨
        polygon = {0, 1, 5, 6, 14} ∨
        polygon = {0, 1, 5, 6, 10} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 6} ∨
        polygon = {0, 1, 2, 10, 14} ∨
        polygon = {0, 1, 2, 6, 14} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 5, 14} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 5, 6} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 6} ∨
        polygon = {0, 1, 2, 3, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 5, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17519] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12399 :
    (({0, 1, 2, 3, 5, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 12, 13}, {2, 5, 6, 12, 13}, {2, 3, 6, 12, 13}, {2, 3, 5, 12, 13}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 12}, {1, 5, 6, 12, 13}, {1, 3, 6, 12, 13}, {1, 3, 5, 12, 13}, {1, 3, 5, 6, 13}, {1, 3, 5, 6, 12}, {1, 2, 6, 12, 13}, {1, 2, 5, 12, 13}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 12}, {1, 2, 3, 12, 13}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 12}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 6}, {0, 5, 6, 12, 13}, {0, 3, 6, 12, 13}, {0, 3, 5, 12, 13}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 12}, {0, 2, 6, 12, 13}, {0, 2, 5, 12, 13}, {0, 2, 5, 6, 13}, {0, 2, 5, 6, 12}, {0, 2, 3, 12, 13}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 12}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 6}, {0, 1, 6, 12, 13}, {0, 1, 5, 12, 13}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 12}, {0, 1, 3, 12, 13}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 12}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 6}, {0, 1, 2, 12, 13}, {0, 1, 2, 6, 13}, {0, 1, 2, 6, 12}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 12}, {0, 1, 2, 5, 6}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 6}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12399 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 5, 6, 12, 13} →
      polygon.card = 5 →
        polygon = {3, 5, 6, 12, 13} ∨
        polygon = {2, 5, 6, 12, 13} ∨
        polygon = {2, 3, 6, 12, 13} ∨
        polygon = {2, 3, 5, 12, 13} ∨
        polygon = {2, 3, 5, 6, 13} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {1, 5, 6, 12, 13} ∨
        polygon = {1, 3, 6, 12, 13} ∨
        polygon = {1, 3, 5, 12, 13} ∨
        polygon = {1, 3, 5, 6, 13} ∨
        polygon = {1, 3, 5, 6, 12} ∨
        polygon = {1, 2, 6, 12, 13} ∨
        polygon = {1, 2, 5, 12, 13} ∨
        polygon = {1, 2, 5, 6, 13} ∨
        polygon = {1, 2, 5, 6, 12} ∨
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 6} ∨
        polygon = {0, 5, 6, 12, 13} ∨
        polygon = {0, 3, 6, 12, 13} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 6, 13} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 2, 6, 12, 13} ∨
        polygon = {0, 2, 5, 12, 13} ∨
        polygon = {0, 2, 5, 6, 13} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 6} ∨
        polygon = {0, 1, 6, 12, 13} ∨
        polygon = {0, 1, 5, 12, 13} ∨
        polygon = {0, 1, 5, 6, 13} ∨
        polygon = {0, 1, 5, 6, 12} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 6} ∨
        polygon = {0, 1, 2, 12, 13} ∨
        polygon = {0, 1, 2, 6, 13} ∨
        polygon = {0, 1, 2, 6, 12} ∨
        polygon = {0, 1, 2, 5, 13} ∨
        polygon = {0, 1, 2, 5, 12} ∨
        polygon = {0, 1, 2, 5, 6} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 6} ∨
        polygon = {0, 1, 2, 3, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 5, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12399] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask20591 :
    (({0, 1, 2, 3, 5, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 12, 14}, {2, 5, 6, 12, 14}, {2, 3, 6, 12, 14}, {2, 3, 5, 12, 14}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 12}, {1, 5, 6, 12, 14}, {1, 3, 6, 12, 14}, {1, 3, 5, 12, 14}, {1, 3, 5, 6, 14}, {1, 3, 5, 6, 12}, {1, 2, 6, 12, 14}, {1, 2, 5, 12, 14}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 12}, {1, 2, 3, 12, 14}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 12}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 6}, {0, 5, 6, 12, 14}, {0, 3, 6, 12, 14}, {0, 3, 5, 12, 14}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 12}, {0, 2, 6, 12, 14}, {0, 2, 5, 12, 14}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 12}, {0, 2, 3, 12, 14}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 12}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 6}, {0, 1, 6, 12, 14}, {0, 1, 5, 12, 14}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 12}, {0, 1, 3, 12, 14}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 12}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 6}, {0, 1, 2, 12, 14}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 12}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 12}, {0, 1, 2, 5, 6}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 6}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask20591 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 5, 6, 12, 14} →
      polygon.card = 5 →
        polygon = {3, 5, 6, 12, 14} ∨
        polygon = {2, 5, 6, 12, 14} ∨
        polygon = {2, 3, 6, 12, 14} ∨
        polygon = {2, 3, 5, 12, 14} ∨
        polygon = {2, 3, 5, 6, 14} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {1, 5, 6, 12, 14} ∨
        polygon = {1, 3, 6, 12, 14} ∨
        polygon = {1, 3, 5, 12, 14} ∨
        polygon = {1, 3, 5, 6, 14} ∨
        polygon = {1, 3, 5, 6, 12} ∨
        polygon = {1, 2, 6, 12, 14} ∨
        polygon = {1, 2, 5, 12, 14} ∨
        polygon = {1, 2, 5, 6, 14} ∨
        polygon = {1, 2, 5, 6, 12} ∨
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 6} ∨
        polygon = {0, 5, 6, 12, 14} ∨
        polygon = {0, 3, 6, 12, 14} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 5, 6, 14} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 2, 6, 12, 14} ∨
        polygon = {0, 2, 5, 12, 14} ∨
        polygon = {0, 2, 5, 6, 14} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 6} ∨
        polygon = {0, 1, 6, 12, 14} ∨
        polygon = {0, 1, 5, 12, 14} ∨
        polygon = {0, 1, 5, 6, 14} ∨
        polygon = {0, 1, 5, 6, 12} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 6} ∨
        polygon = {0, 1, 2, 12, 14} ∨
        polygon = {0, 1, 2, 6, 14} ∨
        polygon = {0, 1, 2, 6, 12} ∨
        polygon = {0, 1, 2, 5, 14} ∨
        polygon = {0, 1, 2, 5, 12} ∨
        polygon = {0, 1, 2, 5, 6} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 6} ∨
        polygon = {0, 1, 2, 3, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 5, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask20591] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask24687 :
    (({0, 1, 2, 3, 5, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 13, 14}, {2, 5, 6, 13, 14}, {2, 3, 6, 13, 14}, {2, 3, 5, 13, 14}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 13}, {1, 5, 6, 13, 14}, {1, 3, 6, 13, 14}, {1, 3, 5, 13, 14}, {1, 3, 5, 6, 14}, {1, 3, 5, 6, 13}, {1, 2, 6, 13, 14}, {1, 2, 5, 13, 14}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 13}, {1, 2, 3, 13, 14}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 13}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 6}, {0, 5, 6, 13, 14}, {0, 3, 6, 13, 14}, {0, 3, 5, 13, 14}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 13}, {0, 2, 6, 13, 14}, {0, 2, 5, 13, 14}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 13}, {0, 2, 3, 13, 14}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 13}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 6}, {0, 1, 6, 13, 14}, {0, 1, 5, 13, 14}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 13}, {0, 1, 3, 13, 14}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 13}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 6}, {0, 1, 2, 13, 14}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 13}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 6}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 6}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask24687 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 5, 6, 13, 14} →
      polygon.card = 5 →
        polygon = {3, 5, 6, 13, 14} ∨
        polygon = {2, 5, 6, 13, 14} ∨
        polygon = {2, 3, 6, 13, 14} ∨
        polygon = {2, 3, 5, 13, 14} ∨
        polygon = {2, 3, 5, 6, 14} ∨
        polygon = {2, 3, 5, 6, 13} ∨
        polygon = {1, 5, 6, 13, 14} ∨
        polygon = {1, 3, 6, 13, 14} ∨
        polygon = {1, 3, 5, 13, 14} ∨
        polygon = {1, 3, 5, 6, 14} ∨
        polygon = {1, 3, 5, 6, 13} ∨
        polygon = {1, 2, 6, 13, 14} ∨
        polygon = {1, 2, 5, 13, 14} ∨
        polygon = {1, 2, 5, 6, 14} ∨
        polygon = {1, 2, 5, 6, 13} ∨
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 6} ∨
        polygon = {0, 5, 6, 13, 14} ∨
        polygon = {0, 3, 6, 13, 14} ∨
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 6, 14} ∨
        polygon = {0, 3, 5, 6, 13} ∨
        polygon = {0, 2, 6, 13, 14} ∨
        polygon = {0, 2, 5, 13, 14} ∨
        polygon = {0, 2, 5, 6, 14} ∨
        polygon = {0, 2, 5, 6, 13} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 6} ∨
        polygon = {0, 1, 6, 13, 14} ∨
        polygon = {0, 1, 5, 13, 14} ∨
        polygon = {0, 1, 5, 6, 14} ∨
        polygon = {0, 1, 5, 6, 13} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 6} ∨
        polygon = {0, 1, 2, 13, 14} ∨
        polygon = {0, 1, 2, 6, 14} ∨
        polygon = {0, 1, 2, 6, 13} ∨
        polygon = {0, 1, 2, 5, 14} ∨
        polygon = {0, 1, 2, 5, 13} ∨
        polygon = {0, 1, 2, 5, 6} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 6} ∨
        polygon = {0, 1, 2, 3, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 5, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask24687] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01711 :
    (({0, 1, 2, 3, 5, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 9, 10}, {2, 5, 7, 9, 10}, {2, 3, 7, 9, 10}, {2, 3, 5, 9, 10}, {2, 3, 5, 7, 10}, {2, 3, 5, 7, 9}, {1, 5, 7, 9, 10}, {1, 3, 7, 9, 10}, {1, 3, 5, 9, 10}, {1, 3, 5, 7, 10}, {1, 3, 5, 7, 9}, {1, 2, 7, 9, 10}, {1, 2, 5, 9, 10}, {1, 2, 5, 7, 10}, {1, 2, 5, 7, 9}, {1, 2, 3, 9, 10}, {1, 2, 3, 7, 10}, {1, 2, 3, 7, 9}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 9}, {1, 2, 3, 5, 7}, {0, 5, 7, 9, 10}, {0, 3, 7, 9, 10}, {0, 3, 5, 9, 10}, {0, 3, 5, 7, 10}, {0, 3, 5, 7, 9}, {0, 2, 7, 9, 10}, {0, 2, 5, 9, 10}, {0, 2, 5, 7, 10}, {0, 2, 5, 7, 9}, {0, 2, 3, 9, 10}, {0, 2, 3, 7, 10}, {0, 2, 3, 7, 9}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 9}, {0, 2, 3, 5, 7}, {0, 1, 7, 9, 10}, {0, 1, 5, 9, 10}, {0, 1, 5, 7, 10}, {0, 1, 5, 7, 9}, {0, 1, 3, 9, 10}, {0, 1, 3, 7, 10}, {0, 1, 3, 7, 9}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 7}, {0, 1, 2, 9, 10}, {0, 1, 2, 7, 10}, {0, 1, 2, 7, 9}, {0, 1, 2, 5, 10}, {0, 1, 2, 5, 9}, {0, 1, 2, 5, 7}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01711 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 5, 7, 9, 10} →
      polygon.card = 5 →
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {1, 5, 7, 9, 10} ∨
        polygon = {1, 3, 7, 9, 10} ∨
        polygon = {1, 3, 5, 9, 10} ∨
        polygon = {1, 3, 5, 7, 10} ∨
        polygon = {1, 3, 5, 7, 9} ∨
        polygon = {1, 2, 7, 9, 10} ∨
        polygon = {1, 2, 5, 9, 10} ∨
        polygon = {1, 2, 5, 7, 10} ∨
        polygon = {1, 2, 5, 7, 9} ∨
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {1, 2, 3, 5, 7} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 1, 7, 9, 10} ∨
        polygon = {0, 1, 5, 9, 10} ∨
        polygon = {0, 1, 5, 7, 10} ∨
        polygon = {0, 1, 5, 7, 9} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 2, 9, 10} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 7, 9} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 5, 9} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 5, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01711] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask04783 :
    (({0, 1, 2, 3, 5, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 9, 12}, {2, 5, 7, 9, 12}, {2, 3, 7, 9, 12}, {2, 3, 5, 9, 12}, {2, 3, 5, 7, 12}, {2, 3, 5, 7, 9}, {1, 5, 7, 9, 12}, {1, 3, 7, 9, 12}, {1, 3, 5, 9, 12}, {1, 3, 5, 7, 12}, {1, 3, 5, 7, 9}, {1, 2, 7, 9, 12}, {1, 2, 5, 9, 12}, {1, 2, 5, 7, 12}, {1, 2, 5, 7, 9}, {1, 2, 3, 9, 12}, {1, 2, 3, 7, 12}, {1, 2, 3, 7, 9}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 9}, {1, 2, 3, 5, 7}, {0, 5, 7, 9, 12}, {0, 3, 7, 9, 12}, {0, 3, 5, 9, 12}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 9}, {0, 2, 7, 9, 12}, {0, 2, 5, 9, 12}, {0, 2, 5, 7, 12}, {0, 2, 5, 7, 9}, {0, 2, 3, 9, 12}, {0, 2, 3, 7, 12}, {0, 2, 3, 7, 9}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 9}, {0, 2, 3, 5, 7}, {0, 1, 7, 9, 12}, {0, 1, 5, 9, 12}, {0, 1, 5, 7, 12}, {0, 1, 5, 7, 9}, {0, 1, 3, 9, 12}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 9}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 7}, {0, 1, 2, 9, 12}, {0, 1, 2, 7, 12}, {0, 1, 2, 7, 9}, {0, 1, 2, 5, 12}, {0, 1, 2, 5, 9}, {0, 1, 2, 5, 7}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask04783 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 5, 7, 9, 12} →
      polygon.card = 5 →
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {2, 5, 7, 9, 12} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {1, 5, 7, 9, 12} ∨
        polygon = {1, 3, 7, 9, 12} ∨
        polygon = {1, 3, 5, 9, 12} ∨
        polygon = {1, 3, 5, 7, 12} ∨
        polygon = {1, 3, 5, 7, 9} ∨
        polygon = {1, 2, 7, 9, 12} ∨
        polygon = {1, 2, 5, 9, 12} ∨
        polygon = {1, 2, 5, 7, 12} ∨
        polygon = {1, 2, 5, 7, 9} ∨
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {1, 2, 3, 5, 7} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 1, 7, 9, 12} ∨
        polygon = {0, 1, 5, 9, 12} ∨
        polygon = {0, 1, 5, 7, 12} ∨
        polygon = {0, 1, 5, 7, 9} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 2, 9, 12} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 7, 9} ∨
        polygon = {0, 1, 2, 5, 12} ∨
        polygon = {0, 1, 2, 5, 9} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 5, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask04783] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask08879 :
    (({0, 1, 2, 3, 5, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 9, 13}, {2, 5, 7, 9, 13}, {2, 3, 7, 9, 13}, {2, 3, 5, 9, 13}, {2, 3, 5, 7, 13}, {2, 3, 5, 7, 9}, {1, 5, 7, 9, 13}, {1, 3, 7, 9, 13}, {1, 3, 5, 9, 13}, {1, 3, 5, 7, 13}, {1, 3, 5, 7, 9}, {1, 2, 7, 9, 13}, {1, 2, 5, 9, 13}, {1, 2, 5, 7, 13}, {1, 2, 5, 7, 9}, {1, 2, 3, 9, 13}, {1, 2, 3, 7, 13}, {1, 2, 3, 7, 9}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 9}, {1, 2, 3, 5, 7}, {0, 5, 7, 9, 13}, {0, 3, 7, 9, 13}, {0, 3, 5, 9, 13}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 9}, {0, 2, 7, 9, 13}, {0, 2, 5, 9, 13}, {0, 2, 5, 7, 13}, {0, 2, 5, 7, 9}, {0, 2, 3, 9, 13}, {0, 2, 3, 7, 13}, {0, 2, 3, 7, 9}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 9}, {0, 2, 3, 5, 7}, {0, 1, 7, 9, 13}, {0, 1, 5, 9, 13}, {0, 1, 5, 7, 13}, {0, 1, 5, 7, 9}, {0, 1, 3, 9, 13}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 9}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 7}, {0, 1, 2, 9, 13}, {0, 1, 2, 7, 13}, {0, 1, 2, 7, 9}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 9}, {0, 1, 2, 5, 7}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask08879 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 5, 7, 9, 13} →
      polygon.card = 5 →
        polygon = {3, 5, 7, 9, 13} ∨
        polygon = {2, 5, 7, 9, 13} ∨
        polygon = {2, 3, 7, 9, 13} ∨
        polygon = {2, 3, 5, 9, 13} ∨
        polygon = {2, 3, 5, 7, 13} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {1, 5, 7, 9, 13} ∨
        polygon = {1, 3, 7, 9, 13} ∨
        polygon = {1, 3, 5, 9, 13} ∨
        polygon = {1, 3, 5, 7, 13} ∨
        polygon = {1, 3, 5, 7, 9} ∨
        polygon = {1, 2, 7, 9, 13} ∨
        polygon = {1, 2, 5, 9, 13} ∨
        polygon = {1, 2, 5, 7, 13} ∨
        polygon = {1, 2, 5, 7, 9} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {1, 2, 3, 5, 7} ∨
        polygon = {0, 5, 7, 9, 13} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 2, 7, 9, 13} ∨
        polygon = {0, 2, 5, 9, 13} ∨
        polygon = {0, 2, 5, 7, 13} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 1, 7, 9, 13} ∨
        polygon = {0, 1, 5, 9, 13} ∨
        polygon = {0, 1, 5, 7, 13} ∨
        polygon = {0, 1, 5, 7, 9} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 2, 9, 13} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 7, 9} ∨
        polygon = {0, 1, 2, 5, 13} ∨
        polygon = {0, 1, 2, 5, 9} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 5, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask08879] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17071 :
    (({0, 1, 2, 3, 5, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 9, 14}, {2, 5, 7, 9, 14}, {2, 3, 7, 9, 14}, {2, 3, 5, 9, 14}, {2, 3, 5, 7, 14}, {2, 3, 5, 7, 9}, {1, 5, 7, 9, 14}, {1, 3, 7, 9, 14}, {1, 3, 5, 9, 14}, {1, 3, 5, 7, 14}, {1, 3, 5, 7, 9}, {1, 2, 7, 9, 14}, {1, 2, 5, 9, 14}, {1, 2, 5, 7, 14}, {1, 2, 5, 7, 9}, {1, 2, 3, 9, 14}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 9}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 9}, {1, 2, 3, 5, 7}, {0, 5, 7, 9, 14}, {0, 3, 7, 9, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 9}, {0, 2, 7, 9, 14}, {0, 2, 5, 9, 14}, {0, 2, 5, 7, 14}, {0, 2, 5, 7, 9}, {0, 2, 3, 9, 14}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 9}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 9}, {0, 2, 3, 5, 7}, {0, 1, 7, 9, 14}, {0, 1, 5, 9, 14}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 9}, {0, 1, 3, 9, 14}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 9}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 7}, {0, 1, 2, 9, 14}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 9}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 9}, {0, 1, 2, 5, 7}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17071 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 5, 7, 9, 14} →
      polygon.card = 5 →
        polygon = {3, 5, 7, 9, 14} ∨
        polygon = {2, 5, 7, 9, 14} ∨
        polygon = {2, 3, 7, 9, 14} ∨
        polygon = {2, 3, 5, 9, 14} ∨
        polygon = {2, 3, 5, 7, 14} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {1, 5, 7, 9, 14} ∨
        polygon = {1, 3, 7, 9, 14} ∨
        polygon = {1, 3, 5, 9, 14} ∨
        polygon = {1, 3, 5, 7, 14} ∨
        polygon = {1, 3, 5, 7, 9} ∨
        polygon = {1, 2, 7, 9, 14} ∨
        polygon = {1, 2, 5, 9, 14} ∨
        polygon = {1, 2, 5, 7, 14} ∨
        polygon = {1, 2, 5, 7, 9} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {1, 2, 3, 5, 7} ∨
        polygon = {0, 5, 7, 9, 14} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 2, 7, 9, 14} ∨
        polygon = {0, 2, 5, 9, 14} ∨
        polygon = {0, 2, 5, 7, 14} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 1, 7, 9, 14} ∨
        polygon = {0, 1, 5, 9, 14} ∨
        polygon = {0, 1, 5, 7, 14} ∨
        polygon = {0, 1, 5, 7, 9} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 2, 9, 14} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 7, 9} ∨
        polygon = {0, 1, 2, 5, 14} ∨
        polygon = {0, 1, 2, 5, 9} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 5, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17071] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05295 :
    (({0, 1, 2, 3, 5, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 10, 12}, {2, 5, 7, 10, 12}, {2, 3, 7, 10, 12}, {2, 3, 5, 10, 12}, {2, 3, 5, 7, 12}, {2, 3, 5, 7, 10}, {1, 5, 7, 10, 12}, {1, 3, 7, 10, 12}, {1, 3, 5, 10, 12}, {1, 3, 5, 7, 12}, {1, 3, 5, 7, 10}, {1, 2, 7, 10, 12}, {1, 2, 5, 10, 12}, {1, 2, 5, 7, 12}, {1, 2, 5, 7, 10}, {1, 2, 3, 10, 12}, {1, 2, 3, 7, 12}, {1, 2, 3, 7, 10}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 7}, {0, 5, 7, 10, 12}, {0, 3, 7, 10, 12}, {0, 3, 5, 10, 12}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 10}, {0, 2, 7, 10, 12}, {0, 2, 5, 10, 12}, {0, 2, 5, 7, 12}, {0, 2, 5, 7, 10}, {0, 2, 3, 10, 12}, {0, 2, 3, 7, 12}, {0, 2, 3, 7, 10}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 7}, {0, 1, 7, 10, 12}, {0, 1, 5, 10, 12}, {0, 1, 5, 7, 12}, {0, 1, 5, 7, 10}, {0, 1, 3, 10, 12}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 10}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 7}, {0, 1, 2, 10, 12}, {0, 1, 2, 7, 12}, {0, 1, 2, 7, 10}, {0, 1, 2, 5, 12}, {0, 1, 2, 5, 10}, {0, 1, 2, 5, 7}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05295 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 5, 7, 10, 12} →
      polygon.card = 5 →
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {2, 5, 7, 10, 12} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {1, 5, 7, 10, 12} ∨
        polygon = {1, 3, 7, 10, 12} ∨
        polygon = {1, 3, 5, 10, 12} ∨
        polygon = {1, 3, 5, 7, 12} ∨
        polygon = {1, 3, 5, 7, 10} ∨
        polygon = {1, 2, 7, 10, 12} ∨
        polygon = {1, 2, 5, 10, 12} ∨
        polygon = {1, 2, 5, 7, 12} ∨
        polygon = {1, 2, 5, 7, 10} ∨
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 7} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 1, 7, 10, 12} ∨
        polygon = {0, 1, 5, 10, 12} ∨
        polygon = {0, 1, 5, 7, 12} ∨
        polygon = {0, 1, 5, 7, 10} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 2, 10, 12} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 5, 12} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 5, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05295] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09391 :
    (({0, 1, 2, 3, 5, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 10, 13}, {2, 5, 7, 10, 13}, {2, 3, 7, 10, 13}, {2, 3, 5, 10, 13}, {2, 3, 5, 7, 13}, {2, 3, 5, 7, 10}, {1, 5, 7, 10, 13}, {1, 3, 7, 10, 13}, {1, 3, 5, 10, 13}, {1, 3, 5, 7, 13}, {1, 3, 5, 7, 10}, {1, 2, 7, 10, 13}, {1, 2, 5, 10, 13}, {1, 2, 5, 7, 13}, {1, 2, 5, 7, 10}, {1, 2, 3, 10, 13}, {1, 2, 3, 7, 13}, {1, 2, 3, 7, 10}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 7}, {0, 5, 7, 10, 13}, {0, 3, 7, 10, 13}, {0, 3, 5, 10, 13}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 10}, {0, 2, 7, 10, 13}, {0, 2, 5, 10, 13}, {0, 2, 5, 7, 13}, {0, 2, 5, 7, 10}, {0, 2, 3, 10, 13}, {0, 2, 3, 7, 13}, {0, 2, 3, 7, 10}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 7}, {0, 1, 7, 10, 13}, {0, 1, 5, 10, 13}, {0, 1, 5, 7, 13}, {0, 1, 5, 7, 10}, {0, 1, 3, 10, 13}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 10}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 7}, {0, 1, 2, 10, 13}, {0, 1, 2, 7, 13}, {0, 1, 2, 7, 10}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 10}, {0, 1, 2, 5, 7}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09391 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 5, 7, 10, 13} →
      polygon.card = 5 →
        polygon = {3, 5, 7, 10, 13} ∨
        polygon = {2, 5, 7, 10, 13} ∨
        polygon = {2, 3, 7, 10, 13} ∨
        polygon = {2, 3, 5, 10, 13} ∨
        polygon = {2, 3, 5, 7, 13} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {1, 5, 7, 10, 13} ∨
        polygon = {1, 3, 7, 10, 13} ∨
        polygon = {1, 3, 5, 10, 13} ∨
        polygon = {1, 3, 5, 7, 13} ∨
        polygon = {1, 3, 5, 7, 10} ∨
        polygon = {1, 2, 7, 10, 13} ∨
        polygon = {1, 2, 5, 10, 13} ∨
        polygon = {1, 2, 5, 7, 13} ∨
        polygon = {1, 2, 5, 7, 10} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 7} ∨
        polygon = {0, 5, 7, 10, 13} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 2, 7, 10, 13} ∨
        polygon = {0, 2, 5, 10, 13} ∨
        polygon = {0, 2, 5, 7, 13} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 1, 7, 10, 13} ∨
        polygon = {0, 1, 5, 10, 13} ∨
        polygon = {0, 1, 5, 7, 13} ∨
        polygon = {0, 1, 5, 7, 10} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 2, 10, 13} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 5, 13} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 5, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09391] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17583 :
    (({0, 1, 2, 3, 5, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 10, 14}, {2, 5, 7, 10, 14}, {2, 3, 7, 10, 14}, {2, 3, 5, 10, 14}, {2, 3, 5, 7, 14}, {2, 3, 5, 7, 10}, {1, 5, 7, 10, 14}, {1, 3, 7, 10, 14}, {1, 3, 5, 10, 14}, {1, 3, 5, 7, 14}, {1, 3, 5, 7, 10}, {1, 2, 7, 10, 14}, {1, 2, 5, 10, 14}, {1, 2, 5, 7, 14}, {1, 2, 5, 7, 10}, {1, 2, 3, 10, 14}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 10}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 7}, {0, 5, 7, 10, 14}, {0, 3, 7, 10, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 10}, {0, 2, 7, 10, 14}, {0, 2, 5, 10, 14}, {0, 2, 5, 7, 14}, {0, 2, 5, 7, 10}, {0, 2, 3, 10, 14}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 10}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 7}, {0, 1, 7, 10, 14}, {0, 1, 5, 10, 14}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 10}, {0, 1, 3, 10, 14}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 10}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 7}, {0, 1, 2, 10, 14}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 10}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 10}, {0, 1, 2, 5, 7}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17583 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 5, 7, 10, 14} →
      polygon.card = 5 →
        polygon = {3, 5, 7, 10, 14} ∨
        polygon = {2, 5, 7, 10, 14} ∨
        polygon = {2, 3, 7, 10, 14} ∨
        polygon = {2, 3, 5, 10, 14} ∨
        polygon = {2, 3, 5, 7, 14} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {1, 5, 7, 10, 14} ∨
        polygon = {1, 3, 7, 10, 14} ∨
        polygon = {1, 3, 5, 10, 14} ∨
        polygon = {1, 3, 5, 7, 14} ∨
        polygon = {1, 3, 5, 7, 10} ∨
        polygon = {1, 2, 7, 10, 14} ∨
        polygon = {1, 2, 5, 10, 14} ∨
        polygon = {1, 2, 5, 7, 14} ∨
        polygon = {1, 2, 5, 7, 10} ∨
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 7} ∨
        polygon = {0, 5, 7, 10, 14} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 2, 7, 10, 14} ∨
        polygon = {0, 2, 5, 10, 14} ∨
        polygon = {0, 2, 5, 7, 14} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 1, 7, 10, 14} ∨
        polygon = {0, 1, 5, 10, 14} ∨
        polygon = {0, 1, 5, 7, 14} ∨
        polygon = {0, 1, 5, 7, 10} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 2, 10, 14} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 5, 14} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 5, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17583] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12463 :
    (({0, 1, 2, 3, 5, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 12, 13}, {2, 5, 7, 12, 13}, {2, 3, 7, 12, 13}, {2, 3, 5, 12, 13}, {2, 3, 5, 7, 13}, {2, 3, 5, 7, 12}, {1, 5, 7, 12, 13}, {1, 3, 7, 12, 13}, {1, 3, 5, 12, 13}, {1, 3, 5, 7, 13}, {1, 3, 5, 7, 12}, {1, 2, 7, 12, 13}, {1, 2, 5, 12, 13}, {1, 2, 5, 7, 13}, {1, 2, 5, 7, 12}, {1, 2, 3, 12, 13}, {1, 2, 3, 7, 13}, {1, 2, 3, 7, 12}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 7}, {0, 5, 7, 12, 13}, {0, 3, 7, 12, 13}, {0, 3, 5, 12, 13}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 12}, {0, 2, 7, 12, 13}, {0, 2, 5, 12, 13}, {0, 2, 5, 7, 13}, {0, 2, 5, 7, 12}, {0, 2, 3, 12, 13}, {0, 2, 3, 7, 13}, {0, 2, 3, 7, 12}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 7}, {0, 1, 7, 12, 13}, {0, 1, 5, 12, 13}, {0, 1, 5, 7, 13}, {0, 1, 5, 7, 12}, {0, 1, 3, 12, 13}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 12}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 7}, {0, 1, 2, 12, 13}, {0, 1, 2, 7, 13}, {0, 1, 2, 7, 12}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 12}, {0, 1, 2, 5, 7}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12463 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 5, 7, 12, 13} →
      polygon.card = 5 →
        polygon = {3, 5, 7, 12, 13} ∨
        polygon = {2, 5, 7, 12, 13} ∨
        polygon = {2, 3, 7, 12, 13} ∨
        polygon = {2, 3, 5, 12, 13} ∨
        polygon = {2, 3, 5, 7, 13} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {1, 5, 7, 12, 13} ∨
        polygon = {1, 3, 7, 12, 13} ∨
        polygon = {1, 3, 5, 12, 13} ∨
        polygon = {1, 3, 5, 7, 13} ∨
        polygon = {1, 3, 5, 7, 12} ∨
        polygon = {1, 2, 7, 12, 13} ∨
        polygon = {1, 2, 5, 12, 13} ∨
        polygon = {1, 2, 5, 7, 13} ∨
        polygon = {1, 2, 5, 7, 12} ∨
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 7} ∨
        polygon = {0, 5, 7, 12, 13} ∨
        polygon = {0, 3, 7, 12, 13} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 2, 7, 12, 13} ∨
        polygon = {0, 2, 5, 12, 13} ∨
        polygon = {0, 2, 5, 7, 13} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 1, 7, 12, 13} ∨
        polygon = {0, 1, 5, 12, 13} ∨
        polygon = {0, 1, 5, 7, 13} ∨
        polygon = {0, 1, 5, 7, 12} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 2, 12, 13} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 5, 13} ∨
        polygon = {0, 1, 2, 5, 12} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 5, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12463] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask20655 :
    (({0, 1, 2, 3, 5, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 12, 14}, {2, 5, 7, 12, 14}, {2, 3, 7, 12, 14}, {2, 3, 5, 12, 14}, {2, 3, 5, 7, 14}, {2, 3, 5, 7, 12}, {1, 5, 7, 12, 14}, {1, 3, 7, 12, 14}, {1, 3, 5, 12, 14}, {1, 3, 5, 7, 14}, {1, 3, 5, 7, 12}, {1, 2, 7, 12, 14}, {1, 2, 5, 12, 14}, {1, 2, 5, 7, 14}, {1, 2, 5, 7, 12}, {1, 2, 3, 12, 14}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 12}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 7}, {0, 5, 7, 12, 14}, {0, 3, 7, 12, 14}, {0, 3, 5, 12, 14}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 12}, {0, 2, 7, 12, 14}, {0, 2, 5, 12, 14}, {0, 2, 5, 7, 14}, {0, 2, 5, 7, 12}, {0, 2, 3, 12, 14}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 12}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 7}, {0, 1, 7, 12, 14}, {0, 1, 5, 12, 14}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 12}, {0, 1, 3, 12, 14}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 12}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 7}, {0, 1, 2, 12, 14}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 12}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 12}, {0, 1, 2, 5, 7}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask20655 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 5, 7, 12, 14} →
      polygon.card = 5 →
        polygon = {3, 5, 7, 12, 14} ∨
        polygon = {2, 5, 7, 12, 14} ∨
        polygon = {2, 3, 7, 12, 14} ∨
        polygon = {2, 3, 5, 12, 14} ∨
        polygon = {2, 3, 5, 7, 14} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {1, 5, 7, 12, 14} ∨
        polygon = {1, 3, 7, 12, 14} ∨
        polygon = {1, 3, 5, 12, 14} ∨
        polygon = {1, 3, 5, 7, 14} ∨
        polygon = {1, 3, 5, 7, 12} ∨
        polygon = {1, 2, 7, 12, 14} ∨
        polygon = {1, 2, 5, 12, 14} ∨
        polygon = {1, 2, 5, 7, 14} ∨
        polygon = {1, 2, 5, 7, 12} ∨
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 7} ∨
        polygon = {0, 5, 7, 12, 14} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 2, 7, 12, 14} ∨
        polygon = {0, 2, 5, 12, 14} ∨
        polygon = {0, 2, 5, 7, 14} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 1, 7, 12, 14} ∨
        polygon = {0, 1, 5, 12, 14} ∨
        polygon = {0, 1, 5, 7, 14} ∨
        polygon = {0, 1, 5, 7, 12} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 2, 12, 14} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 5, 14} ∨
        polygon = {0, 1, 2, 5, 12} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 5, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask20655] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask24751 :
    (({0, 1, 2, 3, 5, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 13, 14}, {2, 5, 7, 13, 14}, {2, 3, 7, 13, 14}, {2, 3, 5, 13, 14}, {2, 3, 5, 7, 14}, {2, 3, 5, 7, 13}, {1, 5, 7, 13, 14}, {1, 3, 7, 13, 14}, {1, 3, 5, 13, 14}, {1, 3, 5, 7, 14}, {1, 3, 5, 7, 13}, {1, 2, 7, 13, 14}, {1, 2, 5, 13, 14}, {1, 2, 5, 7, 14}, {1, 2, 5, 7, 13}, {1, 2, 3, 13, 14}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 13}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 7}, {0, 5, 7, 13, 14}, {0, 3, 7, 13, 14}, {0, 3, 5, 13, 14}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 13}, {0, 2, 7, 13, 14}, {0, 2, 5, 13, 14}, {0, 2, 5, 7, 14}, {0, 2, 5, 7, 13}, {0, 2, 3, 13, 14}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 13}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 7}, {0, 1, 7, 13, 14}, {0, 1, 5, 13, 14}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 13}, {0, 1, 3, 13, 14}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 13}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 7}, {0, 1, 2, 13, 14}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 13}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 7}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask24751 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 5, 7, 13, 14} →
      polygon.card = 5 →
        polygon = {3, 5, 7, 13, 14} ∨
        polygon = {2, 5, 7, 13, 14} ∨
        polygon = {2, 3, 7, 13, 14} ∨
        polygon = {2, 3, 5, 13, 14} ∨
        polygon = {2, 3, 5, 7, 14} ∨
        polygon = {2, 3, 5, 7, 13} ∨
        polygon = {1, 5, 7, 13, 14} ∨
        polygon = {1, 3, 7, 13, 14} ∨
        polygon = {1, 3, 5, 13, 14} ∨
        polygon = {1, 3, 5, 7, 14} ∨
        polygon = {1, 3, 5, 7, 13} ∨
        polygon = {1, 2, 7, 13, 14} ∨
        polygon = {1, 2, 5, 13, 14} ∨
        polygon = {1, 2, 5, 7, 14} ∨
        polygon = {1, 2, 5, 7, 13} ∨
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 7} ∨
        polygon = {0, 5, 7, 13, 14} ∨
        polygon = {0, 3, 7, 13, 14} ∨
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 2, 7, 13, 14} ∨
        polygon = {0, 2, 5, 13, 14} ∨
        polygon = {0, 2, 5, 7, 14} ∨
        polygon = {0, 2, 5, 7, 13} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 1, 7, 13, 14} ∨
        polygon = {0, 1, 5, 13, 14} ∨
        polygon = {0, 1, 5, 7, 14} ∨
        polygon = {0, 1, 5, 7, 13} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 2, 13, 14} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 5, 14} ∨
        polygon = {0, 1, 2, 5, 13} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 5, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask24751] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05679 :
    (({0, 1, 2, 3, 5, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 9, 10, 12}, {2, 5, 9, 10, 12}, {2, 3, 9, 10, 12}, {2, 3, 5, 10, 12}, {2, 3, 5, 9, 12}, {2, 3, 5, 9, 10}, {1, 5, 9, 10, 12}, {1, 3, 9, 10, 12}, {1, 3, 5, 10, 12}, {1, 3, 5, 9, 12}, {1, 3, 5, 9, 10}, {1, 2, 9, 10, 12}, {1, 2, 5, 10, 12}, {1, 2, 5, 9, 12}, {1, 2, 5, 9, 10}, {1, 2, 3, 10, 12}, {1, 2, 3, 9, 12}, {1, 2, 3, 9, 10}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 9}, {0, 5, 9, 10, 12}, {0, 3, 9, 10, 12}, {0, 3, 5, 10, 12}, {0, 3, 5, 9, 12}, {0, 3, 5, 9, 10}, {0, 2, 9, 10, 12}, {0, 2, 5, 10, 12}, {0, 2, 5, 9, 12}, {0, 2, 5, 9, 10}, {0, 2, 3, 10, 12}, {0, 2, 3, 9, 12}, {0, 2, 3, 9, 10}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 9}, {0, 1, 9, 10, 12}, {0, 1, 5, 10, 12}, {0, 1, 5, 9, 12}, {0, 1, 5, 9, 10}, {0, 1, 3, 10, 12}, {0, 1, 3, 9, 12}, {0, 1, 3, 9, 10}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 9}, {0, 1, 2, 10, 12}, {0, 1, 2, 9, 12}, {0, 1, 2, 9, 10}, {0, 1, 2, 5, 12}, {0, 1, 2, 5, 10}, {0, 1, 2, 5, 9}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05679 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 5, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {2, 5, 9, 10, 12} ∨
        polygon = {2, 3, 9, 10, 12} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {1, 5, 9, 10, 12} ∨
        polygon = {1, 3, 9, 10, 12} ∨
        polygon = {1, 3, 5, 10, 12} ∨
        polygon = {1, 3, 5, 9, 12} ∨
        polygon = {1, 3, 5, 9, 10} ∨
        polygon = {1, 2, 9, 10, 12} ∨
        polygon = {1, 2, 5, 10, 12} ∨
        polygon = {1, 2, 5, 9, 12} ∨
        polygon = {1, 2, 5, 9, 10} ∨
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {0, 5, 9, 10, 12} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 1, 9, 10, 12} ∨
        polygon = {0, 1, 5, 10, 12} ∨
        polygon = {0, 1, 5, 9, 12} ∨
        polygon = {0, 1, 5, 9, 10} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 2, 10, 12} ∨
        polygon = {0, 1, 2, 9, 12} ∨
        polygon = {0, 1, 2, 9, 10} ∨
        polygon = {0, 1, 2, 5, 12} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 5, 9} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 5, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05679] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09775 :
    (({0, 1, 2, 3, 5, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 9, 10, 13}, {2, 5, 9, 10, 13}, {2, 3, 9, 10, 13}, {2, 3, 5, 10, 13}, {2, 3, 5, 9, 13}, {2, 3, 5, 9, 10}, {1, 5, 9, 10, 13}, {1, 3, 9, 10, 13}, {1, 3, 5, 10, 13}, {1, 3, 5, 9, 13}, {1, 3, 5, 9, 10}, {1, 2, 9, 10, 13}, {1, 2, 5, 10, 13}, {1, 2, 5, 9, 13}, {1, 2, 5, 9, 10}, {1, 2, 3, 10, 13}, {1, 2, 3, 9, 13}, {1, 2, 3, 9, 10}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 9}, {0, 5, 9, 10, 13}, {0, 3, 9, 10, 13}, {0, 3, 5, 10, 13}, {0, 3, 5, 9, 13}, {0, 3, 5, 9, 10}, {0, 2, 9, 10, 13}, {0, 2, 5, 10, 13}, {0, 2, 5, 9, 13}, {0, 2, 5, 9, 10}, {0, 2, 3, 10, 13}, {0, 2, 3, 9, 13}, {0, 2, 3, 9, 10}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 9}, {0, 1, 9, 10, 13}, {0, 1, 5, 10, 13}, {0, 1, 5, 9, 13}, {0, 1, 5, 9, 10}, {0, 1, 3, 10, 13}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 10}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 9}, {0, 1, 2, 10, 13}, {0, 1, 2, 9, 13}, {0, 1, 2, 9, 10}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 10}, {0, 1, 2, 5, 9}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09775 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 5, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {3, 5, 9, 10, 13} ∨
        polygon = {2, 5, 9, 10, 13} ∨
        polygon = {2, 3, 9, 10, 13} ∨
        polygon = {2, 3, 5, 10, 13} ∨
        polygon = {2, 3, 5, 9, 13} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {1, 5, 9, 10, 13} ∨
        polygon = {1, 3, 9, 10, 13} ∨
        polygon = {1, 3, 5, 10, 13} ∨
        polygon = {1, 3, 5, 9, 13} ∨
        polygon = {1, 3, 5, 9, 10} ∨
        polygon = {1, 2, 9, 10, 13} ∨
        polygon = {1, 2, 5, 10, 13} ∨
        polygon = {1, 2, 5, 9, 13} ∨
        polygon = {1, 2, 5, 9, 10} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {0, 5, 9, 10, 13} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 2, 9, 10, 13} ∨
        polygon = {0, 2, 5, 10, 13} ∨
        polygon = {0, 2, 5, 9, 13} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 1, 9, 10, 13} ∨
        polygon = {0, 1, 5, 10, 13} ∨
        polygon = {0, 1, 5, 9, 13} ∨
        polygon = {0, 1, 5, 9, 10} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 2, 10, 13} ∨
        polygon = {0, 1, 2, 9, 13} ∨
        polygon = {0, 1, 2, 9, 10} ∨
        polygon = {0, 1, 2, 5, 13} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 5, 9} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 5, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09775] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17967 :
    (({0, 1, 2, 3, 5, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 9, 10, 14}, {2, 5, 9, 10, 14}, {2, 3, 9, 10, 14}, {2, 3, 5, 10, 14}, {2, 3, 5, 9, 14}, {2, 3, 5, 9, 10}, {1, 5, 9, 10, 14}, {1, 3, 9, 10, 14}, {1, 3, 5, 10, 14}, {1, 3, 5, 9, 14}, {1, 3, 5, 9, 10}, {1, 2, 9, 10, 14}, {1, 2, 5, 10, 14}, {1, 2, 5, 9, 14}, {1, 2, 5, 9, 10}, {1, 2, 3, 10, 14}, {1, 2, 3, 9, 14}, {1, 2, 3, 9, 10}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 9}, {0, 5, 9, 10, 14}, {0, 3, 9, 10, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 10}, {0, 2, 9, 10, 14}, {0, 2, 5, 10, 14}, {0, 2, 5, 9, 14}, {0, 2, 5, 9, 10}, {0, 2, 3, 10, 14}, {0, 2, 3, 9, 14}, {0, 2, 3, 9, 10}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 9}, {0, 1, 9, 10, 14}, {0, 1, 5, 10, 14}, {0, 1, 5, 9, 14}, {0, 1, 5, 9, 10}, {0, 1, 3, 10, 14}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 10}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 9}, {0, 1, 2, 10, 14}, {0, 1, 2, 9, 14}, {0, 1, 2, 9, 10}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 10}, {0, 1, 2, 5, 9}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17967 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 5, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {3, 5, 9, 10, 14} ∨
        polygon = {2, 5, 9, 10, 14} ∨
        polygon = {2, 3, 9, 10, 14} ∨
        polygon = {2, 3, 5, 10, 14} ∨
        polygon = {2, 3, 5, 9, 14} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {1, 5, 9, 10, 14} ∨
        polygon = {1, 3, 9, 10, 14} ∨
        polygon = {1, 3, 5, 10, 14} ∨
        polygon = {1, 3, 5, 9, 14} ∨
        polygon = {1, 3, 5, 9, 10} ∨
        polygon = {1, 2, 9, 10, 14} ∨
        polygon = {1, 2, 5, 10, 14} ∨
        polygon = {1, 2, 5, 9, 14} ∨
        polygon = {1, 2, 5, 9, 10} ∨
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {0, 5, 9, 10, 14} ∨
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 2, 9, 10, 14} ∨
        polygon = {0, 2, 5, 10, 14} ∨
        polygon = {0, 2, 5, 9, 14} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 1, 9, 10, 14} ∨
        polygon = {0, 1, 5, 10, 14} ∨
        polygon = {0, 1, 5, 9, 14} ∨
        polygon = {0, 1, 5, 9, 10} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 2, 10, 14} ∨
        polygon = {0, 1, 2, 9, 14} ∨
        polygon = {0, 1, 2, 9, 10} ∨
        polygon = {0, 1, 2, 5, 14} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 5, 9} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 5, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17967] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12847 :
    (({0, 1, 2, 3, 5, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 9, 12, 13}, {2, 5, 9, 12, 13}, {2, 3, 9, 12, 13}, {2, 3, 5, 12, 13}, {2, 3, 5, 9, 13}, {2, 3, 5, 9, 12}, {1, 5, 9, 12, 13}, {1, 3, 9, 12, 13}, {1, 3, 5, 12, 13}, {1, 3, 5, 9, 13}, {1, 3, 5, 9, 12}, {1, 2, 9, 12, 13}, {1, 2, 5, 12, 13}, {1, 2, 5, 9, 13}, {1, 2, 5, 9, 12}, {1, 2, 3, 12, 13}, {1, 2, 3, 9, 13}, {1, 2, 3, 9, 12}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 9}, {0, 5, 9, 12, 13}, {0, 3, 9, 12, 13}, {0, 3, 5, 12, 13}, {0, 3, 5, 9, 13}, {0, 3, 5, 9, 12}, {0, 2, 9, 12, 13}, {0, 2, 5, 12, 13}, {0, 2, 5, 9, 13}, {0, 2, 5, 9, 12}, {0, 2, 3, 12, 13}, {0, 2, 3, 9, 13}, {0, 2, 3, 9, 12}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 9}, {0, 1, 9, 12, 13}, {0, 1, 5, 12, 13}, {0, 1, 5, 9, 13}, {0, 1, 5, 9, 12}, {0, 1, 3, 12, 13}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 12}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 9}, {0, 1, 2, 12, 13}, {0, 1, 2, 9, 13}, {0, 1, 2, 9, 12}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 12}, {0, 1, 2, 5, 9}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12847 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 5, 9, 12, 13} →
      polygon.card = 5 →
        polygon = {3, 5, 9, 12, 13} ∨
        polygon = {2, 5, 9, 12, 13} ∨
        polygon = {2, 3, 9, 12, 13} ∨
        polygon = {2, 3, 5, 12, 13} ∨
        polygon = {2, 3, 5, 9, 13} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {1, 5, 9, 12, 13} ∨
        polygon = {1, 3, 9, 12, 13} ∨
        polygon = {1, 3, 5, 12, 13} ∨
        polygon = {1, 3, 5, 9, 13} ∨
        polygon = {1, 3, 5, 9, 12} ∨
        polygon = {1, 2, 9, 12, 13} ∨
        polygon = {1, 2, 5, 12, 13} ∨
        polygon = {1, 2, 5, 9, 13} ∨
        polygon = {1, 2, 5, 9, 12} ∨
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {0, 5, 9, 12, 13} ∨
        polygon = {0, 3, 9, 12, 13} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 2, 9, 12, 13} ∨
        polygon = {0, 2, 5, 12, 13} ∨
        polygon = {0, 2, 5, 9, 13} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 1, 9, 12, 13} ∨
        polygon = {0, 1, 5, 12, 13} ∨
        polygon = {0, 1, 5, 9, 13} ∨
        polygon = {0, 1, 5, 9, 12} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 2, 12, 13} ∨
        polygon = {0, 1, 2, 9, 13} ∨
        polygon = {0, 1, 2, 9, 12} ∨
        polygon = {0, 1, 2, 5, 13} ∨
        polygon = {0, 1, 2, 5, 12} ∨
        polygon = {0, 1, 2, 5, 9} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 5, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12847] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21039 :
    (({0, 1, 2, 3, 5, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 9, 12, 14}, {2, 5, 9, 12, 14}, {2, 3, 9, 12, 14}, {2, 3, 5, 12, 14}, {2, 3, 5, 9, 14}, {2, 3, 5, 9, 12}, {1, 5, 9, 12, 14}, {1, 3, 9, 12, 14}, {1, 3, 5, 12, 14}, {1, 3, 5, 9, 14}, {1, 3, 5, 9, 12}, {1, 2, 9, 12, 14}, {1, 2, 5, 12, 14}, {1, 2, 5, 9, 14}, {1, 2, 5, 9, 12}, {1, 2, 3, 12, 14}, {1, 2, 3, 9, 14}, {1, 2, 3, 9, 12}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 9}, {0, 5, 9, 12, 14}, {0, 3, 9, 12, 14}, {0, 3, 5, 12, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 12}, {0, 2, 9, 12, 14}, {0, 2, 5, 12, 14}, {0, 2, 5, 9, 14}, {0, 2, 5, 9, 12}, {0, 2, 3, 12, 14}, {0, 2, 3, 9, 14}, {0, 2, 3, 9, 12}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 9}, {0, 1, 9, 12, 14}, {0, 1, 5, 12, 14}, {0, 1, 5, 9, 14}, {0, 1, 5, 9, 12}, {0, 1, 3, 12, 14}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 12}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 9}, {0, 1, 2, 12, 14}, {0, 1, 2, 9, 14}, {0, 1, 2, 9, 12}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 12}, {0, 1, 2, 5, 9}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21039 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 5, 9, 12, 14} →
      polygon.card = 5 →
        polygon = {3, 5, 9, 12, 14} ∨
        polygon = {2, 5, 9, 12, 14} ∨
        polygon = {2, 3, 9, 12, 14} ∨
        polygon = {2, 3, 5, 12, 14} ∨
        polygon = {2, 3, 5, 9, 14} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {1, 5, 9, 12, 14} ∨
        polygon = {1, 3, 9, 12, 14} ∨
        polygon = {1, 3, 5, 12, 14} ∨
        polygon = {1, 3, 5, 9, 14} ∨
        polygon = {1, 3, 5, 9, 12} ∨
        polygon = {1, 2, 9, 12, 14} ∨
        polygon = {1, 2, 5, 12, 14} ∨
        polygon = {1, 2, 5, 9, 14} ∨
        polygon = {1, 2, 5, 9, 12} ∨
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {0, 5, 9, 12, 14} ∨
        polygon = {0, 3, 9, 12, 14} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 2, 9, 12, 14} ∨
        polygon = {0, 2, 5, 12, 14} ∨
        polygon = {0, 2, 5, 9, 14} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 1, 9, 12, 14} ∨
        polygon = {0, 1, 5, 12, 14} ∨
        polygon = {0, 1, 5, 9, 14} ∨
        polygon = {0, 1, 5, 9, 12} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 2, 12, 14} ∨
        polygon = {0, 1, 2, 9, 14} ∨
        polygon = {0, 1, 2, 9, 12} ∨
        polygon = {0, 1, 2, 5, 14} ∨
        polygon = {0, 1, 2, 5, 12} ∨
        polygon = {0, 1, 2, 5, 9} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 5, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21039] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25135 :
    (({0, 1, 2, 3, 5, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 9, 13, 14}, {2, 5, 9, 13, 14}, {2, 3, 9, 13, 14}, {2, 3, 5, 13, 14}, {2, 3, 5, 9, 14}, {2, 3, 5, 9, 13}, {1, 5, 9, 13, 14}, {1, 3, 9, 13, 14}, {1, 3, 5, 13, 14}, {1, 3, 5, 9, 14}, {1, 3, 5, 9, 13}, {1, 2, 9, 13, 14}, {1, 2, 5, 13, 14}, {1, 2, 5, 9, 14}, {1, 2, 5, 9, 13}, {1, 2, 3, 13, 14}, {1, 2, 3, 9, 14}, {1, 2, 3, 9, 13}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 9}, {0, 5, 9, 13, 14}, {0, 3, 9, 13, 14}, {0, 3, 5, 13, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 13}, {0, 2, 9, 13, 14}, {0, 2, 5, 13, 14}, {0, 2, 5, 9, 14}, {0, 2, 5, 9, 13}, {0, 2, 3, 13, 14}, {0, 2, 3, 9, 14}, {0, 2, 3, 9, 13}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 9}, {0, 1, 9, 13, 14}, {0, 1, 5, 13, 14}, {0, 1, 5, 9, 14}, {0, 1, 5, 9, 13}, {0, 1, 3, 13, 14}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 13}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 9}, {0, 1, 2, 13, 14}, {0, 1, 2, 9, 14}, {0, 1, 2, 9, 13}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 9}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25135 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 5, 9, 13, 14} →
      polygon.card = 5 →
        polygon = {3, 5, 9, 13, 14} ∨
        polygon = {2, 5, 9, 13, 14} ∨
        polygon = {2, 3, 9, 13, 14} ∨
        polygon = {2, 3, 5, 13, 14} ∨
        polygon = {2, 3, 5, 9, 14} ∨
        polygon = {2, 3, 5, 9, 13} ∨
        polygon = {1, 5, 9, 13, 14} ∨
        polygon = {1, 3, 9, 13, 14} ∨
        polygon = {1, 3, 5, 13, 14} ∨
        polygon = {1, 3, 5, 9, 14} ∨
        polygon = {1, 3, 5, 9, 13} ∨
        polygon = {1, 2, 9, 13, 14} ∨
        polygon = {1, 2, 5, 13, 14} ∨
        polygon = {1, 2, 5, 9, 14} ∨
        polygon = {1, 2, 5, 9, 13} ∨
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {0, 5, 9, 13, 14} ∨
        polygon = {0, 3, 9, 13, 14} ∨
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 2, 9, 13, 14} ∨
        polygon = {0, 2, 5, 13, 14} ∨
        polygon = {0, 2, 5, 9, 14} ∨
        polygon = {0, 2, 5, 9, 13} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 1, 9, 13, 14} ∨
        polygon = {0, 1, 5, 13, 14} ∨
        polygon = {0, 1, 5, 9, 14} ∨
        polygon = {0, 1, 5, 9, 13} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 2, 13, 14} ∨
        polygon = {0, 1, 2, 9, 14} ∨
        polygon = {0, 1, 2, 9, 13} ∨
        polygon = {0, 1, 2, 5, 14} ∨
        polygon = {0, 1, 2, 5, 13} ∨
        polygon = {0, 1, 2, 5, 9} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 5, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25135] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13359 :
    (({0, 1, 2, 3, 5, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 10, 12, 13}, {2, 5, 10, 12, 13}, {2, 3, 10, 12, 13}, {2, 3, 5, 12, 13}, {2, 3, 5, 10, 13}, {2, 3, 5, 10, 12}, {1, 5, 10, 12, 13}, {1, 3, 10, 12, 13}, {1, 3, 5, 12, 13}, {1, 3, 5, 10, 13}, {1, 3, 5, 10, 12}, {1, 2, 10, 12, 13}, {1, 2, 5, 12, 13}, {1, 2, 5, 10, 13}, {1, 2, 5, 10, 12}, {1, 2, 3, 12, 13}, {1, 2, 3, 10, 13}, {1, 2, 3, 10, 12}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 10}, {0, 5, 10, 12, 13}, {0, 3, 10, 12, 13}, {0, 3, 5, 12, 13}, {0, 3, 5, 10, 13}, {0, 3, 5, 10, 12}, {0, 2, 10, 12, 13}, {0, 2, 5, 12, 13}, {0, 2, 5, 10, 13}, {0, 2, 5, 10, 12}, {0, 2, 3, 12, 13}, {0, 2, 3, 10, 13}, {0, 2, 3, 10, 12}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 10}, {0, 1, 10, 12, 13}, {0, 1, 5, 12, 13}, {0, 1, 5, 10, 13}, {0, 1, 5, 10, 12}, {0, 1, 3, 12, 13}, {0, 1, 3, 10, 13}, {0, 1, 3, 10, 12}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 10}, {0, 1, 2, 12, 13}, {0, 1, 2, 10, 13}, {0, 1, 2, 10, 12}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 12}, {0, 1, 2, 5, 10}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13359 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 5, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {3, 5, 10, 12, 13} ∨
        polygon = {2, 5, 10, 12, 13} ∨
        polygon = {2, 3, 10, 12, 13} ∨
        polygon = {2, 3, 5, 12, 13} ∨
        polygon = {2, 3, 5, 10, 13} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {1, 5, 10, 12, 13} ∨
        polygon = {1, 3, 10, 12, 13} ∨
        polygon = {1, 3, 5, 12, 13} ∨
        polygon = {1, 3, 5, 10, 13} ∨
        polygon = {1, 3, 5, 10, 12} ∨
        polygon = {1, 2, 10, 12, 13} ∨
        polygon = {1, 2, 5, 12, 13} ∨
        polygon = {1, 2, 5, 10, 13} ∨
        polygon = {1, 2, 5, 10, 12} ∨
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {0, 5, 10, 12, 13} ∨
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 2, 10, 12, 13} ∨
        polygon = {0, 2, 5, 12, 13} ∨
        polygon = {0, 2, 5, 10, 13} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 1, 10, 12, 13} ∨
        polygon = {0, 1, 5, 12, 13} ∨
        polygon = {0, 1, 5, 10, 13} ∨
        polygon = {0, 1, 5, 10, 12} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 2, 12, 13} ∨
        polygon = {0, 1, 2, 10, 13} ∨
        polygon = {0, 1, 2, 10, 12} ∨
        polygon = {0, 1, 2, 5, 13} ∨
        polygon = {0, 1, 2, 5, 12} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 5, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13359] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21551 :
    (({0, 1, 2, 3, 5, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 10, 12, 14}, {2, 5, 10, 12, 14}, {2, 3, 10, 12, 14}, {2, 3, 5, 12, 14}, {2, 3, 5, 10, 14}, {2, 3, 5, 10, 12}, {1, 5, 10, 12, 14}, {1, 3, 10, 12, 14}, {1, 3, 5, 12, 14}, {1, 3, 5, 10, 14}, {1, 3, 5, 10, 12}, {1, 2, 10, 12, 14}, {1, 2, 5, 12, 14}, {1, 2, 5, 10, 14}, {1, 2, 5, 10, 12}, {1, 2, 3, 12, 14}, {1, 2, 3, 10, 14}, {1, 2, 3, 10, 12}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 10}, {0, 5, 10, 12, 14}, {0, 3, 10, 12, 14}, {0, 3, 5, 12, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 10, 12}, {0, 2, 10, 12, 14}, {0, 2, 5, 12, 14}, {0, 2, 5, 10, 14}, {0, 2, 5, 10, 12}, {0, 2, 3, 12, 14}, {0, 2, 3, 10, 14}, {0, 2, 3, 10, 12}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 10}, {0, 1, 10, 12, 14}, {0, 1, 5, 12, 14}, {0, 1, 5, 10, 14}, {0, 1, 5, 10, 12}, {0, 1, 3, 12, 14}, {0, 1, 3, 10, 14}, {0, 1, 3, 10, 12}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 10}, {0, 1, 2, 12, 14}, {0, 1, 2, 10, 14}, {0, 1, 2, 10, 12}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 12}, {0, 1, 2, 5, 10}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21551 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 5, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {3, 5, 10, 12, 14} ∨
        polygon = {2, 5, 10, 12, 14} ∨
        polygon = {2, 3, 10, 12, 14} ∨
        polygon = {2, 3, 5, 12, 14} ∨
        polygon = {2, 3, 5, 10, 14} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {1, 5, 10, 12, 14} ∨
        polygon = {1, 3, 10, 12, 14} ∨
        polygon = {1, 3, 5, 12, 14} ∨
        polygon = {1, 3, 5, 10, 14} ∨
        polygon = {1, 3, 5, 10, 12} ∨
        polygon = {1, 2, 10, 12, 14} ∨
        polygon = {1, 2, 5, 12, 14} ∨
        polygon = {1, 2, 5, 10, 14} ∨
        polygon = {1, 2, 5, 10, 12} ∨
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {0, 5, 10, 12, 14} ∨
        polygon = {0, 3, 10, 12, 14} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 2, 10, 12, 14} ∨
        polygon = {0, 2, 5, 12, 14} ∨
        polygon = {0, 2, 5, 10, 14} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 1, 10, 12, 14} ∨
        polygon = {0, 1, 5, 12, 14} ∨
        polygon = {0, 1, 5, 10, 14} ∨
        polygon = {0, 1, 5, 10, 12} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 2, 12, 14} ∨
        polygon = {0, 1, 2, 10, 14} ∨
        polygon = {0, 1, 2, 10, 12} ∨
        polygon = {0, 1, 2, 5, 14} ∨
        polygon = {0, 1, 2, 5, 12} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 5, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21551] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25647 :
    (({0, 1, 2, 3, 5, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 10, 13, 14}, {2, 5, 10, 13, 14}, {2, 3, 10, 13, 14}, {2, 3, 5, 13, 14}, {2, 3, 5, 10, 14}, {2, 3, 5, 10, 13}, {1, 5, 10, 13, 14}, {1, 3, 10, 13, 14}, {1, 3, 5, 13, 14}, {1, 3, 5, 10, 14}, {1, 3, 5, 10, 13}, {1, 2, 10, 13, 14}, {1, 2, 5, 13, 14}, {1, 2, 5, 10, 14}, {1, 2, 5, 10, 13}, {1, 2, 3, 13, 14}, {1, 2, 3, 10, 14}, {1, 2, 3, 10, 13}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 10}, {0, 5, 10, 13, 14}, {0, 3, 10, 13, 14}, {0, 3, 5, 13, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 10, 13}, {0, 2, 10, 13, 14}, {0, 2, 5, 13, 14}, {0, 2, 5, 10, 14}, {0, 2, 5, 10, 13}, {0, 2, 3, 13, 14}, {0, 2, 3, 10, 14}, {0, 2, 3, 10, 13}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 10}, {0, 1, 10, 13, 14}, {0, 1, 5, 13, 14}, {0, 1, 5, 10, 14}, {0, 1, 5, 10, 13}, {0, 1, 3, 13, 14}, {0, 1, 3, 10, 14}, {0, 1, 3, 10, 13}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 10}, {0, 1, 2, 13, 14}, {0, 1, 2, 10, 14}, {0, 1, 2, 10, 13}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 10}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25647 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 5, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {3, 5, 10, 13, 14} ∨
        polygon = {2, 5, 10, 13, 14} ∨
        polygon = {2, 3, 10, 13, 14} ∨
        polygon = {2, 3, 5, 13, 14} ∨
        polygon = {2, 3, 5, 10, 14} ∨
        polygon = {2, 3, 5, 10, 13} ∨
        polygon = {1, 5, 10, 13, 14} ∨
        polygon = {1, 3, 10, 13, 14} ∨
        polygon = {1, 3, 5, 13, 14} ∨
        polygon = {1, 3, 5, 10, 14} ∨
        polygon = {1, 3, 5, 10, 13} ∨
        polygon = {1, 2, 10, 13, 14} ∨
        polygon = {1, 2, 5, 13, 14} ∨
        polygon = {1, 2, 5, 10, 14} ∨
        polygon = {1, 2, 5, 10, 13} ∨
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {0, 5, 10, 13, 14} ∨
        polygon = {0, 3, 10, 13, 14} ∨
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 2, 10, 13, 14} ∨
        polygon = {0, 2, 5, 13, 14} ∨
        polygon = {0, 2, 5, 10, 14} ∨
        polygon = {0, 2, 5, 10, 13} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 1, 10, 13, 14} ∨
        polygon = {0, 1, 5, 13, 14} ∨
        polygon = {0, 1, 5, 10, 14} ∨
        polygon = {0, 1, 5, 10, 13} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 2, 13, 14} ∨
        polygon = {0, 1, 2, 10, 14} ∨
        polygon = {0, 1, 2, 10, 13} ∨
        polygon = {0, 1, 2, 5, 14} ∨
        polygon = {0, 1, 2, 5, 13} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 5, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25647] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask28719 :
    (({0, 1, 2, 3, 5, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 12, 13, 14}, {2, 5, 12, 13, 14}, {2, 3, 12, 13, 14}, {2, 3, 5, 13, 14}, {2, 3, 5, 12, 14}, {2, 3, 5, 12, 13}, {1, 5, 12, 13, 14}, {1, 3, 12, 13, 14}, {1, 3, 5, 13, 14}, {1, 3, 5, 12, 14}, {1, 3, 5, 12, 13}, {1, 2, 12, 13, 14}, {1, 2, 5, 13, 14}, {1, 2, 5, 12, 14}, {1, 2, 5, 12, 13}, {1, 2, 3, 13, 14}, {1, 2, 3, 12, 14}, {1, 2, 3, 12, 13}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 12}, {0, 5, 12, 13, 14}, {0, 3, 12, 13, 14}, {0, 3, 5, 13, 14}, {0, 3, 5, 12, 14}, {0, 3, 5, 12, 13}, {0, 2, 12, 13, 14}, {0, 2, 5, 13, 14}, {0, 2, 5, 12, 14}, {0, 2, 5, 12, 13}, {0, 2, 3, 13, 14}, {0, 2, 3, 12, 14}, {0, 2, 3, 12, 13}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 12}, {0, 1, 12, 13, 14}, {0, 1, 5, 13, 14}, {0, 1, 5, 12, 14}, {0, 1, 5, 12, 13}, {0, 1, 3, 13, 14}, {0, 1, 3, 12, 14}, {0, 1, 3, 12, 13}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 12}, {0, 1, 2, 13, 14}, {0, 1, 2, 12, 14}, {0, 1, 2, 12, 13}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 12}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask28719 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 5, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {3, 5, 12, 13, 14} ∨
        polygon = {2, 5, 12, 13, 14} ∨
        polygon = {2, 3, 12, 13, 14} ∨
        polygon = {2, 3, 5, 13, 14} ∨
        polygon = {2, 3, 5, 12, 14} ∨
        polygon = {2, 3, 5, 12, 13} ∨
        polygon = {1, 5, 12, 13, 14} ∨
        polygon = {1, 3, 12, 13, 14} ∨
        polygon = {1, 3, 5, 13, 14} ∨
        polygon = {1, 3, 5, 12, 14} ∨
        polygon = {1, 3, 5, 12, 13} ∨
        polygon = {1, 2, 12, 13, 14} ∨
        polygon = {1, 2, 5, 13, 14} ∨
        polygon = {1, 2, 5, 12, 14} ∨
        polygon = {1, 2, 5, 12, 13} ∨
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {0, 5, 12, 13, 14} ∨
        polygon = {0, 3, 12, 13, 14} ∨
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 2, 12, 13, 14} ∨
        polygon = {0, 2, 5, 13, 14} ∨
        polygon = {0, 2, 5, 12, 14} ∨
        polygon = {0, 2, 5, 12, 13} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 1, 12, 13, 14} ∨
        polygon = {0, 1, 5, 13, 14} ∨
        polygon = {0, 1, 5, 12, 14} ∨
        polygon = {0, 1, 5, 12, 13} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 2, 13, 14} ∨
        polygon = {0, 1, 2, 12, 14} ∨
        polygon = {0, 1, 2, 12, 13} ∨
        polygon = {0, 1, 2, 5, 14} ∨
        polygon = {0, 1, 2, 5, 13} ∨
        polygon = {0, 1, 2, 5, 12} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 5, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask28719] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01743 :
    (({0, 1, 2, 3, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 9, 10}, {2, 6, 7, 9, 10}, {2, 3, 7, 9, 10}, {2, 3, 6, 9, 10}, {2, 3, 6, 7, 10}, {2, 3, 6, 7, 9}, {1, 6, 7, 9, 10}, {1, 3, 7, 9, 10}, {1, 3, 6, 9, 10}, {1, 3, 6, 7, 10}, {1, 3, 6, 7, 9}, {1, 2, 7, 9, 10}, {1, 2, 6, 9, 10}, {1, 2, 6, 7, 10}, {1, 2, 6, 7, 9}, {1, 2, 3, 9, 10}, {1, 2, 3, 7, 10}, {1, 2, 3, 7, 9}, {1, 2, 3, 6, 10}, {1, 2, 3, 6, 9}, {1, 2, 3, 6, 7}, {0, 6, 7, 9, 10}, {0, 3, 7, 9, 10}, {0, 3, 6, 9, 10}, {0, 3, 6, 7, 10}, {0, 3, 6, 7, 9}, {0, 2, 7, 9, 10}, {0, 2, 6, 9, 10}, {0, 2, 6, 7, 10}, {0, 2, 6, 7, 9}, {0, 2, 3, 9, 10}, {0, 2, 3, 7, 10}, {0, 2, 3, 7, 9}, {0, 2, 3, 6, 10}, {0, 2, 3, 6, 9}, {0, 2, 3, 6, 7}, {0, 1, 7, 9, 10}, {0, 1, 6, 9, 10}, {0, 1, 6, 7, 10}, {0, 1, 6, 7, 9}, {0, 1, 3, 9, 10}, {0, 1, 3, 7, 10}, {0, 1, 3, 7, 9}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 9}, {0, 1, 3, 6, 7}, {0, 1, 2, 9, 10}, {0, 1, 2, 7, 10}, {0, 1, 2, 7, 9}, {0, 1, 2, 6, 10}, {0, 1, 2, 6, 9}, {0, 1, 2, 6, 7}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01743 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 6, 7, 9, 10} →
      polygon.card = 5 →
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {2, 6, 7, 9, 10} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {1, 6, 7, 9, 10} ∨
        polygon = {1, 3, 7, 9, 10} ∨
        polygon = {1, 3, 6, 9, 10} ∨
        polygon = {1, 3, 6, 7, 10} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {1, 2, 7, 9, 10} ∨
        polygon = {1, 2, 6, 9, 10} ∨
        polygon = {1, 2, 6, 7, 10} ∨
        polygon = {1, 2, 6, 7, 9} ∨
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {1, 2, 3, 6, 9} ∨
        polygon = {1, 2, 3, 6, 7} ∨
        polygon = {0, 6, 7, 9, 10} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 2, 6, 9, 10} ∨
        polygon = {0, 2, 6, 7, 10} ∨
        polygon = {0, 2, 6, 7, 9} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 1, 7, 9, 10} ∨
        polygon = {0, 1, 6, 9, 10} ∨
        polygon = {0, 1, 6, 7, 10} ∨
        polygon = {0, 1, 6, 7, 9} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 2, 9, 10} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 7, 9} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01743] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask02767 :
    (({0, 1, 2, 3, 6, 7, 9, 11} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 9, 11}, {2, 6, 7, 9, 11}, {2, 3, 7, 9, 11}, {2, 3, 6, 9, 11}, {2, 3, 6, 7, 11}, {2, 3, 6, 7, 9}, {1, 6, 7, 9, 11}, {1, 3, 7, 9, 11}, {1, 3, 6, 9, 11}, {1, 3, 6, 7, 11}, {1, 3, 6, 7, 9}, {1, 2, 7, 9, 11}, {1, 2, 6, 9, 11}, {1, 2, 6, 7, 11}, {1, 2, 6, 7, 9}, {1, 2, 3, 9, 11}, {1, 2, 3, 7, 11}, {1, 2, 3, 7, 9}, {1, 2, 3, 6, 11}, {1, 2, 3, 6, 9}, {1, 2, 3, 6, 7}, {0, 6, 7, 9, 11}, {0, 3, 7, 9, 11}, {0, 3, 6, 9, 11}, {0, 3, 6, 7, 11}, {0, 3, 6, 7, 9}, {0, 2, 7, 9, 11}, {0, 2, 6, 9, 11}, {0, 2, 6, 7, 11}, {0, 2, 6, 7, 9}, {0, 2, 3, 9, 11}, {0, 2, 3, 7, 11}, {0, 2, 3, 7, 9}, {0, 2, 3, 6, 11}, {0, 2, 3, 6, 9}, {0, 2, 3, 6, 7}, {0, 1, 7, 9, 11}, {0, 1, 6, 9, 11}, {0, 1, 6, 7, 11}, {0, 1, 6, 7, 9}, {0, 1, 3, 9, 11}, {0, 1, 3, 7, 11}, {0, 1, 3, 7, 9}, {0, 1, 3, 6, 11}, {0, 1, 3, 6, 9}, {0, 1, 3, 6, 7}, {0, 1, 2, 9, 11}, {0, 1, 2, 7, 11}, {0, 1, 2, 7, 9}, {0, 1, 2, 6, 11}, {0, 1, 2, 6, 9}, {0, 1, 2, 6, 7}, {0, 1, 2, 3, 11}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask02767 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 6, 7, 9, 11} →
      polygon.card = 5 →
        polygon = {3, 6, 7, 9, 11} ∨
        polygon = {2, 6, 7, 9, 11} ∨
        polygon = {2, 3, 7, 9, 11} ∨
        polygon = {2, 3, 6, 9, 11} ∨
        polygon = {2, 3, 6, 7, 11} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {1, 6, 7, 9, 11} ∨
        polygon = {1, 3, 7, 9, 11} ∨
        polygon = {1, 3, 6, 9, 11} ∨
        polygon = {1, 3, 6, 7, 11} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {1, 2, 7, 9, 11} ∨
        polygon = {1, 2, 6, 9, 11} ∨
        polygon = {1, 2, 6, 7, 11} ∨
        polygon = {1, 2, 6, 7, 9} ∨
        polygon = {1, 2, 3, 9, 11} ∨
        polygon = {1, 2, 3, 7, 11} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {1, 2, 3, 6, 11} ∨
        polygon = {1, 2, 3, 6, 9} ∨
        polygon = {1, 2, 3, 6, 7} ∨
        polygon = {0, 6, 7, 9, 11} ∨
        polygon = {0, 3, 7, 9, 11} ∨
        polygon = {0, 3, 6, 9, 11} ∨
        polygon = {0, 3, 6, 7, 11} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 2, 7, 9, 11} ∨
        polygon = {0, 2, 6, 9, 11} ∨
        polygon = {0, 2, 6, 7, 11} ∨
        polygon = {0, 2, 6, 7, 9} ∨
        polygon = {0, 2, 3, 9, 11} ∨
        polygon = {0, 2, 3, 7, 11} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 6, 11} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 1, 7, 9, 11} ∨
        polygon = {0, 1, 6, 9, 11} ∨
        polygon = {0, 1, 6, 7, 11} ∨
        polygon = {0, 1, 6, 7, 9} ∨
        polygon = {0, 1, 3, 9, 11} ∨
        polygon = {0, 1, 3, 7, 11} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 6, 11} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 2, 9, 11} ∨
        polygon = {0, 1, 2, 7, 11} ∨
        polygon = {0, 1, 2, 7, 9} ∨
        polygon = {0, 1, 2, 6, 11} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 3, 11} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 6, 7, 9, 11} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask02767] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

end ErdosSzekeres

end
