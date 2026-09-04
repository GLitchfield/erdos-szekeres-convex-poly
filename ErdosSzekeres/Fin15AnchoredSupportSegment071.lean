module

public import ErdosSzekeres.Fin15AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 071. -/

theorem fin15Anchored_fiveFamily_mask13959 :
    (({0, 1, 2, 7, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 12, 13}, {2, 9, 10, 12, 13}, {2, 7, 10, 12, 13}, {2, 7, 9, 12, 13}, {2, 7, 9, 10, 13}, {2, 7, 9, 10, 12}, {1, 9, 10, 12, 13}, {1, 7, 10, 12, 13}, {1, 7, 9, 12, 13}, {1, 7, 9, 10, 13}, {1, 7, 9, 10, 12}, {1, 2, 10, 12, 13}, {1, 2, 9, 12, 13}, {1, 2, 9, 10, 13}, {1, 2, 9, 10, 12}, {1, 2, 7, 12, 13}, {1, 2, 7, 10, 13}, {1, 2, 7, 10, 12}, {1, 2, 7, 9, 13}, {1, 2, 7, 9, 12}, {1, 2, 7, 9, 10}, {0, 9, 10, 12, 13}, {0, 7, 10, 12, 13}, {0, 7, 9, 12, 13}, {0, 7, 9, 10, 13}, {0, 7, 9, 10, 12}, {0, 2, 10, 12, 13}, {0, 2, 9, 12, 13}, {0, 2, 9, 10, 13}, {0, 2, 9, 10, 12}, {0, 2, 7, 12, 13}, {0, 2, 7, 10, 13}, {0, 2, 7, 10, 12}, {0, 2, 7, 9, 13}, {0, 2, 7, 9, 12}, {0, 2, 7, 9, 10}, {0, 1, 10, 12, 13}, {0, 1, 9, 12, 13}, {0, 1, 9, 10, 13}, {0, 1, 9, 10, 12}, {0, 1, 7, 12, 13}, {0, 1, 7, 10, 13}, {0, 1, 7, 10, 12}, {0, 1, 7, 9, 13}, {0, 1, 7, 9, 12}, {0, 1, 7, 9, 10}, {0, 1, 2, 12, 13}, {0, 1, 2, 10, 13}, {0, 1, 2, 10, 12}, {0, 1, 2, 9, 13}, {0, 1, 2, 9, 12}, {0, 1, 2, 9, 10}, {0, 1, 2, 7, 13}, {0, 1, 2, 7, 12}, {0, 1, 2, 7, 10}, {0, 1, 2, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13959 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 7, 9, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {7, 9, 10, 12, 13} ∨
        polygon = {2, 9, 10, 12, 13} ∨
        polygon = {2, 7, 10, 12, 13} ∨
        polygon = {2, 7, 9, 12, 13} ∨
        polygon = {2, 7, 9, 10, 13} ∨
        polygon = {2, 7, 9, 10, 12} ∨
        polygon = {1, 9, 10, 12, 13} ∨
        polygon = {1, 7, 10, 12, 13} ∨
        polygon = {1, 7, 9, 12, 13} ∨
        polygon = {1, 7, 9, 10, 13} ∨
        polygon = {1, 7, 9, 10, 12} ∨
        polygon = {1, 2, 10, 12, 13} ∨
        polygon = {1, 2, 9, 12, 13} ∨
        polygon = {1, 2, 9, 10, 13} ∨
        polygon = {1, 2, 9, 10, 12} ∨
        polygon = {1, 2, 7, 12, 13} ∨
        polygon = {1, 2, 7, 10, 13} ∨
        polygon = {1, 2, 7, 10, 12} ∨
        polygon = {1, 2, 7, 9, 13} ∨
        polygon = {1, 2, 7, 9, 12} ∨
        polygon = {1, 2, 7, 9, 10} ∨
        polygon = {0, 9, 10, 12, 13} ∨
        polygon = {0, 7, 10, 12, 13} ∨
        polygon = {0, 7, 9, 12, 13} ∨
        polygon = {0, 7, 9, 10, 13} ∨
        polygon = {0, 7, 9, 10, 12} ∨
        polygon = {0, 2, 10, 12, 13} ∨
        polygon = {0, 2, 9, 12, 13} ∨
        polygon = {0, 2, 9, 10, 13} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 2, 7, 12, 13} ∨
        polygon = {0, 2, 7, 10, 13} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 2, 7, 9, 13} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 1, 10, 12, 13} ∨
        polygon = {0, 1, 9, 12, 13} ∨
        polygon = {0, 1, 9, 10, 13} ∨
        polygon = {0, 1, 9, 10, 12} ∨
        polygon = {0, 1, 7, 12, 13} ∨
        polygon = {0, 1, 7, 10, 13} ∨
        polygon = {0, 1, 7, 10, 12} ∨
        polygon = {0, 1, 7, 9, 13} ∨
        polygon = {0, 1, 7, 9, 12} ∨
        polygon = {0, 1, 7, 9, 10} ∨
        polygon = {0, 1, 2, 12, 13} ∨
        polygon = {0, 1, 2, 10, 13} ∨
        polygon = {0, 1, 2, 10, 12} ∨
        polygon = {0, 1, 2, 9, 13} ∨
        polygon = {0, 1, 2, 9, 12} ∨
        polygon = {0, 1, 2, 9, 10} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 7, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13959] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask22151 :
    (({0, 1, 2, 7, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 12, 14}, {2, 9, 10, 12, 14}, {2, 7, 10, 12, 14}, {2, 7, 9, 12, 14}, {2, 7, 9, 10, 14}, {2, 7, 9, 10, 12}, {1, 9, 10, 12, 14}, {1, 7, 10, 12, 14}, {1, 7, 9, 12, 14}, {1, 7, 9, 10, 14}, {1, 7, 9, 10, 12}, {1, 2, 10, 12, 14}, {1, 2, 9, 12, 14}, {1, 2, 9, 10, 14}, {1, 2, 9, 10, 12}, {1, 2, 7, 12, 14}, {1, 2, 7, 10, 14}, {1, 2, 7, 10, 12}, {1, 2, 7, 9, 14}, {1, 2, 7, 9, 12}, {1, 2, 7, 9, 10}, {0, 9, 10, 12, 14}, {0, 7, 10, 12, 14}, {0, 7, 9, 12, 14}, {0, 7, 9, 10, 14}, {0, 7, 9, 10, 12}, {0, 2, 10, 12, 14}, {0, 2, 9, 12, 14}, {0, 2, 9, 10, 14}, {0, 2, 9, 10, 12}, {0, 2, 7, 12, 14}, {0, 2, 7, 10, 14}, {0, 2, 7, 10, 12}, {0, 2, 7, 9, 14}, {0, 2, 7, 9, 12}, {0, 2, 7, 9, 10}, {0, 1, 10, 12, 14}, {0, 1, 9, 12, 14}, {0, 1, 9, 10, 14}, {0, 1, 9, 10, 12}, {0, 1, 7, 12, 14}, {0, 1, 7, 10, 14}, {0, 1, 7, 10, 12}, {0, 1, 7, 9, 14}, {0, 1, 7, 9, 12}, {0, 1, 7, 9, 10}, {0, 1, 2, 12, 14}, {0, 1, 2, 10, 14}, {0, 1, 2, 10, 12}, {0, 1, 2, 9, 14}, {0, 1, 2, 9, 12}, {0, 1, 2, 9, 10}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 12}, {0, 1, 2, 7, 10}, {0, 1, 2, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask22151 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 7, 9, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {7, 9, 10, 12, 14} ∨
        polygon = {2, 9, 10, 12, 14} ∨
        polygon = {2, 7, 10, 12, 14} ∨
        polygon = {2, 7, 9, 12, 14} ∨
        polygon = {2, 7, 9, 10, 14} ∨
        polygon = {2, 7, 9, 10, 12} ∨
        polygon = {1, 9, 10, 12, 14} ∨
        polygon = {1, 7, 10, 12, 14} ∨
        polygon = {1, 7, 9, 12, 14} ∨
        polygon = {1, 7, 9, 10, 14} ∨
        polygon = {1, 7, 9, 10, 12} ∨
        polygon = {1, 2, 10, 12, 14} ∨
        polygon = {1, 2, 9, 12, 14} ∨
        polygon = {1, 2, 9, 10, 14} ∨
        polygon = {1, 2, 9, 10, 12} ∨
        polygon = {1, 2, 7, 12, 14} ∨
        polygon = {1, 2, 7, 10, 14} ∨
        polygon = {1, 2, 7, 10, 12} ∨
        polygon = {1, 2, 7, 9, 14} ∨
        polygon = {1, 2, 7, 9, 12} ∨
        polygon = {1, 2, 7, 9, 10} ∨
        polygon = {0, 9, 10, 12, 14} ∨
        polygon = {0, 7, 10, 12, 14} ∨
        polygon = {0, 7, 9, 12, 14} ∨
        polygon = {0, 7, 9, 10, 14} ∨
        polygon = {0, 7, 9, 10, 12} ∨
        polygon = {0, 2, 10, 12, 14} ∨
        polygon = {0, 2, 9, 12, 14} ∨
        polygon = {0, 2, 9, 10, 14} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 2, 7, 12, 14} ∨
        polygon = {0, 2, 7, 10, 14} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 2, 7, 9, 14} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 1, 10, 12, 14} ∨
        polygon = {0, 1, 9, 12, 14} ∨
        polygon = {0, 1, 9, 10, 14} ∨
        polygon = {0, 1, 9, 10, 12} ∨
        polygon = {0, 1, 7, 12, 14} ∨
        polygon = {0, 1, 7, 10, 14} ∨
        polygon = {0, 1, 7, 10, 12} ∨
        polygon = {0, 1, 7, 9, 14} ∨
        polygon = {0, 1, 7, 9, 12} ∨
        polygon = {0, 1, 7, 9, 10} ∨
        polygon = {0, 1, 2, 12, 14} ∨
        polygon = {0, 1, 2, 10, 14} ∨
        polygon = {0, 1, 2, 10, 12} ∨
        polygon = {0, 1, 2, 9, 14} ∨
        polygon = {0, 1, 2, 9, 12} ∨
        polygon = {0, 1, 2, 9, 10} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 7, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask22151] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask26247 :
    (({0, 1, 2, 7, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 13, 14}, {2, 9, 10, 13, 14}, {2, 7, 10, 13, 14}, {2, 7, 9, 13, 14}, {2, 7, 9, 10, 14}, {2, 7, 9, 10, 13}, {1, 9, 10, 13, 14}, {1, 7, 10, 13, 14}, {1, 7, 9, 13, 14}, {1, 7, 9, 10, 14}, {1, 7, 9, 10, 13}, {1, 2, 10, 13, 14}, {1, 2, 9, 13, 14}, {1, 2, 9, 10, 14}, {1, 2, 9, 10, 13}, {1, 2, 7, 13, 14}, {1, 2, 7, 10, 14}, {1, 2, 7, 10, 13}, {1, 2, 7, 9, 14}, {1, 2, 7, 9, 13}, {1, 2, 7, 9, 10}, {0, 9, 10, 13, 14}, {0, 7, 10, 13, 14}, {0, 7, 9, 13, 14}, {0, 7, 9, 10, 14}, {0, 7, 9, 10, 13}, {0, 2, 10, 13, 14}, {0, 2, 9, 13, 14}, {0, 2, 9, 10, 14}, {0, 2, 9, 10, 13}, {0, 2, 7, 13, 14}, {0, 2, 7, 10, 14}, {0, 2, 7, 10, 13}, {0, 2, 7, 9, 14}, {0, 2, 7, 9, 13}, {0, 2, 7, 9, 10}, {0, 1, 10, 13, 14}, {0, 1, 9, 13, 14}, {0, 1, 9, 10, 14}, {0, 1, 9, 10, 13}, {0, 1, 7, 13, 14}, {0, 1, 7, 10, 14}, {0, 1, 7, 10, 13}, {0, 1, 7, 9, 14}, {0, 1, 7, 9, 13}, {0, 1, 7, 9, 10}, {0, 1, 2, 13, 14}, {0, 1, 2, 10, 14}, {0, 1, 2, 10, 13}, {0, 1, 2, 9, 14}, {0, 1, 2, 9, 13}, {0, 1, 2, 9, 10}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 13}, {0, 1, 2, 7, 10}, {0, 1, 2, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26247 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 7, 9, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {7, 9, 10, 13, 14} ∨
        polygon = {2, 9, 10, 13, 14} ∨
        polygon = {2, 7, 10, 13, 14} ∨
        polygon = {2, 7, 9, 13, 14} ∨
        polygon = {2, 7, 9, 10, 14} ∨
        polygon = {2, 7, 9, 10, 13} ∨
        polygon = {1, 9, 10, 13, 14} ∨
        polygon = {1, 7, 10, 13, 14} ∨
        polygon = {1, 7, 9, 13, 14} ∨
        polygon = {1, 7, 9, 10, 14} ∨
        polygon = {1, 7, 9, 10, 13} ∨
        polygon = {1, 2, 10, 13, 14} ∨
        polygon = {1, 2, 9, 13, 14} ∨
        polygon = {1, 2, 9, 10, 14} ∨
        polygon = {1, 2, 9, 10, 13} ∨
        polygon = {1, 2, 7, 13, 14} ∨
        polygon = {1, 2, 7, 10, 14} ∨
        polygon = {1, 2, 7, 10, 13} ∨
        polygon = {1, 2, 7, 9, 14} ∨
        polygon = {1, 2, 7, 9, 13} ∨
        polygon = {1, 2, 7, 9, 10} ∨
        polygon = {0, 9, 10, 13, 14} ∨
        polygon = {0, 7, 10, 13, 14} ∨
        polygon = {0, 7, 9, 13, 14} ∨
        polygon = {0, 7, 9, 10, 14} ∨
        polygon = {0, 7, 9, 10, 13} ∨
        polygon = {0, 2, 10, 13, 14} ∨
        polygon = {0, 2, 9, 13, 14} ∨
        polygon = {0, 2, 9, 10, 14} ∨
        polygon = {0, 2, 9, 10, 13} ∨
        polygon = {0, 2, 7, 13, 14} ∨
        polygon = {0, 2, 7, 10, 14} ∨
        polygon = {0, 2, 7, 10, 13} ∨
        polygon = {0, 2, 7, 9, 14} ∨
        polygon = {0, 2, 7, 9, 13} ∨
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 1, 10, 13, 14} ∨
        polygon = {0, 1, 9, 13, 14} ∨
        polygon = {0, 1, 9, 10, 14} ∨
        polygon = {0, 1, 9, 10, 13} ∨
        polygon = {0, 1, 7, 13, 14} ∨
        polygon = {0, 1, 7, 10, 14} ∨
        polygon = {0, 1, 7, 10, 13} ∨
        polygon = {0, 1, 7, 9, 14} ∨
        polygon = {0, 1, 7, 9, 13} ∨
        polygon = {0, 1, 7, 9, 10} ∨
        polygon = {0, 1, 2, 13, 14} ∨
        polygon = {0, 1, 2, 10, 14} ∨
        polygon = {0, 1, 2, 10, 13} ∨
        polygon = {0, 1, 2, 9, 14} ∨
        polygon = {0, 1, 2, 9, 13} ∨
        polygon = {0, 1, 2, 9, 10} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 7, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26247] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29319 :
    (({0, 1, 2, 7, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 12, 13, 14}, {2, 9, 12, 13, 14}, {2, 7, 12, 13, 14}, {2, 7, 9, 13, 14}, {2, 7, 9, 12, 14}, {2, 7, 9, 12, 13}, {1, 9, 12, 13, 14}, {1, 7, 12, 13, 14}, {1, 7, 9, 13, 14}, {1, 7, 9, 12, 14}, {1, 7, 9, 12, 13}, {1, 2, 12, 13, 14}, {1, 2, 9, 13, 14}, {1, 2, 9, 12, 14}, {1, 2, 9, 12, 13}, {1, 2, 7, 13, 14}, {1, 2, 7, 12, 14}, {1, 2, 7, 12, 13}, {1, 2, 7, 9, 14}, {1, 2, 7, 9, 13}, {1, 2, 7, 9, 12}, {0, 9, 12, 13, 14}, {0, 7, 12, 13, 14}, {0, 7, 9, 13, 14}, {0, 7, 9, 12, 14}, {0, 7, 9, 12, 13}, {0, 2, 12, 13, 14}, {0, 2, 9, 13, 14}, {0, 2, 9, 12, 14}, {0, 2, 9, 12, 13}, {0, 2, 7, 13, 14}, {0, 2, 7, 12, 14}, {0, 2, 7, 12, 13}, {0, 2, 7, 9, 14}, {0, 2, 7, 9, 13}, {0, 2, 7, 9, 12}, {0, 1, 12, 13, 14}, {0, 1, 9, 13, 14}, {0, 1, 9, 12, 14}, {0, 1, 9, 12, 13}, {0, 1, 7, 13, 14}, {0, 1, 7, 12, 14}, {0, 1, 7, 12, 13}, {0, 1, 7, 9, 14}, {0, 1, 7, 9, 13}, {0, 1, 7, 9, 12}, {0, 1, 2, 13, 14}, {0, 1, 2, 12, 14}, {0, 1, 2, 12, 13}, {0, 1, 2, 9, 14}, {0, 1, 2, 9, 13}, {0, 1, 2, 9, 12}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 13}, {0, 1, 2, 7, 12}, {0, 1, 2, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29319 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 7, 9, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {7, 9, 12, 13, 14} ∨
        polygon = {2, 9, 12, 13, 14} ∨
        polygon = {2, 7, 12, 13, 14} ∨
        polygon = {2, 7, 9, 13, 14} ∨
        polygon = {2, 7, 9, 12, 14} ∨
        polygon = {2, 7, 9, 12, 13} ∨
        polygon = {1, 9, 12, 13, 14} ∨
        polygon = {1, 7, 12, 13, 14} ∨
        polygon = {1, 7, 9, 13, 14} ∨
        polygon = {1, 7, 9, 12, 14} ∨
        polygon = {1, 7, 9, 12, 13} ∨
        polygon = {1, 2, 12, 13, 14} ∨
        polygon = {1, 2, 9, 13, 14} ∨
        polygon = {1, 2, 9, 12, 14} ∨
        polygon = {1, 2, 9, 12, 13} ∨
        polygon = {1, 2, 7, 13, 14} ∨
        polygon = {1, 2, 7, 12, 14} ∨
        polygon = {1, 2, 7, 12, 13} ∨
        polygon = {1, 2, 7, 9, 14} ∨
        polygon = {1, 2, 7, 9, 13} ∨
        polygon = {1, 2, 7, 9, 12} ∨
        polygon = {0, 9, 12, 13, 14} ∨
        polygon = {0, 7, 12, 13, 14} ∨
        polygon = {0, 7, 9, 13, 14} ∨
        polygon = {0, 7, 9, 12, 14} ∨
        polygon = {0, 7, 9, 12, 13} ∨
        polygon = {0, 2, 12, 13, 14} ∨
        polygon = {0, 2, 9, 13, 14} ∨
        polygon = {0, 2, 9, 12, 14} ∨
        polygon = {0, 2, 9, 12, 13} ∨
        polygon = {0, 2, 7, 13, 14} ∨
        polygon = {0, 2, 7, 12, 14} ∨
        polygon = {0, 2, 7, 12, 13} ∨
        polygon = {0, 2, 7, 9, 14} ∨
        polygon = {0, 2, 7, 9, 13} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 1, 12, 13, 14} ∨
        polygon = {0, 1, 9, 13, 14} ∨
        polygon = {0, 1, 9, 12, 14} ∨
        polygon = {0, 1, 9, 12, 13} ∨
        polygon = {0, 1, 7, 13, 14} ∨
        polygon = {0, 1, 7, 12, 14} ∨
        polygon = {0, 1, 7, 12, 13} ∨
        polygon = {0, 1, 7, 9, 14} ∨
        polygon = {0, 1, 7, 9, 13} ∨
        polygon = {0, 1, 7, 9, 12} ∨
        polygon = {0, 1, 2, 13, 14} ∨
        polygon = {0, 1, 2, 12, 14} ∨
        polygon = {0, 1, 2, 12, 13} ∨
        polygon = {0, 1, 2, 9, 14} ∨
        polygon = {0, 1, 2, 9, 13} ∨
        polygon = {0, 1, 2, 9, 12} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 7, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29319] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29831 :
    (({0, 1, 2, 7, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 10, 12, 13, 14}, {2, 10, 12, 13, 14}, {2, 7, 12, 13, 14}, {2, 7, 10, 13, 14}, {2, 7, 10, 12, 14}, {2, 7, 10, 12, 13}, {1, 10, 12, 13, 14}, {1, 7, 12, 13, 14}, {1, 7, 10, 13, 14}, {1, 7, 10, 12, 14}, {1, 7, 10, 12, 13}, {1, 2, 12, 13, 14}, {1, 2, 10, 13, 14}, {1, 2, 10, 12, 14}, {1, 2, 10, 12, 13}, {1, 2, 7, 13, 14}, {1, 2, 7, 12, 14}, {1, 2, 7, 12, 13}, {1, 2, 7, 10, 14}, {1, 2, 7, 10, 13}, {1, 2, 7, 10, 12}, {0, 10, 12, 13, 14}, {0, 7, 12, 13, 14}, {0, 7, 10, 13, 14}, {0, 7, 10, 12, 14}, {0, 7, 10, 12, 13}, {0, 2, 12, 13, 14}, {0, 2, 10, 13, 14}, {0, 2, 10, 12, 14}, {0, 2, 10, 12, 13}, {0, 2, 7, 13, 14}, {0, 2, 7, 12, 14}, {0, 2, 7, 12, 13}, {0, 2, 7, 10, 14}, {0, 2, 7, 10, 13}, {0, 2, 7, 10, 12}, {0, 1, 12, 13, 14}, {0, 1, 10, 13, 14}, {0, 1, 10, 12, 14}, {0, 1, 10, 12, 13}, {0, 1, 7, 13, 14}, {0, 1, 7, 12, 14}, {0, 1, 7, 12, 13}, {0, 1, 7, 10, 14}, {0, 1, 7, 10, 13}, {0, 1, 7, 10, 12}, {0, 1, 2, 13, 14}, {0, 1, 2, 12, 14}, {0, 1, 2, 12, 13}, {0, 1, 2, 10, 14}, {0, 1, 2, 10, 13}, {0, 1, 2, 10, 12}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 13}, {0, 1, 2, 7, 12}, {0, 1, 2, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29831 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 7, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {7, 10, 12, 13, 14} ∨
        polygon = {2, 10, 12, 13, 14} ∨
        polygon = {2, 7, 12, 13, 14} ∨
        polygon = {2, 7, 10, 13, 14} ∨
        polygon = {2, 7, 10, 12, 14} ∨
        polygon = {2, 7, 10, 12, 13} ∨
        polygon = {1, 10, 12, 13, 14} ∨
        polygon = {1, 7, 12, 13, 14} ∨
        polygon = {1, 7, 10, 13, 14} ∨
        polygon = {1, 7, 10, 12, 14} ∨
        polygon = {1, 7, 10, 12, 13} ∨
        polygon = {1, 2, 12, 13, 14} ∨
        polygon = {1, 2, 10, 13, 14} ∨
        polygon = {1, 2, 10, 12, 14} ∨
        polygon = {1, 2, 10, 12, 13} ∨
        polygon = {1, 2, 7, 13, 14} ∨
        polygon = {1, 2, 7, 12, 14} ∨
        polygon = {1, 2, 7, 12, 13} ∨
        polygon = {1, 2, 7, 10, 14} ∨
        polygon = {1, 2, 7, 10, 13} ∨
        polygon = {1, 2, 7, 10, 12} ∨
        polygon = {0, 10, 12, 13, 14} ∨
        polygon = {0, 7, 12, 13, 14} ∨
        polygon = {0, 7, 10, 13, 14} ∨
        polygon = {0, 7, 10, 12, 14} ∨
        polygon = {0, 7, 10, 12, 13} ∨
        polygon = {0, 2, 12, 13, 14} ∨
        polygon = {0, 2, 10, 13, 14} ∨
        polygon = {0, 2, 10, 12, 14} ∨
        polygon = {0, 2, 10, 12, 13} ∨
        polygon = {0, 2, 7, 13, 14} ∨
        polygon = {0, 2, 7, 12, 14} ∨
        polygon = {0, 2, 7, 12, 13} ∨
        polygon = {0, 2, 7, 10, 14} ∨
        polygon = {0, 2, 7, 10, 13} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 1, 12, 13, 14} ∨
        polygon = {0, 1, 10, 13, 14} ∨
        polygon = {0, 1, 10, 12, 14} ∨
        polygon = {0, 1, 10, 12, 13} ∨
        polygon = {0, 1, 7, 13, 14} ∨
        polygon = {0, 1, 7, 12, 14} ∨
        polygon = {0, 1, 7, 12, 13} ∨
        polygon = {0, 1, 7, 10, 14} ∨
        polygon = {0, 1, 7, 10, 13} ∨
        polygon = {0, 1, 7, 10, 12} ∨
        polygon = {0, 1, 2, 13, 14} ∨
        polygon = {0, 1, 2, 12, 14} ∨
        polygon = {0, 1, 2, 12, 13} ∨
        polygon = {0, 1, 2, 10, 14} ∨
        polygon = {0, 1, 2, 10, 13} ∨
        polygon = {0, 1, 2, 10, 12} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 7, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 7, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29831] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask30215 :
    (({0, 1, 2, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 10, 12, 13, 14}, {2, 10, 12, 13, 14}, {2, 9, 12, 13, 14}, {2, 9, 10, 13, 14}, {2, 9, 10, 12, 14}, {2, 9, 10, 12, 13}, {1, 10, 12, 13, 14}, {1, 9, 12, 13, 14}, {1, 9, 10, 13, 14}, {1, 9, 10, 12, 14}, {1, 9, 10, 12, 13}, {1, 2, 12, 13, 14}, {1, 2, 10, 13, 14}, {1, 2, 10, 12, 14}, {1, 2, 10, 12, 13}, {1, 2, 9, 13, 14}, {1, 2, 9, 12, 14}, {1, 2, 9, 12, 13}, {1, 2, 9, 10, 14}, {1, 2, 9, 10, 13}, {1, 2, 9, 10, 12}, {0, 10, 12, 13, 14}, {0, 9, 12, 13, 14}, {0, 9, 10, 13, 14}, {0, 9, 10, 12, 14}, {0, 9, 10, 12, 13}, {0, 2, 12, 13, 14}, {0, 2, 10, 13, 14}, {0, 2, 10, 12, 14}, {0, 2, 10, 12, 13}, {0, 2, 9, 13, 14}, {0, 2, 9, 12, 14}, {0, 2, 9, 12, 13}, {0, 2, 9, 10, 14}, {0, 2, 9, 10, 13}, {0, 2, 9, 10, 12}, {0, 1, 12, 13, 14}, {0, 1, 10, 13, 14}, {0, 1, 10, 12, 14}, {0, 1, 10, 12, 13}, {0, 1, 9, 13, 14}, {0, 1, 9, 12, 14}, {0, 1, 9, 12, 13}, {0, 1, 9, 10, 14}, {0, 1, 9, 10, 13}, {0, 1, 9, 10, 12}, {0, 1, 2, 13, 14}, {0, 1, 2, 12, 14}, {0, 1, 2, 12, 13}, {0, 1, 2, 10, 14}, {0, 1, 2, 10, 13}, {0, 1, 2, 10, 12}, {0, 1, 2, 9, 14}, {0, 1, 2, 9, 13}, {0, 1, 2, 9, 12}, {0, 1, 2, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask30215 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 9, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {9, 10, 12, 13, 14} ∨
        polygon = {2, 10, 12, 13, 14} ∨
        polygon = {2, 9, 12, 13, 14} ∨
        polygon = {2, 9, 10, 13, 14} ∨
        polygon = {2, 9, 10, 12, 14} ∨
        polygon = {2, 9, 10, 12, 13} ∨
        polygon = {1, 10, 12, 13, 14} ∨
        polygon = {1, 9, 12, 13, 14} ∨
        polygon = {1, 9, 10, 13, 14} ∨
        polygon = {1, 9, 10, 12, 14} ∨
        polygon = {1, 9, 10, 12, 13} ∨
        polygon = {1, 2, 12, 13, 14} ∨
        polygon = {1, 2, 10, 13, 14} ∨
        polygon = {1, 2, 10, 12, 14} ∨
        polygon = {1, 2, 10, 12, 13} ∨
        polygon = {1, 2, 9, 13, 14} ∨
        polygon = {1, 2, 9, 12, 14} ∨
        polygon = {1, 2, 9, 12, 13} ∨
        polygon = {1, 2, 9, 10, 14} ∨
        polygon = {1, 2, 9, 10, 13} ∨
        polygon = {1, 2, 9, 10, 12} ∨
        polygon = {0, 10, 12, 13, 14} ∨
        polygon = {0, 9, 12, 13, 14} ∨
        polygon = {0, 9, 10, 13, 14} ∨
        polygon = {0, 9, 10, 12, 14} ∨
        polygon = {0, 9, 10, 12, 13} ∨
        polygon = {0, 2, 12, 13, 14} ∨
        polygon = {0, 2, 10, 13, 14} ∨
        polygon = {0, 2, 10, 12, 14} ∨
        polygon = {0, 2, 10, 12, 13} ∨
        polygon = {0, 2, 9, 13, 14} ∨
        polygon = {0, 2, 9, 12, 14} ∨
        polygon = {0, 2, 9, 12, 13} ∨
        polygon = {0, 2, 9, 10, 14} ∨
        polygon = {0, 2, 9, 10, 13} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 1, 12, 13, 14} ∨
        polygon = {0, 1, 10, 13, 14} ∨
        polygon = {0, 1, 10, 12, 14} ∨
        polygon = {0, 1, 10, 12, 13} ∨
        polygon = {0, 1, 9, 13, 14} ∨
        polygon = {0, 1, 9, 12, 14} ∨
        polygon = {0, 1, 9, 12, 13} ∨
        polygon = {0, 1, 9, 10, 14} ∨
        polygon = {0, 1, 9, 10, 13} ∨
        polygon = {0, 1, 9, 10, 12} ∨
        polygon = {0, 1, 2, 13, 14} ∨
        polygon = {0, 1, 2, 12, 14} ∨
        polygon = {0, 1, 2, 12, 13} ∨
        polygon = {0, 1, 2, 10, 14} ∨
        polygon = {0, 1, 2, 10, 13} ∨
        polygon = {0, 1, 2, 10, 12} ∨
        polygon = {0, 1, 2, 9, 14} ∨
        polygon = {0, 1, 2, 9, 13} ∨
        polygon = {0, 1, 2, 9, 12} ∨
        polygon = {0, 1, 2, 9, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask30215] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask00763 :
    (({0, 1, 3, 4, 5, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 9}, {3, 5, 6, 7, 9}, {3, 4, 6, 7, 9}, {3, 4, 5, 7, 9}, {3, 4, 5, 6, 9}, {3, 4, 5, 6, 7}, {1, 5, 6, 7, 9}, {1, 4, 6, 7, 9}, {1, 4, 5, 7, 9}, {1, 4, 5, 6, 9}, {1, 4, 5, 6, 7}, {1, 3, 6, 7, 9}, {1, 3, 5, 7, 9}, {1, 3, 5, 6, 9}, {1, 3, 5, 6, 7}, {1, 3, 4, 7, 9}, {1, 3, 4, 6, 9}, {1, 3, 4, 6, 7}, {1, 3, 4, 5, 9}, {1, 3, 4, 5, 7}, {1, 3, 4, 5, 6}, {0, 5, 6, 7, 9}, {0, 4, 6, 7, 9}, {0, 4, 5, 7, 9}, {0, 4, 5, 6, 9}, {0, 4, 5, 6, 7}, {0, 3, 6, 7, 9}, {0, 3, 5, 7, 9}, {0, 3, 5, 6, 9}, {0, 3, 5, 6, 7}, {0, 3, 4, 7, 9}, {0, 3, 4, 6, 9}, {0, 3, 4, 6, 7}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 7}, {0, 3, 4, 5, 6}, {0, 1, 6, 7, 9}, {0, 1, 5, 7, 9}, {0, 1, 5, 6, 9}, {0, 1, 5, 6, 7}, {0, 1, 4, 7, 9}, {0, 1, 4, 6, 9}, {0, 1, 4, 6, 7}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 7}, {0, 1, 4, 5, 6}, {0, 1, 3, 7, 9}, {0, 1, 3, 6, 9}, {0, 1, 3, 6, 7}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 7}, {0, 1, 3, 5, 6}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 6}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask00763 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 6, 7, 9} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 7, 9} ∨
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {3, 4, 5, 6, 7} ∨
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
        polygon = {0, 5, 6, 7, 9} ∨
        polygon = {0, 4, 6, 7, 9} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 4, 5, 6, 7} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 3, 5, 6, 7} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 3, 4, 5, 6} ∨
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
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 5, 6} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 6} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask00763] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01275 :
    (({0, 1, 3, 4, 5, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 10}, {3, 5, 6, 7, 10}, {3, 4, 6, 7, 10}, {3, 4, 5, 7, 10}, {3, 4, 5, 6, 10}, {3, 4, 5, 6, 7}, {1, 5, 6, 7, 10}, {1, 4, 6, 7, 10}, {1, 4, 5, 7, 10}, {1, 4, 5, 6, 10}, {1, 4, 5, 6, 7}, {1, 3, 6, 7, 10}, {1, 3, 5, 7, 10}, {1, 3, 5, 6, 10}, {1, 3, 5, 6, 7}, {1, 3, 4, 7, 10}, {1, 3, 4, 6, 10}, {1, 3, 4, 6, 7}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 7}, {1, 3, 4, 5, 6}, {0, 5, 6, 7, 10}, {0, 4, 6, 7, 10}, {0, 4, 5, 7, 10}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 7}, {0, 3, 6, 7, 10}, {0, 3, 5, 7, 10}, {0, 3, 5, 6, 10}, {0, 3, 5, 6, 7}, {0, 3, 4, 7, 10}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 7}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 7}, {0, 3, 4, 5, 6}, {0, 1, 6, 7, 10}, {0, 1, 5, 7, 10}, {0, 1, 5, 6, 10}, {0, 1, 5, 6, 7}, {0, 1, 4, 7, 10}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 7}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 7}, {0, 1, 4, 5, 6}, {0, 1, 3, 7, 10}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 7}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 7}, {0, 1, 3, 5, 6}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 6}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01275 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 6, 7, 10} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 7, 10} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {3, 4, 5, 6, 7} ∨
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
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 7} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 3, 5, 6, 7} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 3, 4, 5, 6} ∨
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
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 5, 6} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 6} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01275] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask04347 :
    (({0, 1, 3, 4, 5, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 12}, {3, 5, 6, 7, 12}, {3, 4, 6, 7, 12}, {3, 4, 5, 7, 12}, {3, 4, 5, 6, 12}, {3, 4, 5, 6, 7}, {1, 5, 6, 7, 12}, {1, 4, 6, 7, 12}, {1, 4, 5, 7, 12}, {1, 4, 5, 6, 12}, {1, 4, 5, 6, 7}, {1, 3, 6, 7, 12}, {1, 3, 5, 7, 12}, {1, 3, 5, 6, 12}, {1, 3, 5, 6, 7}, {1, 3, 4, 7, 12}, {1, 3, 4, 6, 12}, {1, 3, 4, 6, 7}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 7}, {1, 3, 4, 5, 6}, {0, 5, 6, 7, 12}, {0, 4, 6, 7, 12}, {0, 4, 5, 7, 12}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 7}, {0, 3, 6, 7, 12}, {0, 3, 5, 7, 12}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 7}, {0, 3, 4, 7, 12}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 7}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 7}, {0, 3, 4, 5, 6}, {0, 1, 6, 7, 12}, {0, 1, 5, 7, 12}, {0, 1, 5, 6, 12}, {0, 1, 5, 6, 7}, {0, 1, 4, 7, 12}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 7}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 7}, {0, 1, 4, 5, 6}, {0, 1, 3, 7, 12}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 7}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 7}, {0, 1, 3, 5, 6}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 6}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask04347 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 6, 7, 12} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 7, 12} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {3, 4, 5, 6, 7} ∨
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
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 4, 6, 7, 12} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 6, 7} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 5, 6, 7} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 3, 4, 5, 6} ∨
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
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 5, 6} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 6} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask04347] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask08443 :
    (({0, 1, 3, 4, 5, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 13}, {3, 5, 6, 7, 13}, {3, 4, 6, 7, 13}, {3, 4, 5, 7, 13}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 7}, {1, 5, 6, 7, 13}, {1, 4, 6, 7, 13}, {1, 4, 5, 7, 13}, {1, 4, 5, 6, 13}, {1, 4, 5, 6, 7}, {1, 3, 6, 7, 13}, {1, 3, 5, 7, 13}, {1, 3, 5, 6, 13}, {1, 3, 5, 6, 7}, {1, 3, 4, 7, 13}, {1, 3, 4, 6, 13}, {1, 3, 4, 6, 7}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 7}, {1, 3, 4, 5, 6}, {0, 5, 6, 7, 13}, {0, 4, 6, 7, 13}, {0, 4, 5, 7, 13}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 7}, {0, 3, 6, 7, 13}, {0, 3, 5, 7, 13}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 7}, {0, 3, 4, 7, 13}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 7}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 7}, {0, 3, 4, 5, 6}, {0, 1, 6, 7, 13}, {0, 1, 5, 7, 13}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 7}, {0, 1, 4, 7, 13}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 7}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 7}, {0, 1, 4, 5, 6}, {0, 1, 3, 7, 13}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 7}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 7}, {0, 1, 3, 5, 6}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 6}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask08443 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 6, 7, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 7, 13} ∨
        polygon = {3, 5, 6, 7, 13} ∨
        polygon = {3, 4, 6, 7, 13} ∨
        polygon = {3, 4, 5, 7, 13} ∨
        polygon = {3, 4, 5, 6, 13} ∨
        polygon = {3, 4, 5, 6, 7} ∨
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
        polygon = {0, 5, 6, 7, 13} ∨
        polygon = {0, 4, 6, 7, 13} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 7} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 6, 13} ∨
        polygon = {0, 3, 5, 6, 7} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 3, 4, 5, 6} ∨
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
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 5, 6} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 6} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask08443] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask16635 :
    (({0, 1, 3, 4, 5, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 14}, {3, 5, 6, 7, 14}, {3, 4, 6, 7, 14}, {3, 4, 5, 7, 14}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 7}, {1, 5, 6, 7, 14}, {1, 4, 6, 7, 14}, {1, 4, 5, 7, 14}, {1, 4, 5, 6, 14}, {1, 4, 5, 6, 7}, {1, 3, 6, 7, 14}, {1, 3, 5, 7, 14}, {1, 3, 5, 6, 14}, {1, 3, 5, 6, 7}, {1, 3, 4, 7, 14}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 7}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 7}, {1, 3, 4, 5, 6}, {0, 5, 6, 7, 14}, {0, 4, 6, 7, 14}, {0, 4, 5, 7, 14}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 7}, {0, 3, 6, 7, 14}, {0, 3, 5, 7, 14}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 7}, {0, 3, 4, 7, 14}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 7}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 7}, {0, 3, 4, 5, 6}, {0, 1, 6, 7, 14}, {0, 1, 5, 7, 14}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 7}, {0, 1, 4, 7, 14}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 7}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 7}, {0, 1, 4, 5, 6}, {0, 1, 3, 7, 14}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 7}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 7}, {0, 1, 3, 5, 6}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 6}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask16635 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 6, 7, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 7, 14} ∨
        polygon = {3, 5, 6, 7, 14} ∨
        polygon = {3, 4, 6, 7, 14} ∨
        polygon = {3, 4, 5, 7, 14} ∨
        polygon = {3, 4, 5, 6, 14} ∨
        polygon = {3, 4, 5, 6, 7} ∨
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
        polygon = {0, 5, 6, 7, 14} ∨
        polygon = {0, 4, 6, 7, 14} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 7} ∨
        polygon = {0, 3, 6, 7, 14} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 6, 14} ∨
        polygon = {0, 3, 5, 6, 7} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 3, 4, 5, 6} ∨
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
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 5, 6} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 6} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask16635] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01403 :
    (({0, 1, 3, 4, 5, 6, 8, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 8, 10}, {3, 5, 6, 8, 10}, {3, 4, 6, 8, 10}, {3, 4, 5, 8, 10}, {3, 4, 5, 6, 10}, {3, 4, 5, 6, 8}, {1, 5, 6, 8, 10}, {1, 4, 6, 8, 10}, {1, 4, 5, 8, 10}, {1, 4, 5, 6, 10}, {1, 4, 5, 6, 8}, {1, 3, 6, 8, 10}, {1, 3, 5, 8, 10}, {1, 3, 5, 6, 10}, {1, 3, 5, 6, 8}, {1, 3, 4, 8, 10}, {1, 3, 4, 6, 10}, {1, 3, 4, 6, 8}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 8}, {1, 3, 4, 5, 6}, {0, 5, 6, 8, 10}, {0, 4, 6, 8, 10}, {0, 4, 5, 8, 10}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 8}, {0, 3, 6, 8, 10}, {0, 3, 5, 8, 10}, {0, 3, 5, 6, 10}, {0, 3, 5, 6, 8}, {0, 3, 4, 8, 10}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 8}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 8}, {0, 3, 4, 5, 6}, {0, 1, 6, 8, 10}, {0, 1, 5, 8, 10}, {0, 1, 5, 6, 10}, {0, 1, 5, 6, 8}, {0, 1, 4, 8, 10}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 8}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 8}, {0, 1, 4, 5, 6}, {0, 1, 3, 8, 10}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 8}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 8}, {0, 1, 3, 5, 6}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 8}, {0, 1, 3, 4, 6}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01403 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 6, 8, 10} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 8, 10} ∨
        polygon = {3, 5, 6, 8, 10} ∨
        polygon = {3, 4, 6, 8, 10} ∨
        polygon = {3, 4, 5, 8, 10} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {3, 4, 5, 6, 8} ∨
        polygon = {1, 5, 6, 8, 10} ∨
        polygon = {1, 4, 6, 8, 10} ∨
        polygon = {1, 4, 5, 8, 10} ∨
        polygon = {1, 4, 5, 6, 10} ∨
        polygon = {1, 4, 5, 6, 8} ∨
        polygon = {1, 3, 6, 8, 10} ∨
        polygon = {1, 3, 5, 8, 10} ∨
        polygon = {1, 3, 5, 6, 10} ∨
        polygon = {1, 3, 5, 6, 8} ∨
        polygon = {1, 3, 4, 8, 10} ∨
        polygon = {1, 3, 4, 6, 10} ∨
        polygon = {1, 3, 4, 6, 8} ∨
        polygon = {1, 3, 4, 5, 10} ∨
        polygon = {1, 3, 4, 5, 8} ∨
        polygon = {1, 3, 4, 5, 6} ∨
        polygon = {0, 5, 6, 8, 10} ∨
        polygon = {0, 4, 6, 8, 10} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 8} ∨
        polygon = {0, 3, 6, 8, 10} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 3, 5, 6, 8} ∨
        polygon = {0, 3, 4, 8, 10} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 8} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 3, 4, 5, 6} ∨
        polygon = {0, 1, 6, 8, 10} ∨
        polygon = {0, 1, 5, 8, 10} ∨
        polygon = {0, 1, 5, 6, 10} ∨
        polygon = {0, 1, 5, 6, 8} ∨
        polygon = {0, 1, 4, 8, 10} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 6, 8} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 8} ∨
        polygon = {0, 1, 4, 5, 6} ∨
        polygon = {0, 1, 3, 8, 10} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 8} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 8} ∨
        polygon = {0, 1, 3, 5, 6} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 8} ∨
        polygon = {0, 1, 3, 4, 6} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 6, 8, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01403] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask08571 :
    (({0, 1, 3, 4, 5, 6, 8, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 8, 13}, {3, 5, 6, 8, 13}, {3, 4, 6, 8, 13}, {3, 4, 5, 8, 13}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 8}, {1, 5, 6, 8, 13}, {1, 4, 6, 8, 13}, {1, 4, 5, 8, 13}, {1, 4, 5, 6, 13}, {1, 4, 5, 6, 8}, {1, 3, 6, 8, 13}, {1, 3, 5, 8, 13}, {1, 3, 5, 6, 13}, {1, 3, 5, 6, 8}, {1, 3, 4, 8, 13}, {1, 3, 4, 6, 13}, {1, 3, 4, 6, 8}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 8}, {1, 3, 4, 5, 6}, {0, 5, 6, 8, 13}, {0, 4, 6, 8, 13}, {0, 4, 5, 8, 13}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 8}, {0, 3, 6, 8, 13}, {0, 3, 5, 8, 13}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 8}, {0, 3, 4, 8, 13}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 8}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 8}, {0, 3, 4, 5, 6}, {0, 1, 6, 8, 13}, {0, 1, 5, 8, 13}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 8}, {0, 1, 4, 8, 13}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 8}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 8}, {0, 1, 4, 5, 6}, {0, 1, 3, 8, 13}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 8}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 8}, {0, 1, 3, 5, 6}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 8}, {0, 1, 3, 4, 6}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask08571 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 6, 8, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 8, 13} ∨
        polygon = {3, 5, 6, 8, 13} ∨
        polygon = {3, 4, 6, 8, 13} ∨
        polygon = {3, 4, 5, 8, 13} ∨
        polygon = {3, 4, 5, 6, 13} ∨
        polygon = {3, 4, 5, 6, 8} ∨
        polygon = {1, 5, 6, 8, 13} ∨
        polygon = {1, 4, 6, 8, 13} ∨
        polygon = {1, 4, 5, 8, 13} ∨
        polygon = {1, 4, 5, 6, 13} ∨
        polygon = {1, 4, 5, 6, 8} ∨
        polygon = {1, 3, 6, 8, 13} ∨
        polygon = {1, 3, 5, 8, 13} ∨
        polygon = {1, 3, 5, 6, 13} ∨
        polygon = {1, 3, 5, 6, 8} ∨
        polygon = {1, 3, 4, 8, 13} ∨
        polygon = {1, 3, 4, 6, 13} ∨
        polygon = {1, 3, 4, 6, 8} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 3, 4, 5, 8} ∨
        polygon = {1, 3, 4, 5, 6} ∨
        polygon = {0, 5, 6, 8, 13} ∨
        polygon = {0, 4, 6, 8, 13} ∨
        polygon = {0, 4, 5, 8, 13} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 8} ∨
        polygon = {0, 3, 6, 8, 13} ∨
        polygon = {0, 3, 5, 8, 13} ∨
        polygon = {0, 3, 5, 6, 13} ∨
        polygon = {0, 3, 5, 6, 8} ∨
        polygon = {0, 3, 4, 8, 13} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 8} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 3, 4, 5, 6} ∨
        polygon = {0, 1, 6, 8, 13} ∨
        polygon = {0, 1, 5, 8, 13} ∨
        polygon = {0, 1, 5, 6, 13} ∨
        polygon = {0, 1, 5, 6, 8} ∨
        polygon = {0, 1, 4, 8, 13} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 8} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 8} ∨
        polygon = {0, 1, 4, 5, 6} ∨
        polygon = {0, 1, 3, 8, 13} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 8} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 8} ∨
        polygon = {0, 1, 3, 5, 6} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 8} ∨
        polygon = {0, 1, 3, 4, 6} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 6, 8, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask08571] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask16763 :
    (({0, 1, 3, 4, 5, 6, 8, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 8, 14}, {3, 5, 6, 8, 14}, {3, 4, 6, 8, 14}, {3, 4, 5, 8, 14}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 8}, {1, 5, 6, 8, 14}, {1, 4, 6, 8, 14}, {1, 4, 5, 8, 14}, {1, 4, 5, 6, 14}, {1, 4, 5, 6, 8}, {1, 3, 6, 8, 14}, {1, 3, 5, 8, 14}, {1, 3, 5, 6, 14}, {1, 3, 5, 6, 8}, {1, 3, 4, 8, 14}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 8}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 8}, {1, 3, 4, 5, 6}, {0, 5, 6, 8, 14}, {0, 4, 6, 8, 14}, {0, 4, 5, 8, 14}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 8}, {0, 3, 6, 8, 14}, {0, 3, 5, 8, 14}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 8}, {0, 3, 4, 8, 14}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 8}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 8}, {0, 3, 4, 5, 6}, {0, 1, 6, 8, 14}, {0, 1, 5, 8, 14}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 8}, {0, 1, 4, 8, 14}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 8}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 8}, {0, 1, 4, 5, 6}, {0, 1, 3, 8, 14}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 8}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 8}, {0, 1, 3, 5, 6}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 8}, {0, 1, 3, 4, 6}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask16763 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 6, 8, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 8, 14} ∨
        polygon = {3, 5, 6, 8, 14} ∨
        polygon = {3, 4, 6, 8, 14} ∨
        polygon = {3, 4, 5, 8, 14} ∨
        polygon = {3, 4, 5, 6, 14} ∨
        polygon = {3, 4, 5, 6, 8} ∨
        polygon = {1, 5, 6, 8, 14} ∨
        polygon = {1, 4, 6, 8, 14} ∨
        polygon = {1, 4, 5, 8, 14} ∨
        polygon = {1, 4, 5, 6, 14} ∨
        polygon = {1, 4, 5, 6, 8} ∨
        polygon = {1, 3, 6, 8, 14} ∨
        polygon = {1, 3, 5, 8, 14} ∨
        polygon = {1, 3, 5, 6, 14} ∨
        polygon = {1, 3, 5, 6, 8} ∨
        polygon = {1, 3, 4, 8, 14} ∨
        polygon = {1, 3, 4, 6, 14} ∨
        polygon = {1, 3, 4, 6, 8} ∨
        polygon = {1, 3, 4, 5, 14} ∨
        polygon = {1, 3, 4, 5, 8} ∨
        polygon = {1, 3, 4, 5, 6} ∨
        polygon = {0, 5, 6, 8, 14} ∨
        polygon = {0, 4, 6, 8, 14} ∨
        polygon = {0, 4, 5, 8, 14} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 8} ∨
        polygon = {0, 3, 6, 8, 14} ∨
        polygon = {0, 3, 5, 8, 14} ∨
        polygon = {0, 3, 5, 6, 14} ∨
        polygon = {0, 3, 5, 6, 8} ∨
        polygon = {0, 3, 4, 8, 14} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 8} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 3, 4, 5, 6} ∨
        polygon = {0, 1, 6, 8, 14} ∨
        polygon = {0, 1, 5, 8, 14} ∨
        polygon = {0, 1, 5, 6, 14} ∨
        polygon = {0, 1, 5, 6, 8} ∨
        polygon = {0, 1, 4, 8, 14} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 8} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 8} ∨
        polygon = {0, 1, 4, 5, 6} ∨
        polygon = {0, 1, 3, 8, 14} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 8} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 8} ∨
        polygon = {0, 1, 3, 5, 6} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 8} ∨
        polygon = {0, 1, 3, 4, 6} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 6, 8, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask16763] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01659 :
    (({0, 1, 3, 4, 5, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 9, 10}, {3, 5, 6, 9, 10}, {3, 4, 6, 9, 10}, {3, 4, 5, 9, 10}, {3, 4, 5, 6, 10}, {3, 4, 5, 6, 9}, {1, 5, 6, 9, 10}, {1, 4, 6, 9, 10}, {1, 4, 5, 9, 10}, {1, 4, 5, 6, 10}, {1, 4, 5, 6, 9}, {1, 3, 6, 9, 10}, {1, 3, 5, 9, 10}, {1, 3, 5, 6, 10}, {1, 3, 5, 6, 9}, {1, 3, 4, 9, 10}, {1, 3, 4, 6, 10}, {1, 3, 4, 6, 9}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 9}, {1, 3, 4, 5, 6}, {0, 5, 6, 9, 10}, {0, 4, 6, 9, 10}, {0, 4, 5, 9, 10}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 9}, {0, 3, 6, 9, 10}, {0, 3, 5, 9, 10}, {0, 3, 5, 6, 10}, {0, 3, 5, 6, 9}, {0, 3, 4, 9, 10}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 9}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 6}, {0, 1, 6, 9, 10}, {0, 1, 5, 9, 10}, {0, 1, 5, 6, 10}, {0, 1, 5, 6, 9}, {0, 1, 4, 9, 10}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 9}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 6}, {0, 1, 3, 9, 10}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 9}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 6}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 6}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01659 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 6, 9, 10} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 9, 10} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {3, 4, 5, 6, 9} ∨
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
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 4, 6, 9, 10} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 6} ∨
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
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 6} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 6} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01659] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask04731 :
    (({0, 1, 3, 4, 5, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 9, 12}, {3, 5, 6, 9, 12}, {3, 4, 6, 9, 12}, {3, 4, 5, 9, 12}, {3, 4, 5, 6, 12}, {3, 4, 5, 6, 9}, {1, 5, 6, 9, 12}, {1, 4, 6, 9, 12}, {1, 4, 5, 9, 12}, {1, 4, 5, 6, 12}, {1, 4, 5, 6, 9}, {1, 3, 6, 9, 12}, {1, 3, 5, 9, 12}, {1, 3, 5, 6, 12}, {1, 3, 5, 6, 9}, {1, 3, 4, 9, 12}, {1, 3, 4, 6, 12}, {1, 3, 4, 6, 9}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 9}, {1, 3, 4, 5, 6}, {0, 5, 6, 9, 12}, {0, 4, 6, 9, 12}, {0, 4, 5, 9, 12}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 9}, {0, 3, 6, 9, 12}, {0, 3, 5, 9, 12}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 9}, {0, 3, 4, 9, 12}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 9}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 6}, {0, 1, 6, 9, 12}, {0, 1, 5, 9, 12}, {0, 1, 5, 6, 12}, {0, 1, 5, 6, 9}, {0, 1, 4, 9, 12}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 9}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 6}, {0, 1, 3, 9, 12}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 9}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 6}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 6}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask04731 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 6, 9, 12} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 9, 12} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {3, 4, 5, 6, 9} ∨
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
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 4, 6, 9, 12} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 6} ∨
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
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 6} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 6} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask04731] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask08827 :
    (({0, 1, 3, 4, 5, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 9, 13}, {3, 5, 6, 9, 13}, {3, 4, 6, 9, 13}, {3, 4, 5, 9, 13}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 9}, {1, 5, 6, 9, 13}, {1, 4, 6, 9, 13}, {1, 4, 5, 9, 13}, {1, 4, 5, 6, 13}, {1, 4, 5, 6, 9}, {1, 3, 6, 9, 13}, {1, 3, 5, 9, 13}, {1, 3, 5, 6, 13}, {1, 3, 5, 6, 9}, {1, 3, 4, 9, 13}, {1, 3, 4, 6, 13}, {1, 3, 4, 6, 9}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 9}, {1, 3, 4, 5, 6}, {0, 5, 6, 9, 13}, {0, 4, 6, 9, 13}, {0, 4, 5, 9, 13}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 9}, {0, 3, 6, 9, 13}, {0, 3, 5, 9, 13}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 9}, {0, 3, 4, 9, 13}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 9}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 6}, {0, 1, 6, 9, 13}, {0, 1, 5, 9, 13}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 9}, {0, 1, 4, 9, 13}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 9}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 6}, {0, 1, 3, 9, 13}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 9}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 6}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 6}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask08827 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 6, 9, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 9, 13} ∨
        polygon = {3, 5, 6, 9, 13} ∨
        polygon = {3, 4, 6, 9, 13} ∨
        polygon = {3, 4, 5, 9, 13} ∨
        polygon = {3, 4, 5, 6, 13} ∨
        polygon = {3, 4, 5, 6, 9} ∨
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
        polygon = {0, 5, 6, 9, 13} ∨
        polygon = {0, 4, 6, 9, 13} ∨
        polygon = {0, 4, 5, 9, 13} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 6, 13} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 6} ∨
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
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 6} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 6} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask08827] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17019 :
    (({0, 1, 3, 4, 5, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 9, 14}, {3, 5, 6, 9, 14}, {3, 4, 6, 9, 14}, {3, 4, 5, 9, 14}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 9}, {1, 5, 6, 9, 14}, {1, 4, 6, 9, 14}, {1, 4, 5, 9, 14}, {1, 4, 5, 6, 14}, {1, 4, 5, 6, 9}, {1, 3, 6, 9, 14}, {1, 3, 5, 9, 14}, {1, 3, 5, 6, 14}, {1, 3, 5, 6, 9}, {1, 3, 4, 9, 14}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 9}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 9}, {1, 3, 4, 5, 6}, {0, 5, 6, 9, 14}, {0, 4, 6, 9, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 9}, {0, 3, 6, 9, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 9}, {0, 3, 4, 9, 14}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 9}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 6}, {0, 1, 6, 9, 14}, {0, 1, 5, 9, 14}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 9}, {0, 1, 4, 9, 14}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 9}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 6}, {0, 1, 3, 9, 14}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 9}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 6}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 6}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17019 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 6, 9, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 9, 14} ∨
        polygon = {3, 5, 6, 9, 14} ∨
        polygon = {3, 4, 6, 9, 14} ∨
        polygon = {3, 4, 5, 9, 14} ∨
        polygon = {3, 4, 5, 6, 14} ∨
        polygon = {3, 4, 5, 6, 9} ∨
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
        polygon = {0, 5, 6, 9, 14} ∨
        polygon = {0, 4, 6, 9, 14} ∨
        polygon = {0, 4, 5, 9, 14} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 3, 6, 9, 14} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 6, 14} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 6} ∨
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
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 6} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 6} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17019] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05243 :
    (({0, 1, 3, 4, 5, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 10, 12}, {3, 5, 6, 10, 12}, {3, 4, 6, 10, 12}, {3, 4, 5, 10, 12}, {3, 4, 5, 6, 12}, {3, 4, 5, 6, 10}, {1, 5, 6, 10, 12}, {1, 4, 6, 10, 12}, {1, 4, 5, 10, 12}, {1, 4, 5, 6, 12}, {1, 4, 5, 6, 10}, {1, 3, 6, 10, 12}, {1, 3, 5, 10, 12}, {1, 3, 5, 6, 12}, {1, 3, 5, 6, 10}, {1, 3, 4, 10, 12}, {1, 3, 4, 6, 12}, {1, 3, 4, 6, 10}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 6}, {0, 5, 6, 10, 12}, {0, 4, 6, 10, 12}, {0, 4, 5, 10, 12}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 10}, {0, 3, 6, 10, 12}, {0, 3, 5, 10, 12}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 10}, {0, 3, 4, 10, 12}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 10}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 6}, {0, 1, 6, 10, 12}, {0, 1, 5, 10, 12}, {0, 1, 5, 6, 12}, {0, 1, 5, 6, 10}, {0, 1, 4, 10, 12}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 10}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 6}, {0, 1, 3, 10, 12}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 10}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 6}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 6}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05243 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 6, 10, 12} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 10, 12} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {3, 4, 5, 6, 10} ∨
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
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 6} ∨
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
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 6} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 6} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05243] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09339 :
    (({0, 1, 3, 4, 5, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 10, 13}, {3, 5, 6, 10, 13}, {3, 4, 6, 10, 13}, {3, 4, 5, 10, 13}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 10}, {1, 5, 6, 10, 13}, {1, 4, 6, 10, 13}, {1, 4, 5, 10, 13}, {1, 4, 5, 6, 13}, {1, 4, 5, 6, 10}, {1, 3, 6, 10, 13}, {1, 3, 5, 10, 13}, {1, 3, 5, 6, 13}, {1, 3, 5, 6, 10}, {1, 3, 4, 10, 13}, {1, 3, 4, 6, 13}, {1, 3, 4, 6, 10}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 6}, {0, 5, 6, 10, 13}, {0, 4, 6, 10, 13}, {0, 4, 5, 10, 13}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 10}, {0, 3, 6, 10, 13}, {0, 3, 5, 10, 13}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 10}, {0, 3, 4, 10, 13}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 10}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 6}, {0, 1, 6, 10, 13}, {0, 1, 5, 10, 13}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 10}, {0, 1, 4, 10, 13}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 10}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 6}, {0, 1, 3, 10, 13}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 10}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 6}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 6}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09339 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 6, 10, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 10, 13} ∨
        polygon = {3, 5, 6, 10, 13} ∨
        polygon = {3, 4, 6, 10, 13} ∨
        polygon = {3, 4, 5, 10, 13} ∨
        polygon = {3, 4, 5, 6, 13} ∨
        polygon = {3, 4, 5, 6, 10} ∨
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
        polygon = {0, 5, 6, 10, 13} ∨
        polygon = {0, 4, 6, 10, 13} ∨
        polygon = {0, 4, 5, 10, 13} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 6, 13} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 6} ∨
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
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 6} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 6} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09339] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17531 :
    (({0, 1, 3, 4, 5, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 10, 14}, {3, 5, 6, 10, 14}, {3, 4, 6, 10, 14}, {3, 4, 5, 10, 14}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 10}, {1, 5, 6, 10, 14}, {1, 4, 6, 10, 14}, {1, 4, 5, 10, 14}, {1, 4, 5, 6, 14}, {1, 4, 5, 6, 10}, {1, 3, 6, 10, 14}, {1, 3, 5, 10, 14}, {1, 3, 5, 6, 14}, {1, 3, 5, 6, 10}, {1, 3, 4, 10, 14}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 10}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 6}, {0, 5, 6, 10, 14}, {0, 4, 6, 10, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 10}, {0, 3, 6, 10, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 10}, {0, 3, 4, 10, 14}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 10}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 6}, {0, 1, 6, 10, 14}, {0, 1, 5, 10, 14}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 10}, {0, 1, 4, 10, 14}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 10}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 6}, {0, 1, 3, 10, 14}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 10}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 6}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 6}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17531 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 6, 10, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 10, 14} ∨
        polygon = {3, 5, 6, 10, 14} ∨
        polygon = {3, 4, 6, 10, 14} ∨
        polygon = {3, 4, 5, 10, 14} ∨
        polygon = {3, 4, 5, 6, 14} ∨
        polygon = {3, 4, 5, 6, 10} ∨
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
        polygon = {0, 5, 6, 10, 14} ∨
        polygon = {0, 4, 6, 10, 14} ∨
        polygon = {0, 4, 5, 10, 14} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 3, 6, 10, 14} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 6, 14} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 6} ∨
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
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 6} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 6} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17531] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12411 :
    (({0, 1, 3, 4, 5, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 12, 13}, {3, 5, 6, 12, 13}, {3, 4, 6, 12, 13}, {3, 4, 5, 12, 13}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 12}, {1, 5, 6, 12, 13}, {1, 4, 6, 12, 13}, {1, 4, 5, 12, 13}, {1, 4, 5, 6, 13}, {1, 4, 5, 6, 12}, {1, 3, 6, 12, 13}, {1, 3, 5, 12, 13}, {1, 3, 5, 6, 13}, {1, 3, 5, 6, 12}, {1, 3, 4, 12, 13}, {1, 3, 4, 6, 13}, {1, 3, 4, 6, 12}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 6}, {0, 5, 6, 12, 13}, {0, 4, 6, 12, 13}, {0, 4, 5, 12, 13}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 12}, {0, 3, 6, 12, 13}, {0, 3, 5, 12, 13}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 12}, {0, 3, 4, 12, 13}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 12}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 6}, {0, 1, 6, 12, 13}, {0, 1, 5, 12, 13}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 12}, {0, 1, 4, 12, 13}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 12}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 6}, {0, 1, 3, 12, 13}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 12}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 6}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 6}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12411 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 6, 12, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 12, 13} ∨
        polygon = {3, 5, 6, 12, 13} ∨
        polygon = {3, 4, 6, 12, 13} ∨
        polygon = {3, 4, 5, 12, 13} ∨
        polygon = {3, 4, 5, 6, 13} ∨
        polygon = {3, 4, 5, 6, 12} ∨
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
        polygon = {0, 5, 6, 12, 13} ∨
        polygon = {0, 4, 6, 12, 13} ∨
        polygon = {0, 4, 5, 12, 13} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 3, 6, 12, 13} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 6, 13} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 6} ∨
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
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 6} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 6} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12411] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask20603 :
    (({0, 1, 3, 4, 5, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 12, 14}, {3, 5, 6, 12, 14}, {3, 4, 6, 12, 14}, {3, 4, 5, 12, 14}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 12}, {1, 5, 6, 12, 14}, {1, 4, 6, 12, 14}, {1, 4, 5, 12, 14}, {1, 4, 5, 6, 14}, {1, 4, 5, 6, 12}, {1, 3, 6, 12, 14}, {1, 3, 5, 12, 14}, {1, 3, 5, 6, 14}, {1, 3, 5, 6, 12}, {1, 3, 4, 12, 14}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 12}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 6}, {0, 5, 6, 12, 14}, {0, 4, 6, 12, 14}, {0, 4, 5, 12, 14}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 12}, {0, 3, 6, 12, 14}, {0, 3, 5, 12, 14}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 12}, {0, 3, 4, 12, 14}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 12}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 6}, {0, 1, 6, 12, 14}, {0, 1, 5, 12, 14}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 12}, {0, 1, 4, 12, 14}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 12}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 6}, {0, 1, 3, 12, 14}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 12}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 6}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 6}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask20603 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 6, 12, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 12, 14} ∨
        polygon = {3, 5, 6, 12, 14} ∨
        polygon = {3, 4, 6, 12, 14} ∨
        polygon = {3, 4, 5, 12, 14} ∨
        polygon = {3, 4, 5, 6, 14} ∨
        polygon = {3, 4, 5, 6, 12} ∨
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
        polygon = {0, 5, 6, 12, 14} ∨
        polygon = {0, 4, 6, 12, 14} ∨
        polygon = {0, 4, 5, 12, 14} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 3, 6, 12, 14} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 5, 6, 14} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 6} ∨
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
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 6} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 6} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask20603] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask24699 :
    (({0, 1, 3, 4, 5, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 13, 14}, {3, 5, 6, 13, 14}, {3, 4, 6, 13, 14}, {3, 4, 5, 13, 14}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 13}, {1, 5, 6, 13, 14}, {1, 4, 6, 13, 14}, {1, 4, 5, 13, 14}, {1, 4, 5, 6, 14}, {1, 4, 5, 6, 13}, {1, 3, 6, 13, 14}, {1, 3, 5, 13, 14}, {1, 3, 5, 6, 14}, {1, 3, 5, 6, 13}, {1, 3, 4, 13, 14}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 13}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 6}, {0, 5, 6, 13, 14}, {0, 4, 6, 13, 14}, {0, 4, 5, 13, 14}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 13}, {0, 3, 6, 13, 14}, {0, 3, 5, 13, 14}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 13}, {0, 3, 4, 13, 14}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 13}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 6}, {0, 1, 6, 13, 14}, {0, 1, 5, 13, 14}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 13}, {0, 1, 4, 13, 14}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 13}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 6}, {0, 1, 3, 13, 14}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 13}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 6}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 6}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask24699 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 6, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 13, 14} ∨
        polygon = {3, 5, 6, 13, 14} ∨
        polygon = {3, 4, 6, 13, 14} ∨
        polygon = {3, 4, 5, 13, 14} ∨
        polygon = {3, 4, 5, 6, 14} ∨
        polygon = {3, 4, 5, 6, 13} ∨
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
        polygon = {0, 5, 6, 13, 14} ∨
        polygon = {0, 4, 6, 13, 14} ∨
        polygon = {0, 4, 5, 13, 14} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 3, 6, 13, 14} ∨
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 6, 14} ∨
        polygon = {0, 3, 5, 6, 13} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 6} ∨
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
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 6} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 6} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask24699] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask00955 :
    (({0, 1, 3, 4, 5, 7, 8, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 8, 9}, {3, 5, 7, 8, 9}, {3, 4, 7, 8, 9}, {3, 4, 5, 8, 9}, {3, 4, 5, 7, 9}, {3, 4, 5, 7, 8}, {1, 5, 7, 8, 9}, {1, 4, 7, 8, 9}, {1, 4, 5, 8, 9}, {1, 4, 5, 7, 9}, {1, 4, 5, 7, 8}, {1, 3, 7, 8, 9}, {1, 3, 5, 8, 9}, {1, 3, 5, 7, 9}, {1, 3, 5, 7, 8}, {1, 3, 4, 8, 9}, {1, 3, 4, 7, 9}, {1, 3, 4, 7, 8}, {1, 3, 4, 5, 9}, {1, 3, 4, 5, 8}, {1, 3, 4, 5, 7}, {0, 5, 7, 8, 9}, {0, 4, 7, 8, 9}, {0, 4, 5, 8, 9}, {0, 4, 5, 7, 9}, {0, 4, 5, 7, 8}, {0, 3, 7, 8, 9}, {0, 3, 5, 8, 9}, {0, 3, 5, 7, 9}, {0, 3, 5, 7, 8}, {0, 3, 4, 8, 9}, {0, 3, 4, 7, 9}, {0, 3, 4, 7, 8}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 8}, {0, 3, 4, 5, 7}, {0, 1, 7, 8, 9}, {0, 1, 5, 8, 9}, {0, 1, 5, 7, 9}, {0, 1, 5, 7, 8}, {0, 1, 4, 8, 9}, {0, 1, 4, 7, 9}, {0, 1, 4, 7, 8}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 8}, {0, 1, 4, 5, 7}, {0, 1, 3, 8, 9}, {0, 1, 3, 7, 9}, {0, 1, 3, 7, 8}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 8}, {0, 1, 3, 5, 7}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 8}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask00955 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 7, 8, 9} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 8, 9} ∨
        polygon = {3, 5, 7, 8, 9} ∨
        polygon = {3, 4, 7, 8, 9} ∨
        polygon = {3, 4, 5, 8, 9} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {3, 4, 5, 7, 8} ∨
        polygon = {1, 5, 7, 8, 9} ∨
        polygon = {1, 4, 7, 8, 9} ∨
        polygon = {1, 4, 5, 8, 9} ∨
        polygon = {1, 4, 5, 7, 9} ∨
        polygon = {1, 4, 5, 7, 8} ∨
        polygon = {1, 3, 7, 8, 9} ∨
        polygon = {1, 3, 5, 8, 9} ∨
        polygon = {1, 3, 5, 7, 9} ∨
        polygon = {1, 3, 5, 7, 8} ∨
        polygon = {1, 3, 4, 8, 9} ∨
        polygon = {1, 3, 4, 7, 9} ∨
        polygon = {1, 3, 4, 7, 8} ∨
        polygon = {1, 3, 4, 5, 9} ∨
        polygon = {1, 3, 4, 5, 8} ∨
        polygon = {1, 3, 4, 5, 7} ∨
        polygon = {0, 5, 7, 8, 9} ∨
        polygon = {0, 4, 7, 8, 9} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 4, 5, 7, 8} ∨
        polygon = {0, 3, 7, 8, 9} ∨
        polygon = {0, 3, 5, 8, 9} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 5, 7, 8} ∨
        polygon = {0, 3, 4, 8, 9} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 7, 8} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 1, 7, 8, 9} ∨
        polygon = {0, 1, 5, 8, 9} ∨
        polygon = {0, 1, 5, 7, 9} ∨
        polygon = {0, 1, 5, 7, 8} ∨
        polygon = {0, 1, 4, 8, 9} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 7, 8} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 4, 5, 8} ∨
        polygon = {0, 1, 4, 5, 7} ∨
        polygon = {0, 1, 3, 8, 9} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 7, 8} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 8} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 8} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 7, 8, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask00955] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01467 :
    (({0, 1, 3, 4, 5, 7, 8, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 8, 10}, {3, 5, 7, 8, 10}, {3, 4, 7, 8, 10}, {3, 4, 5, 8, 10}, {3, 4, 5, 7, 10}, {3, 4, 5, 7, 8}, {1, 5, 7, 8, 10}, {1, 4, 7, 8, 10}, {1, 4, 5, 8, 10}, {1, 4, 5, 7, 10}, {1, 4, 5, 7, 8}, {1, 3, 7, 8, 10}, {1, 3, 5, 8, 10}, {1, 3, 5, 7, 10}, {1, 3, 5, 7, 8}, {1, 3, 4, 8, 10}, {1, 3, 4, 7, 10}, {1, 3, 4, 7, 8}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 8}, {1, 3, 4, 5, 7}, {0, 5, 7, 8, 10}, {0, 4, 7, 8, 10}, {0, 4, 5, 8, 10}, {0, 4, 5, 7, 10}, {0, 4, 5, 7, 8}, {0, 3, 7, 8, 10}, {0, 3, 5, 8, 10}, {0, 3, 5, 7, 10}, {0, 3, 5, 7, 8}, {0, 3, 4, 8, 10}, {0, 3, 4, 7, 10}, {0, 3, 4, 7, 8}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 8}, {0, 3, 4, 5, 7}, {0, 1, 7, 8, 10}, {0, 1, 5, 8, 10}, {0, 1, 5, 7, 10}, {0, 1, 5, 7, 8}, {0, 1, 4, 8, 10}, {0, 1, 4, 7, 10}, {0, 1, 4, 7, 8}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 8}, {0, 1, 4, 5, 7}, {0, 1, 3, 8, 10}, {0, 1, 3, 7, 10}, {0, 1, 3, 7, 8}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 8}, {0, 1, 3, 5, 7}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 8}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01467 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 7, 8, 10} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 8, 10} ∨
        polygon = {3, 5, 7, 8, 10} ∨
        polygon = {3, 4, 7, 8, 10} ∨
        polygon = {3, 4, 5, 8, 10} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {3, 4, 5, 7, 8} ∨
        polygon = {1, 5, 7, 8, 10} ∨
        polygon = {1, 4, 7, 8, 10} ∨
        polygon = {1, 4, 5, 8, 10} ∨
        polygon = {1, 4, 5, 7, 10} ∨
        polygon = {1, 4, 5, 7, 8} ∨
        polygon = {1, 3, 7, 8, 10} ∨
        polygon = {1, 3, 5, 8, 10} ∨
        polygon = {1, 3, 5, 7, 10} ∨
        polygon = {1, 3, 5, 7, 8} ∨
        polygon = {1, 3, 4, 8, 10} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {1, 3, 4, 7, 8} ∨
        polygon = {1, 3, 4, 5, 10} ∨
        polygon = {1, 3, 4, 5, 8} ∨
        polygon = {1, 3, 4, 5, 7} ∨
        polygon = {0, 5, 7, 8, 10} ∨
        polygon = {0, 4, 7, 8, 10} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 7, 8} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 5, 7, 8} ∨
        polygon = {0, 3, 4, 8, 10} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 7, 8} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 1, 7, 8, 10} ∨
        polygon = {0, 1, 5, 8, 10} ∨
        polygon = {0, 1, 5, 7, 10} ∨
        polygon = {0, 1, 5, 7, 8} ∨
        polygon = {0, 1, 4, 8, 10} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 7, 8} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 8} ∨
        polygon = {0, 1, 4, 5, 7} ∨
        polygon = {0, 1, 3, 8, 10} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 7, 8} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 8} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 8} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 7, 8, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01467] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask04539 :
    (({0, 1, 3, 4, 5, 7, 8, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 8, 12}, {3, 5, 7, 8, 12}, {3, 4, 7, 8, 12}, {3, 4, 5, 8, 12}, {3, 4, 5, 7, 12}, {3, 4, 5, 7, 8}, {1, 5, 7, 8, 12}, {1, 4, 7, 8, 12}, {1, 4, 5, 8, 12}, {1, 4, 5, 7, 12}, {1, 4, 5, 7, 8}, {1, 3, 7, 8, 12}, {1, 3, 5, 8, 12}, {1, 3, 5, 7, 12}, {1, 3, 5, 7, 8}, {1, 3, 4, 8, 12}, {1, 3, 4, 7, 12}, {1, 3, 4, 7, 8}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 8}, {1, 3, 4, 5, 7}, {0, 5, 7, 8, 12}, {0, 4, 7, 8, 12}, {0, 4, 5, 8, 12}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 8}, {0, 3, 7, 8, 12}, {0, 3, 5, 8, 12}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 8}, {0, 3, 4, 8, 12}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 8}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 8}, {0, 3, 4, 5, 7}, {0, 1, 7, 8, 12}, {0, 1, 5, 8, 12}, {0, 1, 5, 7, 12}, {0, 1, 5, 7, 8}, {0, 1, 4, 8, 12}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 8}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 8}, {0, 1, 4, 5, 7}, {0, 1, 3, 8, 12}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 8}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 8}, {0, 1, 3, 5, 7}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 8}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask04539 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 7, 8, 12} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 8, 12} ∨
        polygon = {3, 5, 7, 8, 12} ∨
        polygon = {3, 4, 7, 8, 12} ∨
        polygon = {3, 4, 5, 8, 12} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {3, 4, 5, 7, 8} ∨
        polygon = {1, 5, 7, 8, 12} ∨
        polygon = {1, 4, 7, 8, 12} ∨
        polygon = {1, 4, 5, 8, 12} ∨
        polygon = {1, 4, 5, 7, 12} ∨
        polygon = {1, 4, 5, 7, 8} ∨
        polygon = {1, 3, 7, 8, 12} ∨
        polygon = {1, 3, 5, 8, 12} ∨
        polygon = {1, 3, 5, 7, 12} ∨
        polygon = {1, 3, 5, 7, 8} ∨
        polygon = {1, 3, 4, 8, 12} ∨
        polygon = {1, 3, 4, 7, 12} ∨
        polygon = {1, 3, 4, 7, 8} ∨
        polygon = {1, 3, 4, 5, 12} ∨
        polygon = {1, 3, 4, 5, 8} ∨
        polygon = {1, 3, 4, 5, 7} ∨
        polygon = {0, 5, 7, 8, 12} ∨
        polygon = {0, 4, 7, 8, 12} ∨
        polygon = {0, 4, 5, 8, 12} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 7, 8} ∨
        polygon = {0, 3, 7, 8, 12} ∨
        polygon = {0, 3, 5, 8, 12} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 7, 8} ∨
        polygon = {0, 3, 4, 8, 12} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 7, 8} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 1, 7, 8, 12} ∨
        polygon = {0, 1, 5, 8, 12} ∨
        polygon = {0, 1, 5, 7, 12} ∨
        polygon = {0, 1, 5, 7, 8} ∨
        polygon = {0, 1, 4, 8, 12} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 7, 8} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 8} ∨
        polygon = {0, 1, 4, 5, 7} ∨
        polygon = {0, 1, 3, 8, 12} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 8} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 8} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 8} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 7, 8, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask04539] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask08635 :
    (({0, 1, 3, 4, 5, 7, 8, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 8, 13}, {3, 5, 7, 8, 13}, {3, 4, 7, 8, 13}, {3, 4, 5, 8, 13}, {3, 4, 5, 7, 13}, {3, 4, 5, 7, 8}, {1, 5, 7, 8, 13}, {1, 4, 7, 8, 13}, {1, 4, 5, 8, 13}, {1, 4, 5, 7, 13}, {1, 4, 5, 7, 8}, {1, 3, 7, 8, 13}, {1, 3, 5, 8, 13}, {1, 3, 5, 7, 13}, {1, 3, 5, 7, 8}, {1, 3, 4, 8, 13}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 8}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 8}, {1, 3, 4, 5, 7}, {0, 5, 7, 8, 13}, {0, 4, 7, 8, 13}, {0, 4, 5, 8, 13}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 8}, {0, 3, 7, 8, 13}, {0, 3, 5, 8, 13}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 8}, {0, 3, 4, 8, 13}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 8}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 8}, {0, 3, 4, 5, 7}, {0, 1, 7, 8, 13}, {0, 1, 5, 8, 13}, {0, 1, 5, 7, 13}, {0, 1, 5, 7, 8}, {0, 1, 4, 8, 13}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 8}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 8}, {0, 1, 4, 5, 7}, {0, 1, 3, 8, 13}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 8}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 8}, {0, 1, 3, 5, 7}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 8}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask08635 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 7, 8, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 8, 13} ∨
        polygon = {3, 5, 7, 8, 13} ∨
        polygon = {3, 4, 7, 8, 13} ∨
        polygon = {3, 4, 5, 8, 13} ∨
        polygon = {3, 4, 5, 7, 13} ∨
        polygon = {3, 4, 5, 7, 8} ∨
        polygon = {1, 5, 7, 8, 13} ∨
        polygon = {1, 4, 7, 8, 13} ∨
        polygon = {1, 4, 5, 8, 13} ∨
        polygon = {1, 4, 5, 7, 13} ∨
        polygon = {1, 4, 5, 7, 8} ∨
        polygon = {1, 3, 7, 8, 13} ∨
        polygon = {1, 3, 5, 8, 13} ∨
        polygon = {1, 3, 5, 7, 13} ∨
        polygon = {1, 3, 5, 7, 8} ∨
        polygon = {1, 3, 4, 8, 13} ∨
        polygon = {1, 3, 4, 7, 13} ∨
        polygon = {1, 3, 4, 7, 8} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 3, 4, 5, 8} ∨
        polygon = {1, 3, 4, 5, 7} ∨
        polygon = {0, 5, 7, 8, 13} ∨
        polygon = {0, 4, 7, 8, 13} ∨
        polygon = {0, 4, 5, 8, 13} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 4, 5, 7, 8} ∨
        polygon = {0, 3, 7, 8, 13} ∨
        polygon = {0, 3, 5, 8, 13} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 7, 8} ∨
        polygon = {0, 3, 4, 8, 13} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 8} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 1, 7, 8, 13} ∨
        polygon = {0, 1, 5, 8, 13} ∨
        polygon = {0, 1, 5, 7, 13} ∨
        polygon = {0, 1, 5, 7, 8} ∨
        polygon = {0, 1, 4, 8, 13} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 7, 8} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 8} ∨
        polygon = {0, 1, 4, 5, 7} ∨
        polygon = {0, 1, 3, 8, 13} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 8} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 8} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 8} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 7, 8, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask08635] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask16827 :
    (({0, 1, 3, 4, 5, 7, 8, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 8, 14}, {3, 5, 7, 8, 14}, {3, 4, 7, 8, 14}, {3, 4, 5, 8, 14}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 8}, {1, 5, 7, 8, 14}, {1, 4, 7, 8, 14}, {1, 4, 5, 8, 14}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 8}, {1, 3, 7, 8, 14}, {1, 3, 5, 8, 14}, {1, 3, 5, 7, 14}, {1, 3, 5, 7, 8}, {1, 3, 4, 8, 14}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 8}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 8}, {1, 3, 4, 5, 7}, {0, 5, 7, 8, 14}, {0, 4, 7, 8, 14}, {0, 4, 5, 8, 14}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 8}, {0, 3, 7, 8, 14}, {0, 3, 5, 8, 14}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 8}, {0, 3, 4, 8, 14}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 8}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 8}, {0, 3, 4, 5, 7}, {0, 1, 7, 8, 14}, {0, 1, 5, 8, 14}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 8}, {0, 1, 4, 8, 14}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 8}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 8}, {0, 1, 4, 5, 7}, {0, 1, 3, 8, 14}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 8}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 8}, {0, 1, 3, 5, 7}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 8}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask16827 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 7, 8, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 8, 14} ∨
        polygon = {3, 5, 7, 8, 14} ∨
        polygon = {3, 4, 7, 8, 14} ∨
        polygon = {3, 4, 5, 8, 14} ∨
        polygon = {3, 4, 5, 7, 14} ∨
        polygon = {3, 4, 5, 7, 8} ∨
        polygon = {1, 5, 7, 8, 14} ∨
        polygon = {1, 4, 7, 8, 14} ∨
        polygon = {1, 4, 5, 8, 14} ∨
        polygon = {1, 4, 5, 7, 14} ∨
        polygon = {1, 4, 5, 7, 8} ∨
        polygon = {1, 3, 7, 8, 14} ∨
        polygon = {1, 3, 5, 8, 14} ∨
        polygon = {1, 3, 5, 7, 14} ∨
        polygon = {1, 3, 5, 7, 8} ∨
        polygon = {1, 3, 4, 8, 14} ∨
        polygon = {1, 3, 4, 7, 14} ∨
        polygon = {1, 3, 4, 7, 8} ∨
        polygon = {1, 3, 4, 5, 14} ∨
        polygon = {1, 3, 4, 5, 8} ∨
        polygon = {1, 3, 4, 5, 7} ∨
        polygon = {0, 5, 7, 8, 14} ∨
        polygon = {0, 4, 7, 8, 14} ∨
        polygon = {0, 4, 5, 8, 14} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 7, 8} ∨
        polygon = {0, 3, 7, 8, 14} ∨
        polygon = {0, 3, 5, 8, 14} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 8} ∨
        polygon = {0, 3, 4, 8, 14} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 8} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 1, 7, 8, 14} ∨
        polygon = {0, 1, 5, 8, 14} ∨
        polygon = {0, 1, 5, 7, 14} ∨
        polygon = {0, 1, 5, 7, 8} ∨
        polygon = {0, 1, 4, 8, 14} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 8} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 8} ∨
        polygon = {0, 1, 4, 5, 7} ∨
        polygon = {0, 1, 3, 8, 14} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 8} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 8} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 8} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 7, 8, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask16827] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01723 :
    (({0, 1, 3, 4, 5, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 9, 10}, {3, 5, 7, 9, 10}, {3, 4, 7, 9, 10}, {3, 4, 5, 9, 10}, {3, 4, 5, 7, 10}, {3, 4, 5, 7, 9}, {1, 5, 7, 9, 10}, {1, 4, 7, 9, 10}, {1, 4, 5, 9, 10}, {1, 4, 5, 7, 10}, {1, 4, 5, 7, 9}, {1, 3, 7, 9, 10}, {1, 3, 5, 9, 10}, {1, 3, 5, 7, 10}, {1, 3, 5, 7, 9}, {1, 3, 4, 9, 10}, {1, 3, 4, 7, 10}, {1, 3, 4, 7, 9}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 9}, {1, 3, 4, 5, 7}, {0, 5, 7, 9, 10}, {0, 4, 7, 9, 10}, {0, 4, 5, 9, 10}, {0, 4, 5, 7, 10}, {0, 4, 5, 7, 9}, {0, 3, 7, 9, 10}, {0, 3, 5, 9, 10}, {0, 3, 5, 7, 10}, {0, 3, 5, 7, 9}, {0, 3, 4, 9, 10}, {0, 3, 4, 7, 10}, {0, 3, 4, 7, 9}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 7}, {0, 1, 7, 9, 10}, {0, 1, 5, 9, 10}, {0, 1, 5, 7, 10}, {0, 1, 5, 7, 9}, {0, 1, 4, 9, 10}, {0, 1, 4, 7, 10}, {0, 1, 4, 7, 9}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 7}, {0, 1, 3, 9, 10}, {0, 1, 3, 7, 10}, {0, 1, 3, 7, 9}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 7}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01723 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 7, 9, 10} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 9, 10} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {3, 4, 5, 7, 9} ∨
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
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {0, 4, 7, 9, 10} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 7} ∨
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
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01723] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask04795 :
    (({0, 1, 3, 4, 5, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 9, 12}, {3, 5, 7, 9, 12}, {3, 4, 7, 9, 12}, {3, 4, 5, 9, 12}, {3, 4, 5, 7, 12}, {3, 4, 5, 7, 9}, {1, 5, 7, 9, 12}, {1, 4, 7, 9, 12}, {1, 4, 5, 9, 12}, {1, 4, 5, 7, 12}, {1, 4, 5, 7, 9}, {1, 3, 7, 9, 12}, {1, 3, 5, 9, 12}, {1, 3, 5, 7, 12}, {1, 3, 5, 7, 9}, {1, 3, 4, 9, 12}, {1, 3, 4, 7, 12}, {1, 3, 4, 7, 9}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 9}, {1, 3, 4, 5, 7}, {0, 5, 7, 9, 12}, {0, 4, 7, 9, 12}, {0, 4, 5, 9, 12}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 9}, {0, 3, 7, 9, 12}, {0, 3, 5, 9, 12}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 9}, {0, 3, 4, 9, 12}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 9}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 7}, {0, 1, 7, 9, 12}, {0, 1, 5, 9, 12}, {0, 1, 5, 7, 12}, {0, 1, 5, 7, 9}, {0, 1, 4, 9, 12}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 9}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 7}, {0, 1, 3, 9, 12}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 9}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 7}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask04795 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 7, 9, 12} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 9, 12} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {3, 4, 5, 7, 9} ∨
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
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {0, 4, 7, 9, 12} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 7} ∨
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
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask04795] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask08891 :
    (({0, 1, 3, 4, 5, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 9, 13}, {3, 5, 7, 9, 13}, {3, 4, 7, 9, 13}, {3, 4, 5, 9, 13}, {3, 4, 5, 7, 13}, {3, 4, 5, 7, 9}, {1, 5, 7, 9, 13}, {1, 4, 7, 9, 13}, {1, 4, 5, 9, 13}, {1, 4, 5, 7, 13}, {1, 4, 5, 7, 9}, {1, 3, 7, 9, 13}, {1, 3, 5, 9, 13}, {1, 3, 5, 7, 13}, {1, 3, 5, 7, 9}, {1, 3, 4, 9, 13}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 9}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 9}, {1, 3, 4, 5, 7}, {0, 5, 7, 9, 13}, {0, 4, 7, 9, 13}, {0, 4, 5, 9, 13}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 9}, {0, 3, 7, 9, 13}, {0, 3, 5, 9, 13}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 9}, {0, 3, 4, 9, 13}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 9}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 7}, {0, 1, 7, 9, 13}, {0, 1, 5, 9, 13}, {0, 1, 5, 7, 13}, {0, 1, 5, 7, 9}, {0, 1, 4, 9, 13}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 9}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 7}, {0, 1, 3, 9, 13}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 9}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 7}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask08891 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 7, 9, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 9, 13} ∨
        polygon = {3, 5, 7, 9, 13} ∨
        polygon = {3, 4, 7, 9, 13} ∨
        polygon = {3, 4, 5, 9, 13} ∨
        polygon = {3, 4, 5, 7, 13} ∨
        polygon = {3, 4, 5, 7, 9} ∨
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
        polygon = {0, 5, 7, 9, 13} ∨
        polygon = {0, 4, 7, 9, 13} ∨
        polygon = {0, 4, 5, 9, 13} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 7} ∨
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
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask08891] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17083 :
    (({0, 1, 3, 4, 5, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 9, 14}, {3, 5, 7, 9, 14}, {3, 4, 7, 9, 14}, {3, 4, 5, 9, 14}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 9}, {1, 5, 7, 9, 14}, {1, 4, 7, 9, 14}, {1, 4, 5, 9, 14}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 9}, {1, 3, 7, 9, 14}, {1, 3, 5, 9, 14}, {1, 3, 5, 7, 14}, {1, 3, 5, 7, 9}, {1, 3, 4, 9, 14}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 9}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 9}, {1, 3, 4, 5, 7}, {0, 5, 7, 9, 14}, {0, 4, 7, 9, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 9}, {0, 3, 7, 9, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 9}, {0, 3, 4, 9, 14}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 9}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 7}, {0, 1, 7, 9, 14}, {0, 1, 5, 9, 14}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 9}, {0, 1, 4, 9, 14}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 9}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 7}, {0, 1, 3, 9, 14}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 9}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 7}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17083 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 7, 9, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 9, 14} ∨
        polygon = {3, 5, 7, 9, 14} ∨
        polygon = {3, 4, 7, 9, 14} ∨
        polygon = {3, 4, 5, 9, 14} ∨
        polygon = {3, 4, 5, 7, 14} ∨
        polygon = {3, 4, 5, 7, 9} ∨
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
        polygon = {0, 5, 7, 9, 14} ∨
        polygon = {0, 4, 7, 9, 14} ∨
        polygon = {0, 4, 5, 9, 14} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 7} ∨
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
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17083] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05307 :
    (({0, 1, 3, 4, 5, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 10, 12}, {3, 5, 7, 10, 12}, {3, 4, 7, 10, 12}, {3, 4, 5, 10, 12}, {3, 4, 5, 7, 12}, {3, 4, 5, 7, 10}, {1, 5, 7, 10, 12}, {1, 4, 7, 10, 12}, {1, 4, 5, 10, 12}, {1, 4, 5, 7, 12}, {1, 4, 5, 7, 10}, {1, 3, 7, 10, 12}, {1, 3, 5, 10, 12}, {1, 3, 5, 7, 12}, {1, 3, 5, 7, 10}, {1, 3, 4, 10, 12}, {1, 3, 4, 7, 12}, {1, 3, 4, 7, 10}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 7}, {0, 5, 7, 10, 12}, {0, 4, 7, 10, 12}, {0, 4, 5, 10, 12}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 10}, {0, 3, 7, 10, 12}, {0, 3, 5, 10, 12}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 10}, {0, 3, 4, 10, 12}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 10}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 7}, {0, 1, 7, 10, 12}, {0, 1, 5, 10, 12}, {0, 1, 5, 7, 12}, {0, 1, 5, 7, 10}, {0, 1, 4, 10, 12}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 10}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 7}, {0, 1, 3, 10, 12}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 10}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 7}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05307 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 7, 10, 12} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 10, 12} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {3, 4, 5, 7, 10} ∨
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
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 4, 7, 10, 12} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 7} ∨
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
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05307] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09403 :
    (({0, 1, 3, 4, 5, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 10, 13}, {3, 5, 7, 10, 13}, {3, 4, 7, 10, 13}, {3, 4, 5, 10, 13}, {3, 4, 5, 7, 13}, {3, 4, 5, 7, 10}, {1, 5, 7, 10, 13}, {1, 4, 7, 10, 13}, {1, 4, 5, 10, 13}, {1, 4, 5, 7, 13}, {1, 4, 5, 7, 10}, {1, 3, 7, 10, 13}, {1, 3, 5, 10, 13}, {1, 3, 5, 7, 13}, {1, 3, 5, 7, 10}, {1, 3, 4, 10, 13}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 10}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 7}, {0, 5, 7, 10, 13}, {0, 4, 7, 10, 13}, {0, 4, 5, 10, 13}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 10}, {0, 3, 7, 10, 13}, {0, 3, 5, 10, 13}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 10}, {0, 3, 4, 10, 13}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 10}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 7}, {0, 1, 7, 10, 13}, {0, 1, 5, 10, 13}, {0, 1, 5, 7, 13}, {0, 1, 5, 7, 10}, {0, 1, 4, 10, 13}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 10}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 7}, {0, 1, 3, 10, 13}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 10}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 7}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09403 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 7, 10, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 10, 13} ∨
        polygon = {3, 5, 7, 10, 13} ∨
        polygon = {3, 4, 7, 10, 13} ∨
        polygon = {3, 4, 5, 10, 13} ∨
        polygon = {3, 4, 5, 7, 13} ∨
        polygon = {3, 4, 5, 7, 10} ∨
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
        polygon = {0, 5, 7, 10, 13} ∨
        polygon = {0, 4, 7, 10, 13} ∨
        polygon = {0, 4, 5, 10, 13} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 7} ∨
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
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09403] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17595 :
    (({0, 1, 3, 4, 5, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 10, 14}, {3, 5, 7, 10, 14}, {3, 4, 7, 10, 14}, {3, 4, 5, 10, 14}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 10}, {1, 5, 7, 10, 14}, {1, 4, 7, 10, 14}, {1, 4, 5, 10, 14}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 10}, {1, 3, 7, 10, 14}, {1, 3, 5, 10, 14}, {1, 3, 5, 7, 14}, {1, 3, 5, 7, 10}, {1, 3, 4, 10, 14}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 10}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 7}, {0, 5, 7, 10, 14}, {0, 4, 7, 10, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 10}, {0, 3, 7, 10, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 10}, {0, 3, 4, 10, 14}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 10}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 7}, {0, 1, 7, 10, 14}, {0, 1, 5, 10, 14}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 10}, {0, 1, 4, 10, 14}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 10}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 7}, {0, 1, 3, 10, 14}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 10}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 7}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17595 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 7, 10, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 10, 14} ∨
        polygon = {3, 5, 7, 10, 14} ∨
        polygon = {3, 4, 7, 10, 14} ∨
        polygon = {3, 4, 5, 10, 14} ∨
        polygon = {3, 4, 5, 7, 14} ∨
        polygon = {3, 4, 5, 7, 10} ∨
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
        polygon = {0, 5, 7, 10, 14} ∨
        polygon = {0, 4, 7, 10, 14} ∨
        polygon = {0, 4, 5, 10, 14} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 7} ∨
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
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17595] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12475 :
    (({0, 1, 3, 4, 5, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 12, 13}, {3, 5, 7, 12, 13}, {3, 4, 7, 12, 13}, {3, 4, 5, 12, 13}, {3, 4, 5, 7, 13}, {3, 4, 5, 7, 12}, {1, 5, 7, 12, 13}, {1, 4, 7, 12, 13}, {1, 4, 5, 12, 13}, {1, 4, 5, 7, 13}, {1, 4, 5, 7, 12}, {1, 3, 7, 12, 13}, {1, 3, 5, 12, 13}, {1, 3, 5, 7, 13}, {1, 3, 5, 7, 12}, {1, 3, 4, 12, 13}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 12}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 7}, {0, 5, 7, 12, 13}, {0, 4, 7, 12, 13}, {0, 4, 5, 12, 13}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 12}, {0, 3, 7, 12, 13}, {0, 3, 5, 12, 13}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 12}, {0, 3, 4, 12, 13}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 12}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 7}, {0, 1, 7, 12, 13}, {0, 1, 5, 12, 13}, {0, 1, 5, 7, 13}, {0, 1, 5, 7, 12}, {0, 1, 4, 12, 13}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 12}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 7}, {0, 1, 3, 12, 13}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 12}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 7}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12475 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 7, 12, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 12, 13} ∨
        polygon = {3, 5, 7, 12, 13} ∨
        polygon = {3, 4, 7, 12, 13} ∨
        polygon = {3, 4, 5, 12, 13} ∨
        polygon = {3, 4, 5, 7, 13} ∨
        polygon = {3, 4, 5, 7, 12} ∨
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
        polygon = {0, 5, 7, 12, 13} ∨
        polygon = {0, 4, 7, 12, 13} ∨
        polygon = {0, 4, 5, 12, 13} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 3, 7, 12, 13} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 7} ∨
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
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12475] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask20667 :
    (({0, 1, 3, 4, 5, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 12, 14}, {3, 5, 7, 12, 14}, {3, 4, 7, 12, 14}, {3, 4, 5, 12, 14}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 12}, {1, 5, 7, 12, 14}, {1, 4, 7, 12, 14}, {1, 4, 5, 12, 14}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 12}, {1, 3, 7, 12, 14}, {1, 3, 5, 12, 14}, {1, 3, 5, 7, 14}, {1, 3, 5, 7, 12}, {1, 3, 4, 12, 14}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 12}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 7}, {0, 5, 7, 12, 14}, {0, 4, 7, 12, 14}, {0, 4, 5, 12, 14}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 12}, {0, 3, 7, 12, 14}, {0, 3, 5, 12, 14}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 12}, {0, 3, 4, 12, 14}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 12}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 7}, {0, 1, 7, 12, 14}, {0, 1, 5, 12, 14}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 12}, {0, 1, 4, 12, 14}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 12}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 7}, {0, 1, 3, 12, 14}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 12}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 7}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask20667 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 7, 12, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 12, 14} ∨
        polygon = {3, 5, 7, 12, 14} ∨
        polygon = {3, 4, 7, 12, 14} ∨
        polygon = {3, 4, 5, 12, 14} ∨
        polygon = {3, 4, 5, 7, 14} ∨
        polygon = {3, 4, 5, 7, 12} ∨
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
        polygon = {0, 5, 7, 12, 14} ∨
        polygon = {0, 4, 7, 12, 14} ∨
        polygon = {0, 4, 5, 12, 14} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 7} ∨
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
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask20667] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask24763 :
    (({0, 1, 3, 4, 5, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 13, 14}, {3, 5, 7, 13, 14}, {3, 4, 7, 13, 14}, {3, 4, 5, 13, 14}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 13}, {1, 5, 7, 13, 14}, {1, 4, 7, 13, 14}, {1, 4, 5, 13, 14}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 13}, {1, 3, 7, 13, 14}, {1, 3, 5, 13, 14}, {1, 3, 5, 7, 14}, {1, 3, 5, 7, 13}, {1, 3, 4, 13, 14}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 13}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 7}, {0, 5, 7, 13, 14}, {0, 4, 7, 13, 14}, {0, 4, 5, 13, 14}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 13}, {0, 3, 7, 13, 14}, {0, 3, 5, 13, 14}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 13}, {0, 3, 4, 13, 14}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 13}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 7}, {0, 1, 7, 13, 14}, {0, 1, 5, 13, 14}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 13}, {0, 1, 4, 13, 14}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 13}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 7}, {0, 1, 3, 13, 14}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 13}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 7}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask24763 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 7, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 13, 14} ∨
        polygon = {3, 5, 7, 13, 14} ∨
        polygon = {3, 4, 7, 13, 14} ∨
        polygon = {3, 4, 5, 13, 14} ∨
        polygon = {3, 4, 5, 7, 14} ∨
        polygon = {3, 4, 5, 7, 13} ∨
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
        polygon = {0, 5, 7, 13, 14} ∨
        polygon = {0, 4, 7, 13, 14} ∨
        polygon = {0, 4, 5, 13, 14} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 3, 7, 13, 14} ∨
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 7} ∨
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
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask24763] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01851 :
    (({0, 1, 3, 4, 5, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 8, 9, 10}, {3, 5, 8, 9, 10}, {3, 4, 8, 9, 10}, {3, 4, 5, 9, 10}, {3, 4, 5, 8, 10}, {3, 4, 5, 8, 9}, {1, 5, 8, 9, 10}, {1, 4, 8, 9, 10}, {1, 4, 5, 9, 10}, {1, 4, 5, 8, 10}, {1, 4, 5, 8, 9}, {1, 3, 8, 9, 10}, {1, 3, 5, 9, 10}, {1, 3, 5, 8, 10}, {1, 3, 5, 8, 9}, {1, 3, 4, 9, 10}, {1, 3, 4, 8, 10}, {1, 3, 4, 8, 9}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 9}, {1, 3, 4, 5, 8}, {0, 5, 8, 9, 10}, {0, 4, 8, 9, 10}, {0, 4, 5, 9, 10}, {0, 4, 5, 8, 10}, {0, 4, 5, 8, 9}, {0, 3, 8, 9, 10}, {0, 3, 5, 9, 10}, {0, 3, 5, 8, 10}, {0, 3, 5, 8, 9}, {0, 3, 4, 9, 10}, {0, 3, 4, 8, 10}, {0, 3, 4, 8, 9}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 8}, {0, 1, 8, 9, 10}, {0, 1, 5, 9, 10}, {0, 1, 5, 8, 10}, {0, 1, 5, 8, 9}, {0, 1, 4, 9, 10}, {0, 1, 4, 8, 10}, {0, 1, 4, 8, 9}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 8}, {0, 1, 3, 9, 10}, {0, 1, 3, 8, 10}, {0, 1, 3, 8, 9}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 8}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 8}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01851 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {4, 5, 8, 9, 10} ∨
        polygon = {3, 5, 8, 9, 10} ∨
        polygon = {3, 4, 8, 9, 10} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {3, 4, 5, 8, 10} ∨
        polygon = {3, 4, 5, 8, 9} ∨
        polygon = {1, 5, 8, 9, 10} ∨
        polygon = {1, 4, 8, 9, 10} ∨
        polygon = {1, 4, 5, 9, 10} ∨
        polygon = {1, 4, 5, 8, 10} ∨
        polygon = {1, 4, 5, 8, 9} ∨
        polygon = {1, 3, 8, 9, 10} ∨
        polygon = {1, 3, 5, 9, 10} ∨
        polygon = {1, 3, 5, 8, 10} ∨
        polygon = {1, 3, 5, 8, 9} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {1, 3, 4, 8, 10} ∨
        polygon = {1, 3, 4, 8, 9} ∨
        polygon = {1, 3, 4, 5, 10} ∨
        polygon = {1, 3, 4, 5, 9} ∨
        polygon = {1, 3, 4, 5, 8} ∨
        polygon = {0, 5, 8, 9, 10} ∨
        polygon = {0, 4, 8, 9, 10} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 3, 5, 8, 9} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 8, 10} ∨
        polygon = {0, 3, 4, 8, 9} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 1, 8, 9, 10} ∨
        polygon = {0, 1, 5, 9, 10} ∨
        polygon = {0, 1, 5, 8, 10} ∨
        polygon = {0, 1, 5, 8, 9} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 4, 8, 10} ∨
        polygon = {0, 1, 4, 8, 9} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 4, 5, 8} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 8, 10} ∨
        polygon = {0, 1, 3, 8, 9} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 8} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 8} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01851] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

end ErdosSzekeres

end
