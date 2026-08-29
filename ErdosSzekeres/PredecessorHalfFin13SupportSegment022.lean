module

public import ErdosSzekeres.PredecessorHalfFin13Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 022. -/

theorem predecessorHalfFin13_fiveSubset_mask6049 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 5, 7, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 5, 7, 8, 9} ∨
        polygon = {0, 5, 7, 8, 10} ∨
        polygon = {0, 5, 7, 8, 12} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 5, 8, 9, 10} ∨
        polygon = {0, 5, 8, 9, 12} ∨
        polygon = {0, 5, 8, 10, 12} ∨
        polygon = {0, 5, 9, 10, 12} ∨
        polygon = {0, 7, 8, 9, 10} ∨
        polygon = {0, 7, 8, 9, 12} ∨
        polygon = {0, 7, 8, 10, 12} ∨
        polygon = {0, 7, 9, 10, 12} ∨
        polygon = {0, 8, 9, 10, 12} ∨
        polygon = {5, 7, 8, 9, 10} ∨
        polygon = {5, 7, 8, 9, 12} ∨
        polygon = {5, 7, 8, 10, 12} ∨
        polygon = {5, 7, 9, 10, 12} ∨
        polygon = {5, 8, 9, 10, 12} ∨
        polygon = {7, 8, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 5, 7, 8, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 5, 7, 8, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 5, 7, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 5, 7, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 5, 7, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 5, 7, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 5, 7, 8, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 5, 7, 8, 9, 10, 12} \ ({0, 5, 7, 8, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 5, 7, 8, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask6081 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 6, 7, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 6, 7, 8, 9} ∨
        polygon = {0, 6, 7, 8, 10} ∨
        polygon = {0, 6, 7, 8, 12} ∨
        polygon = {0, 6, 7, 9, 10} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {0, 6, 8, 9, 10} ∨
        polygon = {0, 6, 8, 9, 12} ∨
        polygon = {0, 6, 8, 10, 12} ∨
        polygon = {0, 6, 9, 10, 12} ∨
        polygon = {0, 7, 8, 9, 10} ∨
        polygon = {0, 7, 8, 9, 12} ∨
        polygon = {0, 7, 8, 10, 12} ∨
        polygon = {0, 7, 9, 10, 12} ∨
        polygon = {0, 8, 9, 10, 12} ∨
        polygon = {6, 7, 8, 9, 10} ∨
        polygon = {6, 7, 8, 9, 12} ∨
        polygon = {6, 7, 8, 10, 12} ∨
        polygon = {6, 7, 9, 10, 12} ∨
        polygon = {6, 8, 9, 10, 12} ∨
        polygon = {7, 8, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 6, 7, 8, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 6, 7, 8, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 6, 7, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 6, 7, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 6, 7, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 6, 7, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 6, 7, 8, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 6, 7, 8, 9, 10, 12} \ ({0, 6, 7, 8, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 6, 7, 8, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask0508 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 5, 6, 7, 8} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {2, 3, 4, 5, 8} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {2, 3, 4, 6, 8} ∨
        polygon = {2, 3, 4, 7, 8} ∨
        polygon = {2, 3, 5, 6, 7} ∨
        polygon = {2, 3, 5, 6, 8} ∨
        polygon = {2, 3, 5, 7, 8} ∨
        polygon = {2, 3, 6, 7, 8} ∨
        polygon = {2, 4, 5, 6, 7} ∨
        polygon = {2, 4, 5, 6, 8} ∨
        polygon = {2, 4, 5, 7, 8} ∨
        polygon = {2, 4, 6, 7, 8} ∨
        polygon = {2, 5, 6, 7, 8} ∨
        polygon = {3, 4, 5, 6, 7} ∨
        polygon = {3, 4, 5, 6, 8} ∨
        polygon = {3, 4, 5, 7, 8} ∨
        polygon = {3, 4, 6, 7, 8} ∨
        polygon = {3, 5, 6, 7, 8} ∨
        polygon = {4, 5, 6, 7, 8} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 5, 6, 7, 8} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 5, 6, 7, 8} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 5, 6, 7, 8} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 5, 6, 7, 8} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 5, 6, 7, 8} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 5, 6, 7, 8} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 5, 6, 7, 8} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 5, 6, 7, 8} \ ({2, 3, 4, 5, 6, 7, 8} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 5, 6, 7, 8} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask0764 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 5, 6, 7, 9} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 5, 6, 7} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {2, 4, 5, 6, 7} ∨
        polygon = {2, 4, 5, 6, 9} ∨
        polygon = {2, 4, 5, 7, 9} ∨
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {2, 5, 6, 7, 9} ∨
        polygon = {3, 4, 5, 6, 7} ∨
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {4, 5, 6, 7, 9} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 5, 6, 7, 9} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 5, 6, 7, 9} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 5, 6, 7, 9} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 5, 6, 7, 9} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 5, 6, 7, 9} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 5, 6, 7, 9} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 5, 6, 7, 9} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 5, 6, 7, 9} \ ({2, 3, 4, 5, 6, 7, 9} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 5, 6, 7, 9} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1276 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 5, 6, 7, 10} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 5, 6, 7} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {2, 4, 5, 6, 7} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {2, 5, 6, 7, 10} ∨
        polygon = {3, 4, 5, 6, 7} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {4, 5, 6, 7, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 5, 6, 7, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 5, 6, 7, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 5, 6, 7, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 5, 6, 7, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 5, 6, 7, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 5, 6, 7, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 5, 6, 7, 10} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 5, 6, 7, 10} \ ({2, 3, 4, 5, 6, 7, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 5, 6, 7, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask2300 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 5, 6, 7, 11} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {2, 3, 4, 5, 11} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {2, 3, 4, 6, 11} ∨
        polygon = {2, 3, 4, 7, 11} ∨
        polygon = {2, 3, 5, 6, 7} ∨
        polygon = {2, 3, 5, 6, 11} ∨
        polygon = {2, 3, 5, 7, 11} ∨
        polygon = {2, 3, 6, 7, 11} ∨
        polygon = {2, 4, 5, 6, 7} ∨
        polygon = {2, 4, 5, 6, 11} ∨
        polygon = {2, 4, 5, 7, 11} ∨
        polygon = {2, 4, 6, 7, 11} ∨
        polygon = {2, 5, 6, 7, 11} ∨
        polygon = {3, 4, 5, 6, 7} ∨
        polygon = {3, 4, 5, 6, 11} ∨
        polygon = {3, 4, 5, 7, 11} ∨
        polygon = {3, 4, 6, 7, 11} ∨
        polygon = {3, 5, 6, 7, 11} ∨
        polygon = {4, 5, 6, 7, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 5, 6, 7, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 5, 6, 7, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 5, 6, 7, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 5, 6, 7, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 5, 6, 7, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 5, 6, 7, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 5, 6, 7, 11} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 5, 6, 7, 11} \ ({2, 3, 4, 5, 6, 7, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 5, 6, 7, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4348 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 5, 6, 7, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 5, 6, 7} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 6, 7, 12} ∨
        polygon = {2, 4, 5, 6, 7} ∨
        polygon = {2, 4, 5, 6, 12} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {2, 4, 6, 7, 12} ∨
        polygon = {2, 5, 6, 7, 12} ∨
        polygon = {3, 4, 5, 6, 7} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {4, 5, 6, 7, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 5, 6, 7, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 5, 6, 7, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 5, 6, 7, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 5, 6, 7, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 5, 6, 7, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 5, 6, 7, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 5, 6, 7, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 5, 6, 7, 12} \ ({2, 3, 4, 5, 6, 7, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 5, 6, 7, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask0892 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 5, 6, 8, 9} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {2, 3, 4, 5, 8} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 6, 8} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 8, 9} ∨
        polygon = {2, 3, 5, 6, 8} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {2, 3, 5, 8, 9} ∨
        polygon = {2, 3, 6, 8, 9} ∨
        polygon = {2, 4, 5, 6, 8} ∨
        polygon = {2, 4, 5, 6, 9} ∨
        polygon = {2, 4, 5, 8, 9} ∨
        polygon = {2, 4, 6, 8, 9} ∨
        polygon = {2, 5, 6, 8, 9} ∨
        polygon = {3, 4, 5, 6, 8} ∨
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {3, 4, 5, 8, 9} ∨
        polygon = {3, 4, 6, 8, 9} ∨
        polygon = {3, 5, 6, 8, 9} ∨
        polygon = {4, 5, 6, 8, 9} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 5, 6, 8, 9} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 5, 6, 8, 9} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 5, 6, 8, 9} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 5, 6, 8, 9} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 5, 6, 8, 9} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 5, 6, 8, 9} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 5, 6, 8, 9} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 5, 6, 8, 9} \ ({2, 3, 4, 5, 6, 8, 9} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 5, 6, 8, 9} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1404 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 5, 6, 8, 10} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {2, 3, 4, 5, 8} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 6, 8} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 8, 10} ∨
        polygon = {2, 3, 5, 6, 8} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {2, 3, 5, 8, 10} ∨
        polygon = {2, 3, 6, 8, 10} ∨
        polygon = {2, 4, 5, 6, 8} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {2, 4, 5, 8, 10} ∨
        polygon = {2, 4, 6, 8, 10} ∨
        polygon = {2, 5, 6, 8, 10} ∨
        polygon = {3, 4, 5, 6, 8} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {3, 4, 5, 8, 10} ∨
        polygon = {3, 4, 6, 8, 10} ∨
        polygon = {3, 5, 6, 8, 10} ∨
        polygon = {4, 5, 6, 8, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 5, 6, 8, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 5, 6, 8, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 5, 6, 8, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 5, 6, 8, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 5, 6, 8, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 5, 6, 8, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 5, 6, 8, 10} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 5, 6, 8, 10} \ ({2, 3, 4, 5, 6, 8, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 5, 6, 8, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask2428 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 5, 6, 8, 11} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {2, 3, 4, 5, 8} ∨
        polygon = {2, 3, 4, 5, 11} ∨
        polygon = {2, 3, 4, 6, 8} ∨
        polygon = {2, 3, 4, 6, 11} ∨
        polygon = {2, 3, 4, 8, 11} ∨
        polygon = {2, 3, 5, 6, 8} ∨
        polygon = {2, 3, 5, 6, 11} ∨
        polygon = {2, 3, 5, 8, 11} ∨
        polygon = {2, 3, 6, 8, 11} ∨
        polygon = {2, 4, 5, 6, 8} ∨
        polygon = {2, 4, 5, 6, 11} ∨
        polygon = {2, 4, 5, 8, 11} ∨
        polygon = {2, 4, 6, 8, 11} ∨
        polygon = {2, 5, 6, 8, 11} ∨
        polygon = {3, 4, 5, 6, 8} ∨
        polygon = {3, 4, 5, 6, 11} ∨
        polygon = {3, 4, 5, 8, 11} ∨
        polygon = {3, 4, 6, 8, 11} ∨
        polygon = {3, 5, 6, 8, 11} ∨
        polygon = {4, 5, 6, 8, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 5, 6, 8, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 5, 6, 8, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 5, 6, 8, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 5, 6, 8, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 5, 6, 8, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 5, 6, 8, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 5, 6, 8, 11} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 5, 6, 8, 11} \ ({2, 3, 4, 5, 6, 8, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 5, 6, 8, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4476 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 5, 6, 8, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {2, 3, 4, 5, 8} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 6, 8} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 8, 12} ∨
        polygon = {2, 3, 5, 6, 8} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {2, 3, 5, 8, 12} ∨
        polygon = {2, 3, 6, 8, 12} ∨
        polygon = {2, 4, 5, 6, 8} ∨
        polygon = {2, 4, 5, 6, 12} ∨
        polygon = {2, 4, 5, 8, 12} ∨
        polygon = {2, 4, 6, 8, 12} ∨
        polygon = {2, 5, 6, 8, 12} ∨
        polygon = {3, 4, 5, 6, 8} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {3, 4, 5, 8, 12} ∨
        polygon = {3, 4, 6, 8, 12} ∨
        polygon = {3, 5, 6, 8, 12} ∨
        polygon = {4, 5, 6, 8, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 5, 6, 8, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 5, 6, 8, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 5, 6, 8, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 5, 6, 8, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 5, 6, 8, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 5, 6, 8, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 5, 6, 8, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 5, 6, 8, 12} \ ({2, 3, 4, 5, 6, 8, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 5, 6, 8, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1660 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 5, 6, 9, 10} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {2, 4, 5, 6, 9} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {2, 5, 6, 9, 10} ∨
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {4, 5, 6, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 5, 6, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 5, 6, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 5, 6, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 5, 6, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 5, 6, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 5, 6, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 5, 6, 9, 10} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 5, 6, 9, 10} \ ({2, 3, 4, 5, 6, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 5, 6, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask2684 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 5, 6, 9, 11} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 11} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 6, 11} ∨
        polygon = {2, 3, 4, 9, 11} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {2, 3, 5, 6, 11} ∨
        polygon = {2, 3, 5, 9, 11} ∨
        polygon = {2, 3, 6, 9, 11} ∨
        polygon = {2, 4, 5, 6, 9} ∨
        polygon = {2, 4, 5, 6, 11} ∨
        polygon = {2, 4, 5, 9, 11} ∨
        polygon = {2, 4, 6, 9, 11} ∨
        polygon = {2, 5, 6, 9, 11} ∨
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {3, 4, 5, 6, 11} ∨
        polygon = {3, 4, 5, 9, 11} ∨
        polygon = {3, 4, 6, 9, 11} ∨
        polygon = {3, 5, 6, 9, 11} ∨
        polygon = {4, 5, 6, 9, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 5, 6, 9, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 5, 6, 9, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 5, 6, 9, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 5, 6, 9, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 5, 6, 9, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 5, 6, 9, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 5, 6, 9, 11} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 5, 6, 9, 11} \ ({2, 3, 4, 5, 6, 9, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 5, 6, 9, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4732 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 5, 6, 9, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 6, 9, 12} ∨
        polygon = {2, 4, 5, 6, 9} ∨
        polygon = {2, 4, 5, 6, 12} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {2, 4, 6, 9, 12} ∨
        polygon = {2, 5, 6, 9, 12} ∨
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {4, 5, 6, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 5, 6, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 5, 6, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 5, 6, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 5, 6, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 5, 6, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 5, 6, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 5, 6, 9, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 5, 6, 9, 12} \ ({2, 3, 4, 5, 6, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 5, 6, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3196 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 5, 6, 10, 11} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 11} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 6, 11} ∨
        polygon = {2, 3, 4, 10, 11} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {2, 3, 5, 6, 11} ∨
        polygon = {2, 3, 5, 10, 11} ∨
        polygon = {2, 3, 6, 10, 11} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {2, 4, 5, 6, 11} ∨
        polygon = {2, 4, 5, 10, 11} ∨
        polygon = {2, 4, 6, 10, 11} ∨
        polygon = {2, 5, 6, 10, 11} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {3, 4, 5, 6, 11} ∨
        polygon = {3, 4, 5, 10, 11} ∨
        polygon = {3, 4, 6, 10, 11} ∨
        polygon = {3, 5, 6, 10, 11} ∨
        polygon = {4, 5, 6, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 5, 6, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 5, 6, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 5, 6, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 5, 6, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 5, 6, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 5, 6, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 5, 6, 10, 11} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 5, 6, 10, 11} \ ({2, 3, 4, 5, 6, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 5, 6, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5244 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 5, 6, 10, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 6, 10, 12} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {2, 4, 5, 6, 12} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {2, 4, 6, 10, 12} ∨
        polygon = {2, 5, 6, 10, 12} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {4, 5, 6, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 5, 6, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 5, 6, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 5, 6, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 5, 6, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 5, 6, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 5, 6, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 5, 6, 10, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 5, 6, 10, 12} \ ({2, 3, 4, 5, 6, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 5, 6, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask6268 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 5, 6, 11, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {2, 3, 4, 5, 11} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 6, 11} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 11, 12} ∨
        polygon = {2, 3, 5, 6, 11} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {2, 3, 5, 11, 12} ∨
        polygon = {2, 3, 6, 11, 12} ∨
        polygon = {2, 4, 5, 6, 11} ∨
        polygon = {2, 4, 5, 6, 12} ∨
        polygon = {2, 4, 5, 11, 12} ∨
        polygon = {2, 4, 6, 11, 12} ∨
        polygon = {2, 5, 6, 11, 12} ∨
        polygon = {3, 4, 5, 6, 11} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {3, 4, 5, 11, 12} ∨
        polygon = {3, 4, 6, 11, 12} ∨
        polygon = {3, 5, 6, 11, 12} ∨
        polygon = {4, 5, 6, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 5, 6, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 5, 6, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 5, 6, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 5, 6, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 5, 6, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 5, 6, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 5, 6, 11, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 5, 6, 11, 12} \ ({2, 3, 4, 5, 6, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 5, 6, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask0956 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 5, 7, 8, 9} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {2, 3, 4, 5, 8} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 7, 8} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 8, 9} ∨
        polygon = {2, 3, 5, 7, 8} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {2, 3, 5, 8, 9} ∨
        polygon = {2, 3, 7, 8, 9} ∨
        polygon = {2, 4, 5, 7, 8} ∨
        polygon = {2, 4, 5, 7, 9} ∨
        polygon = {2, 4, 5, 8, 9} ∨
        polygon = {2, 4, 7, 8, 9} ∨
        polygon = {2, 5, 7, 8, 9} ∨
        polygon = {3, 4, 5, 7, 8} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {3, 4, 5, 8, 9} ∨
        polygon = {3, 4, 7, 8, 9} ∨
        polygon = {3, 5, 7, 8, 9} ∨
        polygon = {4, 5, 7, 8, 9} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 5, 7, 8, 9} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 5, 7, 8, 9} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 5, 7, 8, 9} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 5, 7, 8, 9} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 5, 7, 8, 9} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 5, 7, 8, 9} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 5, 7, 8, 9} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 5, 7, 8, 9} \ ({2, 3, 4, 5, 7, 8, 9} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 5, 7, 8, 9} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1468 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 5, 7, 8, 10} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {2, 3, 4, 5, 8} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 7, 8} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 8, 10} ∨
        polygon = {2, 3, 5, 7, 8} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 5, 8, 10} ∨
        polygon = {2, 3, 7, 8, 10} ∨
        polygon = {2, 4, 5, 7, 8} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {2, 4, 5, 8, 10} ∨
        polygon = {2, 4, 7, 8, 10} ∨
        polygon = {2, 5, 7, 8, 10} ∨
        polygon = {3, 4, 5, 7, 8} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {3, 4, 5, 8, 10} ∨
        polygon = {3, 4, 7, 8, 10} ∨
        polygon = {3, 5, 7, 8, 10} ∨
        polygon = {4, 5, 7, 8, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 5, 7, 8, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 5, 7, 8, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 5, 7, 8, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 5, 7, 8, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 5, 7, 8, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 5, 7, 8, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 5, 7, 8, 10} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 5, 7, 8, 10} \ ({2, 3, 4, 5, 7, 8, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 5, 7, 8, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask2492 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 5, 7, 8, 11} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {2, 3, 4, 5, 8} ∨
        polygon = {2, 3, 4, 5, 11} ∨
        polygon = {2, 3, 4, 7, 8} ∨
        polygon = {2, 3, 4, 7, 11} ∨
        polygon = {2, 3, 4, 8, 11} ∨
        polygon = {2, 3, 5, 7, 8} ∨
        polygon = {2, 3, 5, 7, 11} ∨
        polygon = {2, 3, 5, 8, 11} ∨
        polygon = {2, 3, 7, 8, 11} ∨
        polygon = {2, 4, 5, 7, 8} ∨
        polygon = {2, 4, 5, 7, 11} ∨
        polygon = {2, 4, 5, 8, 11} ∨
        polygon = {2, 4, 7, 8, 11} ∨
        polygon = {2, 5, 7, 8, 11} ∨
        polygon = {3, 4, 5, 7, 8} ∨
        polygon = {3, 4, 5, 7, 11} ∨
        polygon = {3, 4, 5, 8, 11} ∨
        polygon = {3, 4, 7, 8, 11} ∨
        polygon = {3, 5, 7, 8, 11} ∨
        polygon = {4, 5, 7, 8, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 5, 7, 8, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 5, 7, 8, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 5, 7, 8, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 5, 7, 8, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 5, 7, 8, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 5, 7, 8, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 5, 7, 8, 11} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 5, 7, 8, 11} \ ({2, 3, 4, 5, 7, 8, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 5, 7, 8, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4540 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 5, 7, 8, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {2, 3, 4, 5, 8} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 7, 8} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 8, 12} ∨
        polygon = {2, 3, 5, 7, 8} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 5, 8, 12} ∨
        polygon = {2, 3, 7, 8, 12} ∨
        polygon = {2, 4, 5, 7, 8} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {2, 4, 5, 8, 12} ∨
        polygon = {2, 4, 7, 8, 12} ∨
        polygon = {2, 5, 7, 8, 12} ∨
        polygon = {3, 4, 5, 7, 8} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {3, 4, 5, 8, 12} ∨
        polygon = {3, 4, 7, 8, 12} ∨
        polygon = {3, 5, 7, 8, 12} ∨
        polygon = {4, 5, 7, 8, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 5, 7, 8, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 5, 7, 8, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 5, 7, 8, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 5, 7, 8, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 5, 7, 8, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 5, 7, 8, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 5, 7, 8, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 5, 7, 8, 12} \ ({2, 3, 4, 5, 7, 8, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 5, 7, 8, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1724 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 5, 7, 9, 10} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 4, 5, 7, 9} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {4, 5, 7, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 5, 7, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 5, 7, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 5, 7, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 5, 7, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 5, 7, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 5, 7, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 5, 7, 9, 10} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 5, 7, 9, 10} \ ({2, 3, 4, 5, 7, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 5, 7, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask2748 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 5, 7, 9, 11} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 11} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 7, 11} ∨
        polygon = {2, 3, 4, 9, 11} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {2, 3, 5, 7, 11} ∨
        polygon = {2, 3, 5, 9, 11} ∨
        polygon = {2, 3, 7, 9, 11} ∨
        polygon = {2, 4, 5, 7, 9} ∨
        polygon = {2, 4, 5, 7, 11} ∨
        polygon = {2, 4, 5, 9, 11} ∨
        polygon = {2, 4, 7, 9, 11} ∨
        polygon = {2, 5, 7, 9, 11} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {3, 4, 5, 7, 11} ∨
        polygon = {3, 4, 5, 9, 11} ∨
        polygon = {3, 4, 7, 9, 11} ∨
        polygon = {3, 5, 7, 9, 11} ∨
        polygon = {4, 5, 7, 9, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 5, 7, 9, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 5, 7, 9, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 5, 7, 9, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 5, 7, 9, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 5, 7, 9, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 5, 7, 9, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 5, 7, 9, 11} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 5, 7, 9, 11} \ ({2, 3, 4, 5, 7, 9, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 5, 7, 9, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4796 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 5, 7, 9, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 4, 5, 7, 9} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {2, 4, 7, 9, 12} ∨
        polygon = {2, 5, 7, 9, 12} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {4, 5, 7, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 5, 7, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 5, 7, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 5, 7, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 5, 7, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 5, 7, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 5, 7, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 5, 7, 9, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 5, 7, 9, 12} \ ({2, 3, 4, 5, 7, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 5, 7, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3260 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 5, 7, 10, 11} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 11} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 7, 11} ∨
        polygon = {2, 3, 4, 10, 11} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 5, 7, 11} ∨
        polygon = {2, 3, 5, 10, 11} ∨
        polygon = {2, 3, 7, 10, 11} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {2, 4, 5, 7, 11} ∨
        polygon = {2, 4, 5, 10, 11} ∨
        polygon = {2, 4, 7, 10, 11} ∨
        polygon = {2, 5, 7, 10, 11} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {3, 4, 5, 7, 11} ∨
        polygon = {3, 4, 5, 10, 11} ∨
        polygon = {3, 4, 7, 10, 11} ∨
        polygon = {3, 5, 7, 10, 11} ∨
        polygon = {4, 5, 7, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 5, 7, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 5, 7, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 5, 7, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 5, 7, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 5, 7, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 5, 7, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 5, 7, 10, 11} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 5, 7, 10, 11} \ ({2, 3, 4, 5, 7, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 5, 7, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5308 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 5, 7, 10, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {2, 4, 7, 10, 12} ∨
        polygon = {2, 5, 7, 10, 12} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {4, 5, 7, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 5, 7, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 5, 7, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 5, 7, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 5, 7, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 5, 7, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 5, 7, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 5, 7, 10, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 5, 7, 10, 12} \ ({2, 3, 4, 5, 7, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 5, 7, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask6332 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 5, 7, 11, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {2, 3, 4, 5, 11} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 7, 11} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 11, 12} ∨
        polygon = {2, 3, 5, 7, 11} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 5, 11, 12} ∨
        polygon = {2, 3, 7, 11, 12} ∨
        polygon = {2, 4, 5, 7, 11} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {2, 4, 5, 11, 12} ∨
        polygon = {2, 4, 7, 11, 12} ∨
        polygon = {2, 5, 7, 11, 12} ∨
        polygon = {3, 4, 5, 7, 11} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {3, 4, 5, 11, 12} ∨
        polygon = {3, 4, 7, 11, 12} ∨
        polygon = {3, 5, 7, 11, 12} ∨
        polygon = {4, 5, 7, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 5, 7, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 5, 7, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 5, 7, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 5, 7, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 5, 7, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 5, 7, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 5, 7, 11, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 5, 7, 11, 12} \ ({2, 3, 4, 5, 7, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 5, 7, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1852 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 5, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 5, 8} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 8, 9} ∨
        polygon = {2, 3, 4, 8, 10} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 5, 8, 9} ∨
        polygon = {2, 3, 5, 8, 10} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 8, 9, 10} ∨
        polygon = {2, 4, 5, 8, 9} ∨
        polygon = {2, 4, 5, 8, 10} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {2, 4, 8, 9, 10} ∨
        polygon = {2, 5, 8, 9, 10} ∨
        polygon = {3, 4, 5, 8, 9} ∨
        polygon = {3, 4, 5, 8, 10} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {3, 4, 8, 9, 10} ∨
        polygon = {3, 5, 8, 9, 10} ∨
        polygon = {4, 5, 8, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 5, 8, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 5, 8, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 5, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 5, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 5, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 5, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 5, 8, 9, 10} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 5, 8, 9, 10} \ ({2, 3, 4, 5, 8, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 5, 8, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask2876 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 5, 8, 9, 11} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 5, 8} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 11} ∨
        polygon = {2, 3, 4, 8, 9} ∨
        polygon = {2, 3, 4, 8, 11} ∨
        polygon = {2, 3, 4, 9, 11} ∨
        polygon = {2, 3, 5, 8, 9} ∨
        polygon = {2, 3, 5, 8, 11} ∨
        polygon = {2, 3, 5, 9, 11} ∨
        polygon = {2, 3, 8, 9, 11} ∨
        polygon = {2, 4, 5, 8, 9} ∨
        polygon = {2, 4, 5, 8, 11} ∨
        polygon = {2, 4, 5, 9, 11} ∨
        polygon = {2, 4, 8, 9, 11} ∨
        polygon = {2, 5, 8, 9, 11} ∨
        polygon = {3, 4, 5, 8, 9} ∨
        polygon = {3, 4, 5, 8, 11} ∨
        polygon = {3, 4, 5, 9, 11} ∨
        polygon = {3, 4, 8, 9, 11} ∨
        polygon = {3, 5, 8, 9, 11} ∨
        polygon = {4, 5, 8, 9, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 5, 8, 9, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 5, 8, 9, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 5, 8, 9, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 5, 8, 9, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 5, 8, 9, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 5, 8, 9, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 5, 8, 9, 11} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 5, 8, 9, 11} \ ({2, 3, 4, 5, 8, 9, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 5, 8, 9, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4924 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 5, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 5, 8} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 8, 9} ∨
        polygon = {2, 3, 4, 8, 12} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 5, 8, 9} ∨
        polygon = {2, 3, 5, 8, 12} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 8, 9, 12} ∨
        polygon = {2, 4, 5, 8, 9} ∨
        polygon = {2, 4, 5, 8, 12} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {2, 4, 8, 9, 12} ∨
        polygon = {2, 5, 8, 9, 12} ∨
        polygon = {3, 4, 5, 8, 9} ∨
        polygon = {3, 4, 5, 8, 12} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 8, 9, 12} ∨
        polygon = {3, 5, 8, 9, 12} ∨
        polygon = {4, 5, 8, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 5, 8, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 5, 8, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 5, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 5, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 5, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 5, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 5, 8, 9, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 5, 8, 9, 12} \ ({2, 3, 4, 5, 8, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 5, 8, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3388 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 5, 8, 10, 11} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 5, 8} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 11} ∨
        polygon = {2, 3, 4, 8, 10} ∨
        polygon = {2, 3, 4, 8, 11} ∨
        polygon = {2, 3, 4, 10, 11} ∨
        polygon = {2, 3, 5, 8, 10} ∨
        polygon = {2, 3, 5, 8, 11} ∨
        polygon = {2, 3, 5, 10, 11} ∨
        polygon = {2, 3, 8, 10, 11} ∨
        polygon = {2, 4, 5, 8, 10} ∨
        polygon = {2, 4, 5, 8, 11} ∨
        polygon = {2, 4, 5, 10, 11} ∨
        polygon = {2, 4, 8, 10, 11} ∨
        polygon = {2, 5, 8, 10, 11} ∨
        polygon = {3, 4, 5, 8, 10} ∨
        polygon = {3, 4, 5, 8, 11} ∨
        polygon = {3, 4, 5, 10, 11} ∨
        polygon = {3, 4, 8, 10, 11} ∨
        polygon = {3, 5, 8, 10, 11} ∨
        polygon = {4, 5, 8, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 5, 8, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 5, 8, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 5, 8, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 5, 8, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 5, 8, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 5, 8, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 5, 8, 10, 11} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 5, 8, 10, 11} \ ({2, 3, 4, 5, 8, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 5, 8, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5436 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 5, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 5, 8} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 8, 10} ∨
        polygon = {2, 3, 4, 8, 12} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 5, 8, 10} ∨
        polygon = {2, 3, 5, 8, 12} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 8, 10, 12} ∨
        polygon = {2, 4, 5, 8, 10} ∨
        polygon = {2, 4, 5, 8, 12} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {2, 4, 8, 10, 12} ∨
        polygon = {2, 5, 8, 10, 12} ∨
        polygon = {3, 4, 5, 8, 10} ∨
        polygon = {3, 4, 5, 8, 12} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 8, 10, 12} ∨
        polygon = {3, 5, 8, 10, 12} ∨
        polygon = {4, 5, 8, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 5, 8, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 5, 8, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 5, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 5, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 5, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 5, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 5, 8, 10, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 5, 8, 10, 12} \ ({2, 3, 4, 5, 8, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 5, 8, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask6460 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 5, 8, 11, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 5, 8} ∨
        polygon = {2, 3, 4, 5, 11} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 8, 11} ∨
        polygon = {2, 3, 4, 8, 12} ∨
        polygon = {2, 3, 4, 11, 12} ∨
        polygon = {2, 3, 5, 8, 11} ∨
        polygon = {2, 3, 5, 8, 12} ∨
        polygon = {2, 3, 5, 11, 12} ∨
        polygon = {2, 3, 8, 11, 12} ∨
        polygon = {2, 4, 5, 8, 11} ∨
        polygon = {2, 4, 5, 8, 12} ∨
        polygon = {2, 4, 5, 11, 12} ∨
        polygon = {2, 4, 8, 11, 12} ∨
        polygon = {2, 5, 8, 11, 12} ∨
        polygon = {3, 4, 5, 8, 11} ∨
        polygon = {3, 4, 5, 8, 12} ∨
        polygon = {3, 4, 5, 11, 12} ∨
        polygon = {3, 4, 8, 11, 12} ∨
        polygon = {3, 5, 8, 11, 12} ∨
        polygon = {4, 5, 8, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 5, 8, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 5, 8, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 5, 8, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 5, 8, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 5, 8, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 5, 8, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 5, 8, 11, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 5, 8, 11, 12} \ ({2, 3, 4, 5, 8, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 5, 8, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3644 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 5, 9, 10, 11} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 11} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 4, 9, 11} ∨
        polygon = {2, 3, 4, 10, 11} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 5, 9, 11} ∨
        polygon = {2, 3, 5, 10, 11} ∨
        polygon = {2, 3, 9, 10, 11} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {2, 4, 5, 9, 11} ∨
        polygon = {2, 4, 5, 10, 11} ∨
        polygon = {2, 4, 9, 10, 11} ∨
        polygon = {2, 5, 9, 10, 11} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {3, 4, 5, 9, 11} ∨
        polygon = {3, 4, 5, 10, 11} ∨
        polygon = {3, 4, 9, 10, 11} ∨
        polygon = {3, 5, 9, 10, 11} ∨
        polygon = {4, 5, 9, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 5, 9, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 5, 9, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 5, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 5, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 5, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 5, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 5, 9, 10, 11} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 5, 9, 10, 11} \ ({2, 3, 4, 5, 9, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 5, 9, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5692 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 5, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 9, 10, 12} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {2, 4, 9, 10, 12} ∨
        polygon = {2, 5, 9, 10, 12} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {4, 5, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 5, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 5, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 5, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 5, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 5, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 5, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 5, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 5, 9, 10, 12} \ ({2, 3, 4, 5, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 5, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask6716 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 5, 9, 11, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 11} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 9, 11} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 11, 12} ∨
        polygon = {2, 3, 5, 9, 11} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 5, 11, 12} ∨
        polygon = {2, 3, 9, 11, 12} ∨
        polygon = {2, 4, 5, 9, 11} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {2, 4, 5, 11, 12} ∨
        polygon = {2, 4, 9, 11, 12} ∨
        polygon = {2, 5, 9, 11, 12} ∨
        polygon = {3, 4, 5, 9, 11} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 5, 11, 12} ∨
        polygon = {3, 4, 9, 11, 12} ∨
        polygon = {3, 5, 9, 11, 12} ∨
        polygon = {4, 5, 9, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 5, 9, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 5, 9, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 5, 9, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 5, 9, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 5, 9, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 5, 9, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 5, 9, 11, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 5, 9, 11, 12} \ ({2, 3, 4, 5, 9, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 5, 9, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask7228 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 5, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 11} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 10, 11} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 4, 11, 12} ∨
        polygon = {2, 3, 5, 10, 11} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 5, 11, 12} ∨
        polygon = {2, 3, 10, 11, 12} ∨
        polygon = {2, 4, 5, 10, 11} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {2, 4, 5, 11, 12} ∨
        polygon = {2, 4, 10, 11, 12} ∨
        polygon = {2, 5, 10, 11, 12} ∨
        polygon = {3, 4, 5, 10, 11} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 5, 11, 12} ∨
        polygon = {3, 4, 10, 11, 12} ∨
        polygon = {3, 5, 10, 11, 12} ∨
        polygon = {4, 5, 10, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 5, 10, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 5, 10, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 5, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 5, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 5, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 5, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 5, 10, 11, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 5, 10, 11, 12} \ ({2, 3, 4, 5, 10, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 5, 10, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask0988 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 6, 7, 8, 9} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {2, 3, 4, 6, 8} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 7, 8} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 8, 9} ∨
        polygon = {2, 3, 6, 7, 8} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {2, 3, 6, 8, 9} ∨
        polygon = {2, 3, 7, 8, 9} ∨
        polygon = {2, 4, 6, 7, 8} ∨
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {2, 4, 6, 8, 9} ∨
        polygon = {2, 4, 7, 8, 9} ∨
        polygon = {2, 6, 7, 8, 9} ∨
        polygon = {3, 4, 6, 7, 8} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {3, 4, 6, 8, 9} ∨
        polygon = {3, 4, 7, 8, 9} ∨
        polygon = {3, 6, 7, 8, 9} ∨
        polygon = {4, 6, 7, 8, 9} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 6, 7, 8, 9} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 6, 7, 8, 9} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 6, 7, 8, 9} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 6, 7, 8, 9} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 6, 7, 8, 9} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 6, 7, 8, 9} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 6, 7, 8, 9} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 6, 7, 8, 9} \ ({2, 3, 4, 6, 7, 8, 9} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 6, 7, 8, 9} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1500 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 6, 7, 8, 10} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {2, 3, 4, 6, 8} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 7, 8} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 8, 10} ∨
        polygon = {2, 3, 6, 7, 8} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {2, 3, 6, 8, 10} ∨
        polygon = {2, 3, 7, 8, 10} ∨
        polygon = {2, 4, 6, 7, 8} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {2, 4, 6, 8, 10} ∨
        polygon = {2, 4, 7, 8, 10} ∨
        polygon = {2, 6, 7, 8, 10} ∨
        polygon = {3, 4, 6, 7, 8} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {3, 4, 6, 8, 10} ∨
        polygon = {3, 4, 7, 8, 10} ∨
        polygon = {3, 6, 7, 8, 10} ∨
        polygon = {4, 6, 7, 8, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 6, 7, 8, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 6, 7, 8, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 6, 7, 8, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 6, 7, 8, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 6, 7, 8, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 6, 7, 8, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 6, 7, 8, 10} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 6, 7, 8, 10} \ ({2, 3, 4, 6, 7, 8, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 6, 7, 8, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask2524 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 6, 7, 8, 11} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {2, 3, 4, 6, 8} ∨
        polygon = {2, 3, 4, 6, 11} ∨
        polygon = {2, 3, 4, 7, 8} ∨
        polygon = {2, 3, 4, 7, 11} ∨
        polygon = {2, 3, 4, 8, 11} ∨
        polygon = {2, 3, 6, 7, 8} ∨
        polygon = {2, 3, 6, 7, 11} ∨
        polygon = {2, 3, 6, 8, 11} ∨
        polygon = {2, 3, 7, 8, 11} ∨
        polygon = {2, 4, 6, 7, 8} ∨
        polygon = {2, 4, 6, 7, 11} ∨
        polygon = {2, 4, 6, 8, 11} ∨
        polygon = {2, 4, 7, 8, 11} ∨
        polygon = {2, 6, 7, 8, 11} ∨
        polygon = {3, 4, 6, 7, 8} ∨
        polygon = {3, 4, 6, 7, 11} ∨
        polygon = {3, 4, 6, 8, 11} ∨
        polygon = {3, 4, 7, 8, 11} ∨
        polygon = {3, 6, 7, 8, 11} ∨
        polygon = {4, 6, 7, 8, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 6, 7, 8, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 6, 7, 8, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 6, 7, 8, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 6, 7, 8, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 6, 7, 8, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 6, 7, 8, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 6, 7, 8, 11} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 6, 7, 8, 11} \ ({2, 3, 4, 6, 7, 8, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 6, 7, 8, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

end ErdosSzekeres

end
