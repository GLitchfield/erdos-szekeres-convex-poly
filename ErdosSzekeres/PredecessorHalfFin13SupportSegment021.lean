module

public import ErdosSzekeres.PredecessorHalfFin13Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 021. -/

theorem predecessorHalfFin13_fiveSubset_mask4969 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 5, 6, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {0, 3, 5, 6, 8} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 5, 8, 9} ∨
        polygon = {0, 3, 5, 8, 12} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 6, 8, 9} ∨
        polygon = {0, 3, 6, 8, 12} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 8, 9, 12} ∨
        polygon = {0, 5, 6, 8, 9} ∨
        polygon = {0, 5, 6, 8, 12} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 5, 8, 9, 12} ∨
        polygon = {0, 6, 8, 9, 12} ∨
        polygon = {3, 5, 6, 8, 9} ∨
        polygon = {3, 5, 6, 8, 12} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {3, 5, 8, 9, 12} ∨
        polygon = {3, 6, 8, 9, 12} ∨
        polygon = {5, 6, 8, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 5, 6, 8, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 5, 6, 8, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 5, 6, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 5, 6, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 5, 6, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 5, 6, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 5, 6, 8, 9, 12} \ {x, y} := by
    calc
      polygon = {0, 3, 5, 6, 8, 9, 12} \ ({0, 3, 5, 6, 8, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 5, 6, 8, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5481 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 5, 6, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 3, 5, 6, 8} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 3, 5, 8, 12} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 6, 8, 10} ∨
        polygon = {0, 3, 6, 8, 12} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 8, 10, 12} ∨
        polygon = {0, 5, 6, 8, 10} ∨
        polygon = {0, 5, 6, 8, 12} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 8, 10, 12} ∨
        polygon = {0, 6, 8, 10, 12} ∨
        polygon = {3, 5, 6, 8, 10} ∨
        polygon = {3, 5, 6, 8, 12} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {3, 5, 8, 10, 12} ∨
        polygon = {3, 6, 8, 10, 12} ∨
        polygon = {5, 6, 8, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 5, 6, 8, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 5, 6, 8, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 5, 6, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 5, 6, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 5, 6, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 5, 6, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 5, 6, 8, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 3, 5, 6, 8, 10, 12} \ ({0, 3, 5, 6, 8, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 5, 6, 8, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5737 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 5, 6, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 9, 10, 12} ∨
        polygon = {0, 6, 9, 10, 12} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {5, 6, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 5, 6, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 5, 6, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 5, 6, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 5, 6, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 5, 6, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 5, 6, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 5, 6, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 3, 5, 6, 9, 10, 12} \ ({0, 3, 5, 6, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 5, 6, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1961 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 5, 7, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {0, 3, 5, 7, 8} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 5, 8, 9} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 7, 8, 9} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 5, 7, 8, 9} ∨
        polygon = {0, 5, 7, 8, 10} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {0, 5, 8, 9, 10} ∨
        polygon = {0, 7, 8, 9, 10} ∨
        polygon = {3, 5, 7, 8, 9} ∨
        polygon = {3, 5, 7, 8, 10} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {3, 5, 8, 9, 10} ∨
        polygon = {3, 7, 8, 9, 10} ∨
        polygon = {5, 7, 8, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 5, 7, 8, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 5, 7, 8, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 5, 7, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 5, 7, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 5, 7, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 5, 7, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 5, 7, 8, 9, 10} \ {x, y} := by
    calc
      polygon = {0, 3, 5, 7, 8, 9, 10} \ ({0, 3, 5, 7, 8, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 5, 7, 8, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5033 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 5, 7, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {0, 3, 5, 7, 8} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 8, 9} ∨
        polygon = {0, 3, 5, 8, 12} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 7, 8, 9} ∨
        polygon = {0, 3, 7, 8, 12} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 8, 9, 12} ∨
        polygon = {0, 5, 7, 8, 9} ∨
        polygon = {0, 5, 7, 8, 12} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {0, 5, 8, 9, 12} ∨
        polygon = {0, 7, 8, 9, 12} ∨
        polygon = {3, 5, 7, 8, 9} ∨
        polygon = {3, 5, 7, 8, 12} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {3, 5, 8, 9, 12} ∨
        polygon = {3, 7, 8, 9, 12} ∨
        polygon = {5, 7, 8, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 5, 7, 8, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 5, 7, 8, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 5, 7, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 5, 7, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 5, 7, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 5, 7, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 5, 7, 8, 9, 12} \ {x, y} := by
    calc
      polygon = {0, 3, 5, 7, 8, 9, 12} \ ({0, 3, 5, 7, 8, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 5, 7, 8, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5545 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 5, 7, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 3, 5, 7, 8} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 3, 5, 8, 12} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 3, 7, 8, 12} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 8, 10, 12} ∨
        polygon = {0, 5, 7, 8, 10} ∨
        polygon = {0, 5, 7, 8, 12} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 5, 8, 10, 12} ∨
        polygon = {0, 7, 8, 10, 12} ∨
        polygon = {3, 5, 7, 8, 10} ∨
        polygon = {3, 5, 7, 8, 12} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {3, 5, 8, 10, 12} ∨
        polygon = {3, 7, 8, 10, 12} ∨
        polygon = {5, 7, 8, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 5, 7, 8, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 5, 7, 8, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 5, 7, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 5, 7, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 5, 7, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 5, 7, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 5, 7, 8, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 3, 5, 7, 8, 10, 12} \ ({0, 3, 5, 7, 8, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 5, 7, 8, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5801 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 5, 7, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 5, 9, 10, 12} ∨
        polygon = {0, 7, 9, 10, 12} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {5, 7, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 5, 7, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 5, 7, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 5, 7, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 5, 7, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 5, 7, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 5, 7, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 5, 7, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 3, 5, 7, 9, 10, 12} \ ({0, 3, 5, 7, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 5, 7, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5929 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 5, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 3, 5, 8, 9} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 3, 5, 8, 12} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 3, 8, 9, 12} ∨
        polygon = {0, 3, 8, 10, 12} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 5, 8, 9, 10} ∨
        polygon = {0, 5, 8, 9, 12} ∨
        polygon = {0, 5, 8, 10, 12} ∨
        polygon = {0, 5, 9, 10, 12} ∨
        polygon = {0, 8, 9, 10, 12} ∨
        polygon = {3, 5, 8, 9, 10} ∨
        polygon = {3, 5, 8, 9, 12} ∨
        polygon = {3, 5, 8, 10, 12} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 8, 9, 10, 12} ∨
        polygon = {5, 8, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 5, 8, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 5, 8, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 5, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 5, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 5, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 5, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 5, 8, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 3, 5, 8, 9, 10, 12} \ ({0, 3, 5, 8, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 5, 8, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1993 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 6, 7, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {0, 3, 6, 7, 8} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 6, 8, 9} ∨
        polygon = {0, 3, 6, 8, 10} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 7, 8, 9} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 6, 7, 8, 9} ∨
        polygon = {0, 6, 7, 8, 10} ∨
        polygon = {0, 6, 7, 9, 10} ∨
        polygon = {0, 6, 8, 9, 10} ∨
        polygon = {0, 7, 8, 9, 10} ∨
        polygon = {3, 6, 7, 8, 9} ∨
        polygon = {3, 6, 7, 8, 10} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {3, 6, 8, 9, 10} ∨
        polygon = {3, 7, 8, 9, 10} ∨
        polygon = {6, 7, 8, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 6, 7, 8, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 6, 7, 8, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 6, 7, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 6, 7, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 6, 7, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 6, 7, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 6, 7, 8, 9, 10} \ {x, y} := by
    calc
      polygon = {0, 3, 6, 7, 8, 9, 10} \ ({0, 3, 6, 7, 8, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 6, 7, 8, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5065 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 6, 7, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {0, 3, 6, 7, 8} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 8, 9} ∨
        polygon = {0, 3, 6, 8, 12} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 7, 8, 9} ∨
        polygon = {0, 3, 7, 8, 12} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 8, 9, 12} ∨
        polygon = {0, 6, 7, 8, 9} ∨
        polygon = {0, 6, 7, 8, 12} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {0, 6, 8, 9, 12} ∨
        polygon = {0, 7, 8, 9, 12} ∨
        polygon = {3, 6, 7, 8, 9} ∨
        polygon = {3, 6, 7, 8, 12} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {3, 6, 8, 9, 12} ∨
        polygon = {3, 7, 8, 9, 12} ∨
        polygon = {6, 7, 8, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 6, 7, 8, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 6, 7, 8, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 6, 7, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 6, 7, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 6, 7, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 6, 7, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 6, 7, 8, 9, 12} \ {x, y} := by
    calc
      polygon = {0, 3, 6, 7, 8, 9, 12} \ ({0, 3, 6, 7, 8, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 6, 7, 8, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5577 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 6, 7, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 3, 6, 7, 8} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 8, 10} ∨
        polygon = {0, 3, 6, 8, 12} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 3, 7, 8, 12} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 8, 10, 12} ∨
        polygon = {0, 6, 7, 8, 10} ∨
        polygon = {0, 6, 7, 8, 12} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {0, 6, 8, 10, 12} ∨
        polygon = {0, 7, 8, 10, 12} ∨
        polygon = {3, 6, 7, 8, 10} ∨
        polygon = {3, 6, 7, 8, 12} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {3, 6, 8, 10, 12} ∨
        polygon = {3, 7, 8, 10, 12} ∨
        polygon = {6, 7, 8, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 6, 7, 8, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 6, 7, 8, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 6, 7, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 6, 7, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 6, 7, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 6, 7, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 6, 7, 8, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 3, 6, 7, 8, 10, 12} \ ({0, 3, 6, 7, 8, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 6, 7, 8, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5833 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 6, 7, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 6, 7, 9, 10} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {0, 6, 9, 10, 12} ∨
        polygon = {0, 7, 9, 10, 12} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {6, 7, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 6, 7, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 6, 7, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 6, 7, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 6, 7, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 6, 7, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 6, 7, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 6, 7, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 3, 6, 7, 9, 10, 12} \ ({0, 3, 6, 7, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 6, 7, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5961 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 6, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 3, 6, 8, 9} ∨
        polygon = {0, 3, 6, 8, 10} ∨
        polygon = {0, 3, 6, 8, 12} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 3, 8, 9, 12} ∨
        polygon = {0, 3, 8, 10, 12} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 6, 8, 9, 10} ∨
        polygon = {0, 6, 8, 9, 12} ∨
        polygon = {0, 6, 8, 10, 12} ∨
        polygon = {0, 6, 9, 10, 12} ∨
        polygon = {0, 8, 9, 10, 12} ∨
        polygon = {3, 6, 8, 9, 10} ∨
        polygon = {3, 6, 8, 9, 12} ∨
        polygon = {3, 6, 8, 10, 12} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {3, 8, 9, 10, 12} ∨
        polygon = {6, 8, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 6, 8, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 6, 8, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 6, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 6, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 6, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 6, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 6, 8, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 3, 6, 8, 9, 10, 12} \ ({0, 3, 6, 8, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 6, 8, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask6025 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 7, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 3, 7, 8, 9} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 3, 7, 8, 12} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 3, 8, 9, 12} ∨
        polygon = {0, 3, 8, 10, 12} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 7, 8, 9, 10} ∨
        polygon = {0, 7, 8, 9, 12} ∨
        polygon = {0, 7, 8, 10, 12} ∨
        polygon = {0, 7, 9, 10, 12} ∨
        polygon = {0, 8, 9, 10, 12} ∨
        polygon = {3, 7, 8, 9, 10} ∨
        polygon = {3, 7, 8, 9, 12} ∨
        polygon = {3, 7, 8, 10, 12} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {3, 8, 9, 10, 12} ∨
        polygon = {7, 8, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 7, 8, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 7, 8, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 7, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 7, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 7, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 7, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 7, 8, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 3, 7, 8, 9, 10, 12} \ ({0, 3, 7, 8, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 7, 8, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1009 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 4, 5, 6, 7, 8, 9} →
      polygon.card = 5 →
        polygon = {0, 4, 5, 6, 7} ∨
        polygon = {0, 4, 5, 6, 8} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 4, 5, 7, 8} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 4, 6, 7, 8} ∨
        polygon = {0, 4, 6, 7, 9} ∨
        polygon = {0, 4, 6, 8, 9} ∨
        polygon = {0, 4, 7, 8, 9} ∨
        polygon = {0, 5, 6, 7, 8} ∨
        polygon = {0, 5, 6, 7, 9} ∨
        polygon = {0, 5, 6, 8, 9} ∨
        polygon = {0, 5, 7, 8, 9} ∨
        polygon = {0, 6, 7, 8, 9} ∨
        polygon = {4, 5, 6, 7, 8} ∨
        polygon = {4, 5, 6, 7, 9} ∨
        polygon = {4, 5, 6, 8, 9} ∨
        polygon = {4, 5, 7, 8, 9} ∨
        polygon = {4, 6, 7, 8, 9} ∨
        polygon = {5, 6, 7, 8, 9} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 4, 5, 6, 7, 8, 9} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 4, 5, 6, 7, 8, 9} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 4, 5, 6, 7, 8, 9} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 4, 5, 6, 7, 8, 9} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 4, 5, 6, 7, 8, 9} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 4, 5, 6, 7, 8, 9} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 4, 5, 6, 7, 8, 9} \ {x, y} := by
    calc
      polygon = {0, 4, 5, 6, 7, 8, 9} \ ({0, 4, 5, 6, 7, 8, 9} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 4, 5, 6, 7, 8, 9} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1521 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 4, 5, 6, 7, 8, 10} →
      polygon.card = 5 →
        polygon = {0, 4, 5, 6, 7} ∨
        polygon = {0, 4, 5, 6, 8} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 7, 8} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 4, 6, 7, 8} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 4, 6, 8, 10} ∨
        polygon = {0, 4, 7, 8, 10} ∨
        polygon = {0, 5, 6, 7, 8} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 5, 6, 8, 10} ∨
        polygon = {0, 5, 7, 8, 10} ∨
        polygon = {0, 6, 7, 8, 10} ∨
        polygon = {4, 5, 6, 7, 8} ∨
        polygon = {4, 5, 6, 7, 10} ∨
        polygon = {4, 5, 6, 8, 10} ∨
        polygon = {4, 5, 7, 8, 10} ∨
        polygon = {4, 6, 7, 8, 10} ∨
        polygon = {5, 6, 7, 8, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 4, 5, 6, 7, 8, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 4, 5, 6, 7, 8, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 4, 5, 6, 7, 8, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 4, 5, 6, 7, 8, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 4, 5, 6, 7, 8, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 4, 5, 6, 7, 8, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 4, 5, 6, 7, 8, 10} \ {x, y} := by
    calc
      polygon = {0, 4, 5, 6, 7, 8, 10} \ ({0, 4, 5, 6, 7, 8, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 4, 5, 6, 7, 8, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4593 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 4, 5, 6, 7, 8, 12} →
      polygon.card = 5 →
        polygon = {0, 4, 5, 6, 7} ∨
        polygon = {0, 4, 5, 6, 8} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 7, 8} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 8, 12} ∨
        polygon = {0, 4, 6, 7, 8} ∨
        polygon = {0, 4, 6, 7, 12} ∨
        polygon = {0, 4, 6, 8, 12} ∨
        polygon = {0, 4, 7, 8, 12} ∨
        polygon = {0, 5, 6, 7, 8} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 5, 6, 8, 12} ∨
        polygon = {0, 5, 7, 8, 12} ∨
        polygon = {0, 6, 7, 8, 12} ∨
        polygon = {4, 5, 6, 7, 8} ∨
        polygon = {4, 5, 6, 7, 12} ∨
        polygon = {4, 5, 6, 8, 12} ∨
        polygon = {4, 5, 7, 8, 12} ∨
        polygon = {4, 6, 7, 8, 12} ∨
        polygon = {5, 6, 7, 8, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 4, 5, 6, 7, 8, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 4, 5, 6, 7, 8, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 4, 5, 6, 7, 8, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 4, 5, 6, 7, 8, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 4, 5, 6, 7, 8, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 4, 5, 6, 7, 8, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 4, 5, 6, 7, 8, 12} \ {x, y} := by
    calc
      polygon = {0, 4, 5, 6, 7, 8, 12} \ ({0, 4, 5, 6, 7, 8, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 4, 5, 6, 7, 8, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1777 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 4, 5, 6, 7, 9, 10} →
      polygon.card = 5 →
        polygon = {0, 4, 5, 6, 7} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 6, 7, 9} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 4, 6, 9, 10} ∨
        polygon = {0, 4, 7, 9, 10} ∨
        polygon = {0, 5, 6, 7, 9} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {0, 6, 7, 9, 10} ∨
        polygon = {4, 5, 6, 7, 9} ∨
        polygon = {4, 5, 6, 7, 10} ∨
        polygon = {4, 5, 6, 9, 10} ∨
        polygon = {4, 5, 7, 9, 10} ∨
        polygon = {4, 6, 7, 9, 10} ∨
        polygon = {5, 6, 7, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 4, 5, 6, 7, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 4, 5, 6, 7, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 4, 5, 6, 7, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 4, 5, 6, 7, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 4, 5, 6, 7, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 4, 5, 6, 7, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 4, 5, 6, 7, 9, 10} \ {x, y} := by
    calc
      polygon = {0, 4, 5, 6, 7, 9, 10} \ ({0, 4, 5, 6, 7, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 4, 5, 6, 7, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4849 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 4, 5, 6, 7, 9, 12} →
      polygon.card = 5 →
        polygon = {0, 4, 5, 6, 7} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 6, 7, 9} ∨
        polygon = {0, 4, 6, 7, 12} ∨
        polygon = {0, 4, 6, 9, 12} ∨
        polygon = {0, 4, 7, 9, 12} ∨
        polygon = {0, 5, 6, 7, 9} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {4, 5, 6, 7, 9} ∨
        polygon = {4, 5, 6, 7, 12} ∨
        polygon = {4, 5, 6, 9, 12} ∨
        polygon = {4, 5, 7, 9, 12} ∨
        polygon = {4, 6, 7, 9, 12} ∨
        polygon = {5, 6, 7, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 4, 5, 6, 7, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 4, 5, 6, 7, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 4, 5, 6, 7, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 4, 5, 6, 7, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 4, 5, 6, 7, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 4, 5, 6, 7, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 4, 5, 6, 7, 9, 12} \ {x, y} := by
    calc
      polygon = {0, 4, 5, 6, 7, 9, 12} \ ({0, 4, 5, 6, 7, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 4, 5, 6, 7, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5361 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 4, 5, 6, 7, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 4, 5, 6, 7} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 4, 6, 7, 12} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 4, 7, 10, 12} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {4, 5, 6, 7, 10} ∨
        polygon = {4, 5, 6, 7, 12} ∨
        polygon = {4, 5, 6, 10, 12} ∨
        polygon = {4, 5, 7, 10, 12} ∨
        polygon = {4, 6, 7, 10, 12} ∨
        polygon = {5, 6, 7, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 4, 5, 6, 7, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 4, 5, 6, 7, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 4, 5, 6, 7, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 4, 5, 6, 7, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 4, 5, 6, 7, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 4, 5, 6, 7, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 4, 5, 6, 7, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 4, 5, 6, 7, 10, 12} \ ({0, 4, 5, 6, 7, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 4, 5, 6, 7, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1905 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 4, 5, 6, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {0, 4, 5, 6, 8} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 6, 8, 9} ∨
        polygon = {0, 4, 6, 8, 10} ∨
        polygon = {0, 4, 6, 9, 10} ∨
        polygon = {0, 4, 8, 9, 10} ∨
        polygon = {0, 5, 6, 8, 9} ∨
        polygon = {0, 5, 6, 8, 10} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 5, 8, 9, 10} ∨
        polygon = {0, 6, 8, 9, 10} ∨
        polygon = {4, 5, 6, 8, 9} ∨
        polygon = {4, 5, 6, 8, 10} ∨
        polygon = {4, 5, 6, 9, 10} ∨
        polygon = {4, 5, 8, 9, 10} ∨
        polygon = {4, 6, 8, 9, 10} ∨
        polygon = {5, 6, 8, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 4, 5, 6, 8, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 4, 5, 6, 8, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 4, 5, 6, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 4, 5, 6, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 4, 5, 6, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 4, 5, 6, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 4, 5, 6, 8, 9, 10} \ {x, y} := by
    calc
      polygon = {0, 4, 5, 6, 8, 9, 10} \ ({0, 4, 5, 6, 8, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 4, 5, 6, 8, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4977 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 4, 5, 6, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {0, 4, 5, 6, 8} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 4, 5, 8, 12} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 6, 8, 9} ∨
        polygon = {0, 4, 6, 8, 12} ∨
        polygon = {0, 4, 6, 9, 12} ∨
        polygon = {0, 4, 8, 9, 12} ∨
        polygon = {0, 5, 6, 8, 9} ∨
        polygon = {0, 5, 6, 8, 12} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 5, 8, 9, 12} ∨
        polygon = {0, 6, 8, 9, 12} ∨
        polygon = {4, 5, 6, 8, 9} ∨
        polygon = {4, 5, 6, 8, 12} ∨
        polygon = {4, 5, 6, 9, 12} ∨
        polygon = {4, 5, 8, 9, 12} ∨
        polygon = {4, 6, 8, 9, 12} ∨
        polygon = {5, 6, 8, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 4, 5, 6, 8, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 4, 5, 6, 8, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 4, 5, 6, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 4, 5, 6, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 4, 5, 6, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 4, 5, 6, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 4, 5, 6, 8, 9, 12} \ {x, y} := by
    calc
      polygon = {0, 4, 5, 6, 8, 9, 12} \ ({0, 4, 5, 6, 8, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 4, 5, 6, 8, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5489 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 4, 5, 6, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 4, 5, 6, 8} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 4, 5, 8, 12} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 6, 8, 10} ∨
        polygon = {0, 4, 6, 8, 12} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 4, 8, 10, 12} ∨
        polygon = {0, 5, 6, 8, 10} ∨
        polygon = {0, 5, 6, 8, 12} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 8, 10, 12} ∨
        polygon = {0, 6, 8, 10, 12} ∨
        polygon = {4, 5, 6, 8, 10} ∨
        polygon = {4, 5, 6, 8, 12} ∨
        polygon = {4, 5, 6, 10, 12} ∨
        polygon = {4, 5, 8, 10, 12} ∨
        polygon = {4, 6, 8, 10, 12} ∨
        polygon = {5, 6, 8, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 4, 5, 6, 8, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 4, 5, 6, 8, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 4, 5, 6, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 4, 5, 6, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 4, 5, 6, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 4, 5, 6, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 4, 5, 6, 8, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 4, 5, 6, 8, 10, 12} \ ({0, 4, 5, 6, 8, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 4, 5, 6, 8, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5745 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 4, 5, 6, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 6, 9, 10} ∨
        polygon = {0, 4, 6, 9, 12} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 4, 9, 10, 12} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 9, 10, 12} ∨
        polygon = {0, 6, 9, 10, 12} ∨
        polygon = {4, 5, 6, 9, 10} ∨
        polygon = {4, 5, 6, 9, 12} ∨
        polygon = {4, 5, 6, 10, 12} ∨
        polygon = {4, 5, 9, 10, 12} ∨
        polygon = {4, 6, 9, 10, 12} ∨
        polygon = {5, 6, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 4, 5, 6, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 4, 5, 6, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 4, 5, 6, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 4, 5, 6, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 4, 5, 6, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 4, 5, 6, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 4, 5, 6, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 4, 5, 6, 9, 10, 12} \ ({0, 4, 5, 6, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 4, 5, 6, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1969 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 4, 5, 7, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {0, 4, 5, 7, 8} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 7, 8, 9} ∨
        polygon = {0, 4, 7, 8, 10} ∨
        polygon = {0, 4, 7, 9, 10} ∨
        polygon = {0, 4, 8, 9, 10} ∨
        polygon = {0, 5, 7, 8, 9} ∨
        polygon = {0, 5, 7, 8, 10} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {0, 5, 8, 9, 10} ∨
        polygon = {0, 7, 8, 9, 10} ∨
        polygon = {4, 5, 7, 8, 9} ∨
        polygon = {4, 5, 7, 8, 10} ∨
        polygon = {4, 5, 7, 9, 10} ∨
        polygon = {4, 5, 8, 9, 10} ∨
        polygon = {4, 7, 8, 9, 10} ∨
        polygon = {5, 7, 8, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 4, 5, 7, 8, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 4, 5, 7, 8, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 4, 5, 7, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 4, 5, 7, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 4, 5, 7, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 4, 5, 7, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 4, 5, 7, 8, 9, 10} \ {x, y} := by
    calc
      polygon = {0, 4, 5, 7, 8, 9, 10} \ ({0, 4, 5, 7, 8, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 4, 5, 7, 8, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5041 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 4, 5, 7, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {0, 4, 5, 7, 8} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 4, 5, 8, 12} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 7, 8, 9} ∨
        polygon = {0, 4, 7, 8, 12} ∨
        polygon = {0, 4, 7, 9, 12} ∨
        polygon = {0, 4, 8, 9, 12} ∨
        polygon = {0, 5, 7, 8, 9} ∨
        polygon = {0, 5, 7, 8, 12} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {0, 5, 8, 9, 12} ∨
        polygon = {0, 7, 8, 9, 12} ∨
        polygon = {4, 5, 7, 8, 9} ∨
        polygon = {4, 5, 7, 8, 12} ∨
        polygon = {4, 5, 7, 9, 12} ∨
        polygon = {4, 5, 8, 9, 12} ∨
        polygon = {4, 7, 8, 9, 12} ∨
        polygon = {5, 7, 8, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 4, 5, 7, 8, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 4, 5, 7, 8, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 4, 5, 7, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 4, 5, 7, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 4, 5, 7, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 4, 5, 7, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 4, 5, 7, 8, 9, 12} \ {x, y} := by
    calc
      polygon = {0, 4, 5, 7, 8, 9, 12} \ ({0, 4, 5, 7, 8, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 4, 5, 7, 8, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5553 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 4, 5, 7, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 4, 5, 7, 8} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 4, 5, 8, 12} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 7, 8, 10} ∨
        polygon = {0, 4, 7, 8, 12} ∨
        polygon = {0, 4, 7, 10, 12} ∨
        polygon = {0, 4, 8, 10, 12} ∨
        polygon = {0, 5, 7, 8, 10} ∨
        polygon = {0, 5, 7, 8, 12} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 5, 8, 10, 12} ∨
        polygon = {0, 7, 8, 10, 12} ∨
        polygon = {4, 5, 7, 8, 10} ∨
        polygon = {4, 5, 7, 8, 12} ∨
        polygon = {4, 5, 7, 10, 12} ∨
        polygon = {4, 5, 8, 10, 12} ∨
        polygon = {4, 7, 8, 10, 12} ∨
        polygon = {5, 7, 8, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 4, 5, 7, 8, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 4, 5, 7, 8, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 4, 5, 7, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 4, 5, 7, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 4, 5, 7, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 4, 5, 7, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 4, 5, 7, 8, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 4, 5, 7, 8, 10, 12} \ ({0, 4, 5, 7, 8, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 4, 5, 7, 8, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5809 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 4, 5, 7, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 7, 9, 10} ∨
        polygon = {0, 4, 7, 9, 12} ∨
        polygon = {0, 4, 7, 10, 12} ∨
        polygon = {0, 4, 9, 10, 12} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 5, 9, 10, 12} ∨
        polygon = {0, 7, 9, 10, 12} ∨
        polygon = {4, 5, 7, 9, 10} ∨
        polygon = {4, 5, 7, 9, 12} ∨
        polygon = {4, 5, 7, 10, 12} ∨
        polygon = {4, 5, 9, 10, 12} ∨
        polygon = {4, 7, 9, 10, 12} ∨
        polygon = {5, 7, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 4, 5, 7, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 4, 5, 7, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 4, 5, 7, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 4, 5, 7, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 4, 5, 7, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 4, 5, 7, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 4, 5, 7, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 4, 5, 7, 9, 10, 12} \ ({0, 4, 5, 7, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 4, 5, 7, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5937 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 4, 5, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 4, 5, 8, 12} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 8, 9, 10} ∨
        polygon = {0, 4, 8, 9, 12} ∨
        polygon = {0, 4, 8, 10, 12} ∨
        polygon = {0, 4, 9, 10, 12} ∨
        polygon = {0, 5, 8, 9, 10} ∨
        polygon = {0, 5, 8, 9, 12} ∨
        polygon = {0, 5, 8, 10, 12} ∨
        polygon = {0, 5, 9, 10, 12} ∨
        polygon = {0, 8, 9, 10, 12} ∨
        polygon = {4, 5, 8, 9, 10} ∨
        polygon = {4, 5, 8, 9, 12} ∨
        polygon = {4, 5, 8, 10, 12} ∨
        polygon = {4, 5, 9, 10, 12} ∨
        polygon = {4, 8, 9, 10, 12} ∨
        polygon = {5, 8, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 4, 5, 8, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 4, 5, 8, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 4, 5, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 4, 5, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 4, 5, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 4, 5, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 4, 5, 8, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 4, 5, 8, 9, 10, 12} \ ({0, 4, 5, 8, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 4, 5, 8, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask2001 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 4, 6, 7, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {0, 4, 6, 7, 8} ∨
        polygon = {0, 4, 6, 7, 9} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 4, 6, 8, 9} ∨
        polygon = {0, 4, 6, 8, 10} ∨
        polygon = {0, 4, 6, 9, 10} ∨
        polygon = {0, 4, 7, 8, 9} ∨
        polygon = {0, 4, 7, 8, 10} ∨
        polygon = {0, 4, 7, 9, 10} ∨
        polygon = {0, 4, 8, 9, 10} ∨
        polygon = {0, 6, 7, 8, 9} ∨
        polygon = {0, 6, 7, 8, 10} ∨
        polygon = {0, 6, 7, 9, 10} ∨
        polygon = {0, 6, 8, 9, 10} ∨
        polygon = {0, 7, 8, 9, 10} ∨
        polygon = {4, 6, 7, 8, 9} ∨
        polygon = {4, 6, 7, 8, 10} ∨
        polygon = {4, 6, 7, 9, 10} ∨
        polygon = {4, 6, 8, 9, 10} ∨
        polygon = {4, 7, 8, 9, 10} ∨
        polygon = {6, 7, 8, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 4, 6, 7, 8, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 4, 6, 7, 8, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 4, 6, 7, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 4, 6, 7, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 4, 6, 7, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 4, 6, 7, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 4, 6, 7, 8, 9, 10} \ {x, y} := by
    calc
      polygon = {0, 4, 6, 7, 8, 9, 10} \ ({0, 4, 6, 7, 8, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 4, 6, 7, 8, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5073 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 4, 6, 7, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {0, 4, 6, 7, 8} ∨
        polygon = {0, 4, 6, 7, 9} ∨
        polygon = {0, 4, 6, 7, 12} ∨
        polygon = {0, 4, 6, 8, 9} ∨
        polygon = {0, 4, 6, 8, 12} ∨
        polygon = {0, 4, 6, 9, 12} ∨
        polygon = {0, 4, 7, 8, 9} ∨
        polygon = {0, 4, 7, 8, 12} ∨
        polygon = {0, 4, 7, 9, 12} ∨
        polygon = {0, 4, 8, 9, 12} ∨
        polygon = {0, 6, 7, 8, 9} ∨
        polygon = {0, 6, 7, 8, 12} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {0, 6, 8, 9, 12} ∨
        polygon = {0, 7, 8, 9, 12} ∨
        polygon = {4, 6, 7, 8, 9} ∨
        polygon = {4, 6, 7, 8, 12} ∨
        polygon = {4, 6, 7, 9, 12} ∨
        polygon = {4, 6, 8, 9, 12} ∨
        polygon = {4, 7, 8, 9, 12} ∨
        polygon = {6, 7, 8, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 4, 6, 7, 8, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 4, 6, 7, 8, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 4, 6, 7, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 4, 6, 7, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 4, 6, 7, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 4, 6, 7, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 4, 6, 7, 8, 9, 12} \ {x, y} := by
    calc
      polygon = {0, 4, 6, 7, 8, 9, 12} \ ({0, 4, 6, 7, 8, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 4, 6, 7, 8, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5585 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 4, 6, 7, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 4, 6, 7, 8} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 4, 6, 7, 12} ∨
        polygon = {0, 4, 6, 8, 10} ∨
        polygon = {0, 4, 6, 8, 12} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 4, 7, 8, 10} ∨
        polygon = {0, 4, 7, 8, 12} ∨
        polygon = {0, 4, 7, 10, 12} ∨
        polygon = {0, 4, 8, 10, 12} ∨
        polygon = {0, 6, 7, 8, 10} ∨
        polygon = {0, 6, 7, 8, 12} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {0, 6, 8, 10, 12} ∨
        polygon = {0, 7, 8, 10, 12} ∨
        polygon = {4, 6, 7, 8, 10} ∨
        polygon = {4, 6, 7, 8, 12} ∨
        polygon = {4, 6, 7, 10, 12} ∨
        polygon = {4, 6, 8, 10, 12} ∨
        polygon = {4, 7, 8, 10, 12} ∨
        polygon = {6, 7, 8, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 4, 6, 7, 8, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 4, 6, 7, 8, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 4, 6, 7, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 4, 6, 7, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 4, 6, 7, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 4, 6, 7, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 4, 6, 7, 8, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 4, 6, 7, 8, 10, 12} \ ({0, 4, 6, 7, 8, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 4, 6, 7, 8, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5841 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 4, 6, 7, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 4, 6, 7, 9} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 4, 6, 7, 12} ∨
        polygon = {0, 4, 6, 9, 10} ∨
        polygon = {0, 4, 6, 9, 12} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 4, 7, 9, 10} ∨
        polygon = {0, 4, 7, 9, 12} ∨
        polygon = {0, 4, 7, 10, 12} ∨
        polygon = {0, 4, 9, 10, 12} ∨
        polygon = {0, 6, 7, 9, 10} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {0, 6, 9, 10, 12} ∨
        polygon = {0, 7, 9, 10, 12} ∨
        polygon = {4, 6, 7, 9, 10} ∨
        polygon = {4, 6, 7, 9, 12} ∨
        polygon = {4, 6, 7, 10, 12} ∨
        polygon = {4, 6, 9, 10, 12} ∨
        polygon = {4, 7, 9, 10, 12} ∨
        polygon = {6, 7, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 4, 6, 7, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 4, 6, 7, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 4, 6, 7, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 4, 6, 7, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 4, 6, 7, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 4, 6, 7, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 4, 6, 7, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 4, 6, 7, 9, 10, 12} \ ({0, 4, 6, 7, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 4, 6, 7, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5969 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 4, 6, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 4, 6, 8, 9} ∨
        polygon = {0, 4, 6, 8, 10} ∨
        polygon = {0, 4, 6, 8, 12} ∨
        polygon = {0, 4, 6, 9, 10} ∨
        polygon = {0, 4, 6, 9, 12} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 4, 8, 9, 10} ∨
        polygon = {0, 4, 8, 9, 12} ∨
        polygon = {0, 4, 8, 10, 12} ∨
        polygon = {0, 4, 9, 10, 12} ∨
        polygon = {0, 6, 8, 9, 10} ∨
        polygon = {0, 6, 8, 9, 12} ∨
        polygon = {0, 6, 8, 10, 12} ∨
        polygon = {0, 6, 9, 10, 12} ∨
        polygon = {0, 8, 9, 10, 12} ∨
        polygon = {4, 6, 8, 9, 10} ∨
        polygon = {4, 6, 8, 9, 12} ∨
        polygon = {4, 6, 8, 10, 12} ∨
        polygon = {4, 6, 9, 10, 12} ∨
        polygon = {4, 8, 9, 10, 12} ∨
        polygon = {6, 8, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 4, 6, 8, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 4, 6, 8, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 4, 6, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 4, 6, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 4, 6, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 4, 6, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 4, 6, 8, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 4, 6, 8, 9, 10, 12} \ ({0, 4, 6, 8, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 4, 6, 8, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask6033 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 4, 7, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 4, 7, 8, 9} ∨
        polygon = {0, 4, 7, 8, 10} ∨
        polygon = {0, 4, 7, 8, 12} ∨
        polygon = {0, 4, 7, 9, 10} ∨
        polygon = {0, 4, 7, 9, 12} ∨
        polygon = {0, 4, 7, 10, 12} ∨
        polygon = {0, 4, 8, 9, 10} ∨
        polygon = {0, 4, 8, 9, 12} ∨
        polygon = {0, 4, 8, 10, 12} ∨
        polygon = {0, 4, 9, 10, 12} ∨
        polygon = {0, 7, 8, 9, 10} ∨
        polygon = {0, 7, 8, 9, 12} ∨
        polygon = {0, 7, 8, 10, 12} ∨
        polygon = {0, 7, 9, 10, 12} ∨
        polygon = {0, 8, 9, 10, 12} ∨
        polygon = {4, 7, 8, 9, 10} ∨
        polygon = {4, 7, 8, 9, 12} ∨
        polygon = {4, 7, 8, 10, 12} ∨
        polygon = {4, 7, 9, 10, 12} ∨
        polygon = {4, 8, 9, 10, 12} ∨
        polygon = {7, 8, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 4, 7, 8, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 4, 7, 8, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 4, 7, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 4, 7, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 4, 7, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 4, 7, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 4, 7, 8, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 4, 7, 8, 9, 10, 12} \ ({0, 4, 7, 8, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 4, 7, 8, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask2017 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 5, 6, 7, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {0, 5, 6, 7, 8} ∨
        polygon = {0, 5, 6, 7, 9} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 5, 6, 8, 9} ∨
        polygon = {0, 5, 6, 8, 10} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 5, 7, 8, 9} ∨
        polygon = {0, 5, 7, 8, 10} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {0, 5, 8, 9, 10} ∨
        polygon = {0, 6, 7, 8, 9} ∨
        polygon = {0, 6, 7, 8, 10} ∨
        polygon = {0, 6, 7, 9, 10} ∨
        polygon = {0, 6, 8, 9, 10} ∨
        polygon = {0, 7, 8, 9, 10} ∨
        polygon = {5, 6, 7, 8, 9} ∨
        polygon = {5, 6, 7, 8, 10} ∨
        polygon = {5, 6, 7, 9, 10} ∨
        polygon = {5, 6, 8, 9, 10} ∨
        polygon = {5, 7, 8, 9, 10} ∨
        polygon = {6, 7, 8, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 5, 6, 7, 8, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 5, 6, 7, 8, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 5, 6, 7, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 5, 6, 7, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 5, 6, 7, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 5, 6, 7, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 5, 6, 7, 8, 9, 10} \ {x, y} := by
    calc
      polygon = {0, 5, 6, 7, 8, 9, 10} \ ({0, 5, 6, 7, 8, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 5, 6, 7, 8, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5089 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 5, 6, 7, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {0, 5, 6, 7, 8} ∨
        polygon = {0, 5, 6, 7, 9} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 5, 6, 8, 9} ∨
        polygon = {0, 5, 6, 8, 12} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 5, 7, 8, 9} ∨
        polygon = {0, 5, 7, 8, 12} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {0, 5, 8, 9, 12} ∨
        polygon = {0, 6, 7, 8, 9} ∨
        polygon = {0, 6, 7, 8, 12} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {0, 6, 8, 9, 12} ∨
        polygon = {0, 7, 8, 9, 12} ∨
        polygon = {5, 6, 7, 8, 9} ∨
        polygon = {5, 6, 7, 8, 12} ∨
        polygon = {5, 6, 7, 9, 12} ∨
        polygon = {5, 6, 8, 9, 12} ∨
        polygon = {5, 7, 8, 9, 12} ∨
        polygon = {6, 7, 8, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 5, 6, 7, 8, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 5, 6, 7, 8, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 5, 6, 7, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 5, 6, 7, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 5, 6, 7, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 5, 6, 7, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 5, 6, 7, 8, 9, 12} \ {x, y} := by
    calc
      polygon = {0, 5, 6, 7, 8, 9, 12} \ ({0, 5, 6, 7, 8, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 5, 6, 7, 8, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5601 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 5, 6, 7, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 5, 6, 7, 8} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 5, 6, 8, 10} ∨
        polygon = {0, 5, 6, 8, 12} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 7, 8, 10} ∨
        polygon = {0, 5, 7, 8, 12} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 5, 8, 10, 12} ∨
        polygon = {0, 6, 7, 8, 10} ∨
        polygon = {0, 6, 7, 8, 12} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {0, 6, 8, 10, 12} ∨
        polygon = {0, 7, 8, 10, 12} ∨
        polygon = {5, 6, 7, 8, 10} ∨
        polygon = {5, 6, 7, 8, 12} ∨
        polygon = {5, 6, 7, 10, 12} ∨
        polygon = {5, 6, 8, 10, 12} ∨
        polygon = {5, 7, 8, 10, 12} ∨
        polygon = {6, 7, 8, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 5, 6, 7, 8, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 5, 6, 7, 8, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 5, 6, 7, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 5, 6, 7, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 5, 6, 7, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 5, 6, 7, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 5, 6, 7, 8, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 5, 6, 7, 8, 10, 12} \ ({0, 5, 6, 7, 8, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 5, 6, 7, 8, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5857 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 5, 6, 7, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 5, 6, 7, 9} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 5, 9, 10, 12} ∨
        polygon = {0, 6, 7, 9, 10} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {0, 6, 9, 10, 12} ∨
        polygon = {0, 7, 9, 10, 12} ∨
        polygon = {5, 6, 7, 9, 10} ∨
        polygon = {5, 6, 7, 9, 12} ∨
        polygon = {5, 6, 7, 10, 12} ∨
        polygon = {5, 6, 9, 10, 12} ∨
        polygon = {5, 7, 9, 10, 12} ∨
        polygon = {6, 7, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 5, 6, 7, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 5, 6, 7, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 5, 6, 7, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 5, 6, 7, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 5, 6, 7, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 5, 6, 7, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 5, 6, 7, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 5, 6, 7, 9, 10, 12} \ ({0, 5, 6, 7, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 5, 6, 7, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5985 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 5, 6, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 5, 6, 8, 9} ∨
        polygon = {0, 5, 6, 8, 10} ∨
        polygon = {0, 5, 6, 8, 12} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 8, 9, 10} ∨
        polygon = {0, 5, 8, 9, 12} ∨
        polygon = {0, 5, 8, 10, 12} ∨
        polygon = {0, 5, 9, 10, 12} ∨
        polygon = {0, 6, 8, 9, 10} ∨
        polygon = {0, 6, 8, 9, 12} ∨
        polygon = {0, 6, 8, 10, 12} ∨
        polygon = {0, 6, 9, 10, 12} ∨
        polygon = {0, 8, 9, 10, 12} ∨
        polygon = {5, 6, 8, 9, 10} ∨
        polygon = {5, 6, 8, 9, 12} ∨
        polygon = {5, 6, 8, 10, 12} ∨
        polygon = {5, 6, 9, 10, 12} ∨
        polygon = {5, 8, 9, 10, 12} ∨
        polygon = {6, 8, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 5, 6, 8, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 5, 6, 8, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 5, 6, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 5, 6, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 5, 6, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 5, 6, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 5, 6, 8, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 5, 6, 8, 9, 10, 12} \ ({0, 5, 6, 8, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 5, 6, 8, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

end ErdosSzekeres

end
