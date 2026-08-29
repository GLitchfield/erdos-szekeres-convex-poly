module

public import ErdosSzekeres.PredecessorHalfFin13Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 024. -/

theorem predecessorHalfFin13_fiveSubset_mask1964 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 5, 7, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {2, 3, 5, 7, 8} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 5, 8, 9} ∨
        polygon = {2, 3, 5, 8, 10} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 7, 8, 9} ∨
        polygon = {2, 3, 7, 8, 10} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 3, 8, 9, 10} ∨
        polygon = {2, 5, 7, 8, 9} ∨
        polygon = {2, 5, 7, 8, 10} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {2, 5, 8, 9, 10} ∨
        polygon = {2, 7, 8, 9, 10} ∨
        polygon = {3, 5, 7, 8, 9} ∨
        polygon = {3, 5, 7, 8, 10} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {3, 5, 8, 9, 10} ∨
        polygon = {3, 7, 8, 9, 10} ∨
        polygon = {5, 7, 8, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 5, 7, 8, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 5, 7, 8, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 5, 7, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 5, 7, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 5, 7, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 5, 7, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 5, 7, 8, 9, 10} \ {x, y} := by
    calc
      polygon = {2, 3, 5, 7, 8, 9, 10} \ ({2, 3, 5, 7, 8, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 5, 7, 8, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5036 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 5, 7, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 5, 7, 8} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 5, 8, 9} ∨
        polygon = {2, 3, 5, 8, 12} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 7, 8, 9} ∨
        polygon = {2, 3, 7, 8, 12} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 3, 8, 9, 12} ∨
        polygon = {2, 5, 7, 8, 9} ∨
        polygon = {2, 5, 7, 8, 12} ∨
        polygon = {2, 5, 7, 9, 12} ∨
        polygon = {2, 5, 8, 9, 12} ∨
        polygon = {2, 7, 8, 9, 12} ∨
        polygon = {3, 5, 7, 8, 9} ∨
        polygon = {3, 5, 7, 8, 12} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {3, 5, 8, 9, 12} ∨
        polygon = {3, 7, 8, 9, 12} ∨
        polygon = {5, 7, 8, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 5, 7, 8, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 5, 7, 8, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 5, 7, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 5, 7, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 5, 7, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 5, 7, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 5, 7, 8, 9, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 5, 7, 8, 9, 12} \ ({2, 3, 5, 7, 8, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 5, 7, 8, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3500 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 5, 7, 8, 10, 11} →
      polygon.card = 5 →
        polygon = {2, 3, 5, 7, 8} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 5, 7, 11} ∨
        polygon = {2, 3, 5, 8, 10} ∨
        polygon = {2, 3, 5, 8, 11} ∨
        polygon = {2, 3, 5, 10, 11} ∨
        polygon = {2, 3, 7, 8, 10} ∨
        polygon = {2, 3, 7, 8, 11} ∨
        polygon = {2, 3, 7, 10, 11} ∨
        polygon = {2, 3, 8, 10, 11} ∨
        polygon = {2, 5, 7, 8, 10} ∨
        polygon = {2, 5, 7, 8, 11} ∨
        polygon = {2, 5, 7, 10, 11} ∨
        polygon = {2, 5, 8, 10, 11} ∨
        polygon = {2, 7, 8, 10, 11} ∨
        polygon = {3, 5, 7, 8, 10} ∨
        polygon = {3, 5, 7, 8, 11} ∨
        polygon = {3, 5, 7, 10, 11} ∨
        polygon = {3, 5, 8, 10, 11} ∨
        polygon = {3, 7, 8, 10, 11} ∨
        polygon = {5, 7, 8, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 5, 7, 8, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 5, 7, 8, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 5, 7, 8, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 5, 7, 8, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 5, 7, 8, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 5, 7, 8, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 5, 7, 8, 10, 11} \ {x, y} := by
    calc
      polygon = {2, 3, 5, 7, 8, 10, 11} \ ({2, 3, 5, 7, 8, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 5, 7, 8, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5548 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 5, 7, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 5, 7, 8} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 5, 8, 10} ∨
        polygon = {2, 3, 5, 8, 12} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 7, 8, 10} ∨
        polygon = {2, 3, 7, 8, 12} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {2, 3, 8, 10, 12} ∨
        polygon = {2, 5, 7, 8, 10} ∨
        polygon = {2, 5, 7, 8, 12} ∨
        polygon = {2, 5, 7, 10, 12} ∨
        polygon = {2, 5, 8, 10, 12} ∨
        polygon = {2, 7, 8, 10, 12} ∨
        polygon = {3, 5, 7, 8, 10} ∨
        polygon = {3, 5, 7, 8, 12} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {3, 5, 8, 10, 12} ∨
        polygon = {3, 7, 8, 10, 12} ∨
        polygon = {5, 7, 8, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 5, 7, 8, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 5, 7, 8, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 5, 7, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 5, 7, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 5, 7, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 5, 7, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 5, 7, 8, 10, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 5, 7, 8, 10, 12} \ ({2, 3, 5, 7, 8, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 5, 7, 8, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3756 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 5, 7, 9, 10, 11} →
      polygon.card = 5 →
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 5, 7, 11} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 5, 9, 11} ∨
        polygon = {2, 3, 5, 10, 11} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 3, 7, 9, 11} ∨
        polygon = {2, 3, 7, 10, 11} ∨
        polygon = {2, 3, 9, 10, 11} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {2, 5, 7, 9, 11} ∨
        polygon = {2, 5, 7, 10, 11} ∨
        polygon = {2, 5, 9, 10, 11} ∨
        polygon = {2, 7, 9, 10, 11} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {3, 5, 7, 9, 11} ∨
        polygon = {3, 5, 7, 10, 11} ∨
        polygon = {3, 5, 9, 10, 11} ∨
        polygon = {3, 7, 9, 10, 11} ∨
        polygon = {5, 7, 9, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 5, 7, 9, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 5, 7, 9, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 5, 7, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 5, 7, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 5, 7, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 5, 7, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 5, 7, 9, 10, 11} \ {x, y} := by
    calc
      polygon = {2, 3, 5, 7, 9, 10, 11} \ ({2, 3, 5, 7, 9, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 5, 7, 9, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5804 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 5, 7, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {2, 3, 9, 10, 12} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {2, 5, 7, 9, 12} ∨
        polygon = {2, 5, 7, 10, 12} ∨
        polygon = {2, 5, 9, 10, 12} ∨
        polygon = {2, 7, 9, 10, 12} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {5, 7, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 5, 7, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 5, 7, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 5, 7, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 5, 7, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 5, 7, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 5, 7, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 5, 7, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 5, 7, 9, 10, 12} \ ({2, 3, 5, 7, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 5, 7, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask6828 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 5, 7, 9, 11, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {2, 3, 5, 7, 11} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 5, 9, 11} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 5, 11, 12} ∨
        polygon = {2, 3, 7, 9, 11} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 3, 7, 11, 12} ∨
        polygon = {2, 3, 9, 11, 12} ∨
        polygon = {2, 5, 7, 9, 11} ∨
        polygon = {2, 5, 7, 9, 12} ∨
        polygon = {2, 5, 7, 11, 12} ∨
        polygon = {2, 5, 9, 11, 12} ∨
        polygon = {2, 7, 9, 11, 12} ∨
        polygon = {3, 5, 7, 9, 11} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {3, 5, 7, 11, 12} ∨
        polygon = {3, 5, 9, 11, 12} ∨
        polygon = {3, 7, 9, 11, 12} ∨
        polygon = {5, 7, 9, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 5, 7, 9, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 5, 7, 9, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 5, 7, 9, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 5, 7, 9, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 5, 7, 9, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 5, 7, 9, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 5, 7, 9, 11, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 5, 7, 9, 11, 12} \ ({2, 3, 5, 7, 9, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 5, 7, 9, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask7340 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 5, 7, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 5, 7, 11} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 5, 10, 11} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 5, 11, 12} ∨
        polygon = {2, 3, 7, 10, 11} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {2, 3, 7, 11, 12} ∨
        polygon = {2, 3, 10, 11, 12} ∨
        polygon = {2, 5, 7, 10, 11} ∨
        polygon = {2, 5, 7, 10, 12} ∨
        polygon = {2, 5, 7, 11, 12} ∨
        polygon = {2, 5, 10, 11, 12} ∨
        polygon = {2, 7, 10, 11, 12} ∨
        polygon = {3, 5, 7, 10, 11} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {3, 5, 7, 11, 12} ∨
        polygon = {3, 5, 10, 11, 12} ∨
        polygon = {3, 7, 10, 11, 12} ∨
        polygon = {5, 7, 10, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 5, 7, 10, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 5, 7, 10, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 5, 7, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 5, 7, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 5, 7, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 5, 7, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 5, 7, 10, 11, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 5, 7, 10, 11, 12} \ ({2, 3, 5, 7, 10, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 5, 7, 10, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3884 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 5, 8, 9, 10, 11} →
      polygon.card = 5 →
        polygon = {2, 3, 5, 8, 9} ∨
        polygon = {2, 3, 5, 8, 10} ∨
        polygon = {2, 3, 5, 8, 11} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 5, 9, 11} ∨
        polygon = {2, 3, 5, 10, 11} ∨
        polygon = {2, 3, 8, 9, 10} ∨
        polygon = {2, 3, 8, 9, 11} ∨
        polygon = {2, 3, 8, 10, 11} ∨
        polygon = {2, 3, 9, 10, 11} ∨
        polygon = {2, 5, 8, 9, 10} ∨
        polygon = {2, 5, 8, 9, 11} ∨
        polygon = {2, 5, 8, 10, 11} ∨
        polygon = {2, 5, 9, 10, 11} ∨
        polygon = {2, 8, 9, 10, 11} ∨
        polygon = {3, 5, 8, 9, 10} ∨
        polygon = {3, 5, 8, 9, 11} ∨
        polygon = {3, 5, 8, 10, 11} ∨
        polygon = {3, 5, 9, 10, 11} ∨
        polygon = {3, 8, 9, 10, 11} ∨
        polygon = {5, 8, 9, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 5, 8, 9, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 5, 8, 9, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 5, 8, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 5, 8, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 5, 8, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 5, 8, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 5, 8, 9, 10, 11} \ {x, y} := by
    calc
      polygon = {2, 3, 5, 8, 9, 10, 11} \ ({2, 3, 5, 8, 9, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 5, 8, 9, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5932 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 5, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 5, 8, 9} ∨
        polygon = {2, 3, 5, 8, 10} ∨
        polygon = {2, 3, 5, 8, 12} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 8, 9, 10} ∨
        polygon = {2, 3, 8, 9, 12} ∨
        polygon = {2, 3, 8, 10, 12} ∨
        polygon = {2, 3, 9, 10, 12} ∨
        polygon = {2, 5, 8, 9, 10} ∨
        polygon = {2, 5, 8, 9, 12} ∨
        polygon = {2, 5, 8, 10, 12} ∨
        polygon = {2, 5, 9, 10, 12} ∨
        polygon = {2, 8, 9, 10, 12} ∨
        polygon = {3, 5, 8, 9, 10} ∨
        polygon = {3, 5, 8, 9, 12} ∨
        polygon = {3, 5, 8, 10, 12} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 8, 9, 10, 12} ∨
        polygon = {5, 8, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 5, 8, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 5, 8, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 5, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 5, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 5, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 5, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 5, 8, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 5, 8, 9, 10, 12} \ ({2, 3, 5, 8, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 5, 8, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask7724 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 5, 9, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 5, 9, 11} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 5, 10, 11} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 5, 11, 12} ∨
        polygon = {2, 3, 9, 10, 11} ∨
        polygon = {2, 3, 9, 10, 12} ∨
        polygon = {2, 3, 9, 11, 12} ∨
        polygon = {2, 3, 10, 11, 12} ∨
        polygon = {2, 5, 9, 10, 11} ∨
        polygon = {2, 5, 9, 10, 12} ∨
        polygon = {2, 5, 9, 11, 12} ∨
        polygon = {2, 5, 10, 11, 12} ∨
        polygon = {2, 9, 10, 11, 12} ∨
        polygon = {3, 5, 9, 10, 11} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 5, 9, 11, 12} ∨
        polygon = {3, 5, 10, 11, 12} ∨
        polygon = {3, 9, 10, 11, 12} ∨
        polygon = {5, 9, 10, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 5, 9, 10, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 5, 9, 10, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 5, 9, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 5, 9, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 5, 9, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 5, 9, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 5, 9, 10, 11, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 5, 9, 10, 11, 12} \ ({2, 3, 5, 9, 10, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 5, 9, 10, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1996 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 6, 7, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {2, 3, 6, 7, 8} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {2, 3, 6, 8, 9} ∨
        polygon = {2, 3, 6, 8, 10} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {2, 3, 7, 8, 9} ∨
        polygon = {2, 3, 7, 8, 10} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 3, 8, 9, 10} ∨
        polygon = {2, 6, 7, 8, 9} ∨
        polygon = {2, 6, 7, 8, 10} ∨
        polygon = {2, 6, 7, 9, 10} ∨
        polygon = {2, 6, 8, 9, 10} ∨
        polygon = {2, 7, 8, 9, 10} ∨
        polygon = {3, 6, 7, 8, 9} ∨
        polygon = {3, 6, 7, 8, 10} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {3, 6, 8, 9, 10} ∨
        polygon = {3, 7, 8, 9, 10} ∨
        polygon = {6, 7, 8, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 6, 7, 8, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 6, 7, 8, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 6, 7, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 6, 7, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 6, 7, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 6, 7, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 6, 7, 8, 9, 10} \ {x, y} := by
    calc
      polygon = {2, 3, 6, 7, 8, 9, 10} \ ({2, 3, 6, 7, 8, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 6, 7, 8, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3020 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 6, 7, 8, 9, 11} →
      polygon.card = 5 →
        polygon = {2, 3, 6, 7, 8} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {2, 3, 6, 7, 11} ∨
        polygon = {2, 3, 6, 8, 9} ∨
        polygon = {2, 3, 6, 8, 11} ∨
        polygon = {2, 3, 6, 9, 11} ∨
        polygon = {2, 3, 7, 8, 9} ∨
        polygon = {2, 3, 7, 8, 11} ∨
        polygon = {2, 3, 7, 9, 11} ∨
        polygon = {2, 3, 8, 9, 11} ∨
        polygon = {2, 6, 7, 8, 9} ∨
        polygon = {2, 6, 7, 8, 11} ∨
        polygon = {2, 6, 7, 9, 11} ∨
        polygon = {2, 6, 8, 9, 11} ∨
        polygon = {2, 7, 8, 9, 11} ∨
        polygon = {3, 6, 7, 8, 9} ∨
        polygon = {3, 6, 7, 8, 11} ∨
        polygon = {3, 6, 7, 9, 11} ∨
        polygon = {3, 6, 8, 9, 11} ∨
        polygon = {3, 7, 8, 9, 11} ∨
        polygon = {6, 7, 8, 9, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 6, 7, 8, 9, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 6, 7, 8, 9, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 6, 7, 8, 9, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 6, 7, 8, 9, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 6, 7, 8, 9, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 6, 7, 8, 9, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 6, 7, 8, 9, 11} \ {x, y} := by
    calc
      polygon = {2, 3, 6, 7, 8, 9, 11} \ ({2, 3, 6, 7, 8, 9, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 6, 7, 8, 9, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5068 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 6, 7, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 6, 7, 8} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {2, 3, 6, 7, 12} ∨
        polygon = {2, 3, 6, 8, 9} ∨
        polygon = {2, 3, 6, 8, 12} ∨
        polygon = {2, 3, 6, 9, 12} ∨
        polygon = {2, 3, 7, 8, 9} ∨
        polygon = {2, 3, 7, 8, 12} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 3, 8, 9, 12} ∨
        polygon = {2, 6, 7, 8, 9} ∨
        polygon = {2, 6, 7, 8, 12} ∨
        polygon = {2, 6, 7, 9, 12} ∨
        polygon = {2, 6, 8, 9, 12} ∨
        polygon = {2, 7, 8, 9, 12} ∨
        polygon = {3, 6, 7, 8, 9} ∨
        polygon = {3, 6, 7, 8, 12} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {3, 6, 8, 9, 12} ∨
        polygon = {3, 7, 8, 9, 12} ∨
        polygon = {6, 7, 8, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 6, 7, 8, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 6, 7, 8, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 6, 7, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 6, 7, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 6, 7, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 6, 7, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 6, 7, 8, 9, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 6, 7, 8, 9, 12} \ ({2, 3, 6, 7, 8, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 6, 7, 8, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3532 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 6, 7, 8, 10, 11} →
      polygon.card = 5 →
        polygon = {2, 3, 6, 7, 8} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {2, 3, 6, 7, 11} ∨
        polygon = {2, 3, 6, 8, 10} ∨
        polygon = {2, 3, 6, 8, 11} ∨
        polygon = {2, 3, 6, 10, 11} ∨
        polygon = {2, 3, 7, 8, 10} ∨
        polygon = {2, 3, 7, 8, 11} ∨
        polygon = {2, 3, 7, 10, 11} ∨
        polygon = {2, 3, 8, 10, 11} ∨
        polygon = {2, 6, 7, 8, 10} ∨
        polygon = {2, 6, 7, 8, 11} ∨
        polygon = {2, 6, 7, 10, 11} ∨
        polygon = {2, 6, 8, 10, 11} ∨
        polygon = {2, 7, 8, 10, 11} ∨
        polygon = {3, 6, 7, 8, 10} ∨
        polygon = {3, 6, 7, 8, 11} ∨
        polygon = {3, 6, 7, 10, 11} ∨
        polygon = {3, 6, 8, 10, 11} ∨
        polygon = {3, 7, 8, 10, 11} ∨
        polygon = {6, 7, 8, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 6, 7, 8, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 6, 7, 8, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 6, 7, 8, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 6, 7, 8, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 6, 7, 8, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 6, 7, 8, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 6, 7, 8, 10, 11} \ {x, y} := by
    calc
      polygon = {2, 3, 6, 7, 8, 10, 11} \ ({2, 3, 6, 7, 8, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 6, 7, 8, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5580 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 6, 7, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 6, 7, 8} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {2, 3, 6, 7, 12} ∨
        polygon = {2, 3, 6, 8, 10} ∨
        polygon = {2, 3, 6, 8, 12} ∨
        polygon = {2, 3, 6, 10, 12} ∨
        polygon = {2, 3, 7, 8, 10} ∨
        polygon = {2, 3, 7, 8, 12} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {2, 3, 8, 10, 12} ∨
        polygon = {2, 6, 7, 8, 10} ∨
        polygon = {2, 6, 7, 8, 12} ∨
        polygon = {2, 6, 7, 10, 12} ∨
        polygon = {2, 6, 8, 10, 12} ∨
        polygon = {2, 7, 8, 10, 12} ∨
        polygon = {3, 6, 7, 8, 10} ∨
        polygon = {3, 6, 7, 8, 12} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {3, 6, 8, 10, 12} ∨
        polygon = {3, 7, 8, 10, 12} ∨
        polygon = {6, 7, 8, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 6, 7, 8, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 6, 7, 8, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 6, 7, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 6, 7, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 6, 7, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 6, 7, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 6, 7, 8, 10, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 6, 7, 8, 10, 12} \ ({2, 3, 6, 7, 8, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 6, 7, 8, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask6604 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 6, 7, 8, 11, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 6, 7, 8} ∨
        polygon = {2, 3, 6, 7, 11} ∨
        polygon = {2, 3, 6, 7, 12} ∨
        polygon = {2, 3, 6, 8, 11} ∨
        polygon = {2, 3, 6, 8, 12} ∨
        polygon = {2, 3, 6, 11, 12} ∨
        polygon = {2, 3, 7, 8, 11} ∨
        polygon = {2, 3, 7, 8, 12} ∨
        polygon = {2, 3, 7, 11, 12} ∨
        polygon = {2, 3, 8, 11, 12} ∨
        polygon = {2, 6, 7, 8, 11} ∨
        polygon = {2, 6, 7, 8, 12} ∨
        polygon = {2, 6, 7, 11, 12} ∨
        polygon = {2, 6, 8, 11, 12} ∨
        polygon = {2, 7, 8, 11, 12} ∨
        polygon = {3, 6, 7, 8, 11} ∨
        polygon = {3, 6, 7, 8, 12} ∨
        polygon = {3, 6, 7, 11, 12} ∨
        polygon = {3, 6, 8, 11, 12} ∨
        polygon = {3, 7, 8, 11, 12} ∨
        polygon = {6, 7, 8, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 6, 7, 8, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 6, 7, 8, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 6, 7, 8, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 6, 7, 8, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 6, 7, 8, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 6, 7, 8, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 6, 7, 8, 11, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 6, 7, 8, 11, 12} \ ({2, 3, 6, 7, 8, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 6, 7, 8, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3788 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 6, 7, 9, 10, 11} →
      polygon.card = 5 →
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {2, 3, 6, 7, 11} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {2, 3, 6, 9, 11} ∨
        polygon = {2, 3, 6, 10, 11} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 3, 7, 9, 11} ∨
        polygon = {2, 3, 7, 10, 11} ∨
        polygon = {2, 3, 9, 10, 11} ∨
        polygon = {2, 6, 7, 9, 10} ∨
        polygon = {2, 6, 7, 9, 11} ∨
        polygon = {2, 6, 7, 10, 11} ∨
        polygon = {2, 6, 9, 10, 11} ∨
        polygon = {2, 7, 9, 10, 11} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {3, 6, 7, 9, 11} ∨
        polygon = {3, 6, 7, 10, 11} ∨
        polygon = {3, 6, 9, 10, 11} ∨
        polygon = {3, 7, 9, 10, 11} ∨
        polygon = {6, 7, 9, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 6, 7, 9, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 6, 7, 9, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 6, 7, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 6, 7, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 6, 7, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 6, 7, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 6, 7, 9, 10, 11} \ {x, y} := by
    calc
      polygon = {2, 3, 6, 7, 9, 10, 11} \ ({2, 3, 6, 7, 9, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 6, 7, 9, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5836 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 6, 7, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {2, 3, 6, 7, 12} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {2, 3, 6, 9, 12} ∨
        polygon = {2, 3, 6, 10, 12} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {2, 3, 9, 10, 12} ∨
        polygon = {2, 6, 7, 9, 10} ∨
        polygon = {2, 6, 7, 9, 12} ∨
        polygon = {2, 6, 7, 10, 12} ∨
        polygon = {2, 6, 9, 10, 12} ∨
        polygon = {2, 7, 9, 10, 12} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {6, 7, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 6, 7, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 6, 7, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 6, 7, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 6, 7, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 6, 7, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 6, 7, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 6, 7, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 6, 7, 9, 10, 12} \ ({2, 3, 6, 7, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 6, 7, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask6860 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 6, 7, 9, 11, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {2, 3, 6, 7, 11} ∨
        polygon = {2, 3, 6, 7, 12} ∨
        polygon = {2, 3, 6, 9, 11} ∨
        polygon = {2, 3, 6, 9, 12} ∨
        polygon = {2, 3, 6, 11, 12} ∨
        polygon = {2, 3, 7, 9, 11} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 3, 7, 11, 12} ∨
        polygon = {2, 3, 9, 11, 12} ∨
        polygon = {2, 6, 7, 9, 11} ∨
        polygon = {2, 6, 7, 9, 12} ∨
        polygon = {2, 6, 7, 11, 12} ∨
        polygon = {2, 6, 9, 11, 12} ∨
        polygon = {2, 7, 9, 11, 12} ∨
        polygon = {3, 6, 7, 9, 11} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {3, 6, 7, 11, 12} ∨
        polygon = {3, 6, 9, 11, 12} ∨
        polygon = {3, 7, 9, 11, 12} ∨
        polygon = {6, 7, 9, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 6, 7, 9, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 6, 7, 9, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 6, 7, 9, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 6, 7, 9, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 6, 7, 9, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 6, 7, 9, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 6, 7, 9, 11, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 6, 7, 9, 11, 12} \ ({2, 3, 6, 7, 9, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 6, 7, 9, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5964 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 6, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 6, 8, 9} ∨
        polygon = {2, 3, 6, 8, 10} ∨
        polygon = {2, 3, 6, 8, 12} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {2, 3, 6, 9, 12} ∨
        polygon = {2, 3, 6, 10, 12} ∨
        polygon = {2, 3, 8, 9, 10} ∨
        polygon = {2, 3, 8, 9, 12} ∨
        polygon = {2, 3, 8, 10, 12} ∨
        polygon = {2, 3, 9, 10, 12} ∨
        polygon = {2, 6, 8, 9, 10} ∨
        polygon = {2, 6, 8, 9, 12} ∨
        polygon = {2, 6, 8, 10, 12} ∨
        polygon = {2, 6, 9, 10, 12} ∨
        polygon = {2, 8, 9, 10, 12} ∨
        polygon = {3, 6, 8, 9, 10} ∨
        polygon = {3, 6, 8, 9, 12} ∨
        polygon = {3, 6, 8, 10, 12} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {3, 8, 9, 10, 12} ∨
        polygon = {6, 8, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 6, 8, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 6, 8, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 6, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 6, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 6, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 6, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 6, 8, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 6, 8, 9, 10, 12} \ ({2, 3, 6, 8, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 6, 8, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3980 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 7, 8, 9, 10, 11} →
      polygon.card = 5 →
        polygon = {2, 3, 7, 8, 9} ∨
        polygon = {2, 3, 7, 8, 10} ∨
        polygon = {2, 3, 7, 8, 11} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 3, 7, 9, 11} ∨
        polygon = {2, 3, 7, 10, 11} ∨
        polygon = {2, 3, 8, 9, 10} ∨
        polygon = {2, 3, 8, 9, 11} ∨
        polygon = {2, 3, 8, 10, 11} ∨
        polygon = {2, 3, 9, 10, 11} ∨
        polygon = {2, 7, 8, 9, 10} ∨
        polygon = {2, 7, 8, 9, 11} ∨
        polygon = {2, 7, 8, 10, 11} ∨
        polygon = {2, 7, 9, 10, 11} ∨
        polygon = {2, 8, 9, 10, 11} ∨
        polygon = {3, 7, 8, 9, 10} ∨
        polygon = {3, 7, 8, 9, 11} ∨
        polygon = {3, 7, 8, 10, 11} ∨
        polygon = {3, 7, 9, 10, 11} ∨
        polygon = {3, 8, 9, 10, 11} ∨
        polygon = {7, 8, 9, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 7, 8, 9, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 7, 8, 9, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 7, 8, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 7, 8, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 7, 8, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 7, 8, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 7, 8, 9, 10, 11} \ {x, y} := by
    calc
      polygon = {2, 3, 7, 8, 9, 10, 11} \ ({2, 3, 7, 8, 9, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 7, 8, 9, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask6028 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 7, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 7, 8, 9} ∨
        polygon = {2, 3, 7, 8, 10} ∨
        polygon = {2, 3, 7, 8, 12} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {2, 3, 8, 9, 10} ∨
        polygon = {2, 3, 8, 9, 12} ∨
        polygon = {2, 3, 8, 10, 12} ∨
        polygon = {2, 3, 9, 10, 12} ∨
        polygon = {2, 7, 8, 9, 10} ∨
        polygon = {2, 7, 8, 9, 12} ∨
        polygon = {2, 7, 8, 10, 12} ∨
        polygon = {2, 7, 9, 10, 12} ∨
        polygon = {2, 8, 9, 10, 12} ∨
        polygon = {3, 7, 8, 9, 10} ∨
        polygon = {3, 7, 8, 9, 12} ∨
        polygon = {3, 7, 8, 10, 12} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {3, 8, 9, 10, 12} ∨
        polygon = {7, 8, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 7, 8, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 7, 8, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 7, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 7, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 7, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 7, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 7, 8, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 7, 8, 9, 10, 12} \ ({2, 3, 7, 8, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 7, 8, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask7052 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 7, 8, 9, 11, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 7, 8, 9} ∨
        polygon = {2, 3, 7, 8, 11} ∨
        polygon = {2, 3, 7, 8, 12} ∨
        polygon = {2, 3, 7, 9, 11} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 3, 7, 11, 12} ∨
        polygon = {2, 3, 8, 9, 11} ∨
        polygon = {2, 3, 8, 9, 12} ∨
        polygon = {2, 3, 8, 11, 12} ∨
        polygon = {2, 3, 9, 11, 12} ∨
        polygon = {2, 7, 8, 9, 11} ∨
        polygon = {2, 7, 8, 9, 12} ∨
        polygon = {2, 7, 8, 11, 12} ∨
        polygon = {2, 7, 9, 11, 12} ∨
        polygon = {2, 8, 9, 11, 12} ∨
        polygon = {3, 7, 8, 9, 11} ∨
        polygon = {3, 7, 8, 9, 12} ∨
        polygon = {3, 7, 8, 11, 12} ∨
        polygon = {3, 7, 9, 11, 12} ∨
        polygon = {3, 8, 9, 11, 12} ∨
        polygon = {7, 8, 9, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 7, 8, 9, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 7, 8, 9, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 7, 8, 9, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 7, 8, 9, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 7, 8, 9, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 7, 8, 9, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 7, 8, 9, 11, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 7, 8, 9, 11, 12} \ ({2, 3, 7, 8, 9, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 7, 8, 9, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask7564 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 7, 8, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 7, 8, 10} ∨
        polygon = {2, 3, 7, 8, 11} ∨
        polygon = {2, 3, 7, 8, 12} ∨
        polygon = {2, 3, 7, 10, 11} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {2, 3, 7, 11, 12} ∨
        polygon = {2, 3, 8, 10, 11} ∨
        polygon = {2, 3, 8, 10, 12} ∨
        polygon = {2, 3, 8, 11, 12} ∨
        polygon = {2, 3, 10, 11, 12} ∨
        polygon = {2, 7, 8, 10, 11} ∨
        polygon = {2, 7, 8, 10, 12} ∨
        polygon = {2, 7, 8, 11, 12} ∨
        polygon = {2, 7, 10, 11, 12} ∨
        polygon = {2, 8, 10, 11, 12} ∨
        polygon = {3, 7, 8, 10, 11} ∨
        polygon = {3, 7, 8, 10, 12} ∨
        polygon = {3, 7, 8, 11, 12} ∨
        polygon = {3, 7, 10, 11, 12} ∨
        polygon = {3, 8, 10, 11, 12} ∨
        polygon = {7, 8, 10, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 7, 8, 10, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 7, 8, 10, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 7, 8, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 7, 8, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 7, 8, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 7, 8, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 7, 8, 10, 11, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 7, 8, 10, 11, 12} \ ({2, 3, 7, 8, 10, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 7, 8, 10, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask7820 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 7, 9, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 3, 7, 9, 11} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 3, 7, 10, 11} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {2, 3, 7, 11, 12} ∨
        polygon = {2, 3, 9, 10, 11} ∨
        polygon = {2, 3, 9, 10, 12} ∨
        polygon = {2, 3, 9, 11, 12} ∨
        polygon = {2, 3, 10, 11, 12} ∨
        polygon = {2, 7, 9, 10, 11} ∨
        polygon = {2, 7, 9, 10, 12} ∨
        polygon = {2, 7, 9, 11, 12} ∨
        polygon = {2, 7, 10, 11, 12} ∨
        polygon = {2, 9, 10, 11, 12} ∨
        polygon = {3, 7, 9, 10, 11} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {3, 7, 9, 11, 12} ∨
        polygon = {3, 7, 10, 11, 12} ∨
        polygon = {3, 9, 10, 11, 12} ∨
        polygon = {7, 9, 10, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 7, 9, 10, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 7, 9, 10, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 7, 9, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 7, 9, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 7, 9, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 7, 9, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 7, 9, 10, 11, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 7, 9, 10, 11, 12} \ ({2, 3, 7, 9, 10, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 7, 9, 10, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1012 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 5, 6, 7, 8, 9} →
      polygon.card = 5 →
        polygon = {2, 4, 5, 6, 7} ∨
        polygon = {2, 4, 5, 6, 8} ∨
        polygon = {2, 4, 5, 6, 9} ∨
        polygon = {2, 4, 5, 7, 8} ∨
        polygon = {2, 4, 5, 7, 9} ∨
        polygon = {2, 4, 5, 8, 9} ∨
        polygon = {2, 4, 6, 7, 8} ∨
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {2, 4, 6, 8, 9} ∨
        polygon = {2, 4, 7, 8, 9} ∨
        polygon = {2, 5, 6, 7, 8} ∨
        polygon = {2, 5, 6, 7, 9} ∨
        polygon = {2, 5, 6, 8, 9} ∨
        polygon = {2, 5, 7, 8, 9} ∨
        polygon = {2, 6, 7, 8, 9} ∨
        polygon = {4, 5, 6, 7, 8} ∨
        polygon = {4, 5, 6, 7, 9} ∨
        polygon = {4, 5, 6, 8, 9} ∨
        polygon = {4, 5, 7, 8, 9} ∨
        polygon = {4, 6, 7, 8, 9} ∨
        polygon = {5, 6, 7, 8, 9} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 5, 6, 7, 8, 9} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 5, 6, 7, 8, 9} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 5, 6, 7, 8, 9} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 5, 6, 7, 8, 9} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 5, 6, 7, 8, 9} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 5, 6, 7, 8, 9} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 5, 6, 7, 8, 9} \ {x, y} := by
    calc
      polygon = {2, 4, 5, 6, 7, 8, 9} \ ({2, 4, 5, 6, 7, 8, 9} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 5, 6, 7, 8, 9} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1524 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 5, 6, 7, 8, 10} →
      polygon.card = 5 →
        polygon = {2, 4, 5, 6, 7} ∨
        polygon = {2, 4, 5, 6, 8} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {2, 4, 5, 7, 8} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {2, 4, 5, 8, 10} ∨
        polygon = {2, 4, 6, 7, 8} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {2, 4, 6, 8, 10} ∨
        polygon = {2, 4, 7, 8, 10} ∨
        polygon = {2, 5, 6, 7, 8} ∨
        polygon = {2, 5, 6, 7, 10} ∨
        polygon = {2, 5, 6, 8, 10} ∨
        polygon = {2, 5, 7, 8, 10} ∨
        polygon = {2, 6, 7, 8, 10} ∨
        polygon = {4, 5, 6, 7, 8} ∨
        polygon = {4, 5, 6, 7, 10} ∨
        polygon = {4, 5, 6, 8, 10} ∨
        polygon = {4, 5, 7, 8, 10} ∨
        polygon = {4, 6, 7, 8, 10} ∨
        polygon = {5, 6, 7, 8, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 5, 6, 7, 8, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 5, 6, 7, 8, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 5, 6, 7, 8, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 5, 6, 7, 8, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 5, 6, 7, 8, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 5, 6, 7, 8, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 5, 6, 7, 8, 10} \ {x, y} := by
    calc
      polygon = {2, 4, 5, 6, 7, 8, 10} \ ({2, 4, 5, 6, 7, 8, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 5, 6, 7, 8, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask2548 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 5, 6, 7, 8, 11} →
      polygon.card = 5 →
        polygon = {2, 4, 5, 6, 7} ∨
        polygon = {2, 4, 5, 6, 8} ∨
        polygon = {2, 4, 5, 6, 11} ∨
        polygon = {2, 4, 5, 7, 8} ∨
        polygon = {2, 4, 5, 7, 11} ∨
        polygon = {2, 4, 5, 8, 11} ∨
        polygon = {2, 4, 6, 7, 8} ∨
        polygon = {2, 4, 6, 7, 11} ∨
        polygon = {2, 4, 6, 8, 11} ∨
        polygon = {2, 4, 7, 8, 11} ∨
        polygon = {2, 5, 6, 7, 8} ∨
        polygon = {2, 5, 6, 7, 11} ∨
        polygon = {2, 5, 6, 8, 11} ∨
        polygon = {2, 5, 7, 8, 11} ∨
        polygon = {2, 6, 7, 8, 11} ∨
        polygon = {4, 5, 6, 7, 8} ∨
        polygon = {4, 5, 6, 7, 11} ∨
        polygon = {4, 5, 6, 8, 11} ∨
        polygon = {4, 5, 7, 8, 11} ∨
        polygon = {4, 6, 7, 8, 11} ∨
        polygon = {5, 6, 7, 8, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 5, 6, 7, 8, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 5, 6, 7, 8, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 5, 6, 7, 8, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 5, 6, 7, 8, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 5, 6, 7, 8, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 5, 6, 7, 8, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 5, 6, 7, 8, 11} \ {x, y} := by
    calc
      polygon = {2, 4, 5, 6, 7, 8, 11} \ ({2, 4, 5, 6, 7, 8, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 5, 6, 7, 8, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4596 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 5, 6, 7, 8, 12} →
      polygon.card = 5 →
        polygon = {2, 4, 5, 6, 7} ∨
        polygon = {2, 4, 5, 6, 8} ∨
        polygon = {2, 4, 5, 6, 12} ∨
        polygon = {2, 4, 5, 7, 8} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {2, 4, 5, 8, 12} ∨
        polygon = {2, 4, 6, 7, 8} ∨
        polygon = {2, 4, 6, 7, 12} ∨
        polygon = {2, 4, 6, 8, 12} ∨
        polygon = {2, 4, 7, 8, 12} ∨
        polygon = {2, 5, 6, 7, 8} ∨
        polygon = {2, 5, 6, 7, 12} ∨
        polygon = {2, 5, 6, 8, 12} ∨
        polygon = {2, 5, 7, 8, 12} ∨
        polygon = {2, 6, 7, 8, 12} ∨
        polygon = {4, 5, 6, 7, 8} ∨
        polygon = {4, 5, 6, 7, 12} ∨
        polygon = {4, 5, 6, 8, 12} ∨
        polygon = {4, 5, 7, 8, 12} ∨
        polygon = {4, 6, 7, 8, 12} ∨
        polygon = {5, 6, 7, 8, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 5, 6, 7, 8, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 5, 6, 7, 8, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 5, 6, 7, 8, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 5, 6, 7, 8, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 5, 6, 7, 8, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 5, 6, 7, 8, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 5, 6, 7, 8, 12} \ {x, y} := by
    calc
      polygon = {2, 4, 5, 6, 7, 8, 12} \ ({2, 4, 5, 6, 7, 8, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 5, 6, 7, 8, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1780 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 5, 6, 7, 9, 10} →
      polygon.card = 5 →
        polygon = {2, 4, 5, 6, 7} ∨
        polygon = {2, 4, 5, 6, 9} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {2, 4, 5, 7, 9} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {2, 5, 6, 7, 9} ∨
        polygon = {2, 5, 6, 7, 10} ∨
        polygon = {2, 5, 6, 9, 10} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {2, 6, 7, 9, 10} ∨
        polygon = {4, 5, 6, 7, 9} ∨
        polygon = {4, 5, 6, 7, 10} ∨
        polygon = {4, 5, 6, 9, 10} ∨
        polygon = {4, 5, 7, 9, 10} ∨
        polygon = {4, 6, 7, 9, 10} ∨
        polygon = {5, 6, 7, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 5, 6, 7, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 5, 6, 7, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 5, 6, 7, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 5, 6, 7, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 5, 6, 7, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 5, 6, 7, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 5, 6, 7, 9, 10} \ {x, y} := by
    calc
      polygon = {2, 4, 5, 6, 7, 9, 10} \ ({2, 4, 5, 6, 7, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 5, 6, 7, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask2804 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 5, 6, 7, 9, 11} →
      polygon.card = 5 →
        polygon = {2, 4, 5, 6, 7} ∨
        polygon = {2, 4, 5, 6, 9} ∨
        polygon = {2, 4, 5, 6, 11} ∨
        polygon = {2, 4, 5, 7, 9} ∨
        polygon = {2, 4, 5, 7, 11} ∨
        polygon = {2, 4, 5, 9, 11} ∨
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {2, 4, 6, 7, 11} ∨
        polygon = {2, 4, 6, 9, 11} ∨
        polygon = {2, 4, 7, 9, 11} ∨
        polygon = {2, 5, 6, 7, 9} ∨
        polygon = {2, 5, 6, 7, 11} ∨
        polygon = {2, 5, 6, 9, 11} ∨
        polygon = {2, 5, 7, 9, 11} ∨
        polygon = {2, 6, 7, 9, 11} ∨
        polygon = {4, 5, 6, 7, 9} ∨
        polygon = {4, 5, 6, 7, 11} ∨
        polygon = {4, 5, 6, 9, 11} ∨
        polygon = {4, 5, 7, 9, 11} ∨
        polygon = {4, 6, 7, 9, 11} ∨
        polygon = {5, 6, 7, 9, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 5, 6, 7, 9, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 5, 6, 7, 9, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 5, 6, 7, 9, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 5, 6, 7, 9, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 5, 6, 7, 9, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 5, 6, 7, 9, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 5, 6, 7, 9, 11} \ {x, y} := by
    calc
      polygon = {2, 4, 5, 6, 7, 9, 11} \ ({2, 4, 5, 6, 7, 9, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 5, 6, 7, 9, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4852 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 5, 6, 7, 9, 12} →
      polygon.card = 5 →
        polygon = {2, 4, 5, 6, 7} ∨
        polygon = {2, 4, 5, 6, 9} ∨
        polygon = {2, 4, 5, 6, 12} ∨
        polygon = {2, 4, 5, 7, 9} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {2, 4, 6, 7, 12} ∨
        polygon = {2, 4, 6, 9, 12} ∨
        polygon = {2, 4, 7, 9, 12} ∨
        polygon = {2, 5, 6, 7, 9} ∨
        polygon = {2, 5, 6, 7, 12} ∨
        polygon = {2, 5, 6, 9, 12} ∨
        polygon = {2, 5, 7, 9, 12} ∨
        polygon = {2, 6, 7, 9, 12} ∨
        polygon = {4, 5, 6, 7, 9} ∨
        polygon = {4, 5, 6, 7, 12} ∨
        polygon = {4, 5, 6, 9, 12} ∨
        polygon = {4, 5, 7, 9, 12} ∨
        polygon = {4, 6, 7, 9, 12} ∨
        polygon = {5, 6, 7, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 5, 6, 7, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 5, 6, 7, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 5, 6, 7, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 5, 6, 7, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 5, 6, 7, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 5, 6, 7, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 5, 6, 7, 9, 12} \ {x, y} := by
    calc
      polygon = {2, 4, 5, 6, 7, 9, 12} \ ({2, 4, 5, 6, 7, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 5, 6, 7, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3316 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 5, 6, 7, 10, 11} →
      polygon.card = 5 →
        polygon = {2, 4, 5, 6, 7} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {2, 4, 5, 6, 11} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {2, 4, 5, 7, 11} ∨
        polygon = {2, 4, 5, 10, 11} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {2, 4, 6, 7, 11} ∨
        polygon = {2, 4, 6, 10, 11} ∨
        polygon = {2, 4, 7, 10, 11} ∨
        polygon = {2, 5, 6, 7, 10} ∨
        polygon = {2, 5, 6, 7, 11} ∨
        polygon = {2, 5, 6, 10, 11} ∨
        polygon = {2, 5, 7, 10, 11} ∨
        polygon = {2, 6, 7, 10, 11} ∨
        polygon = {4, 5, 6, 7, 10} ∨
        polygon = {4, 5, 6, 7, 11} ∨
        polygon = {4, 5, 6, 10, 11} ∨
        polygon = {4, 5, 7, 10, 11} ∨
        polygon = {4, 6, 7, 10, 11} ∨
        polygon = {5, 6, 7, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 5, 6, 7, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 5, 6, 7, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 5, 6, 7, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 5, 6, 7, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 5, 6, 7, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 5, 6, 7, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 5, 6, 7, 10, 11} \ {x, y} := by
    calc
      polygon = {2, 4, 5, 6, 7, 10, 11} \ ({2, 4, 5, 6, 7, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 5, 6, 7, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5364 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 5, 6, 7, 10, 12} →
      polygon.card = 5 →
        polygon = {2, 4, 5, 6, 7} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {2, 4, 5, 6, 12} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {2, 4, 6, 7, 12} ∨
        polygon = {2, 4, 6, 10, 12} ∨
        polygon = {2, 4, 7, 10, 12} ∨
        polygon = {2, 5, 6, 7, 10} ∨
        polygon = {2, 5, 6, 7, 12} ∨
        polygon = {2, 5, 6, 10, 12} ∨
        polygon = {2, 5, 7, 10, 12} ∨
        polygon = {2, 6, 7, 10, 12} ∨
        polygon = {4, 5, 6, 7, 10} ∨
        polygon = {4, 5, 6, 7, 12} ∨
        polygon = {4, 5, 6, 10, 12} ∨
        polygon = {4, 5, 7, 10, 12} ∨
        polygon = {4, 6, 7, 10, 12} ∨
        polygon = {5, 6, 7, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 5, 6, 7, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 5, 6, 7, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 5, 6, 7, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 5, 6, 7, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 5, 6, 7, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 5, 6, 7, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 5, 6, 7, 10, 12} \ {x, y} := by
    calc
      polygon = {2, 4, 5, 6, 7, 10, 12} \ ({2, 4, 5, 6, 7, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 5, 6, 7, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1908 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 5, 6, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {2, 4, 5, 6, 8} ∨
        polygon = {2, 4, 5, 6, 9} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {2, 4, 5, 8, 9} ∨
        polygon = {2, 4, 5, 8, 10} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {2, 4, 6, 8, 9} ∨
        polygon = {2, 4, 6, 8, 10} ∨
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {2, 4, 8, 9, 10} ∨
        polygon = {2, 5, 6, 8, 9} ∨
        polygon = {2, 5, 6, 8, 10} ∨
        polygon = {2, 5, 6, 9, 10} ∨
        polygon = {2, 5, 8, 9, 10} ∨
        polygon = {2, 6, 8, 9, 10} ∨
        polygon = {4, 5, 6, 8, 9} ∨
        polygon = {4, 5, 6, 8, 10} ∨
        polygon = {4, 5, 6, 9, 10} ∨
        polygon = {4, 5, 8, 9, 10} ∨
        polygon = {4, 6, 8, 9, 10} ∨
        polygon = {5, 6, 8, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 5, 6, 8, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 5, 6, 8, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 5, 6, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 5, 6, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 5, 6, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 5, 6, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 5, 6, 8, 9, 10} \ {x, y} := by
    calc
      polygon = {2, 4, 5, 6, 8, 9, 10} \ ({2, 4, 5, 6, 8, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 5, 6, 8, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask2932 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 5, 6, 8, 9, 11} →
      polygon.card = 5 →
        polygon = {2, 4, 5, 6, 8} ∨
        polygon = {2, 4, 5, 6, 9} ∨
        polygon = {2, 4, 5, 6, 11} ∨
        polygon = {2, 4, 5, 8, 9} ∨
        polygon = {2, 4, 5, 8, 11} ∨
        polygon = {2, 4, 5, 9, 11} ∨
        polygon = {2, 4, 6, 8, 9} ∨
        polygon = {2, 4, 6, 8, 11} ∨
        polygon = {2, 4, 6, 9, 11} ∨
        polygon = {2, 4, 8, 9, 11} ∨
        polygon = {2, 5, 6, 8, 9} ∨
        polygon = {2, 5, 6, 8, 11} ∨
        polygon = {2, 5, 6, 9, 11} ∨
        polygon = {2, 5, 8, 9, 11} ∨
        polygon = {2, 6, 8, 9, 11} ∨
        polygon = {4, 5, 6, 8, 9} ∨
        polygon = {4, 5, 6, 8, 11} ∨
        polygon = {4, 5, 6, 9, 11} ∨
        polygon = {4, 5, 8, 9, 11} ∨
        polygon = {4, 6, 8, 9, 11} ∨
        polygon = {5, 6, 8, 9, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 5, 6, 8, 9, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 5, 6, 8, 9, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 5, 6, 8, 9, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 5, 6, 8, 9, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 5, 6, 8, 9, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 5, 6, 8, 9, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 5, 6, 8, 9, 11} \ {x, y} := by
    calc
      polygon = {2, 4, 5, 6, 8, 9, 11} \ ({2, 4, 5, 6, 8, 9, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 5, 6, 8, 9, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4980 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 5, 6, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {2, 4, 5, 6, 8} ∨
        polygon = {2, 4, 5, 6, 9} ∨
        polygon = {2, 4, 5, 6, 12} ∨
        polygon = {2, 4, 5, 8, 9} ∨
        polygon = {2, 4, 5, 8, 12} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {2, 4, 6, 8, 9} ∨
        polygon = {2, 4, 6, 8, 12} ∨
        polygon = {2, 4, 6, 9, 12} ∨
        polygon = {2, 4, 8, 9, 12} ∨
        polygon = {2, 5, 6, 8, 9} ∨
        polygon = {2, 5, 6, 8, 12} ∨
        polygon = {2, 5, 6, 9, 12} ∨
        polygon = {2, 5, 8, 9, 12} ∨
        polygon = {2, 6, 8, 9, 12} ∨
        polygon = {4, 5, 6, 8, 9} ∨
        polygon = {4, 5, 6, 8, 12} ∨
        polygon = {4, 5, 6, 9, 12} ∨
        polygon = {4, 5, 8, 9, 12} ∨
        polygon = {4, 6, 8, 9, 12} ∨
        polygon = {5, 6, 8, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 5, 6, 8, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 5, 6, 8, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 5, 6, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 5, 6, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 5, 6, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 5, 6, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 5, 6, 8, 9, 12} \ {x, y} := by
    calc
      polygon = {2, 4, 5, 6, 8, 9, 12} \ ({2, 4, 5, 6, 8, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 5, 6, 8, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3444 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 5, 6, 8, 10, 11} →
      polygon.card = 5 →
        polygon = {2, 4, 5, 6, 8} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {2, 4, 5, 6, 11} ∨
        polygon = {2, 4, 5, 8, 10} ∨
        polygon = {2, 4, 5, 8, 11} ∨
        polygon = {2, 4, 5, 10, 11} ∨
        polygon = {2, 4, 6, 8, 10} ∨
        polygon = {2, 4, 6, 8, 11} ∨
        polygon = {2, 4, 6, 10, 11} ∨
        polygon = {2, 4, 8, 10, 11} ∨
        polygon = {2, 5, 6, 8, 10} ∨
        polygon = {2, 5, 6, 8, 11} ∨
        polygon = {2, 5, 6, 10, 11} ∨
        polygon = {2, 5, 8, 10, 11} ∨
        polygon = {2, 6, 8, 10, 11} ∨
        polygon = {4, 5, 6, 8, 10} ∨
        polygon = {4, 5, 6, 8, 11} ∨
        polygon = {4, 5, 6, 10, 11} ∨
        polygon = {4, 5, 8, 10, 11} ∨
        polygon = {4, 6, 8, 10, 11} ∨
        polygon = {5, 6, 8, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 5, 6, 8, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 5, 6, 8, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 5, 6, 8, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 5, 6, 8, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 5, 6, 8, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 5, 6, 8, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 5, 6, 8, 10, 11} \ {x, y} := by
    calc
      polygon = {2, 4, 5, 6, 8, 10, 11} \ ({2, 4, 5, 6, 8, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 5, 6, 8, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5492 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 5, 6, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {2, 4, 5, 6, 8} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {2, 4, 5, 6, 12} ∨
        polygon = {2, 4, 5, 8, 10} ∨
        polygon = {2, 4, 5, 8, 12} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {2, 4, 6, 8, 10} ∨
        polygon = {2, 4, 6, 8, 12} ∨
        polygon = {2, 4, 6, 10, 12} ∨
        polygon = {2, 4, 8, 10, 12} ∨
        polygon = {2, 5, 6, 8, 10} ∨
        polygon = {2, 5, 6, 8, 12} ∨
        polygon = {2, 5, 6, 10, 12} ∨
        polygon = {2, 5, 8, 10, 12} ∨
        polygon = {2, 6, 8, 10, 12} ∨
        polygon = {4, 5, 6, 8, 10} ∨
        polygon = {4, 5, 6, 8, 12} ∨
        polygon = {4, 5, 6, 10, 12} ∨
        polygon = {4, 5, 8, 10, 12} ∨
        polygon = {4, 6, 8, 10, 12} ∨
        polygon = {5, 6, 8, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 5, 6, 8, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 5, 6, 8, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 5, 6, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 5, 6, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 5, 6, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 5, 6, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 5, 6, 8, 10, 12} \ {x, y} := by
    calc
      polygon = {2, 4, 5, 6, 8, 10, 12} \ ({2, 4, 5, 6, 8, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 5, 6, 8, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

end ErdosSzekeres

end
