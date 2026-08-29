module

public import ErdosSzekeres.PredecessorHalfFin13Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 025. -/

theorem predecessorHalfFin13_fiveSubset_mask6516 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 5, 6, 8, 11, 12} →
      polygon.card = 5 →
        polygon = {2, 4, 5, 6, 8} ∨
        polygon = {2, 4, 5, 6, 11} ∨
        polygon = {2, 4, 5, 6, 12} ∨
        polygon = {2, 4, 5, 8, 11} ∨
        polygon = {2, 4, 5, 8, 12} ∨
        polygon = {2, 4, 5, 11, 12} ∨
        polygon = {2, 4, 6, 8, 11} ∨
        polygon = {2, 4, 6, 8, 12} ∨
        polygon = {2, 4, 6, 11, 12} ∨
        polygon = {2, 4, 8, 11, 12} ∨
        polygon = {2, 5, 6, 8, 11} ∨
        polygon = {2, 5, 6, 8, 12} ∨
        polygon = {2, 5, 6, 11, 12} ∨
        polygon = {2, 5, 8, 11, 12} ∨
        polygon = {2, 6, 8, 11, 12} ∨
        polygon = {4, 5, 6, 8, 11} ∨
        polygon = {4, 5, 6, 8, 12} ∨
        polygon = {4, 5, 6, 11, 12} ∨
        polygon = {4, 5, 8, 11, 12} ∨
        polygon = {4, 6, 8, 11, 12} ∨
        polygon = {5, 6, 8, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 5, 6, 8, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 5, 6, 8, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 5, 6, 8, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 5, 6, 8, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 5, 6, 8, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 5, 6, 8, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 5, 6, 8, 11, 12} \ {x, y} := by
    calc
      polygon = {2, 4, 5, 6, 8, 11, 12} \ ({2, 4, 5, 6, 8, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 5, 6, 8, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3700 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 5, 6, 9, 10, 11} →
      polygon.card = 5 →
        polygon = {2, 4, 5, 6, 9} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {2, 4, 5, 6, 11} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {2, 4, 5, 9, 11} ∨
        polygon = {2, 4, 5, 10, 11} ∨
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {2, 4, 6, 9, 11} ∨
        polygon = {2, 4, 6, 10, 11} ∨
        polygon = {2, 4, 9, 10, 11} ∨
        polygon = {2, 5, 6, 9, 10} ∨
        polygon = {2, 5, 6, 9, 11} ∨
        polygon = {2, 5, 6, 10, 11} ∨
        polygon = {2, 5, 9, 10, 11} ∨
        polygon = {2, 6, 9, 10, 11} ∨
        polygon = {4, 5, 6, 9, 10} ∨
        polygon = {4, 5, 6, 9, 11} ∨
        polygon = {4, 5, 6, 10, 11} ∨
        polygon = {4, 5, 9, 10, 11} ∨
        polygon = {4, 6, 9, 10, 11} ∨
        polygon = {5, 6, 9, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 5, 6, 9, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 5, 6, 9, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 5, 6, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 5, 6, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 5, 6, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 5, 6, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 5, 6, 9, 10, 11} \ {x, y} := by
    calc
      polygon = {2, 4, 5, 6, 9, 10, 11} \ ({2, 4, 5, 6, 9, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 5, 6, 9, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5748 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 5, 6, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {2, 4, 5, 6, 9} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {2, 4, 5, 6, 12} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {2, 4, 6, 9, 12} ∨
        polygon = {2, 4, 6, 10, 12} ∨
        polygon = {2, 4, 9, 10, 12} ∨
        polygon = {2, 5, 6, 9, 10} ∨
        polygon = {2, 5, 6, 9, 12} ∨
        polygon = {2, 5, 6, 10, 12} ∨
        polygon = {2, 5, 9, 10, 12} ∨
        polygon = {2, 6, 9, 10, 12} ∨
        polygon = {4, 5, 6, 9, 10} ∨
        polygon = {4, 5, 6, 9, 12} ∨
        polygon = {4, 5, 6, 10, 12} ∨
        polygon = {4, 5, 9, 10, 12} ∨
        polygon = {4, 6, 9, 10, 12} ∨
        polygon = {5, 6, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 5, 6, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 5, 6, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 5, 6, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 5, 6, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 5, 6, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 5, 6, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 5, 6, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {2, 4, 5, 6, 9, 10, 12} \ ({2, 4, 5, 6, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 5, 6, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask6772 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 5, 6, 9, 11, 12} →
      polygon.card = 5 →
        polygon = {2, 4, 5, 6, 9} ∨
        polygon = {2, 4, 5, 6, 11} ∨
        polygon = {2, 4, 5, 6, 12} ∨
        polygon = {2, 4, 5, 9, 11} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {2, 4, 5, 11, 12} ∨
        polygon = {2, 4, 6, 9, 11} ∨
        polygon = {2, 4, 6, 9, 12} ∨
        polygon = {2, 4, 6, 11, 12} ∨
        polygon = {2, 4, 9, 11, 12} ∨
        polygon = {2, 5, 6, 9, 11} ∨
        polygon = {2, 5, 6, 9, 12} ∨
        polygon = {2, 5, 6, 11, 12} ∨
        polygon = {2, 5, 9, 11, 12} ∨
        polygon = {2, 6, 9, 11, 12} ∨
        polygon = {4, 5, 6, 9, 11} ∨
        polygon = {4, 5, 6, 9, 12} ∨
        polygon = {4, 5, 6, 11, 12} ∨
        polygon = {4, 5, 9, 11, 12} ∨
        polygon = {4, 6, 9, 11, 12} ∨
        polygon = {5, 6, 9, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 5, 6, 9, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 5, 6, 9, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 5, 6, 9, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 5, 6, 9, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 5, 6, 9, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 5, 6, 9, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 5, 6, 9, 11, 12} \ {x, y} := by
    calc
      polygon = {2, 4, 5, 6, 9, 11, 12} \ ({2, 4, 5, 6, 9, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 5, 6, 9, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1972 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 5, 7, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {2, 4, 5, 7, 8} ∨
        polygon = {2, 4, 5, 7, 9} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {2, 4, 5, 8, 9} ∨
        polygon = {2, 4, 5, 8, 10} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {2, 4, 7, 8, 9} ∨
        polygon = {2, 4, 7, 8, 10} ∨
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {2, 4, 8, 9, 10} ∨
        polygon = {2, 5, 7, 8, 9} ∨
        polygon = {2, 5, 7, 8, 10} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {2, 5, 8, 9, 10} ∨
        polygon = {2, 7, 8, 9, 10} ∨
        polygon = {4, 5, 7, 8, 9} ∨
        polygon = {4, 5, 7, 8, 10} ∨
        polygon = {4, 5, 7, 9, 10} ∨
        polygon = {4, 5, 8, 9, 10} ∨
        polygon = {4, 7, 8, 9, 10} ∨
        polygon = {5, 7, 8, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 5, 7, 8, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 5, 7, 8, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 5, 7, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 5, 7, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 5, 7, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 5, 7, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 5, 7, 8, 9, 10} \ {x, y} := by
    calc
      polygon = {2, 4, 5, 7, 8, 9, 10} \ ({2, 4, 5, 7, 8, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 5, 7, 8, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask2996 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 5, 7, 8, 9, 11} →
      polygon.card = 5 →
        polygon = {2, 4, 5, 7, 8} ∨
        polygon = {2, 4, 5, 7, 9} ∨
        polygon = {2, 4, 5, 7, 11} ∨
        polygon = {2, 4, 5, 8, 9} ∨
        polygon = {2, 4, 5, 8, 11} ∨
        polygon = {2, 4, 5, 9, 11} ∨
        polygon = {2, 4, 7, 8, 9} ∨
        polygon = {2, 4, 7, 8, 11} ∨
        polygon = {2, 4, 7, 9, 11} ∨
        polygon = {2, 4, 8, 9, 11} ∨
        polygon = {2, 5, 7, 8, 9} ∨
        polygon = {2, 5, 7, 8, 11} ∨
        polygon = {2, 5, 7, 9, 11} ∨
        polygon = {2, 5, 8, 9, 11} ∨
        polygon = {2, 7, 8, 9, 11} ∨
        polygon = {4, 5, 7, 8, 9} ∨
        polygon = {4, 5, 7, 8, 11} ∨
        polygon = {4, 5, 7, 9, 11} ∨
        polygon = {4, 5, 8, 9, 11} ∨
        polygon = {4, 7, 8, 9, 11} ∨
        polygon = {5, 7, 8, 9, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 5, 7, 8, 9, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 5, 7, 8, 9, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 5, 7, 8, 9, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 5, 7, 8, 9, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 5, 7, 8, 9, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 5, 7, 8, 9, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 5, 7, 8, 9, 11} \ {x, y} := by
    calc
      polygon = {2, 4, 5, 7, 8, 9, 11} \ ({2, 4, 5, 7, 8, 9, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 5, 7, 8, 9, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5044 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 5, 7, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {2, 4, 5, 7, 8} ∨
        polygon = {2, 4, 5, 7, 9} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {2, 4, 5, 8, 9} ∨
        polygon = {2, 4, 5, 8, 12} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {2, 4, 7, 8, 9} ∨
        polygon = {2, 4, 7, 8, 12} ∨
        polygon = {2, 4, 7, 9, 12} ∨
        polygon = {2, 4, 8, 9, 12} ∨
        polygon = {2, 5, 7, 8, 9} ∨
        polygon = {2, 5, 7, 8, 12} ∨
        polygon = {2, 5, 7, 9, 12} ∨
        polygon = {2, 5, 8, 9, 12} ∨
        polygon = {2, 7, 8, 9, 12} ∨
        polygon = {4, 5, 7, 8, 9} ∨
        polygon = {4, 5, 7, 8, 12} ∨
        polygon = {4, 5, 7, 9, 12} ∨
        polygon = {4, 5, 8, 9, 12} ∨
        polygon = {4, 7, 8, 9, 12} ∨
        polygon = {5, 7, 8, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 5, 7, 8, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 5, 7, 8, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 5, 7, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 5, 7, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 5, 7, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 5, 7, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 5, 7, 8, 9, 12} \ {x, y} := by
    calc
      polygon = {2, 4, 5, 7, 8, 9, 12} \ ({2, 4, 5, 7, 8, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 5, 7, 8, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3508 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 5, 7, 8, 10, 11} →
      polygon.card = 5 →
        polygon = {2, 4, 5, 7, 8} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {2, 4, 5, 7, 11} ∨
        polygon = {2, 4, 5, 8, 10} ∨
        polygon = {2, 4, 5, 8, 11} ∨
        polygon = {2, 4, 5, 10, 11} ∨
        polygon = {2, 4, 7, 8, 10} ∨
        polygon = {2, 4, 7, 8, 11} ∨
        polygon = {2, 4, 7, 10, 11} ∨
        polygon = {2, 4, 8, 10, 11} ∨
        polygon = {2, 5, 7, 8, 10} ∨
        polygon = {2, 5, 7, 8, 11} ∨
        polygon = {2, 5, 7, 10, 11} ∨
        polygon = {2, 5, 8, 10, 11} ∨
        polygon = {2, 7, 8, 10, 11} ∨
        polygon = {4, 5, 7, 8, 10} ∨
        polygon = {4, 5, 7, 8, 11} ∨
        polygon = {4, 5, 7, 10, 11} ∨
        polygon = {4, 5, 8, 10, 11} ∨
        polygon = {4, 7, 8, 10, 11} ∨
        polygon = {5, 7, 8, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 5, 7, 8, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 5, 7, 8, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 5, 7, 8, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 5, 7, 8, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 5, 7, 8, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 5, 7, 8, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 5, 7, 8, 10, 11} \ {x, y} := by
    calc
      polygon = {2, 4, 5, 7, 8, 10, 11} \ ({2, 4, 5, 7, 8, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 5, 7, 8, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5556 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 5, 7, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {2, 4, 5, 7, 8} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {2, 4, 5, 8, 10} ∨
        polygon = {2, 4, 5, 8, 12} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {2, 4, 7, 8, 10} ∨
        polygon = {2, 4, 7, 8, 12} ∨
        polygon = {2, 4, 7, 10, 12} ∨
        polygon = {2, 4, 8, 10, 12} ∨
        polygon = {2, 5, 7, 8, 10} ∨
        polygon = {2, 5, 7, 8, 12} ∨
        polygon = {2, 5, 7, 10, 12} ∨
        polygon = {2, 5, 8, 10, 12} ∨
        polygon = {2, 7, 8, 10, 12} ∨
        polygon = {4, 5, 7, 8, 10} ∨
        polygon = {4, 5, 7, 8, 12} ∨
        polygon = {4, 5, 7, 10, 12} ∨
        polygon = {4, 5, 8, 10, 12} ∨
        polygon = {4, 7, 8, 10, 12} ∨
        polygon = {5, 7, 8, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 5, 7, 8, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 5, 7, 8, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 5, 7, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 5, 7, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 5, 7, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 5, 7, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 5, 7, 8, 10, 12} \ {x, y} := by
    calc
      polygon = {2, 4, 5, 7, 8, 10, 12} \ ({2, 4, 5, 7, 8, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 5, 7, 8, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask6580 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 5, 7, 8, 11, 12} →
      polygon.card = 5 →
        polygon = {2, 4, 5, 7, 8} ∨
        polygon = {2, 4, 5, 7, 11} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {2, 4, 5, 8, 11} ∨
        polygon = {2, 4, 5, 8, 12} ∨
        polygon = {2, 4, 5, 11, 12} ∨
        polygon = {2, 4, 7, 8, 11} ∨
        polygon = {2, 4, 7, 8, 12} ∨
        polygon = {2, 4, 7, 11, 12} ∨
        polygon = {2, 4, 8, 11, 12} ∨
        polygon = {2, 5, 7, 8, 11} ∨
        polygon = {2, 5, 7, 8, 12} ∨
        polygon = {2, 5, 7, 11, 12} ∨
        polygon = {2, 5, 8, 11, 12} ∨
        polygon = {2, 7, 8, 11, 12} ∨
        polygon = {4, 5, 7, 8, 11} ∨
        polygon = {4, 5, 7, 8, 12} ∨
        polygon = {4, 5, 7, 11, 12} ∨
        polygon = {4, 5, 8, 11, 12} ∨
        polygon = {4, 7, 8, 11, 12} ∨
        polygon = {5, 7, 8, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 5, 7, 8, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 5, 7, 8, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 5, 7, 8, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 5, 7, 8, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 5, 7, 8, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 5, 7, 8, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 5, 7, 8, 11, 12} \ {x, y} := by
    calc
      polygon = {2, 4, 5, 7, 8, 11, 12} \ ({2, 4, 5, 7, 8, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 5, 7, 8, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3764 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 5, 7, 9, 10, 11} →
      polygon.card = 5 →
        polygon = {2, 4, 5, 7, 9} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {2, 4, 5, 7, 11} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {2, 4, 5, 9, 11} ∨
        polygon = {2, 4, 5, 10, 11} ∨
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {2, 4, 7, 9, 11} ∨
        polygon = {2, 4, 7, 10, 11} ∨
        polygon = {2, 4, 9, 10, 11} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {2, 5, 7, 9, 11} ∨
        polygon = {2, 5, 7, 10, 11} ∨
        polygon = {2, 5, 9, 10, 11} ∨
        polygon = {2, 7, 9, 10, 11} ∨
        polygon = {4, 5, 7, 9, 10} ∨
        polygon = {4, 5, 7, 9, 11} ∨
        polygon = {4, 5, 7, 10, 11} ∨
        polygon = {4, 5, 9, 10, 11} ∨
        polygon = {4, 7, 9, 10, 11} ∨
        polygon = {5, 7, 9, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 5, 7, 9, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 5, 7, 9, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 5, 7, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 5, 7, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 5, 7, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 5, 7, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 5, 7, 9, 10, 11} \ {x, y} := by
    calc
      polygon = {2, 4, 5, 7, 9, 10, 11} \ ({2, 4, 5, 7, 9, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 5, 7, 9, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5812 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 5, 7, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {2, 4, 5, 7, 9} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {2, 4, 7, 9, 12} ∨
        polygon = {2, 4, 7, 10, 12} ∨
        polygon = {2, 4, 9, 10, 12} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {2, 5, 7, 9, 12} ∨
        polygon = {2, 5, 7, 10, 12} ∨
        polygon = {2, 5, 9, 10, 12} ∨
        polygon = {2, 7, 9, 10, 12} ∨
        polygon = {4, 5, 7, 9, 10} ∨
        polygon = {4, 5, 7, 9, 12} ∨
        polygon = {4, 5, 7, 10, 12} ∨
        polygon = {4, 5, 9, 10, 12} ∨
        polygon = {4, 7, 9, 10, 12} ∨
        polygon = {5, 7, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 5, 7, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 5, 7, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 5, 7, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 5, 7, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 5, 7, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 5, 7, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 5, 7, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {2, 4, 5, 7, 9, 10, 12} \ ({2, 4, 5, 7, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 5, 7, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask6836 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 5, 7, 9, 11, 12} →
      polygon.card = 5 →
        polygon = {2, 4, 5, 7, 9} ∨
        polygon = {2, 4, 5, 7, 11} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {2, 4, 5, 9, 11} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {2, 4, 5, 11, 12} ∨
        polygon = {2, 4, 7, 9, 11} ∨
        polygon = {2, 4, 7, 9, 12} ∨
        polygon = {2, 4, 7, 11, 12} ∨
        polygon = {2, 4, 9, 11, 12} ∨
        polygon = {2, 5, 7, 9, 11} ∨
        polygon = {2, 5, 7, 9, 12} ∨
        polygon = {2, 5, 7, 11, 12} ∨
        polygon = {2, 5, 9, 11, 12} ∨
        polygon = {2, 7, 9, 11, 12} ∨
        polygon = {4, 5, 7, 9, 11} ∨
        polygon = {4, 5, 7, 9, 12} ∨
        polygon = {4, 5, 7, 11, 12} ∨
        polygon = {4, 5, 9, 11, 12} ∨
        polygon = {4, 7, 9, 11, 12} ∨
        polygon = {5, 7, 9, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 5, 7, 9, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 5, 7, 9, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 5, 7, 9, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 5, 7, 9, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 5, 7, 9, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 5, 7, 9, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 5, 7, 9, 11, 12} \ {x, y} := by
    calc
      polygon = {2, 4, 5, 7, 9, 11, 12} \ ({2, 4, 5, 7, 9, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 5, 7, 9, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask7348 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 5, 7, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {2, 4, 5, 7, 11} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {2, 4, 5, 10, 11} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {2, 4, 5, 11, 12} ∨
        polygon = {2, 4, 7, 10, 11} ∨
        polygon = {2, 4, 7, 10, 12} ∨
        polygon = {2, 4, 7, 11, 12} ∨
        polygon = {2, 4, 10, 11, 12} ∨
        polygon = {2, 5, 7, 10, 11} ∨
        polygon = {2, 5, 7, 10, 12} ∨
        polygon = {2, 5, 7, 11, 12} ∨
        polygon = {2, 5, 10, 11, 12} ∨
        polygon = {2, 7, 10, 11, 12} ∨
        polygon = {4, 5, 7, 10, 11} ∨
        polygon = {4, 5, 7, 10, 12} ∨
        polygon = {4, 5, 7, 11, 12} ∨
        polygon = {4, 5, 10, 11, 12} ∨
        polygon = {4, 7, 10, 11, 12} ∨
        polygon = {5, 7, 10, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 5, 7, 10, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 5, 7, 10, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 5, 7, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 5, 7, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 5, 7, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 5, 7, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 5, 7, 10, 11, 12} \ {x, y} := by
    calc
      polygon = {2, 4, 5, 7, 10, 11, 12} \ ({2, 4, 5, 7, 10, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 5, 7, 10, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3892 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 5, 8, 9, 10, 11} →
      polygon.card = 5 →
        polygon = {2, 4, 5, 8, 9} ∨
        polygon = {2, 4, 5, 8, 10} ∨
        polygon = {2, 4, 5, 8, 11} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {2, 4, 5, 9, 11} ∨
        polygon = {2, 4, 5, 10, 11} ∨
        polygon = {2, 4, 8, 9, 10} ∨
        polygon = {2, 4, 8, 9, 11} ∨
        polygon = {2, 4, 8, 10, 11} ∨
        polygon = {2, 4, 9, 10, 11} ∨
        polygon = {2, 5, 8, 9, 10} ∨
        polygon = {2, 5, 8, 9, 11} ∨
        polygon = {2, 5, 8, 10, 11} ∨
        polygon = {2, 5, 9, 10, 11} ∨
        polygon = {2, 8, 9, 10, 11} ∨
        polygon = {4, 5, 8, 9, 10} ∨
        polygon = {4, 5, 8, 9, 11} ∨
        polygon = {4, 5, 8, 10, 11} ∨
        polygon = {4, 5, 9, 10, 11} ∨
        polygon = {4, 8, 9, 10, 11} ∨
        polygon = {5, 8, 9, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 5, 8, 9, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 5, 8, 9, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 5, 8, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 5, 8, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 5, 8, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 5, 8, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 5, 8, 9, 10, 11} \ {x, y} := by
    calc
      polygon = {2, 4, 5, 8, 9, 10, 11} \ ({2, 4, 5, 8, 9, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 5, 8, 9, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5940 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 5, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {2, 4, 5, 8, 9} ∨
        polygon = {2, 4, 5, 8, 10} ∨
        polygon = {2, 4, 5, 8, 12} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {2, 4, 8, 9, 10} ∨
        polygon = {2, 4, 8, 9, 12} ∨
        polygon = {2, 4, 8, 10, 12} ∨
        polygon = {2, 4, 9, 10, 12} ∨
        polygon = {2, 5, 8, 9, 10} ∨
        polygon = {2, 5, 8, 9, 12} ∨
        polygon = {2, 5, 8, 10, 12} ∨
        polygon = {2, 5, 9, 10, 12} ∨
        polygon = {2, 8, 9, 10, 12} ∨
        polygon = {4, 5, 8, 9, 10} ∨
        polygon = {4, 5, 8, 9, 12} ∨
        polygon = {4, 5, 8, 10, 12} ∨
        polygon = {4, 5, 9, 10, 12} ∨
        polygon = {4, 8, 9, 10, 12} ∨
        polygon = {5, 8, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 5, 8, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 5, 8, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 5, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 5, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 5, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 5, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 5, 8, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {2, 4, 5, 8, 9, 10, 12} \ ({2, 4, 5, 8, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 5, 8, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask7476 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 5, 8, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {2, 4, 5, 8, 10} ∨
        polygon = {2, 4, 5, 8, 11} ∨
        polygon = {2, 4, 5, 8, 12} ∨
        polygon = {2, 4, 5, 10, 11} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {2, 4, 5, 11, 12} ∨
        polygon = {2, 4, 8, 10, 11} ∨
        polygon = {2, 4, 8, 10, 12} ∨
        polygon = {2, 4, 8, 11, 12} ∨
        polygon = {2, 4, 10, 11, 12} ∨
        polygon = {2, 5, 8, 10, 11} ∨
        polygon = {2, 5, 8, 10, 12} ∨
        polygon = {2, 5, 8, 11, 12} ∨
        polygon = {2, 5, 10, 11, 12} ∨
        polygon = {2, 8, 10, 11, 12} ∨
        polygon = {4, 5, 8, 10, 11} ∨
        polygon = {4, 5, 8, 10, 12} ∨
        polygon = {4, 5, 8, 11, 12} ∨
        polygon = {4, 5, 10, 11, 12} ∨
        polygon = {4, 8, 10, 11, 12} ∨
        polygon = {5, 8, 10, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 5, 8, 10, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 5, 8, 10, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 5, 8, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 5, 8, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 5, 8, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 5, 8, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 5, 8, 10, 11, 12} \ {x, y} := by
    calc
      polygon = {2, 4, 5, 8, 10, 11, 12} \ ({2, 4, 5, 8, 10, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 5, 8, 10, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask7732 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 5, 9, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {2, 4, 5, 9, 11} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {2, 4, 5, 10, 11} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {2, 4, 5, 11, 12} ∨
        polygon = {2, 4, 9, 10, 11} ∨
        polygon = {2, 4, 9, 10, 12} ∨
        polygon = {2, 4, 9, 11, 12} ∨
        polygon = {2, 4, 10, 11, 12} ∨
        polygon = {2, 5, 9, 10, 11} ∨
        polygon = {2, 5, 9, 10, 12} ∨
        polygon = {2, 5, 9, 11, 12} ∨
        polygon = {2, 5, 10, 11, 12} ∨
        polygon = {2, 9, 10, 11, 12} ∨
        polygon = {4, 5, 9, 10, 11} ∨
        polygon = {4, 5, 9, 10, 12} ∨
        polygon = {4, 5, 9, 11, 12} ∨
        polygon = {4, 5, 10, 11, 12} ∨
        polygon = {4, 9, 10, 11, 12} ∨
        polygon = {5, 9, 10, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 5, 9, 10, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 5, 9, 10, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 5, 9, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 5, 9, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 5, 9, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 5, 9, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 5, 9, 10, 11, 12} \ {x, y} := by
    calc
      polygon = {2, 4, 5, 9, 10, 11, 12} \ ({2, 4, 5, 9, 10, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 5, 9, 10, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask2004 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 6, 7, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {2, 4, 6, 7, 8} ∨
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {2, 4, 6, 8, 9} ∨
        polygon = {2, 4, 6, 8, 10} ∨
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {2, 4, 7, 8, 9} ∨
        polygon = {2, 4, 7, 8, 10} ∨
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {2, 4, 8, 9, 10} ∨
        polygon = {2, 6, 7, 8, 9} ∨
        polygon = {2, 6, 7, 8, 10} ∨
        polygon = {2, 6, 7, 9, 10} ∨
        polygon = {2, 6, 8, 9, 10} ∨
        polygon = {2, 7, 8, 9, 10} ∨
        polygon = {4, 6, 7, 8, 9} ∨
        polygon = {4, 6, 7, 8, 10} ∨
        polygon = {4, 6, 7, 9, 10} ∨
        polygon = {4, 6, 8, 9, 10} ∨
        polygon = {4, 7, 8, 9, 10} ∨
        polygon = {6, 7, 8, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 6, 7, 8, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 6, 7, 8, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 6, 7, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 6, 7, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 6, 7, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 6, 7, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 6, 7, 8, 9, 10} \ {x, y} := by
    calc
      polygon = {2, 4, 6, 7, 8, 9, 10} \ ({2, 4, 6, 7, 8, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 6, 7, 8, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3028 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 6, 7, 8, 9, 11} →
      polygon.card = 5 →
        polygon = {2, 4, 6, 7, 8} ∨
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {2, 4, 6, 7, 11} ∨
        polygon = {2, 4, 6, 8, 9} ∨
        polygon = {2, 4, 6, 8, 11} ∨
        polygon = {2, 4, 6, 9, 11} ∨
        polygon = {2, 4, 7, 8, 9} ∨
        polygon = {2, 4, 7, 8, 11} ∨
        polygon = {2, 4, 7, 9, 11} ∨
        polygon = {2, 4, 8, 9, 11} ∨
        polygon = {2, 6, 7, 8, 9} ∨
        polygon = {2, 6, 7, 8, 11} ∨
        polygon = {2, 6, 7, 9, 11} ∨
        polygon = {2, 6, 8, 9, 11} ∨
        polygon = {2, 7, 8, 9, 11} ∨
        polygon = {4, 6, 7, 8, 9} ∨
        polygon = {4, 6, 7, 8, 11} ∨
        polygon = {4, 6, 7, 9, 11} ∨
        polygon = {4, 6, 8, 9, 11} ∨
        polygon = {4, 7, 8, 9, 11} ∨
        polygon = {6, 7, 8, 9, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 6, 7, 8, 9, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 6, 7, 8, 9, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 6, 7, 8, 9, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 6, 7, 8, 9, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 6, 7, 8, 9, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 6, 7, 8, 9, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 6, 7, 8, 9, 11} \ {x, y} := by
    calc
      polygon = {2, 4, 6, 7, 8, 9, 11} \ ({2, 4, 6, 7, 8, 9, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 6, 7, 8, 9, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5076 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 6, 7, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {2, 4, 6, 7, 8} ∨
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {2, 4, 6, 7, 12} ∨
        polygon = {2, 4, 6, 8, 9} ∨
        polygon = {2, 4, 6, 8, 12} ∨
        polygon = {2, 4, 6, 9, 12} ∨
        polygon = {2, 4, 7, 8, 9} ∨
        polygon = {2, 4, 7, 8, 12} ∨
        polygon = {2, 4, 7, 9, 12} ∨
        polygon = {2, 4, 8, 9, 12} ∨
        polygon = {2, 6, 7, 8, 9} ∨
        polygon = {2, 6, 7, 8, 12} ∨
        polygon = {2, 6, 7, 9, 12} ∨
        polygon = {2, 6, 8, 9, 12} ∨
        polygon = {2, 7, 8, 9, 12} ∨
        polygon = {4, 6, 7, 8, 9} ∨
        polygon = {4, 6, 7, 8, 12} ∨
        polygon = {4, 6, 7, 9, 12} ∨
        polygon = {4, 6, 8, 9, 12} ∨
        polygon = {4, 7, 8, 9, 12} ∨
        polygon = {6, 7, 8, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 6, 7, 8, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 6, 7, 8, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 6, 7, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 6, 7, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 6, 7, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 6, 7, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 6, 7, 8, 9, 12} \ {x, y} := by
    calc
      polygon = {2, 4, 6, 7, 8, 9, 12} \ ({2, 4, 6, 7, 8, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 6, 7, 8, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3540 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 6, 7, 8, 10, 11} →
      polygon.card = 5 →
        polygon = {2, 4, 6, 7, 8} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {2, 4, 6, 7, 11} ∨
        polygon = {2, 4, 6, 8, 10} ∨
        polygon = {2, 4, 6, 8, 11} ∨
        polygon = {2, 4, 6, 10, 11} ∨
        polygon = {2, 4, 7, 8, 10} ∨
        polygon = {2, 4, 7, 8, 11} ∨
        polygon = {2, 4, 7, 10, 11} ∨
        polygon = {2, 4, 8, 10, 11} ∨
        polygon = {2, 6, 7, 8, 10} ∨
        polygon = {2, 6, 7, 8, 11} ∨
        polygon = {2, 6, 7, 10, 11} ∨
        polygon = {2, 6, 8, 10, 11} ∨
        polygon = {2, 7, 8, 10, 11} ∨
        polygon = {4, 6, 7, 8, 10} ∨
        polygon = {4, 6, 7, 8, 11} ∨
        polygon = {4, 6, 7, 10, 11} ∨
        polygon = {4, 6, 8, 10, 11} ∨
        polygon = {4, 7, 8, 10, 11} ∨
        polygon = {6, 7, 8, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 6, 7, 8, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 6, 7, 8, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 6, 7, 8, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 6, 7, 8, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 6, 7, 8, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 6, 7, 8, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 6, 7, 8, 10, 11} \ {x, y} := by
    calc
      polygon = {2, 4, 6, 7, 8, 10, 11} \ ({2, 4, 6, 7, 8, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 6, 7, 8, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5588 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 6, 7, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {2, 4, 6, 7, 8} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {2, 4, 6, 7, 12} ∨
        polygon = {2, 4, 6, 8, 10} ∨
        polygon = {2, 4, 6, 8, 12} ∨
        polygon = {2, 4, 6, 10, 12} ∨
        polygon = {2, 4, 7, 8, 10} ∨
        polygon = {2, 4, 7, 8, 12} ∨
        polygon = {2, 4, 7, 10, 12} ∨
        polygon = {2, 4, 8, 10, 12} ∨
        polygon = {2, 6, 7, 8, 10} ∨
        polygon = {2, 6, 7, 8, 12} ∨
        polygon = {2, 6, 7, 10, 12} ∨
        polygon = {2, 6, 8, 10, 12} ∨
        polygon = {2, 7, 8, 10, 12} ∨
        polygon = {4, 6, 7, 8, 10} ∨
        polygon = {4, 6, 7, 8, 12} ∨
        polygon = {4, 6, 7, 10, 12} ∨
        polygon = {4, 6, 8, 10, 12} ∨
        polygon = {4, 7, 8, 10, 12} ∨
        polygon = {6, 7, 8, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 6, 7, 8, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 6, 7, 8, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 6, 7, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 6, 7, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 6, 7, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 6, 7, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 6, 7, 8, 10, 12} \ {x, y} := by
    calc
      polygon = {2, 4, 6, 7, 8, 10, 12} \ ({2, 4, 6, 7, 8, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 6, 7, 8, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask6612 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 6, 7, 8, 11, 12} →
      polygon.card = 5 →
        polygon = {2, 4, 6, 7, 8} ∨
        polygon = {2, 4, 6, 7, 11} ∨
        polygon = {2, 4, 6, 7, 12} ∨
        polygon = {2, 4, 6, 8, 11} ∨
        polygon = {2, 4, 6, 8, 12} ∨
        polygon = {2, 4, 6, 11, 12} ∨
        polygon = {2, 4, 7, 8, 11} ∨
        polygon = {2, 4, 7, 8, 12} ∨
        polygon = {2, 4, 7, 11, 12} ∨
        polygon = {2, 4, 8, 11, 12} ∨
        polygon = {2, 6, 7, 8, 11} ∨
        polygon = {2, 6, 7, 8, 12} ∨
        polygon = {2, 6, 7, 11, 12} ∨
        polygon = {2, 6, 8, 11, 12} ∨
        polygon = {2, 7, 8, 11, 12} ∨
        polygon = {4, 6, 7, 8, 11} ∨
        polygon = {4, 6, 7, 8, 12} ∨
        polygon = {4, 6, 7, 11, 12} ∨
        polygon = {4, 6, 8, 11, 12} ∨
        polygon = {4, 7, 8, 11, 12} ∨
        polygon = {6, 7, 8, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 6, 7, 8, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 6, 7, 8, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 6, 7, 8, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 6, 7, 8, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 6, 7, 8, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 6, 7, 8, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 6, 7, 8, 11, 12} \ {x, y} := by
    calc
      polygon = {2, 4, 6, 7, 8, 11, 12} \ ({2, 4, 6, 7, 8, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 6, 7, 8, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3796 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 6, 7, 9, 10, 11} →
      polygon.card = 5 →
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {2, 4, 6, 7, 11} ∨
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {2, 4, 6, 9, 11} ∨
        polygon = {2, 4, 6, 10, 11} ∨
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {2, 4, 7, 9, 11} ∨
        polygon = {2, 4, 7, 10, 11} ∨
        polygon = {2, 4, 9, 10, 11} ∨
        polygon = {2, 6, 7, 9, 10} ∨
        polygon = {2, 6, 7, 9, 11} ∨
        polygon = {2, 6, 7, 10, 11} ∨
        polygon = {2, 6, 9, 10, 11} ∨
        polygon = {2, 7, 9, 10, 11} ∨
        polygon = {4, 6, 7, 9, 10} ∨
        polygon = {4, 6, 7, 9, 11} ∨
        polygon = {4, 6, 7, 10, 11} ∨
        polygon = {4, 6, 9, 10, 11} ∨
        polygon = {4, 7, 9, 10, 11} ∨
        polygon = {6, 7, 9, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 6, 7, 9, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 6, 7, 9, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 6, 7, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 6, 7, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 6, 7, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 6, 7, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 6, 7, 9, 10, 11} \ {x, y} := by
    calc
      polygon = {2, 4, 6, 7, 9, 10, 11} \ ({2, 4, 6, 7, 9, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 6, 7, 9, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5844 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 6, 7, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {2, 4, 6, 7, 12} ∨
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {2, 4, 6, 9, 12} ∨
        polygon = {2, 4, 6, 10, 12} ∨
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {2, 4, 7, 9, 12} ∨
        polygon = {2, 4, 7, 10, 12} ∨
        polygon = {2, 4, 9, 10, 12} ∨
        polygon = {2, 6, 7, 9, 10} ∨
        polygon = {2, 6, 7, 9, 12} ∨
        polygon = {2, 6, 7, 10, 12} ∨
        polygon = {2, 6, 9, 10, 12} ∨
        polygon = {2, 7, 9, 10, 12} ∨
        polygon = {4, 6, 7, 9, 10} ∨
        polygon = {4, 6, 7, 9, 12} ∨
        polygon = {4, 6, 7, 10, 12} ∨
        polygon = {4, 6, 9, 10, 12} ∨
        polygon = {4, 7, 9, 10, 12} ∨
        polygon = {6, 7, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 6, 7, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 6, 7, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 6, 7, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 6, 7, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 6, 7, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 6, 7, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 6, 7, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {2, 4, 6, 7, 9, 10, 12} \ ({2, 4, 6, 7, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 6, 7, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask7380 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 6, 7, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {2, 4, 6, 7, 11} ∨
        polygon = {2, 4, 6, 7, 12} ∨
        polygon = {2, 4, 6, 10, 11} ∨
        polygon = {2, 4, 6, 10, 12} ∨
        polygon = {2, 4, 6, 11, 12} ∨
        polygon = {2, 4, 7, 10, 11} ∨
        polygon = {2, 4, 7, 10, 12} ∨
        polygon = {2, 4, 7, 11, 12} ∨
        polygon = {2, 4, 10, 11, 12} ∨
        polygon = {2, 6, 7, 10, 11} ∨
        polygon = {2, 6, 7, 10, 12} ∨
        polygon = {2, 6, 7, 11, 12} ∨
        polygon = {2, 6, 10, 11, 12} ∨
        polygon = {2, 7, 10, 11, 12} ∨
        polygon = {4, 6, 7, 10, 11} ∨
        polygon = {4, 6, 7, 10, 12} ∨
        polygon = {4, 6, 7, 11, 12} ∨
        polygon = {4, 6, 10, 11, 12} ∨
        polygon = {4, 7, 10, 11, 12} ∨
        polygon = {6, 7, 10, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 6, 7, 10, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 6, 7, 10, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 6, 7, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 6, 7, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 6, 7, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 6, 7, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 6, 7, 10, 11, 12} \ {x, y} := by
    calc
      polygon = {2, 4, 6, 7, 10, 11, 12} \ ({2, 4, 6, 7, 10, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 6, 7, 10, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3924 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 6, 8, 9, 10, 11} →
      polygon.card = 5 →
        polygon = {2, 4, 6, 8, 9} ∨
        polygon = {2, 4, 6, 8, 10} ∨
        polygon = {2, 4, 6, 8, 11} ∨
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {2, 4, 6, 9, 11} ∨
        polygon = {2, 4, 6, 10, 11} ∨
        polygon = {2, 4, 8, 9, 10} ∨
        polygon = {2, 4, 8, 9, 11} ∨
        polygon = {2, 4, 8, 10, 11} ∨
        polygon = {2, 4, 9, 10, 11} ∨
        polygon = {2, 6, 8, 9, 10} ∨
        polygon = {2, 6, 8, 9, 11} ∨
        polygon = {2, 6, 8, 10, 11} ∨
        polygon = {2, 6, 9, 10, 11} ∨
        polygon = {2, 8, 9, 10, 11} ∨
        polygon = {4, 6, 8, 9, 10} ∨
        polygon = {4, 6, 8, 9, 11} ∨
        polygon = {4, 6, 8, 10, 11} ∨
        polygon = {4, 6, 9, 10, 11} ∨
        polygon = {4, 8, 9, 10, 11} ∨
        polygon = {6, 8, 9, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 6, 8, 9, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 6, 8, 9, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 6, 8, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 6, 8, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 6, 8, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 6, 8, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 6, 8, 9, 10, 11} \ {x, y} := by
    calc
      polygon = {2, 4, 6, 8, 9, 10, 11} \ ({2, 4, 6, 8, 9, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 6, 8, 9, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5972 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 6, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {2, 4, 6, 8, 9} ∨
        polygon = {2, 4, 6, 8, 10} ∨
        polygon = {2, 4, 6, 8, 12} ∨
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {2, 4, 6, 9, 12} ∨
        polygon = {2, 4, 6, 10, 12} ∨
        polygon = {2, 4, 8, 9, 10} ∨
        polygon = {2, 4, 8, 9, 12} ∨
        polygon = {2, 4, 8, 10, 12} ∨
        polygon = {2, 4, 9, 10, 12} ∨
        polygon = {2, 6, 8, 9, 10} ∨
        polygon = {2, 6, 8, 9, 12} ∨
        polygon = {2, 6, 8, 10, 12} ∨
        polygon = {2, 6, 9, 10, 12} ∨
        polygon = {2, 8, 9, 10, 12} ∨
        polygon = {4, 6, 8, 9, 10} ∨
        polygon = {4, 6, 8, 9, 12} ∨
        polygon = {4, 6, 8, 10, 12} ∨
        polygon = {4, 6, 9, 10, 12} ∨
        polygon = {4, 8, 9, 10, 12} ∨
        polygon = {6, 8, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 6, 8, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 6, 8, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 6, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 6, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 6, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 6, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 6, 8, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {2, 4, 6, 8, 9, 10, 12} \ ({2, 4, 6, 8, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 6, 8, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask6996 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 6, 8, 9, 11, 12} →
      polygon.card = 5 →
        polygon = {2, 4, 6, 8, 9} ∨
        polygon = {2, 4, 6, 8, 11} ∨
        polygon = {2, 4, 6, 8, 12} ∨
        polygon = {2, 4, 6, 9, 11} ∨
        polygon = {2, 4, 6, 9, 12} ∨
        polygon = {2, 4, 6, 11, 12} ∨
        polygon = {2, 4, 8, 9, 11} ∨
        polygon = {2, 4, 8, 9, 12} ∨
        polygon = {2, 4, 8, 11, 12} ∨
        polygon = {2, 4, 9, 11, 12} ∨
        polygon = {2, 6, 8, 9, 11} ∨
        polygon = {2, 6, 8, 9, 12} ∨
        polygon = {2, 6, 8, 11, 12} ∨
        polygon = {2, 6, 9, 11, 12} ∨
        polygon = {2, 8, 9, 11, 12} ∨
        polygon = {4, 6, 8, 9, 11} ∨
        polygon = {4, 6, 8, 9, 12} ∨
        polygon = {4, 6, 8, 11, 12} ∨
        polygon = {4, 6, 9, 11, 12} ∨
        polygon = {4, 8, 9, 11, 12} ∨
        polygon = {6, 8, 9, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 6, 8, 9, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 6, 8, 9, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 6, 8, 9, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 6, 8, 9, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 6, 8, 9, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 6, 8, 9, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 6, 8, 9, 11, 12} \ {x, y} := by
    calc
      polygon = {2, 4, 6, 8, 9, 11, 12} \ ({2, 4, 6, 8, 9, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 6, 8, 9, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask7508 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 6, 8, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {2, 4, 6, 8, 10} ∨
        polygon = {2, 4, 6, 8, 11} ∨
        polygon = {2, 4, 6, 8, 12} ∨
        polygon = {2, 4, 6, 10, 11} ∨
        polygon = {2, 4, 6, 10, 12} ∨
        polygon = {2, 4, 6, 11, 12} ∨
        polygon = {2, 4, 8, 10, 11} ∨
        polygon = {2, 4, 8, 10, 12} ∨
        polygon = {2, 4, 8, 11, 12} ∨
        polygon = {2, 4, 10, 11, 12} ∨
        polygon = {2, 6, 8, 10, 11} ∨
        polygon = {2, 6, 8, 10, 12} ∨
        polygon = {2, 6, 8, 11, 12} ∨
        polygon = {2, 6, 10, 11, 12} ∨
        polygon = {2, 8, 10, 11, 12} ∨
        polygon = {4, 6, 8, 10, 11} ∨
        polygon = {4, 6, 8, 10, 12} ∨
        polygon = {4, 6, 8, 11, 12} ∨
        polygon = {4, 6, 10, 11, 12} ∨
        polygon = {4, 8, 10, 11, 12} ∨
        polygon = {6, 8, 10, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 6, 8, 10, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 6, 8, 10, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 6, 8, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 6, 8, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 6, 8, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 6, 8, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 6, 8, 10, 11, 12} \ {x, y} := by
    calc
      polygon = {2, 4, 6, 8, 10, 11, 12} \ ({2, 4, 6, 8, 10, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 6, 8, 10, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask7764 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 6, 9, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {2, 4, 6, 9, 11} ∨
        polygon = {2, 4, 6, 9, 12} ∨
        polygon = {2, 4, 6, 10, 11} ∨
        polygon = {2, 4, 6, 10, 12} ∨
        polygon = {2, 4, 6, 11, 12} ∨
        polygon = {2, 4, 9, 10, 11} ∨
        polygon = {2, 4, 9, 10, 12} ∨
        polygon = {2, 4, 9, 11, 12} ∨
        polygon = {2, 4, 10, 11, 12} ∨
        polygon = {2, 6, 9, 10, 11} ∨
        polygon = {2, 6, 9, 10, 12} ∨
        polygon = {2, 6, 9, 11, 12} ∨
        polygon = {2, 6, 10, 11, 12} ∨
        polygon = {2, 9, 10, 11, 12} ∨
        polygon = {4, 6, 9, 10, 11} ∨
        polygon = {4, 6, 9, 10, 12} ∨
        polygon = {4, 6, 9, 11, 12} ∨
        polygon = {4, 6, 10, 11, 12} ∨
        polygon = {4, 9, 10, 11, 12} ∨
        polygon = {6, 9, 10, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 6, 9, 10, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 6, 9, 10, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 6, 9, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 6, 9, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 6, 9, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 6, 9, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 6, 9, 10, 11, 12} \ {x, y} := by
    calc
      polygon = {2, 4, 6, 9, 10, 11, 12} \ ({2, 4, 6, 9, 10, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 6, 9, 10, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3988 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 7, 8, 9, 10, 11} →
      polygon.card = 5 →
        polygon = {2, 4, 7, 8, 9} ∨
        polygon = {2, 4, 7, 8, 10} ∨
        polygon = {2, 4, 7, 8, 11} ∨
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {2, 4, 7, 9, 11} ∨
        polygon = {2, 4, 7, 10, 11} ∨
        polygon = {2, 4, 8, 9, 10} ∨
        polygon = {2, 4, 8, 9, 11} ∨
        polygon = {2, 4, 8, 10, 11} ∨
        polygon = {2, 4, 9, 10, 11} ∨
        polygon = {2, 7, 8, 9, 10} ∨
        polygon = {2, 7, 8, 9, 11} ∨
        polygon = {2, 7, 8, 10, 11} ∨
        polygon = {2, 7, 9, 10, 11} ∨
        polygon = {2, 8, 9, 10, 11} ∨
        polygon = {4, 7, 8, 9, 10} ∨
        polygon = {4, 7, 8, 9, 11} ∨
        polygon = {4, 7, 8, 10, 11} ∨
        polygon = {4, 7, 9, 10, 11} ∨
        polygon = {4, 8, 9, 10, 11} ∨
        polygon = {7, 8, 9, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 7, 8, 9, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 7, 8, 9, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 7, 8, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 7, 8, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 7, 8, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 7, 8, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 7, 8, 9, 10, 11} \ {x, y} := by
    calc
      polygon = {2, 4, 7, 8, 9, 10, 11} \ ({2, 4, 7, 8, 9, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 7, 8, 9, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask6036 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 7, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {2, 4, 7, 8, 9} ∨
        polygon = {2, 4, 7, 8, 10} ∨
        polygon = {2, 4, 7, 8, 12} ∨
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {2, 4, 7, 9, 12} ∨
        polygon = {2, 4, 7, 10, 12} ∨
        polygon = {2, 4, 8, 9, 10} ∨
        polygon = {2, 4, 8, 9, 12} ∨
        polygon = {2, 4, 8, 10, 12} ∨
        polygon = {2, 4, 9, 10, 12} ∨
        polygon = {2, 7, 8, 9, 10} ∨
        polygon = {2, 7, 8, 9, 12} ∨
        polygon = {2, 7, 8, 10, 12} ∨
        polygon = {2, 7, 9, 10, 12} ∨
        polygon = {2, 8, 9, 10, 12} ∨
        polygon = {4, 7, 8, 9, 10} ∨
        polygon = {4, 7, 8, 9, 12} ∨
        polygon = {4, 7, 8, 10, 12} ∨
        polygon = {4, 7, 9, 10, 12} ∨
        polygon = {4, 8, 9, 10, 12} ∨
        polygon = {7, 8, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 7, 8, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 7, 8, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 7, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 7, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 7, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 7, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 7, 8, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {2, 4, 7, 8, 9, 10, 12} \ ({2, 4, 7, 8, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 7, 8, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask7828 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 4, 7, 9, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {2, 4, 7, 9, 11} ∨
        polygon = {2, 4, 7, 9, 12} ∨
        polygon = {2, 4, 7, 10, 11} ∨
        polygon = {2, 4, 7, 10, 12} ∨
        polygon = {2, 4, 7, 11, 12} ∨
        polygon = {2, 4, 9, 10, 11} ∨
        polygon = {2, 4, 9, 10, 12} ∨
        polygon = {2, 4, 9, 11, 12} ∨
        polygon = {2, 4, 10, 11, 12} ∨
        polygon = {2, 7, 9, 10, 11} ∨
        polygon = {2, 7, 9, 10, 12} ∨
        polygon = {2, 7, 9, 11, 12} ∨
        polygon = {2, 7, 10, 11, 12} ∨
        polygon = {2, 9, 10, 11, 12} ∨
        polygon = {4, 7, 9, 10, 11} ∨
        polygon = {4, 7, 9, 10, 12} ∨
        polygon = {4, 7, 9, 11, 12} ∨
        polygon = {4, 7, 10, 11, 12} ∨
        polygon = {4, 9, 10, 11, 12} ∨
        polygon = {7, 9, 10, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 4, 7, 9, 10, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 4, 7, 9, 10, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 4, 7, 9, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 4, 7, 9, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 4, 7, 9, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 4, 7, 9, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 4, 7, 9, 10, 11, 12} \ {x, y} := by
    calc
      polygon = {2, 4, 7, 9, 10, 11, 12} \ ({2, 4, 7, 9, 10, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 4, 7, 9, 10, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask2020 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 5, 6, 7, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {2, 5, 6, 7, 8} ∨
        polygon = {2, 5, 6, 7, 9} ∨
        polygon = {2, 5, 6, 7, 10} ∨
        polygon = {2, 5, 6, 8, 9} ∨
        polygon = {2, 5, 6, 8, 10} ∨
        polygon = {2, 5, 6, 9, 10} ∨
        polygon = {2, 5, 7, 8, 9} ∨
        polygon = {2, 5, 7, 8, 10} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {2, 5, 8, 9, 10} ∨
        polygon = {2, 6, 7, 8, 9} ∨
        polygon = {2, 6, 7, 8, 10} ∨
        polygon = {2, 6, 7, 9, 10} ∨
        polygon = {2, 6, 8, 9, 10} ∨
        polygon = {2, 7, 8, 9, 10} ∨
        polygon = {5, 6, 7, 8, 9} ∨
        polygon = {5, 6, 7, 8, 10} ∨
        polygon = {5, 6, 7, 9, 10} ∨
        polygon = {5, 6, 8, 9, 10} ∨
        polygon = {5, 7, 8, 9, 10} ∨
        polygon = {6, 7, 8, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 5, 6, 7, 8, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 5, 6, 7, 8, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 5, 6, 7, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 5, 6, 7, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 5, 6, 7, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 5, 6, 7, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 5, 6, 7, 8, 9, 10} \ {x, y} := by
    calc
      polygon = {2, 5, 6, 7, 8, 9, 10} \ ({2, 5, 6, 7, 8, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 5, 6, 7, 8, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3044 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 5, 6, 7, 8, 9, 11} →
      polygon.card = 5 →
        polygon = {2, 5, 6, 7, 8} ∨
        polygon = {2, 5, 6, 7, 9} ∨
        polygon = {2, 5, 6, 7, 11} ∨
        polygon = {2, 5, 6, 8, 9} ∨
        polygon = {2, 5, 6, 8, 11} ∨
        polygon = {2, 5, 6, 9, 11} ∨
        polygon = {2, 5, 7, 8, 9} ∨
        polygon = {2, 5, 7, 8, 11} ∨
        polygon = {2, 5, 7, 9, 11} ∨
        polygon = {2, 5, 8, 9, 11} ∨
        polygon = {2, 6, 7, 8, 9} ∨
        polygon = {2, 6, 7, 8, 11} ∨
        polygon = {2, 6, 7, 9, 11} ∨
        polygon = {2, 6, 8, 9, 11} ∨
        polygon = {2, 7, 8, 9, 11} ∨
        polygon = {5, 6, 7, 8, 9} ∨
        polygon = {5, 6, 7, 8, 11} ∨
        polygon = {5, 6, 7, 9, 11} ∨
        polygon = {5, 6, 8, 9, 11} ∨
        polygon = {5, 7, 8, 9, 11} ∨
        polygon = {6, 7, 8, 9, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 5, 6, 7, 8, 9, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 5, 6, 7, 8, 9, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 5, 6, 7, 8, 9, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 5, 6, 7, 8, 9, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 5, 6, 7, 8, 9, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 5, 6, 7, 8, 9, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 5, 6, 7, 8, 9, 11} \ {x, y} := by
    calc
      polygon = {2, 5, 6, 7, 8, 9, 11} \ ({2, 5, 6, 7, 8, 9, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 5, 6, 7, 8, 9, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5092 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 5, 6, 7, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {2, 5, 6, 7, 8} ∨
        polygon = {2, 5, 6, 7, 9} ∨
        polygon = {2, 5, 6, 7, 12} ∨
        polygon = {2, 5, 6, 8, 9} ∨
        polygon = {2, 5, 6, 8, 12} ∨
        polygon = {2, 5, 6, 9, 12} ∨
        polygon = {2, 5, 7, 8, 9} ∨
        polygon = {2, 5, 7, 8, 12} ∨
        polygon = {2, 5, 7, 9, 12} ∨
        polygon = {2, 5, 8, 9, 12} ∨
        polygon = {2, 6, 7, 8, 9} ∨
        polygon = {2, 6, 7, 8, 12} ∨
        polygon = {2, 6, 7, 9, 12} ∨
        polygon = {2, 6, 8, 9, 12} ∨
        polygon = {2, 7, 8, 9, 12} ∨
        polygon = {5, 6, 7, 8, 9} ∨
        polygon = {5, 6, 7, 8, 12} ∨
        polygon = {5, 6, 7, 9, 12} ∨
        polygon = {5, 6, 8, 9, 12} ∨
        polygon = {5, 7, 8, 9, 12} ∨
        polygon = {6, 7, 8, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 5, 6, 7, 8, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 5, 6, 7, 8, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 5, 6, 7, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 5, 6, 7, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 5, 6, 7, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 5, 6, 7, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 5, 6, 7, 8, 9, 12} \ {x, y} := by
    calc
      polygon = {2, 5, 6, 7, 8, 9, 12} \ ({2, 5, 6, 7, 8, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 5, 6, 7, 8, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3556 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 5, 6, 7, 8, 10, 11} →
      polygon.card = 5 →
        polygon = {2, 5, 6, 7, 8} ∨
        polygon = {2, 5, 6, 7, 10} ∨
        polygon = {2, 5, 6, 7, 11} ∨
        polygon = {2, 5, 6, 8, 10} ∨
        polygon = {2, 5, 6, 8, 11} ∨
        polygon = {2, 5, 6, 10, 11} ∨
        polygon = {2, 5, 7, 8, 10} ∨
        polygon = {2, 5, 7, 8, 11} ∨
        polygon = {2, 5, 7, 10, 11} ∨
        polygon = {2, 5, 8, 10, 11} ∨
        polygon = {2, 6, 7, 8, 10} ∨
        polygon = {2, 6, 7, 8, 11} ∨
        polygon = {2, 6, 7, 10, 11} ∨
        polygon = {2, 6, 8, 10, 11} ∨
        polygon = {2, 7, 8, 10, 11} ∨
        polygon = {5, 6, 7, 8, 10} ∨
        polygon = {5, 6, 7, 8, 11} ∨
        polygon = {5, 6, 7, 10, 11} ∨
        polygon = {5, 6, 8, 10, 11} ∨
        polygon = {5, 7, 8, 10, 11} ∨
        polygon = {6, 7, 8, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 5, 6, 7, 8, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 5, 6, 7, 8, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 5, 6, 7, 8, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 5, 6, 7, 8, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 5, 6, 7, 8, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 5, 6, 7, 8, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 5, 6, 7, 8, 10, 11} \ {x, y} := by
    calc
      polygon = {2, 5, 6, 7, 8, 10, 11} \ ({2, 5, 6, 7, 8, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 5, 6, 7, 8, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5604 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 5, 6, 7, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {2, 5, 6, 7, 8} ∨
        polygon = {2, 5, 6, 7, 10} ∨
        polygon = {2, 5, 6, 7, 12} ∨
        polygon = {2, 5, 6, 8, 10} ∨
        polygon = {2, 5, 6, 8, 12} ∨
        polygon = {2, 5, 6, 10, 12} ∨
        polygon = {2, 5, 7, 8, 10} ∨
        polygon = {2, 5, 7, 8, 12} ∨
        polygon = {2, 5, 7, 10, 12} ∨
        polygon = {2, 5, 8, 10, 12} ∨
        polygon = {2, 6, 7, 8, 10} ∨
        polygon = {2, 6, 7, 8, 12} ∨
        polygon = {2, 6, 7, 10, 12} ∨
        polygon = {2, 6, 8, 10, 12} ∨
        polygon = {2, 7, 8, 10, 12} ∨
        polygon = {5, 6, 7, 8, 10} ∨
        polygon = {5, 6, 7, 8, 12} ∨
        polygon = {5, 6, 7, 10, 12} ∨
        polygon = {5, 6, 8, 10, 12} ∨
        polygon = {5, 7, 8, 10, 12} ∨
        polygon = {6, 7, 8, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 5, 6, 7, 8, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 5, 6, 7, 8, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 5, 6, 7, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 5, 6, 7, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 5, 6, 7, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 5, 6, 7, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 5, 6, 7, 8, 10, 12} \ {x, y} := by
    calc
      polygon = {2, 5, 6, 7, 8, 10, 12} \ ({2, 5, 6, 7, 8, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 5, 6, 7, 8, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

end ErdosSzekeres

end
