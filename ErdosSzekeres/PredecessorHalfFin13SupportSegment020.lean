module

public import ErdosSzekeres.PredecessorHalfFin13Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 020. -/

theorem predecessorHalfFin13_fiveSubset_mask1273 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 4, 5, 6, 7, 10} →
      polygon.card = 5 →
        polygon = {0, 3, 4, 5, 6} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 5, 6, 7} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 4, 5, 6, 7} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {3, 4, 5, 6, 7} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {4, 5, 6, 7, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 4, 5, 6, 7, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 4, 5, 6, 7, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 4, 5, 6, 7, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 4, 5, 6, 7, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 4, 5, 6, 7, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 4, 5, 6, 7, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 4, 5, 6, 7, 10} \ {x, y} := by
    calc
      polygon = {0, 3, 4, 5, 6, 7, 10} \ ({0, 3, 4, 5, 6, 7, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 4, 5, 6, 7, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4345 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 4, 5, 6, 7, 12} →
      polygon.card = 5 →
        polygon = {0, 3, 4, 5, 6} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 5, 6, 7} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 4, 5, 6, 7} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 6, 7, 12} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {3, 4, 5, 6, 7} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {4, 5, 6, 7, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 4, 5, 6, 7, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 4, 5, 6, 7, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 4, 5, 6, 7, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 4, 5, 6, 7, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 4, 5, 6, 7, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 4, 5, 6, 7, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 4, 5, 6, 7, 12} \ {x, y} := by
    calc
      polygon = {0, 3, 4, 5, 6, 7, 12} \ ({0, 3, 4, 5, 6, 7, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 4, 5, 6, 7, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask0889 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 4, 5, 6, 8, 9} →
      polygon.card = 5 →
        polygon = {0, 3, 4, 5, 6} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 6, 8} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 8, 9} ∨
        polygon = {0, 3, 5, 6, 8} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 3, 5, 8, 9} ∨
        polygon = {0, 3, 6, 8, 9} ∨
        polygon = {0, 4, 5, 6, 8} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 4, 6, 8, 9} ∨
        polygon = {0, 5, 6, 8, 9} ∨
        polygon = {3, 4, 5, 6, 8} ∨
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {3, 4, 5, 8, 9} ∨
        polygon = {3, 4, 6, 8, 9} ∨
        polygon = {3, 5, 6, 8, 9} ∨
        polygon = {4, 5, 6, 8, 9} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 4, 5, 6, 8, 9} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 4, 5, 6, 8, 9} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 4, 5, 6, 8, 9} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 4, 5, 6, 8, 9} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 4, 5, 6, 8, 9} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 4, 5, 6, 8, 9} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 4, 5, 6, 8, 9} \ {x, y} := by
    calc
      polygon = {0, 3, 4, 5, 6, 8, 9} \ ({0, 3, 4, 5, 6, 8, 9} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 4, 5, 6, 8, 9} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1401 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 4, 5, 6, 8, 10} →
      polygon.card = 5 →
        polygon = {0, 3, 4, 5, 6} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 6, 8} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 8, 10} ∨
        polygon = {0, 3, 5, 6, 8} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 3, 6, 8, 10} ∨
        polygon = {0, 4, 5, 6, 8} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 4, 6, 8, 10} ∨
        polygon = {0, 5, 6, 8, 10} ∨
        polygon = {3, 4, 5, 6, 8} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {3, 4, 5, 8, 10} ∨
        polygon = {3, 4, 6, 8, 10} ∨
        polygon = {3, 5, 6, 8, 10} ∨
        polygon = {4, 5, 6, 8, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 4, 5, 6, 8, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 4, 5, 6, 8, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 4, 5, 6, 8, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 4, 5, 6, 8, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 4, 5, 6, 8, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 4, 5, 6, 8, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 4, 5, 6, 8, 10} \ {x, y} := by
    calc
      polygon = {0, 3, 4, 5, 6, 8, 10} \ ({0, 3, 4, 5, 6, 8, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 4, 5, 6, 8, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4473 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 4, 5, 6, 8, 12} →
      polygon.card = 5 →
        polygon = {0, 3, 4, 5, 6} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 6, 8} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 8, 12} ∨
        polygon = {0, 3, 5, 6, 8} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 5, 8, 12} ∨
        polygon = {0, 3, 6, 8, 12} ∨
        polygon = {0, 4, 5, 6, 8} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 8, 12} ∨
        polygon = {0, 4, 6, 8, 12} ∨
        polygon = {0, 5, 6, 8, 12} ∨
        polygon = {3, 4, 5, 6, 8} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {3, 4, 5, 8, 12} ∨
        polygon = {3, 4, 6, 8, 12} ∨
        polygon = {3, 5, 6, 8, 12} ∨
        polygon = {4, 5, 6, 8, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 4, 5, 6, 8, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 4, 5, 6, 8, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 4, 5, 6, 8, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 4, 5, 6, 8, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 4, 5, 6, 8, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 4, 5, 6, 8, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 4, 5, 6, 8, 12} \ {x, y} := by
    calc
      polygon = {0, 3, 4, 5, 6, 8, 12} \ ({0, 3, 4, 5, 6, 8, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 4, 5, 6, 8, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1657 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 4, 5, 6, 9, 10} →
      polygon.card = 5 →
        polygon = {0, 3, 4, 5, 6} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 6, 9, 10} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {4, 5, 6, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 4, 5, 6, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 4, 5, 6, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 4, 5, 6, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 4, 5, 6, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 4, 5, 6, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 4, 5, 6, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 4, 5, 6, 9, 10} \ {x, y} := by
    calc
      polygon = {0, 3, 4, 5, 6, 9, 10} \ ({0, 3, 4, 5, 6, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 4, 5, 6, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4729 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 4, 5, 6, 9, 12} →
      polygon.card = 5 →
        polygon = {0, 3, 4, 5, 6} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 6, 9, 12} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {4, 5, 6, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 4, 5, 6, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 4, 5, 6, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 4, 5, 6, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 4, 5, 6, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 4, 5, 6, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 4, 5, 6, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 4, 5, 6, 9, 12} \ {x, y} := by
    calc
      polygon = {0, 3, 4, 5, 6, 9, 12} \ ({0, 3, 4, 5, 6, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 4, 5, 6, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5241 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 4, 5, 6, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 3, 4, 5, 6} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {4, 5, 6, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 4, 5, 6, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 4, 5, 6, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 4, 5, 6, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 4, 5, 6, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 4, 5, 6, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 4, 5, 6, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 4, 5, 6, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 3, 4, 5, 6, 10, 12} \ ({0, 3, 4, 5, 6, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 4, 5, 6, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask0953 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 4, 5, 7, 8, 9} →
      polygon.card = 5 →
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 7, 8} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 8, 9} ∨
        polygon = {0, 3, 5, 7, 8} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 5, 8, 9} ∨
        polygon = {0, 3, 7, 8, 9} ∨
        polygon = {0, 4, 5, 7, 8} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 4, 7, 8, 9} ∨
        polygon = {0, 5, 7, 8, 9} ∨
        polygon = {3, 4, 5, 7, 8} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {3, 4, 5, 8, 9} ∨
        polygon = {3, 4, 7, 8, 9} ∨
        polygon = {3, 5, 7, 8, 9} ∨
        polygon = {4, 5, 7, 8, 9} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 4, 5, 7, 8, 9} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 4, 5, 7, 8, 9} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 4, 5, 7, 8, 9} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 4, 5, 7, 8, 9} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 4, 5, 7, 8, 9} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 4, 5, 7, 8, 9} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 4, 5, 7, 8, 9} \ {x, y} := by
    calc
      polygon = {0, 3, 4, 5, 7, 8, 9} \ ({0, 3, 4, 5, 7, 8, 9} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 4, 5, 7, 8, 9} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1465 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 4, 5, 7, 8, 10} →
      polygon.card = 5 →
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 7, 8} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 8, 10} ∨
        polygon = {0, 3, 5, 7, 8} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 4, 5, 7, 8} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 4, 7, 8, 10} ∨
        polygon = {0, 5, 7, 8, 10} ∨
        polygon = {3, 4, 5, 7, 8} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {3, 4, 5, 8, 10} ∨
        polygon = {3, 4, 7, 8, 10} ∨
        polygon = {3, 5, 7, 8, 10} ∨
        polygon = {4, 5, 7, 8, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 4, 5, 7, 8, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 4, 5, 7, 8, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 4, 5, 7, 8, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 4, 5, 7, 8, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 4, 5, 7, 8, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 4, 5, 7, 8, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 4, 5, 7, 8, 10} \ {x, y} := by
    calc
      polygon = {0, 3, 4, 5, 7, 8, 10} \ ({0, 3, 4, 5, 7, 8, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 4, 5, 7, 8, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4537 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 4, 5, 7, 8, 12} →
      polygon.card = 5 →
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 7, 8} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 8, 12} ∨
        polygon = {0, 3, 5, 7, 8} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 8, 12} ∨
        polygon = {0, 3, 7, 8, 12} ∨
        polygon = {0, 4, 5, 7, 8} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 8, 12} ∨
        polygon = {0, 4, 7, 8, 12} ∨
        polygon = {0, 5, 7, 8, 12} ∨
        polygon = {3, 4, 5, 7, 8} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {3, 4, 5, 8, 12} ∨
        polygon = {3, 4, 7, 8, 12} ∨
        polygon = {3, 5, 7, 8, 12} ∨
        polygon = {4, 5, 7, 8, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 4, 5, 7, 8, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 4, 5, 7, 8, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 4, 5, 7, 8, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 4, 5, 7, 8, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 4, 5, 7, 8, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 4, 5, 7, 8, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 4, 5, 7, 8, 12} \ {x, y} := by
    calc
      polygon = {0, 3, 4, 5, 7, 8, 12} \ ({0, 3, 4, 5, 7, 8, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 4, 5, 7, 8, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1721 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 4, 5, 7, 9, 10} →
      polygon.card = 5 →
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 7, 9, 10} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {4, 5, 7, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 4, 5, 7, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 4, 5, 7, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 4, 5, 7, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 4, 5, 7, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 4, 5, 7, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 4, 5, 7, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 4, 5, 7, 9, 10} \ {x, y} := by
    calc
      polygon = {0, 3, 4, 5, 7, 9, 10} \ ({0, 3, 4, 5, 7, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 4, 5, 7, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4793 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 4, 5, 7, 9, 12} →
      polygon.card = 5 →
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 7, 9, 12} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {4, 5, 7, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 4, 5, 7, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 4, 5, 7, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 4, 5, 7, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 4, 5, 7, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 4, 5, 7, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 4, 5, 7, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 4, 5, 7, 9, 12} \ {x, y} := by
    calc
      polygon = {0, 3, 4, 5, 7, 9, 12} \ ({0, 3, 4, 5, 7, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 4, 5, 7, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5305 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 4, 5, 7, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 7, 10, 12} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {4, 5, 7, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 4, 5, 7, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 4, 5, 7, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 4, 5, 7, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 4, 5, 7, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 4, 5, 7, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 4, 5, 7, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 4, 5, 7, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 3, 4, 5, 7, 10, 12} \ ({0, 3, 4, 5, 7, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 4, 5, 7, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1849 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 4, 5, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 8, 9} ∨
        polygon = {0, 3, 4, 8, 10} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 5, 8, 9} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 8, 9, 10} ∨
        polygon = {0, 5, 8, 9, 10} ∨
        polygon = {3, 4, 5, 8, 9} ∨
        polygon = {3, 4, 5, 8, 10} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {3, 4, 8, 9, 10} ∨
        polygon = {3, 5, 8, 9, 10} ∨
        polygon = {4, 5, 8, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 4, 5, 8, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 4, 5, 8, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 4, 5, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 4, 5, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 4, 5, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 4, 5, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 4, 5, 8, 9, 10} \ {x, y} := by
    calc
      polygon = {0, 3, 4, 5, 8, 9, 10} \ ({0, 3, 4, 5, 8, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 4, 5, 8, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4921 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 4, 5, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 8, 9} ∨
        polygon = {0, 3, 4, 8, 12} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 5, 8, 9} ∨
        polygon = {0, 3, 5, 8, 12} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 8, 9, 12} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 4, 5, 8, 12} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 8, 9, 12} ∨
        polygon = {0, 5, 8, 9, 12} ∨
        polygon = {3, 4, 5, 8, 9} ∨
        polygon = {3, 4, 5, 8, 12} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 8, 9, 12} ∨
        polygon = {3, 5, 8, 9, 12} ∨
        polygon = {4, 5, 8, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 4, 5, 8, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 4, 5, 8, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 4, 5, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 4, 5, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 4, 5, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 4, 5, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 4, 5, 8, 9, 12} \ {x, y} := by
    calc
      polygon = {0, 3, 4, 5, 8, 9, 12} \ ({0, 3, 4, 5, 8, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 4, 5, 8, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5433 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 4, 5, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 8, 10} ∨
        polygon = {0, 3, 4, 8, 12} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 3, 5, 8, 12} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 8, 10, 12} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 4, 5, 8, 12} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 8, 10, 12} ∨
        polygon = {0, 5, 8, 10, 12} ∨
        polygon = {3, 4, 5, 8, 10} ∨
        polygon = {3, 4, 5, 8, 12} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 8, 10, 12} ∨
        polygon = {3, 5, 8, 10, 12} ∨
        polygon = {4, 5, 8, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 4, 5, 8, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 4, 5, 8, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 4, 5, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 4, 5, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 4, 5, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 4, 5, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 4, 5, 8, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 3, 4, 5, 8, 10, 12} \ ({0, 3, 4, 5, 8, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 4, 5, 8, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5689 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 4, 5, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 9, 10, 12} ∨
        polygon = {0, 5, 9, 10, 12} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {4, 5, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 4, 5, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 4, 5, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 4, 5, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 4, 5, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 4, 5, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 4, 5, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 4, 5, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 3, 4, 5, 9, 10, 12} \ ({0, 3, 4, 5, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 4, 5, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask0985 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 4, 6, 7, 8, 9} →
      polygon.card = 5 →
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 3, 4, 6, 8} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 7, 8} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 8, 9} ∨
        polygon = {0, 3, 6, 7, 8} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 6, 8, 9} ∨
        polygon = {0, 3, 7, 8, 9} ∨
        polygon = {0, 4, 6, 7, 8} ∨
        polygon = {0, 4, 6, 7, 9} ∨
        polygon = {0, 4, 6, 8, 9} ∨
        polygon = {0, 4, 7, 8, 9} ∨
        polygon = {0, 6, 7, 8, 9} ∨
        polygon = {3, 4, 6, 7, 8} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {3, 4, 6, 8, 9} ∨
        polygon = {3, 4, 7, 8, 9} ∨
        polygon = {3, 6, 7, 8, 9} ∨
        polygon = {4, 6, 7, 8, 9} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 4, 6, 7, 8, 9} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 4, 6, 7, 8, 9} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 4, 6, 7, 8, 9} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 4, 6, 7, 8, 9} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 4, 6, 7, 8, 9} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 4, 6, 7, 8, 9} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 4, 6, 7, 8, 9} \ {x, y} := by
    calc
      polygon = {0, 3, 4, 6, 7, 8, 9} \ ({0, 3, 4, 6, 7, 8, 9} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 4, 6, 7, 8, 9} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1497 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 4, 6, 7, 8, 10} →
      polygon.card = 5 →
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 3, 4, 6, 8} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 7, 8} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 8, 10} ∨
        polygon = {0, 3, 6, 7, 8} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 6, 8, 10} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 4, 6, 7, 8} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 4, 6, 8, 10} ∨
        polygon = {0, 4, 7, 8, 10} ∨
        polygon = {0, 6, 7, 8, 10} ∨
        polygon = {3, 4, 6, 7, 8} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {3, 4, 6, 8, 10} ∨
        polygon = {3, 4, 7, 8, 10} ∨
        polygon = {3, 6, 7, 8, 10} ∨
        polygon = {4, 6, 7, 8, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 4, 6, 7, 8, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 4, 6, 7, 8, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 4, 6, 7, 8, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 4, 6, 7, 8, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 4, 6, 7, 8, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 4, 6, 7, 8, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 4, 6, 7, 8, 10} \ {x, y} := by
    calc
      polygon = {0, 3, 4, 6, 7, 8, 10} \ ({0, 3, 4, 6, 7, 8, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 4, 6, 7, 8, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4569 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 4, 6, 7, 8, 12} →
      polygon.card = 5 →
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 3, 4, 6, 8} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 7, 8} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 8, 12} ∨
        polygon = {0, 3, 6, 7, 8} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 8, 12} ∨
        polygon = {0, 3, 7, 8, 12} ∨
        polygon = {0, 4, 6, 7, 8} ∨
        polygon = {0, 4, 6, 7, 12} ∨
        polygon = {0, 4, 6, 8, 12} ∨
        polygon = {0, 4, 7, 8, 12} ∨
        polygon = {0, 6, 7, 8, 12} ∨
        polygon = {3, 4, 6, 7, 8} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 4, 6, 8, 12} ∨
        polygon = {3, 4, 7, 8, 12} ∨
        polygon = {3, 6, 7, 8, 12} ∨
        polygon = {4, 6, 7, 8, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 4, 6, 7, 8, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 4, 6, 7, 8, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 4, 6, 7, 8, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 4, 6, 7, 8, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 4, 6, 7, 8, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 4, 6, 7, 8, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 4, 6, 7, 8, 12} \ {x, y} := by
    calc
      polygon = {0, 3, 4, 6, 7, 8, 12} \ ({0, 3, 4, 6, 7, 8, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 4, 6, 7, 8, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1753 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 4, 6, 7, 9, 10} →
      polygon.card = 5 →
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 4, 6, 7, 9} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 4, 6, 9, 10} ∨
        polygon = {0, 4, 7, 9, 10} ∨
        polygon = {0, 6, 7, 9, 10} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {4, 6, 7, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 4, 6, 7, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 4, 6, 7, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 4, 6, 7, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 4, 6, 7, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 4, 6, 7, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 4, 6, 7, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 4, 6, 7, 9, 10} \ {x, y} := by
    calc
      polygon = {0, 3, 4, 6, 7, 9, 10} \ ({0, 3, 4, 6, 7, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 4, 6, 7, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4825 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 4, 6, 7, 9, 12} →
      polygon.card = 5 →
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 4, 6, 7, 9} ∨
        polygon = {0, 4, 6, 7, 12} ∨
        polygon = {0, 4, 6, 9, 12} ∨
        polygon = {0, 4, 7, 9, 12} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {4, 6, 7, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 4, 6, 7, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 4, 6, 7, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 4, 6, 7, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 4, 6, 7, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 4, 6, 7, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 4, 6, 7, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 4, 6, 7, 9, 12} \ {x, y} := by
    calc
      polygon = {0, 3, 4, 6, 7, 9, 12} \ ({0, 3, 4, 6, 7, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 4, 6, 7, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5337 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 4, 6, 7, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 4, 6, 7, 12} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 4, 7, 10, 12} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {4, 6, 7, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 4, 6, 7, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 4, 6, 7, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 4, 6, 7, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 4, 6, 7, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 4, 6, 7, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 4, 6, 7, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 4, 6, 7, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 3, 4, 6, 7, 10, 12} \ ({0, 3, 4, 6, 7, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 4, 6, 7, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1881 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 4, 6, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {0, 3, 4, 6, 8} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 8, 9} ∨
        polygon = {0, 3, 4, 8, 10} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 6, 8, 9} ∨
        polygon = {0, 3, 6, 8, 10} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 4, 6, 8, 9} ∨
        polygon = {0, 4, 6, 8, 10} ∨
        polygon = {0, 4, 6, 9, 10} ∨
        polygon = {0, 4, 8, 9, 10} ∨
        polygon = {0, 6, 8, 9, 10} ∨
        polygon = {3, 4, 6, 8, 9} ∨
        polygon = {3, 4, 6, 8, 10} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 4, 8, 9, 10} ∨
        polygon = {3, 6, 8, 9, 10} ∨
        polygon = {4, 6, 8, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 4, 6, 8, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 4, 6, 8, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 4, 6, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 4, 6, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 4, 6, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 4, 6, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 4, 6, 8, 9, 10} \ {x, y} := by
    calc
      polygon = {0, 3, 4, 6, 8, 9, 10} \ ({0, 3, 4, 6, 8, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 4, 6, 8, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4953 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 4, 6, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {0, 3, 4, 6, 8} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 8, 9} ∨
        polygon = {0, 3, 4, 8, 12} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 6, 8, 9} ∨
        polygon = {0, 3, 6, 8, 12} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 8, 9, 12} ∨
        polygon = {0, 4, 6, 8, 9} ∨
        polygon = {0, 4, 6, 8, 12} ∨
        polygon = {0, 4, 6, 9, 12} ∨
        polygon = {0, 4, 8, 9, 12} ∨
        polygon = {0, 6, 8, 9, 12} ∨
        polygon = {3, 4, 6, 8, 9} ∨
        polygon = {3, 4, 6, 8, 12} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 8, 9, 12} ∨
        polygon = {3, 6, 8, 9, 12} ∨
        polygon = {4, 6, 8, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 4, 6, 8, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 4, 6, 8, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 4, 6, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 4, 6, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 4, 6, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 4, 6, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 4, 6, 8, 9, 12} \ {x, y} := by
    calc
      polygon = {0, 3, 4, 6, 8, 9, 12} \ ({0, 3, 4, 6, 8, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 4, 6, 8, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5465 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 4, 6, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 3, 4, 6, 8} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 8, 10} ∨
        polygon = {0, 3, 4, 8, 12} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 6, 8, 10} ∨
        polygon = {0, 3, 6, 8, 12} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 8, 10, 12} ∨
        polygon = {0, 4, 6, 8, 10} ∨
        polygon = {0, 4, 6, 8, 12} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 4, 8, 10, 12} ∨
        polygon = {0, 6, 8, 10, 12} ∨
        polygon = {3, 4, 6, 8, 10} ∨
        polygon = {3, 4, 6, 8, 12} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 8, 10, 12} ∨
        polygon = {3, 6, 8, 10, 12} ∨
        polygon = {4, 6, 8, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 4, 6, 8, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 4, 6, 8, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 4, 6, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 4, 6, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 4, 6, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 4, 6, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 4, 6, 8, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 3, 4, 6, 8, 10, 12} \ ({0, 3, 4, 6, 8, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 4, 6, 8, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5721 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 4, 6, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 4, 6, 9, 10} ∨
        polygon = {0, 4, 6, 9, 12} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 4, 9, 10, 12} ∨
        polygon = {0, 6, 9, 10, 12} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {4, 6, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 4, 6, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 4, 6, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 4, 6, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 4, 6, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 4, 6, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 4, 6, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 4, 6, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 3, 4, 6, 9, 10, 12} \ ({0, 3, 4, 6, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 4, 6, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1945 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 4, 7, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {0, 3, 4, 7, 8} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 8, 9} ∨
        polygon = {0, 3, 4, 8, 10} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 7, 8, 9} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 4, 7, 8, 9} ∨
        polygon = {0, 4, 7, 8, 10} ∨
        polygon = {0, 4, 7, 9, 10} ∨
        polygon = {0, 4, 8, 9, 10} ∨
        polygon = {0, 7, 8, 9, 10} ∨
        polygon = {3, 4, 7, 8, 9} ∨
        polygon = {3, 4, 7, 8, 10} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {3, 4, 8, 9, 10} ∨
        polygon = {3, 7, 8, 9, 10} ∨
        polygon = {4, 7, 8, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 4, 7, 8, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 4, 7, 8, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 4, 7, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 4, 7, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 4, 7, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 4, 7, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 4, 7, 8, 9, 10} \ {x, y} := by
    calc
      polygon = {0, 3, 4, 7, 8, 9, 10} \ ({0, 3, 4, 7, 8, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 4, 7, 8, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5017 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 4, 7, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {0, 3, 4, 7, 8} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 8, 9} ∨
        polygon = {0, 3, 4, 8, 12} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 7, 8, 9} ∨
        polygon = {0, 3, 7, 8, 12} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 8, 9, 12} ∨
        polygon = {0, 4, 7, 8, 9} ∨
        polygon = {0, 4, 7, 8, 12} ∨
        polygon = {0, 4, 7, 9, 12} ∨
        polygon = {0, 4, 8, 9, 12} ∨
        polygon = {0, 7, 8, 9, 12} ∨
        polygon = {3, 4, 7, 8, 9} ∨
        polygon = {3, 4, 7, 8, 12} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 4, 8, 9, 12} ∨
        polygon = {3, 7, 8, 9, 12} ∨
        polygon = {4, 7, 8, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 4, 7, 8, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 4, 7, 8, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 4, 7, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 4, 7, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 4, 7, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 4, 7, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 4, 7, 8, 9, 12} \ {x, y} := by
    calc
      polygon = {0, 3, 4, 7, 8, 9, 12} \ ({0, 3, 4, 7, 8, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 4, 7, 8, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5529 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 4, 7, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 3, 4, 7, 8} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 8, 10} ∨
        polygon = {0, 3, 4, 8, 12} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 3, 7, 8, 12} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 8, 10, 12} ∨
        polygon = {0, 4, 7, 8, 10} ∨
        polygon = {0, 4, 7, 8, 12} ∨
        polygon = {0, 4, 7, 10, 12} ∨
        polygon = {0, 4, 8, 10, 12} ∨
        polygon = {0, 7, 8, 10, 12} ∨
        polygon = {3, 4, 7, 8, 10} ∨
        polygon = {3, 4, 7, 8, 12} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {3, 4, 8, 10, 12} ∨
        polygon = {3, 7, 8, 10, 12} ∨
        polygon = {4, 7, 8, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 4, 7, 8, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 4, 7, 8, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 4, 7, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 4, 7, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 4, 7, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 4, 7, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 4, 7, 8, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 3, 4, 7, 8, 10, 12} \ ({0, 3, 4, 7, 8, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 4, 7, 8, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5785 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 4, 7, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 4, 7, 9, 10} ∨
        polygon = {0, 4, 7, 9, 12} ∨
        polygon = {0, 4, 7, 10, 12} ∨
        polygon = {0, 4, 9, 10, 12} ∨
        polygon = {0, 7, 9, 10, 12} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {4, 7, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 4, 7, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 4, 7, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 4, 7, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 4, 7, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 4, 7, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 4, 7, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 4, 7, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 3, 4, 7, 9, 10, 12} \ ({0, 3, 4, 7, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 4, 7, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5913 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 4, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 3, 4, 8, 9} ∨
        polygon = {0, 3, 4, 8, 10} ∨
        polygon = {0, 3, 4, 8, 12} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 3, 8, 9, 12} ∨
        polygon = {0, 3, 8, 10, 12} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 4, 8, 9, 10} ∨
        polygon = {0, 4, 8, 9, 12} ∨
        polygon = {0, 4, 8, 10, 12} ∨
        polygon = {0, 4, 9, 10, 12} ∨
        polygon = {0, 8, 9, 10, 12} ∨
        polygon = {3, 4, 8, 9, 10} ∨
        polygon = {3, 4, 8, 9, 12} ∨
        polygon = {3, 4, 8, 10, 12} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 8, 9, 10, 12} ∨
        polygon = {4, 8, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 4, 8, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 4, 8, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 4, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 4, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 4, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 4, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 4, 8, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 3, 4, 8, 9, 10, 12} \ ({0, 3, 4, 8, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 4, 8, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1001 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 5, 6, 7, 8, 9} →
      polygon.card = 5 →
        polygon = {0, 3, 5, 6, 7} ∨
        polygon = {0, 3, 5, 6, 8} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 3, 5, 7, 8} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 5, 8, 9} ∨
        polygon = {0, 3, 6, 7, 8} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 6, 8, 9} ∨
        polygon = {0, 3, 7, 8, 9} ∨
        polygon = {0, 5, 6, 7, 8} ∨
        polygon = {0, 5, 6, 7, 9} ∨
        polygon = {0, 5, 6, 8, 9} ∨
        polygon = {0, 5, 7, 8, 9} ∨
        polygon = {0, 6, 7, 8, 9} ∨
        polygon = {3, 5, 6, 7, 8} ∨
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {3, 5, 6, 8, 9} ∨
        polygon = {3, 5, 7, 8, 9} ∨
        polygon = {3, 6, 7, 8, 9} ∨
        polygon = {5, 6, 7, 8, 9} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 5, 6, 7, 8, 9} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 5, 6, 7, 8, 9} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 5, 6, 7, 8, 9} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 5, 6, 7, 8, 9} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 5, 6, 7, 8, 9} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 5, 6, 7, 8, 9} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 5, 6, 7, 8, 9} \ {x, y} := by
    calc
      polygon = {0, 3, 5, 6, 7, 8, 9} \ ({0, 3, 5, 6, 7, 8, 9} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 5, 6, 7, 8, 9} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1513 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 5, 6, 7, 8, 10} →
      polygon.card = 5 →
        polygon = {0, 3, 5, 6, 7} ∨
        polygon = {0, 3, 5, 6, 8} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 3, 5, 7, 8} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 3, 6, 7, 8} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 6, 8, 10} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 5, 6, 7, 8} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 5, 6, 8, 10} ∨
        polygon = {0, 5, 7, 8, 10} ∨
        polygon = {0, 6, 7, 8, 10} ∨
        polygon = {3, 5, 6, 7, 8} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {3, 5, 6, 8, 10} ∨
        polygon = {3, 5, 7, 8, 10} ∨
        polygon = {3, 6, 7, 8, 10} ∨
        polygon = {5, 6, 7, 8, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 5, 6, 7, 8, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 5, 6, 7, 8, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 5, 6, 7, 8, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 5, 6, 7, 8, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 5, 6, 7, 8, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 5, 6, 7, 8, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 5, 6, 7, 8, 10} \ {x, y} := by
    calc
      polygon = {0, 3, 5, 6, 7, 8, 10} \ ({0, 3, 5, 6, 7, 8, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 5, 6, 7, 8, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4585 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 5, 6, 7, 8, 12} →
      polygon.card = 5 →
        polygon = {0, 3, 5, 6, 7} ∨
        polygon = {0, 3, 5, 6, 8} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 5, 7, 8} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 8, 12} ∨
        polygon = {0, 3, 6, 7, 8} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 8, 12} ∨
        polygon = {0, 3, 7, 8, 12} ∨
        polygon = {0, 5, 6, 7, 8} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 5, 6, 8, 12} ∨
        polygon = {0, 5, 7, 8, 12} ∨
        polygon = {0, 6, 7, 8, 12} ∨
        polygon = {3, 5, 6, 7, 8} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {3, 5, 6, 8, 12} ∨
        polygon = {3, 5, 7, 8, 12} ∨
        polygon = {3, 6, 7, 8, 12} ∨
        polygon = {5, 6, 7, 8, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 5, 6, 7, 8, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 5, 6, 7, 8, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 5, 6, 7, 8, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 5, 6, 7, 8, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 5, 6, 7, 8, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 5, 6, 7, 8, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 5, 6, 7, 8, 12} \ {x, y} := by
    calc
      polygon = {0, 3, 5, 6, 7, 8, 12} \ ({0, 3, 5, 6, 7, 8, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 5, 6, 7, 8, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1769 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 5, 6, 7, 9, 10} →
      polygon.card = 5 →
        polygon = {0, 3, 5, 6, 7} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 5, 6, 7, 9} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {0, 6, 7, 9, 10} ∨
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {5, 6, 7, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 5, 6, 7, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 5, 6, 7, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 5, 6, 7, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 5, 6, 7, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 5, 6, 7, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 5, 6, 7, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 5, 6, 7, 9, 10} \ {x, y} := by
    calc
      polygon = {0, 3, 5, 6, 7, 9, 10} \ ({0, 3, 5, 6, 7, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 5, 6, 7, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4841 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 5, 6, 7, 9, 12} →
      polygon.card = 5 →
        polygon = {0, 3, 5, 6, 7} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 5, 6, 7, 9} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {5, 6, 7, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 5, 6, 7, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 5, 6, 7, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 5, 6, 7, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 5, 6, 7, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 5, 6, 7, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 5, 6, 7, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 5, 6, 7, 9, 12} \ {x, y} := by
    calc
      polygon = {0, 3, 5, 6, 7, 9, 12} \ ({0, 3, 5, 6, 7, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 5, 6, 7, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5353 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 5, 6, 7, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 3, 5, 6, 7} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {5, 6, 7, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 5, 6, 7, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 5, 6, 7, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 5, 6, 7, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 5, 6, 7, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 5, 6, 7, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 5, 6, 7, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 5, 6, 7, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 3, 5, 6, 7, 10, 12} \ ({0, 3, 5, 6, 7, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 5, 6, 7, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1897 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 5, 6, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {0, 3, 5, 6, 8} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 3, 5, 8, 9} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 6, 8, 9} ∨
        polygon = {0, 3, 6, 8, 10} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 5, 6, 8, 9} ∨
        polygon = {0, 5, 6, 8, 10} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 5, 8, 9, 10} ∨
        polygon = {0, 6, 8, 9, 10} ∨
        polygon = {3, 5, 6, 8, 9} ∨
        polygon = {3, 5, 6, 8, 10} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {3, 5, 8, 9, 10} ∨
        polygon = {3, 6, 8, 9, 10} ∨
        polygon = {5, 6, 8, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 5, 6, 8, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 5, 6, 8, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 5, 6, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 5, 6, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 5, 6, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 5, 6, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 5, 6, 8, 9, 10} \ {x, y} := by
    calc
      polygon = {0, 3, 5, 6, 8, 9, 10} \ ({0, 3, 5, 6, 8, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 5, 6, 8, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

end ErdosSzekeres

end
