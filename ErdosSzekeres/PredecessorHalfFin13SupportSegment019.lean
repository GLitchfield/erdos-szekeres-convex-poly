module

public import ErdosSzekeres.PredecessorHalfFin13Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 019. -/

theorem predecessorHalfFin13_fiveSubset_mask5429 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 4, 5, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 4, 5, 8} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 8, 10} ∨
        polygon = {0, 2, 4, 8, 12} ∨
        polygon = {0, 2, 4, 10, 12} ∨
        polygon = {0, 2, 5, 8, 10} ∨
        polygon = {0, 2, 5, 8, 12} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 8, 10, 12} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 4, 5, 8, 12} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 8, 10, 12} ∨
        polygon = {0, 5, 8, 10, 12} ∨
        polygon = {2, 4, 5, 8, 10} ∨
        polygon = {2, 4, 5, 8, 12} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {2, 4, 8, 10, 12} ∨
        polygon = {2, 5, 8, 10, 12} ∨
        polygon = {4, 5, 8, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 4, 5, 8, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 4, 5, 8, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 4, 5, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 4, 5, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 4, 5, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 4, 5, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 4, 5, 8, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 4, 5, 8, 10, 12} \ ({0, 2, 4, 5, 8, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 4, 5, 8, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5685 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 4, 5, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 9, 10} ∨
        polygon = {0, 2, 4, 9, 12} ∨
        polygon = {0, 2, 4, 10, 12} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 9, 10, 12} ∨
        polygon = {0, 5, 9, 10, 12} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {2, 4, 9, 10, 12} ∨
        polygon = {2, 5, 9, 10, 12} ∨
        polygon = {4, 5, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 4, 5, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 4, 5, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 4, 5, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 4, 5, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 4, 5, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 4, 5, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 4, 5, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 4, 5, 9, 10, 12} \ ({0, 2, 4, 5, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 4, 5, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask0981 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 4, 6, 7, 8, 9} →
      polygon.card = 5 →
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 2, 4, 6, 8} ∨
        polygon = {0, 2, 4, 6, 9} ∨
        polygon = {0, 2, 4, 7, 8} ∨
        polygon = {0, 2, 4, 7, 9} ∨
        polygon = {0, 2, 4, 8, 9} ∨
        polygon = {0, 2, 6, 7, 8} ∨
        polygon = {0, 2, 6, 7, 9} ∨
        polygon = {0, 2, 6, 8, 9} ∨
        polygon = {0, 2, 7, 8, 9} ∨
        polygon = {0, 4, 6, 7, 8} ∨
        polygon = {0, 4, 6, 7, 9} ∨
        polygon = {0, 4, 6, 8, 9} ∨
        polygon = {0, 4, 7, 8, 9} ∨
        polygon = {0, 6, 7, 8, 9} ∨
        polygon = {2, 4, 6, 7, 8} ∨
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {2, 4, 6, 8, 9} ∨
        polygon = {2, 4, 7, 8, 9} ∨
        polygon = {2, 6, 7, 8, 9} ∨
        polygon = {4, 6, 7, 8, 9} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 4, 6, 7, 8, 9} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 4, 6, 7, 8, 9} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 4, 6, 7, 8, 9} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 4, 6, 7, 8, 9} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 4, 6, 7, 8, 9} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 4, 6, 7, 8, 9} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 4, 6, 7, 8, 9} \ {x, y} := by
    calc
      polygon = {0, 2, 4, 6, 7, 8, 9} \ ({0, 2, 4, 6, 7, 8, 9} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 4, 6, 7, 8, 9} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1493 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 4, 6, 7, 8, 10} →
      polygon.card = 5 →
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 2, 4, 6, 8} ∨
        polygon = {0, 2, 4, 6, 10} ∨
        polygon = {0, 2, 4, 7, 8} ∨
        polygon = {0, 2, 4, 7, 10} ∨
        polygon = {0, 2, 4, 8, 10} ∨
        polygon = {0, 2, 6, 7, 8} ∨
        polygon = {0, 2, 6, 7, 10} ∨
        polygon = {0, 2, 6, 8, 10} ∨
        polygon = {0, 2, 7, 8, 10} ∨
        polygon = {0, 4, 6, 7, 8} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 4, 6, 8, 10} ∨
        polygon = {0, 4, 7, 8, 10} ∨
        polygon = {0, 6, 7, 8, 10} ∨
        polygon = {2, 4, 6, 7, 8} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {2, 4, 6, 8, 10} ∨
        polygon = {2, 4, 7, 8, 10} ∨
        polygon = {2, 6, 7, 8, 10} ∨
        polygon = {4, 6, 7, 8, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 4, 6, 7, 8, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 4, 6, 7, 8, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 4, 6, 7, 8, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 4, 6, 7, 8, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 4, 6, 7, 8, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 4, 6, 7, 8, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 4, 6, 7, 8, 10} \ {x, y} := by
    calc
      polygon = {0, 2, 4, 6, 7, 8, 10} \ ({0, 2, 4, 6, 7, 8, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 4, 6, 7, 8, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4565 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 4, 6, 7, 8, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 2, 4, 6, 8} ∨
        polygon = {0, 2, 4, 6, 12} ∨
        polygon = {0, 2, 4, 7, 8} ∨
        polygon = {0, 2, 4, 7, 12} ∨
        polygon = {0, 2, 4, 8, 12} ∨
        polygon = {0, 2, 6, 7, 8} ∨
        polygon = {0, 2, 6, 7, 12} ∨
        polygon = {0, 2, 6, 8, 12} ∨
        polygon = {0, 2, 7, 8, 12} ∨
        polygon = {0, 4, 6, 7, 8} ∨
        polygon = {0, 4, 6, 7, 12} ∨
        polygon = {0, 4, 6, 8, 12} ∨
        polygon = {0, 4, 7, 8, 12} ∨
        polygon = {0, 6, 7, 8, 12} ∨
        polygon = {2, 4, 6, 7, 8} ∨
        polygon = {2, 4, 6, 7, 12} ∨
        polygon = {2, 4, 6, 8, 12} ∨
        polygon = {2, 4, 7, 8, 12} ∨
        polygon = {2, 6, 7, 8, 12} ∨
        polygon = {4, 6, 7, 8, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 4, 6, 7, 8, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 4, 6, 7, 8, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 4, 6, 7, 8, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 4, 6, 7, 8, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 4, 6, 7, 8, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 4, 6, 7, 8, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 4, 6, 7, 8, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 4, 6, 7, 8, 12} \ ({0, 2, 4, 6, 7, 8, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 4, 6, 7, 8, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1749 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 4, 6, 7, 9, 10} →
      polygon.card = 5 →
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 2, 4, 6, 9} ∨
        polygon = {0, 2, 4, 6, 10} ∨
        polygon = {0, 2, 4, 7, 9} ∨
        polygon = {0, 2, 4, 7, 10} ∨
        polygon = {0, 2, 4, 9, 10} ∨
        polygon = {0, 2, 6, 7, 9} ∨
        polygon = {0, 2, 6, 7, 10} ∨
        polygon = {0, 2, 6, 9, 10} ∨
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 4, 6, 7, 9} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 4, 6, 9, 10} ∨
        polygon = {0, 4, 7, 9, 10} ∨
        polygon = {0, 6, 7, 9, 10} ∨
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {2, 6, 7, 9, 10} ∨
        polygon = {4, 6, 7, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 4, 6, 7, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 4, 6, 7, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 4, 6, 7, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 4, 6, 7, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 4, 6, 7, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 4, 6, 7, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 4, 6, 7, 9, 10} \ {x, y} := by
    calc
      polygon = {0, 2, 4, 6, 7, 9, 10} \ ({0, 2, 4, 6, 7, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 4, 6, 7, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4821 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 4, 6, 7, 9, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 2, 4, 6, 9} ∨
        polygon = {0, 2, 4, 6, 12} ∨
        polygon = {0, 2, 4, 7, 9} ∨
        polygon = {0, 2, 4, 7, 12} ∨
        polygon = {0, 2, 4, 9, 12} ∨
        polygon = {0, 2, 6, 7, 9} ∨
        polygon = {0, 2, 6, 7, 12} ∨
        polygon = {0, 2, 6, 9, 12} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 4, 6, 7, 9} ∨
        polygon = {0, 4, 6, 7, 12} ∨
        polygon = {0, 4, 6, 9, 12} ∨
        polygon = {0, 4, 7, 9, 12} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {2, 4, 6, 7, 12} ∨
        polygon = {2, 4, 6, 9, 12} ∨
        polygon = {2, 4, 7, 9, 12} ∨
        polygon = {2, 6, 7, 9, 12} ∨
        polygon = {4, 6, 7, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 4, 6, 7, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 4, 6, 7, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 4, 6, 7, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 4, 6, 7, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 4, 6, 7, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 4, 6, 7, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 4, 6, 7, 9, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 4, 6, 7, 9, 12} \ ({0, 2, 4, 6, 7, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 4, 6, 7, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5333 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 4, 6, 7, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 2, 4, 6, 10} ∨
        polygon = {0, 2, 4, 6, 12} ∨
        polygon = {0, 2, 4, 7, 10} ∨
        polygon = {0, 2, 4, 7, 12} ∨
        polygon = {0, 2, 4, 10, 12} ∨
        polygon = {0, 2, 6, 7, 10} ∨
        polygon = {0, 2, 6, 7, 12} ∨
        polygon = {0, 2, 6, 10, 12} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 4, 6, 7, 12} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 4, 7, 10, 12} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {2, 4, 6, 7, 12} ∨
        polygon = {2, 4, 6, 10, 12} ∨
        polygon = {2, 4, 7, 10, 12} ∨
        polygon = {2, 6, 7, 10, 12} ∨
        polygon = {4, 6, 7, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 4, 6, 7, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 4, 6, 7, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 4, 6, 7, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 4, 6, 7, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 4, 6, 7, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 4, 6, 7, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 4, 6, 7, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 4, 6, 7, 10, 12} \ ({0, 2, 4, 6, 7, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 4, 6, 7, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1877 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 4, 6, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {0, 2, 4, 6, 8} ∨
        polygon = {0, 2, 4, 6, 9} ∨
        polygon = {0, 2, 4, 6, 10} ∨
        polygon = {0, 2, 4, 8, 9} ∨
        polygon = {0, 2, 4, 8, 10} ∨
        polygon = {0, 2, 4, 9, 10} ∨
        polygon = {0, 2, 6, 8, 9} ∨
        polygon = {0, 2, 6, 8, 10} ∨
        polygon = {0, 2, 6, 9, 10} ∨
        polygon = {0, 2, 8, 9, 10} ∨
        polygon = {0, 4, 6, 8, 9} ∨
        polygon = {0, 4, 6, 8, 10} ∨
        polygon = {0, 4, 6, 9, 10} ∨
        polygon = {0, 4, 8, 9, 10} ∨
        polygon = {0, 6, 8, 9, 10} ∨
        polygon = {2, 4, 6, 8, 9} ∨
        polygon = {2, 4, 6, 8, 10} ∨
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {2, 4, 8, 9, 10} ∨
        polygon = {2, 6, 8, 9, 10} ∨
        polygon = {4, 6, 8, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 4, 6, 8, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 4, 6, 8, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 4, 6, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 4, 6, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 4, 6, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 4, 6, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 4, 6, 8, 9, 10} \ {x, y} := by
    calc
      polygon = {0, 2, 4, 6, 8, 9, 10} \ ({0, 2, 4, 6, 8, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 4, 6, 8, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4949 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 4, 6, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 4, 6, 8} ∨
        polygon = {0, 2, 4, 6, 9} ∨
        polygon = {0, 2, 4, 6, 12} ∨
        polygon = {0, 2, 4, 8, 9} ∨
        polygon = {0, 2, 4, 8, 12} ∨
        polygon = {0, 2, 4, 9, 12} ∨
        polygon = {0, 2, 6, 8, 9} ∨
        polygon = {0, 2, 6, 8, 12} ∨
        polygon = {0, 2, 6, 9, 12} ∨
        polygon = {0, 2, 8, 9, 12} ∨
        polygon = {0, 4, 6, 8, 9} ∨
        polygon = {0, 4, 6, 8, 12} ∨
        polygon = {0, 4, 6, 9, 12} ∨
        polygon = {0, 4, 8, 9, 12} ∨
        polygon = {0, 6, 8, 9, 12} ∨
        polygon = {2, 4, 6, 8, 9} ∨
        polygon = {2, 4, 6, 8, 12} ∨
        polygon = {2, 4, 6, 9, 12} ∨
        polygon = {2, 4, 8, 9, 12} ∨
        polygon = {2, 6, 8, 9, 12} ∨
        polygon = {4, 6, 8, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 4, 6, 8, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 4, 6, 8, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 4, 6, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 4, 6, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 4, 6, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 4, 6, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 4, 6, 8, 9, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 4, 6, 8, 9, 12} \ ({0, 2, 4, 6, 8, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 4, 6, 8, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5461 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 4, 6, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 4, 6, 8} ∨
        polygon = {0, 2, 4, 6, 10} ∨
        polygon = {0, 2, 4, 6, 12} ∨
        polygon = {0, 2, 4, 8, 10} ∨
        polygon = {0, 2, 4, 8, 12} ∨
        polygon = {0, 2, 4, 10, 12} ∨
        polygon = {0, 2, 6, 8, 10} ∨
        polygon = {0, 2, 6, 8, 12} ∨
        polygon = {0, 2, 6, 10, 12} ∨
        polygon = {0, 2, 8, 10, 12} ∨
        polygon = {0, 4, 6, 8, 10} ∨
        polygon = {0, 4, 6, 8, 12} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 4, 8, 10, 12} ∨
        polygon = {0, 6, 8, 10, 12} ∨
        polygon = {2, 4, 6, 8, 10} ∨
        polygon = {2, 4, 6, 8, 12} ∨
        polygon = {2, 4, 6, 10, 12} ∨
        polygon = {2, 4, 8, 10, 12} ∨
        polygon = {2, 6, 8, 10, 12} ∨
        polygon = {4, 6, 8, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 4, 6, 8, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 4, 6, 8, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 4, 6, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 4, 6, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 4, 6, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 4, 6, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 4, 6, 8, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 4, 6, 8, 10, 12} \ ({0, 2, 4, 6, 8, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 4, 6, 8, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5717 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 4, 6, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 4, 6, 9} ∨
        polygon = {0, 2, 4, 6, 10} ∨
        polygon = {0, 2, 4, 6, 12} ∨
        polygon = {0, 2, 4, 9, 10} ∨
        polygon = {0, 2, 4, 9, 12} ∨
        polygon = {0, 2, 4, 10, 12} ∨
        polygon = {0, 2, 6, 9, 10} ∨
        polygon = {0, 2, 6, 9, 12} ∨
        polygon = {0, 2, 6, 10, 12} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 4, 6, 9, 10} ∨
        polygon = {0, 4, 6, 9, 12} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 4, 9, 10, 12} ∨
        polygon = {0, 6, 9, 10, 12} ∨
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {2, 4, 6, 9, 12} ∨
        polygon = {2, 4, 6, 10, 12} ∨
        polygon = {2, 4, 9, 10, 12} ∨
        polygon = {2, 6, 9, 10, 12} ∨
        polygon = {4, 6, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 4, 6, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 4, 6, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 4, 6, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 4, 6, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 4, 6, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 4, 6, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 4, 6, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 4, 6, 9, 10, 12} \ ({0, 2, 4, 6, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 4, 6, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1941 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 4, 7, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {0, 2, 4, 7, 8} ∨
        polygon = {0, 2, 4, 7, 9} ∨
        polygon = {0, 2, 4, 7, 10} ∨
        polygon = {0, 2, 4, 8, 9} ∨
        polygon = {0, 2, 4, 8, 10} ∨
        polygon = {0, 2, 4, 9, 10} ∨
        polygon = {0, 2, 7, 8, 9} ∨
        polygon = {0, 2, 7, 8, 10} ∨
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 2, 8, 9, 10} ∨
        polygon = {0, 4, 7, 8, 9} ∨
        polygon = {0, 4, 7, 8, 10} ∨
        polygon = {0, 4, 7, 9, 10} ∨
        polygon = {0, 4, 8, 9, 10} ∨
        polygon = {0, 7, 8, 9, 10} ∨
        polygon = {2, 4, 7, 8, 9} ∨
        polygon = {2, 4, 7, 8, 10} ∨
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {2, 4, 8, 9, 10} ∨
        polygon = {2, 7, 8, 9, 10} ∨
        polygon = {4, 7, 8, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 4, 7, 8, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 4, 7, 8, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 4, 7, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 4, 7, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 4, 7, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 4, 7, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 4, 7, 8, 9, 10} \ {x, y} := by
    calc
      polygon = {0, 2, 4, 7, 8, 9, 10} \ ({0, 2, 4, 7, 8, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 4, 7, 8, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5013 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 4, 7, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 4, 7, 8} ∨
        polygon = {0, 2, 4, 7, 9} ∨
        polygon = {0, 2, 4, 7, 12} ∨
        polygon = {0, 2, 4, 8, 9} ∨
        polygon = {0, 2, 4, 8, 12} ∨
        polygon = {0, 2, 4, 9, 12} ∨
        polygon = {0, 2, 7, 8, 9} ∨
        polygon = {0, 2, 7, 8, 12} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 2, 8, 9, 12} ∨
        polygon = {0, 4, 7, 8, 9} ∨
        polygon = {0, 4, 7, 8, 12} ∨
        polygon = {0, 4, 7, 9, 12} ∨
        polygon = {0, 4, 8, 9, 12} ∨
        polygon = {0, 7, 8, 9, 12} ∨
        polygon = {2, 4, 7, 8, 9} ∨
        polygon = {2, 4, 7, 8, 12} ∨
        polygon = {2, 4, 7, 9, 12} ∨
        polygon = {2, 4, 8, 9, 12} ∨
        polygon = {2, 7, 8, 9, 12} ∨
        polygon = {4, 7, 8, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 4, 7, 8, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 4, 7, 8, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 4, 7, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 4, 7, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 4, 7, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 4, 7, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 4, 7, 8, 9, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 4, 7, 8, 9, 12} \ ({0, 2, 4, 7, 8, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 4, 7, 8, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5525 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 4, 7, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 4, 7, 8} ∨
        polygon = {0, 2, 4, 7, 10} ∨
        polygon = {0, 2, 4, 7, 12} ∨
        polygon = {0, 2, 4, 8, 10} ∨
        polygon = {0, 2, 4, 8, 12} ∨
        polygon = {0, 2, 4, 10, 12} ∨
        polygon = {0, 2, 7, 8, 10} ∨
        polygon = {0, 2, 7, 8, 12} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 2, 8, 10, 12} ∨
        polygon = {0, 4, 7, 8, 10} ∨
        polygon = {0, 4, 7, 8, 12} ∨
        polygon = {0, 4, 7, 10, 12} ∨
        polygon = {0, 4, 8, 10, 12} ∨
        polygon = {0, 7, 8, 10, 12} ∨
        polygon = {2, 4, 7, 8, 10} ∨
        polygon = {2, 4, 7, 8, 12} ∨
        polygon = {2, 4, 7, 10, 12} ∨
        polygon = {2, 4, 8, 10, 12} ∨
        polygon = {2, 7, 8, 10, 12} ∨
        polygon = {4, 7, 8, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 4, 7, 8, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 4, 7, 8, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 4, 7, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 4, 7, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 4, 7, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 4, 7, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 4, 7, 8, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 4, 7, 8, 10, 12} \ ({0, 2, 4, 7, 8, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 4, 7, 8, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5781 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 4, 7, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 4, 7, 9} ∨
        polygon = {0, 2, 4, 7, 10} ∨
        polygon = {0, 2, 4, 7, 12} ∨
        polygon = {0, 2, 4, 9, 10} ∨
        polygon = {0, 2, 4, 9, 12} ∨
        polygon = {0, 2, 4, 10, 12} ∨
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 4, 7, 9, 10} ∨
        polygon = {0, 4, 7, 9, 12} ∨
        polygon = {0, 4, 7, 10, 12} ∨
        polygon = {0, 4, 9, 10, 12} ∨
        polygon = {0, 7, 9, 10, 12} ∨
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {2, 4, 7, 9, 12} ∨
        polygon = {2, 4, 7, 10, 12} ∨
        polygon = {2, 4, 9, 10, 12} ∨
        polygon = {2, 7, 9, 10, 12} ∨
        polygon = {4, 7, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 4, 7, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 4, 7, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 4, 7, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 4, 7, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 4, 7, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 4, 7, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 4, 7, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 4, 7, 9, 10, 12} \ ({0, 2, 4, 7, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 4, 7, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5909 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 4, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 4, 8, 9} ∨
        polygon = {0, 2, 4, 8, 10} ∨
        polygon = {0, 2, 4, 8, 12} ∨
        polygon = {0, 2, 4, 9, 10} ∨
        polygon = {0, 2, 4, 9, 12} ∨
        polygon = {0, 2, 4, 10, 12} ∨
        polygon = {0, 2, 8, 9, 10} ∨
        polygon = {0, 2, 8, 9, 12} ∨
        polygon = {0, 2, 8, 10, 12} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 4, 8, 9, 10} ∨
        polygon = {0, 4, 8, 9, 12} ∨
        polygon = {0, 4, 8, 10, 12} ∨
        polygon = {0, 4, 9, 10, 12} ∨
        polygon = {0, 8, 9, 10, 12} ∨
        polygon = {2, 4, 8, 9, 10} ∨
        polygon = {2, 4, 8, 9, 12} ∨
        polygon = {2, 4, 8, 10, 12} ∨
        polygon = {2, 4, 9, 10, 12} ∨
        polygon = {2, 8, 9, 10, 12} ∨
        polygon = {4, 8, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 4, 8, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 4, 8, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 4, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 4, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 4, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 4, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 4, 8, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 4, 8, 9, 10, 12} \ ({0, 2, 4, 8, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 4, 8, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask0997 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 5, 6, 7, 8, 9} →
      polygon.card = 5 →
        polygon = {0, 2, 5, 6, 7} ∨
        polygon = {0, 2, 5, 6, 8} ∨
        polygon = {0, 2, 5, 6, 9} ∨
        polygon = {0, 2, 5, 7, 8} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 5, 8, 9} ∨
        polygon = {0, 2, 6, 7, 8} ∨
        polygon = {0, 2, 6, 7, 9} ∨
        polygon = {0, 2, 6, 8, 9} ∨
        polygon = {0, 2, 7, 8, 9} ∨
        polygon = {0, 5, 6, 7, 8} ∨
        polygon = {0, 5, 6, 7, 9} ∨
        polygon = {0, 5, 6, 8, 9} ∨
        polygon = {0, 5, 7, 8, 9} ∨
        polygon = {0, 6, 7, 8, 9} ∨
        polygon = {2, 5, 6, 7, 8} ∨
        polygon = {2, 5, 6, 7, 9} ∨
        polygon = {2, 5, 6, 8, 9} ∨
        polygon = {2, 5, 7, 8, 9} ∨
        polygon = {2, 6, 7, 8, 9} ∨
        polygon = {5, 6, 7, 8, 9} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 5, 6, 7, 8, 9} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 5, 6, 7, 8, 9} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 5, 6, 7, 8, 9} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 5, 6, 7, 8, 9} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 5, 6, 7, 8, 9} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 5, 6, 7, 8, 9} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 5, 6, 7, 8, 9} \ {x, y} := by
    calc
      polygon = {0, 2, 5, 6, 7, 8, 9} \ ({0, 2, 5, 6, 7, 8, 9} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 5, 6, 7, 8, 9} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1509 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 5, 6, 7, 8, 10} →
      polygon.card = 5 →
        polygon = {0, 2, 5, 6, 7} ∨
        polygon = {0, 2, 5, 6, 8} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 5, 7, 8} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 5, 8, 10} ∨
        polygon = {0, 2, 6, 7, 8} ∨
        polygon = {0, 2, 6, 7, 10} ∨
        polygon = {0, 2, 6, 8, 10} ∨
        polygon = {0, 2, 7, 8, 10} ∨
        polygon = {0, 5, 6, 7, 8} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 5, 6, 8, 10} ∨
        polygon = {0, 5, 7, 8, 10} ∨
        polygon = {0, 6, 7, 8, 10} ∨
        polygon = {2, 5, 6, 7, 8} ∨
        polygon = {2, 5, 6, 7, 10} ∨
        polygon = {2, 5, 6, 8, 10} ∨
        polygon = {2, 5, 7, 8, 10} ∨
        polygon = {2, 6, 7, 8, 10} ∨
        polygon = {5, 6, 7, 8, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 5, 6, 7, 8, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 5, 6, 7, 8, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 5, 6, 7, 8, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 5, 6, 7, 8, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 5, 6, 7, 8, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 5, 6, 7, 8, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 5, 6, 7, 8, 10} \ {x, y} := by
    calc
      polygon = {0, 2, 5, 6, 7, 8, 10} \ ({0, 2, 5, 6, 7, 8, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 5, 6, 7, 8, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4581 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 5, 6, 7, 8, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 5, 6, 7} ∨
        polygon = {0, 2, 5, 6, 8} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 5, 7, 8} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 5, 8, 12} ∨
        polygon = {0, 2, 6, 7, 8} ∨
        polygon = {0, 2, 6, 7, 12} ∨
        polygon = {0, 2, 6, 8, 12} ∨
        polygon = {0, 2, 7, 8, 12} ∨
        polygon = {0, 5, 6, 7, 8} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 5, 6, 8, 12} ∨
        polygon = {0, 5, 7, 8, 12} ∨
        polygon = {0, 6, 7, 8, 12} ∨
        polygon = {2, 5, 6, 7, 8} ∨
        polygon = {2, 5, 6, 7, 12} ∨
        polygon = {2, 5, 6, 8, 12} ∨
        polygon = {2, 5, 7, 8, 12} ∨
        polygon = {2, 6, 7, 8, 12} ∨
        polygon = {5, 6, 7, 8, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 5, 6, 7, 8, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 5, 6, 7, 8, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 5, 6, 7, 8, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 5, 6, 7, 8, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 5, 6, 7, 8, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 5, 6, 7, 8, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 5, 6, 7, 8, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 5, 6, 7, 8, 12} \ ({0, 2, 5, 6, 7, 8, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 5, 6, 7, 8, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1765 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 5, 6, 7, 9, 10} →
      polygon.card = 5 →
        polygon = {0, 2, 5, 6, 7} ∨
        polygon = {0, 2, 5, 6, 9} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 6, 7, 9} ∨
        polygon = {0, 2, 6, 7, 10} ∨
        polygon = {0, 2, 6, 9, 10} ∨
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 5, 6, 7, 9} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {0, 6, 7, 9, 10} ∨
        polygon = {2, 5, 6, 7, 9} ∨
        polygon = {2, 5, 6, 7, 10} ∨
        polygon = {2, 5, 6, 9, 10} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {2, 6, 7, 9, 10} ∨
        polygon = {5, 6, 7, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 5, 6, 7, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 5, 6, 7, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 5, 6, 7, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 5, 6, 7, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 5, 6, 7, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 5, 6, 7, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 5, 6, 7, 9, 10} \ {x, y} := by
    calc
      polygon = {0, 2, 5, 6, 7, 9, 10} \ ({0, 2, 5, 6, 7, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 5, 6, 7, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4837 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 5, 6, 7, 9, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 5, 6, 7} ∨
        polygon = {0, 2, 5, 6, 9} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 6, 7, 9} ∨
        polygon = {0, 2, 6, 7, 12} ∨
        polygon = {0, 2, 6, 9, 12} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 5, 6, 7, 9} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {2, 5, 6, 7, 9} ∨
        polygon = {2, 5, 6, 7, 12} ∨
        polygon = {2, 5, 6, 9, 12} ∨
        polygon = {2, 5, 7, 9, 12} ∨
        polygon = {2, 6, 7, 9, 12} ∨
        polygon = {5, 6, 7, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 5, 6, 7, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 5, 6, 7, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 5, 6, 7, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 5, 6, 7, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 5, 6, 7, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 5, 6, 7, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 5, 6, 7, 9, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 5, 6, 7, 9, 12} \ ({0, 2, 5, 6, 7, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 5, 6, 7, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5349 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 5, 6, 7, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 5, 6, 7} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 6, 7, 10} ∨
        polygon = {0, 2, 6, 7, 12} ∨
        polygon = {0, 2, 6, 10, 12} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {2, 5, 6, 7, 10} ∨
        polygon = {2, 5, 6, 7, 12} ∨
        polygon = {2, 5, 6, 10, 12} ∨
        polygon = {2, 5, 7, 10, 12} ∨
        polygon = {2, 6, 7, 10, 12} ∨
        polygon = {5, 6, 7, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 5, 6, 7, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 5, 6, 7, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 5, 6, 7, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 5, 6, 7, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 5, 6, 7, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 5, 6, 7, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 5, 6, 7, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 5, 6, 7, 10, 12} \ ({0, 2, 5, 6, 7, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 5, 6, 7, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1893 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 5, 6, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {0, 2, 5, 6, 8} ∨
        polygon = {0, 2, 5, 6, 9} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 5, 8, 9} ∨
        polygon = {0, 2, 5, 8, 10} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 6, 8, 9} ∨
        polygon = {0, 2, 6, 8, 10} ∨
        polygon = {0, 2, 6, 9, 10} ∨
        polygon = {0, 2, 8, 9, 10} ∨
        polygon = {0, 5, 6, 8, 9} ∨
        polygon = {0, 5, 6, 8, 10} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 5, 8, 9, 10} ∨
        polygon = {0, 6, 8, 9, 10} ∨
        polygon = {2, 5, 6, 8, 9} ∨
        polygon = {2, 5, 6, 8, 10} ∨
        polygon = {2, 5, 6, 9, 10} ∨
        polygon = {2, 5, 8, 9, 10} ∨
        polygon = {2, 6, 8, 9, 10} ∨
        polygon = {5, 6, 8, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 5, 6, 8, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 5, 6, 8, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 5, 6, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 5, 6, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 5, 6, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 5, 6, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 5, 6, 8, 9, 10} \ {x, y} := by
    calc
      polygon = {0, 2, 5, 6, 8, 9, 10} \ ({0, 2, 5, 6, 8, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 5, 6, 8, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4965 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 5, 6, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 5, 6, 8} ∨
        polygon = {0, 2, 5, 6, 9} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 5, 8, 9} ∨
        polygon = {0, 2, 5, 8, 12} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 6, 8, 9} ∨
        polygon = {0, 2, 6, 8, 12} ∨
        polygon = {0, 2, 6, 9, 12} ∨
        polygon = {0, 2, 8, 9, 12} ∨
        polygon = {0, 5, 6, 8, 9} ∨
        polygon = {0, 5, 6, 8, 12} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 5, 8, 9, 12} ∨
        polygon = {0, 6, 8, 9, 12} ∨
        polygon = {2, 5, 6, 8, 9} ∨
        polygon = {2, 5, 6, 8, 12} ∨
        polygon = {2, 5, 6, 9, 12} ∨
        polygon = {2, 5, 8, 9, 12} ∨
        polygon = {2, 6, 8, 9, 12} ∨
        polygon = {5, 6, 8, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 5, 6, 8, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 5, 6, 8, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 5, 6, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 5, 6, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 5, 6, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 5, 6, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 5, 6, 8, 9, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 5, 6, 8, 9, 12} \ ({0, 2, 5, 6, 8, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 5, 6, 8, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5477 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 5, 6, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 5, 6, 8} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 5, 8, 10} ∨
        polygon = {0, 2, 5, 8, 12} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 6, 8, 10} ∨
        polygon = {0, 2, 6, 8, 12} ∨
        polygon = {0, 2, 6, 10, 12} ∨
        polygon = {0, 2, 8, 10, 12} ∨
        polygon = {0, 5, 6, 8, 10} ∨
        polygon = {0, 5, 6, 8, 12} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 8, 10, 12} ∨
        polygon = {0, 6, 8, 10, 12} ∨
        polygon = {2, 5, 6, 8, 10} ∨
        polygon = {2, 5, 6, 8, 12} ∨
        polygon = {2, 5, 6, 10, 12} ∨
        polygon = {2, 5, 8, 10, 12} ∨
        polygon = {2, 6, 8, 10, 12} ∨
        polygon = {5, 6, 8, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 5, 6, 8, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 5, 6, 8, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 5, 6, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 5, 6, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 5, 6, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 5, 6, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 5, 6, 8, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 5, 6, 8, 10, 12} \ ({0, 2, 5, 6, 8, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 5, 6, 8, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5733 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 5, 6, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 5, 6, 9} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 6, 9, 10} ∨
        polygon = {0, 2, 6, 9, 12} ∨
        polygon = {0, 2, 6, 10, 12} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 9, 10, 12} ∨
        polygon = {0, 6, 9, 10, 12} ∨
        polygon = {2, 5, 6, 9, 10} ∨
        polygon = {2, 5, 6, 9, 12} ∨
        polygon = {2, 5, 6, 10, 12} ∨
        polygon = {2, 5, 9, 10, 12} ∨
        polygon = {2, 6, 9, 10, 12} ∨
        polygon = {5, 6, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 5, 6, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 5, 6, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 5, 6, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 5, 6, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 5, 6, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 5, 6, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 5, 6, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 5, 6, 9, 10, 12} \ ({0, 2, 5, 6, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 5, 6, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1957 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 5, 7, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {0, 2, 5, 7, 8} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 5, 8, 9} ∨
        polygon = {0, 2, 5, 8, 10} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 7, 8, 9} ∨
        polygon = {0, 2, 7, 8, 10} ∨
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 2, 8, 9, 10} ∨
        polygon = {0, 5, 7, 8, 9} ∨
        polygon = {0, 5, 7, 8, 10} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {0, 5, 8, 9, 10} ∨
        polygon = {0, 7, 8, 9, 10} ∨
        polygon = {2, 5, 7, 8, 9} ∨
        polygon = {2, 5, 7, 8, 10} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {2, 5, 8, 9, 10} ∨
        polygon = {2, 7, 8, 9, 10} ∨
        polygon = {5, 7, 8, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 5, 7, 8, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 5, 7, 8, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 5, 7, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 5, 7, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 5, 7, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 5, 7, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 5, 7, 8, 9, 10} \ {x, y} := by
    calc
      polygon = {0, 2, 5, 7, 8, 9, 10} \ ({0, 2, 5, 7, 8, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 5, 7, 8, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5029 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 5, 7, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 5, 7, 8} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 5, 8, 9} ∨
        polygon = {0, 2, 5, 8, 12} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 7, 8, 9} ∨
        polygon = {0, 2, 7, 8, 12} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 2, 8, 9, 12} ∨
        polygon = {0, 5, 7, 8, 9} ∨
        polygon = {0, 5, 7, 8, 12} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {0, 5, 8, 9, 12} ∨
        polygon = {0, 7, 8, 9, 12} ∨
        polygon = {2, 5, 7, 8, 9} ∨
        polygon = {2, 5, 7, 8, 12} ∨
        polygon = {2, 5, 7, 9, 12} ∨
        polygon = {2, 5, 8, 9, 12} ∨
        polygon = {2, 7, 8, 9, 12} ∨
        polygon = {5, 7, 8, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 5, 7, 8, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 5, 7, 8, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 5, 7, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 5, 7, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 5, 7, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 5, 7, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 5, 7, 8, 9, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 5, 7, 8, 9, 12} \ ({0, 2, 5, 7, 8, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 5, 7, 8, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5541 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 5, 7, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 5, 7, 8} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 5, 8, 10} ∨
        polygon = {0, 2, 5, 8, 12} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 7, 8, 10} ∨
        polygon = {0, 2, 7, 8, 12} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 2, 8, 10, 12} ∨
        polygon = {0, 5, 7, 8, 10} ∨
        polygon = {0, 5, 7, 8, 12} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 5, 8, 10, 12} ∨
        polygon = {0, 7, 8, 10, 12} ∨
        polygon = {2, 5, 7, 8, 10} ∨
        polygon = {2, 5, 7, 8, 12} ∨
        polygon = {2, 5, 7, 10, 12} ∨
        polygon = {2, 5, 8, 10, 12} ∨
        polygon = {2, 7, 8, 10, 12} ∨
        polygon = {5, 7, 8, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 5, 7, 8, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 5, 7, 8, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 5, 7, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 5, 7, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 5, 7, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 5, 7, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 5, 7, 8, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 5, 7, 8, 10, 12} \ ({0, 2, 5, 7, 8, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 5, 7, 8, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5797 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 5, 7, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 5, 9, 10, 12} ∨
        polygon = {0, 7, 9, 10, 12} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {2, 5, 7, 9, 12} ∨
        polygon = {2, 5, 7, 10, 12} ∨
        polygon = {2, 5, 9, 10, 12} ∨
        polygon = {2, 7, 9, 10, 12} ∨
        polygon = {5, 7, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 5, 7, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 5, 7, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 5, 7, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 5, 7, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 5, 7, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 5, 7, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 5, 7, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 5, 7, 9, 10, 12} \ ({0, 2, 5, 7, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 5, 7, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5925 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 5, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 5, 8, 9} ∨
        polygon = {0, 2, 5, 8, 10} ∨
        polygon = {0, 2, 5, 8, 12} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 8, 9, 10} ∨
        polygon = {0, 2, 8, 9, 12} ∨
        polygon = {0, 2, 8, 10, 12} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 5, 8, 9, 10} ∨
        polygon = {0, 5, 8, 9, 12} ∨
        polygon = {0, 5, 8, 10, 12} ∨
        polygon = {0, 5, 9, 10, 12} ∨
        polygon = {0, 8, 9, 10, 12} ∨
        polygon = {2, 5, 8, 9, 10} ∨
        polygon = {2, 5, 8, 9, 12} ∨
        polygon = {2, 5, 8, 10, 12} ∨
        polygon = {2, 5, 9, 10, 12} ∨
        polygon = {2, 8, 9, 10, 12} ∨
        polygon = {5, 8, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 5, 8, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 5, 8, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 5, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 5, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 5, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 5, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 5, 8, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 5, 8, 9, 10, 12} \ ({0, 2, 5, 8, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 5, 8, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1989 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 6, 7, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {0, 2, 6, 7, 8} ∨
        polygon = {0, 2, 6, 7, 9} ∨
        polygon = {0, 2, 6, 7, 10} ∨
        polygon = {0, 2, 6, 8, 9} ∨
        polygon = {0, 2, 6, 8, 10} ∨
        polygon = {0, 2, 6, 9, 10} ∨
        polygon = {0, 2, 7, 8, 9} ∨
        polygon = {0, 2, 7, 8, 10} ∨
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 2, 8, 9, 10} ∨
        polygon = {0, 6, 7, 8, 9} ∨
        polygon = {0, 6, 7, 8, 10} ∨
        polygon = {0, 6, 7, 9, 10} ∨
        polygon = {0, 6, 8, 9, 10} ∨
        polygon = {0, 7, 8, 9, 10} ∨
        polygon = {2, 6, 7, 8, 9} ∨
        polygon = {2, 6, 7, 8, 10} ∨
        polygon = {2, 6, 7, 9, 10} ∨
        polygon = {2, 6, 8, 9, 10} ∨
        polygon = {2, 7, 8, 9, 10} ∨
        polygon = {6, 7, 8, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 6, 7, 8, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 6, 7, 8, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 6, 7, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 6, 7, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 6, 7, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 6, 7, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 6, 7, 8, 9, 10} \ {x, y} := by
    calc
      polygon = {0, 2, 6, 7, 8, 9, 10} \ ({0, 2, 6, 7, 8, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 6, 7, 8, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5061 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 6, 7, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 6, 7, 8} ∨
        polygon = {0, 2, 6, 7, 9} ∨
        polygon = {0, 2, 6, 7, 12} ∨
        polygon = {0, 2, 6, 8, 9} ∨
        polygon = {0, 2, 6, 8, 12} ∨
        polygon = {0, 2, 6, 9, 12} ∨
        polygon = {0, 2, 7, 8, 9} ∨
        polygon = {0, 2, 7, 8, 12} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 2, 8, 9, 12} ∨
        polygon = {0, 6, 7, 8, 9} ∨
        polygon = {0, 6, 7, 8, 12} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {0, 6, 8, 9, 12} ∨
        polygon = {0, 7, 8, 9, 12} ∨
        polygon = {2, 6, 7, 8, 9} ∨
        polygon = {2, 6, 7, 8, 12} ∨
        polygon = {2, 6, 7, 9, 12} ∨
        polygon = {2, 6, 8, 9, 12} ∨
        polygon = {2, 7, 8, 9, 12} ∨
        polygon = {6, 7, 8, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 6, 7, 8, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 6, 7, 8, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 6, 7, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 6, 7, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 6, 7, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 6, 7, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 6, 7, 8, 9, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 6, 7, 8, 9, 12} \ ({0, 2, 6, 7, 8, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 6, 7, 8, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5573 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 6, 7, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 6, 7, 8} ∨
        polygon = {0, 2, 6, 7, 10} ∨
        polygon = {0, 2, 6, 7, 12} ∨
        polygon = {0, 2, 6, 8, 10} ∨
        polygon = {0, 2, 6, 8, 12} ∨
        polygon = {0, 2, 6, 10, 12} ∨
        polygon = {0, 2, 7, 8, 10} ∨
        polygon = {0, 2, 7, 8, 12} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 2, 8, 10, 12} ∨
        polygon = {0, 6, 7, 8, 10} ∨
        polygon = {0, 6, 7, 8, 12} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {0, 6, 8, 10, 12} ∨
        polygon = {0, 7, 8, 10, 12} ∨
        polygon = {2, 6, 7, 8, 10} ∨
        polygon = {2, 6, 7, 8, 12} ∨
        polygon = {2, 6, 7, 10, 12} ∨
        polygon = {2, 6, 8, 10, 12} ∨
        polygon = {2, 7, 8, 10, 12} ∨
        polygon = {6, 7, 8, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 6, 7, 8, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 6, 7, 8, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 6, 7, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 6, 7, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 6, 7, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 6, 7, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 6, 7, 8, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 6, 7, 8, 10, 12} \ ({0, 2, 6, 7, 8, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 6, 7, 8, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5829 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 6, 7, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 6, 7, 9} ∨
        polygon = {0, 2, 6, 7, 10} ∨
        polygon = {0, 2, 6, 7, 12} ∨
        polygon = {0, 2, 6, 9, 10} ∨
        polygon = {0, 2, 6, 9, 12} ∨
        polygon = {0, 2, 6, 10, 12} ∨
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 6, 7, 9, 10} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {0, 6, 9, 10, 12} ∨
        polygon = {0, 7, 9, 10, 12} ∨
        polygon = {2, 6, 7, 9, 10} ∨
        polygon = {2, 6, 7, 9, 12} ∨
        polygon = {2, 6, 7, 10, 12} ∨
        polygon = {2, 6, 9, 10, 12} ∨
        polygon = {2, 7, 9, 10, 12} ∨
        polygon = {6, 7, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 6, 7, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 6, 7, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 6, 7, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 6, 7, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 6, 7, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 6, 7, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 6, 7, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 6, 7, 9, 10, 12} \ ({0, 2, 6, 7, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 6, 7, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5957 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 6, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 6, 8, 9} ∨
        polygon = {0, 2, 6, 8, 10} ∨
        polygon = {0, 2, 6, 8, 12} ∨
        polygon = {0, 2, 6, 9, 10} ∨
        polygon = {0, 2, 6, 9, 12} ∨
        polygon = {0, 2, 6, 10, 12} ∨
        polygon = {0, 2, 8, 9, 10} ∨
        polygon = {0, 2, 8, 9, 12} ∨
        polygon = {0, 2, 8, 10, 12} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 6, 8, 9, 10} ∨
        polygon = {0, 6, 8, 9, 12} ∨
        polygon = {0, 6, 8, 10, 12} ∨
        polygon = {0, 6, 9, 10, 12} ∨
        polygon = {0, 8, 9, 10, 12} ∨
        polygon = {2, 6, 8, 9, 10} ∨
        polygon = {2, 6, 8, 9, 12} ∨
        polygon = {2, 6, 8, 10, 12} ∨
        polygon = {2, 6, 9, 10, 12} ∨
        polygon = {2, 8, 9, 10, 12} ∨
        polygon = {6, 8, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 6, 8, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 6, 8, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 6, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 6, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 6, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 6, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 6, 8, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 6, 8, 9, 10, 12} \ ({0, 2, 6, 8, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 6, 8, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask6021 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 7, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 7, 8, 9} ∨
        polygon = {0, 2, 7, 8, 10} ∨
        polygon = {0, 2, 7, 8, 12} ∨
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 2, 8, 9, 10} ∨
        polygon = {0, 2, 8, 9, 12} ∨
        polygon = {0, 2, 8, 10, 12} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 7, 8, 9, 10} ∨
        polygon = {0, 7, 8, 9, 12} ∨
        polygon = {0, 7, 8, 10, 12} ∨
        polygon = {0, 7, 9, 10, 12} ∨
        polygon = {0, 8, 9, 10, 12} ∨
        polygon = {2, 7, 8, 9, 10} ∨
        polygon = {2, 7, 8, 9, 12} ∨
        polygon = {2, 7, 8, 10, 12} ∨
        polygon = {2, 7, 9, 10, 12} ∨
        polygon = {2, 8, 9, 10, 12} ∨
        polygon = {7, 8, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 7, 8, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 7, 8, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 7, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 7, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 7, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 7, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 7, 8, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 7, 8, 9, 10, 12} \ ({0, 2, 7, 8, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 7, 8, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask0505 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 4, 5, 6, 7, 8} →
      polygon.card = 5 →
        polygon = {0, 3, 4, 5, 6} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 3, 4, 6, 8} ∨
        polygon = {0, 3, 4, 7, 8} ∨
        polygon = {0, 3, 5, 6, 7} ∨
        polygon = {0, 3, 5, 6, 8} ∨
        polygon = {0, 3, 5, 7, 8} ∨
        polygon = {0, 3, 6, 7, 8} ∨
        polygon = {0, 4, 5, 6, 7} ∨
        polygon = {0, 4, 5, 6, 8} ∨
        polygon = {0, 4, 5, 7, 8} ∨
        polygon = {0, 4, 6, 7, 8} ∨
        polygon = {0, 5, 6, 7, 8} ∨
        polygon = {3, 4, 5, 6, 7} ∨
        polygon = {3, 4, 5, 6, 8} ∨
        polygon = {3, 4, 5, 7, 8} ∨
        polygon = {3, 4, 6, 7, 8} ∨
        polygon = {3, 5, 6, 7, 8} ∨
        polygon = {4, 5, 6, 7, 8} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 4, 5, 6, 7, 8} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 4, 5, 6, 7, 8} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 4, 5, 6, 7, 8} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 4, 5, 6, 7, 8} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 4, 5, 6, 7, 8} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 4, 5, 6, 7, 8} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 4, 5, 6, 7, 8} \ {x, y} := by
    calc
      polygon = {0, 3, 4, 5, 6, 7, 8} \ ({0, 3, 4, 5, 6, 7, 8} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 4, 5, 6, 7, 8} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask0761 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 3, 4, 5, 6, 7, 9} →
      polygon.card = 5 →
        polygon = {0, 3, 4, 5, 6} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 5, 6, 7} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 4, 5, 6, 7} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 4, 6, 7, 9} ∨
        polygon = {0, 5, 6, 7, 9} ∨
        polygon = {3, 4, 5, 6, 7} ∨
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {4, 5, 6, 7, 9} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 3, 4, 5, 6, 7, 9} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 3, 4, 5, 6, 7, 9} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 3, 4, 5, 6, 7, 9} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 3, 4, 5, 6, 7, 9} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 3, 4, 5, 6, 7, 9} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 3, 4, 5, 6, 7, 9} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 3, 4, 5, 6, 7, 9} \ {x, y} := by
    calc
      polygon = {0, 3, 4, 5, 6, 7, 9} \ ({0, 3, 4, 5, 6, 7, 9} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 3, 4, 5, 6, 7, 9} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

end ErdosSzekeres

end
