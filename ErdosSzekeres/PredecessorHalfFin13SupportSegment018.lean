module

public import ErdosSzekeres.PredecessorHalfFin13Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 018. -/

theorem predecessorHalfFin13_fiveSubset_mask1709 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 3, 5, 7, 9, 10} →
      polygon.card = 5 →
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {3, 5, 7, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 3, 5, 7, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 3, 5, 7, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 3, 5, 7, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 3, 5, 7, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 3, 5, 7, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 3, 5, 7, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 3, 5, 7, 9, 10} \ {x, y} := by
    calc
      polygon = {0, 2, 3, 5, 7, 9, 10} \ ({0, 2, 3, 5, 7, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 3, 5, 7, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4781 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 3, 5, 7, 9, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 5, 7, 9, 12} ∨
        polygon = {3, 5, 7, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 3, 5, 7, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 3, 5, 7, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 3, 5, 7, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 3, 5, 7, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 3, 5, 7, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 3, 5, 7, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 3, 5, 7, 9, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 3, 5, 7, 9, 12} \ ({0, 2, 3, 5, 7, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 3, 5, 7, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5293 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 3, 5, 7, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {2, 5, 7, 10, 12} ∨
        polygon = {3, 5, 7, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 3, 5, 7, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 3, 5, 7, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 3, 5, 7, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 3, 5, 7, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 3, 5, 7, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 3, 5, 7, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 3, 5, 7, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 3, 5, 7, 10, 12} \ ({0, 2, 3, 5, 7, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 3, 5, 7, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1837 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 3, 5, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {0, 2, 3, 5, 8} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 8, 9} ∨
        polygon = {0, 2, 3, 8, 10} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 5, 8, 9} ∨
        polygon = {0, 2, 5, 8, 10} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 8, 9, 10} ∨
        polygon = {0, 3, 5, 8, 9} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 5, 8, 9, 10} ∨
        polygon = {2, 3, 5, 8, 9} ∨
        polygon = {2, 3, 5, 8, 10} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 8, 9, 10} ∨
        polygon = {2, 5, 8, 9, 10} ∨
        polygon = {3, 5, 8, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 3, 5, 8, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 3, 5, 8, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 3, 5, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 3, 5, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 3, 5, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 3, 5, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 3, 5, 8, 9, 10} \ {x, y} := by
    calc
      polygon = {0, 2, 3, 5, 8, 9, 10} \ ({0, 2, 3, 5, 8, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 3, 5, 8, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4909 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 3, 5, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 3, 5, 8} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 8, 9} ∨
        polygon = {0, 2, 3, 8, 12} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 5, 8, 9} ∨
        polygon = {0, 2, 5, 8, 12} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 8, 9, 12} ∨
        polygon = {0, 3, 5, 8, 9} ∨
        polygon = {0, 3, 5, 8, 12} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 8, 9, 12} ∨
        polygon = {0, 5, 8, 9, 12} ∨
        polygon = {2, 3, 5, 8, 9} ∨
        polygon = {2, 3, 5, 8, 12} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 8, 9, 12} ∨
        polygon = {2, 5, 8, 9, 12} ∨
        polygon = {3, 5, 8, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 3, 5, 8, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 3, 5, 8, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 3, 5, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 3, 5, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 3, 5, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 3, 5, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 3, 5, 8, 9, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 3, 5, 8, 9, 12} \ ({0, 2, 3, 5, 8, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 3, 5, 8, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5421 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 3, 5, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 3, 5, 8} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 8, 10} ∨
        polygon = {0, 2, 3, 8, 12} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 5, 8, 10} ∨
        polygon = {0, 2, 5, 8, 12} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 8, 10, 12} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 3, 5, 8, 12} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 8, 10, 12} ∨
        polygon = {0, 5, 8, 10, 12} ∨
        polygon = {2, 3, 5, 8, 10} ∨
        polygon = {2, 3, 5, 8, 12} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 8, 10, 12} ∨
        polygon = {2, 5, 8, 10, 12} ∨
        polygon = {3, 5, 8, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 3, 5, 8, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 3, 5, 8, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 3, 5, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 3, 5, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 3, 5, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 3, 5, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 3, 5, 8, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 3, 5, 8, 10, 12} \ ({0, 2, 3, 5, 8, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 3, 5, 8, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5677 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 3, 5, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 5, 9, 10, 12} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 9, 10, 12} ∨
        polygon = {2, 5, 9, 10, 12} ∨
        polygon = {3, 5, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 3, 5, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 3, 5, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 3, 5, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 3, 5, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 3, 5, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 3, 5, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 3, 5, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 3, 5, 9, 10, 12} \ ({0, 2, 3, 5, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 3, 5, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask0973 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 3, 6, 7, 8, 9} →
      polygon.card = 5 →
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 2, 3, 6, 8} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 7, 8} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 8, 9} ∨
        polygon = {0, 2, 6, 7, 8} ∨
        polygon = {0, 2, 6, 7, 9} ∨
        polygon = {0, 2, 6, 8, 9} ∨
        polygon = {0, 2, 7, 8, 9} ∨
        polygon = {0, 3, 6, 7, 8} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 6, 8, 9} ∨
        polygon = {0, 3, 7, 8, 9} ∨
        polygon = {0, 6, 7, 8, 9} ∨
        polygon = {2, 3, 6, 7, 8} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {2, 3, 6, 8, 9} ∨
        polygon = {2, 3, 7, 8, 9} ∨
        polygon = {2, 6, 7, 8, 9} ∨
        polygon = {3, 6, 7, 8, 9} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 3, 6, 7, 8, 9} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 3, 6, 7, 8, 9} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 3, 6, 7, 8, 9} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 3, 6, 7, 8, 9} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 3, 6, 7, 8, 9} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 3, 6, 7, 8, 9} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 3, 6, 7, 8, 9} \ {x, y} := by
    calc
      polygon = {0, 2, 3, 6, 7, 8, 9} \ ({0, 2, 3, 6, 7, 8, 9} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 3, 6, 7, 8, 9} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1485 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 3, 6, 7, 8, 10} →
      polygon.card = 5 →
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 2, 3, 6, 8} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 7, 8} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 8, 10} ∨
        polygon = {0, 2, 6, 7, 8} ∨
        polygon = {0, 2, 6, 7, 10} ∨
        polygon = {0, 2, 6, 8, 10} ∨
        polygon = {0, 2, 7, 8, 10} ∨
        polygon = {0, 3, 6, 7, 8} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 6, 8, 10} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 6, 7, 8, 10} ∨
        polygon = {2, 3, 6, 7, 8} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {2, 3, 6, 8, 10} ∨
        polygon = {2, 3, 7, 8, 10} ∨
        polygon = {2, 6, 7, 8, 10} ∨
        polygon = {3, 6, 7, 8, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 3, 6, 7, 8, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 3, 6, 7, 8, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 3, 6, 7, 8, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 3, 6, 7, 8, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 3, 6, 7, 8, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 3, 6, 7, 8, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 3, 6, 7, 8, 10} \ {x, y} := by
    calc
      polygon = {0, 2, 3, 6, 7, 8, 10} \ ({0, 2, 3, 6, 7, 8, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 3, 6, 7, 8, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4557 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 3, 6, 7, 8, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 2, 3, 6, 8} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 7, 8} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 8, 12} ∨
        polygon = {0, 2, 6, 7, 8} ∨
        polygon = {0, 2, 6, 7, 12} ∨
        polygon = {0, 2, 6, 8, 12} ∨
        polygon = {0, 2, 7, 8, 12} ∨
        polygon = {0, 3, 6, 7, 8} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 8, 12} ∨
        polygon = {0, 3, 7, 8, 12} ∨
        polygon = {0, 6, 7, 8, 12} ∨
        polygon = {2, 3, 6, 7, 8} ∨
        polygon = {2, 3, 6, 7, 12} ∨
        polygon = {2, 3, 6, 8, 12} ∨
        polygon = {2, 3, 7, 8, 12} ∨
        polygon = {2, 6, 7, 8, 12} ∨
        polygon = {3, 6, 7, 8, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 3, 6, 7, 8, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 3, 6, 7, 8, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 3, 6, 7, 8, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 3, 6, 7, 8, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 3, 6, 7, 8, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 3, 6, 7, 8, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 3, 6, 7, 8, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 3, 6, 7, 8, 12} \ ({0, 2, 3, 6, 7, 8, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 3, 6, 7, 8, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1741 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 3, 6, 7, 9, 10} →
      polygon.card = 5 →
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 6, 7, 9} ∨
        polygon = {0, 2, 6, 7, 10} ∨
        polygon = {0, 2, 6, 9, 10} ∨
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 6, 7, 9, 10} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 6, 7, 9, 10} ∨
        polygon = {3, 6, 7, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 3, 6, 7, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 3, 6, 7, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 3, 6, 7, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 3, 6, 7, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 3, 6, 7, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 3, 6, 7, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 3, 6, 7, 9, 10} \ {x, y} := by
    calc
      polygon = {0, 2, 3, 6, 7, 9, 10} \ ({0, 2, 3, 6, 7, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 3, 6, 7, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4813 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 3, 6, 7, 9, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 6, 7, 9} ∨
        polygon = {0, 2, 6, 7, 12} ∨
        polygon = {0, 2, 6, 9, 12} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {2, 3, 6, 7, 12} ∨
        polygon = {2, 3, 6, 9, 12} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 6, 7, 9, 12} ∨
        polygon = {3, 6, 7, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 3, 6, 7, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 3, 6, 7, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 3, 6, 7, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 3, 6, 7, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 3, 6, 7, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 3, 6, 7, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 3, 6, 7, 9, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 3, 6, 7, 9, 12} \ ({0, 2, 3, 6, 7, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 3, 6, 7, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5325 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 3, 6, 7, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 6, 7, 10} ∨
        polygon = {0, 2, 6, 7, 12} ∨
        polygon = {0, 2, 6, 10, 12} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {2, 3, 6, 7, 12} ∨
        polygon = {2, 3, 6, 10, 12} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {2, 6, 7, 10, 12} ∨
        polygon = {3, 6, 7, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 3, 6, 7, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 3, 6, 7, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 3, 6, 7, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 3, 6, 7, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 3, 6, 7, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 3, 6, 7, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 3, 6, 7, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 3, 6, 7, 10, 12} \ ({0, 2, 3, 6, 7, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 3, 6, 7, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1869 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 3, 6, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {0, 2, 3, 6, 8} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 8, 9} ∨
        polygon = {0, 2, 3, 8, 10} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 6, 8, 9} ∨
        polygon = {0, 2, 6, 8, 10} ∨
        polygon = {0, 2, 6, 9, 10} ∨
        polygon = {0, 2, 8, 9, 10} ∨
        polygon = {0, 3, 6, 8, 9} ∨
        polygon = {0, 3, 6, 8, 10} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 6, 8, 9, 10} ∨
        polygon = {2, 3, 6, 8, 9} ∨
        polygon = {2, 3, 6, 8, 10} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {2, 3, 8, 9, 10} ∨
        polygon = {2, 6, 8, 9, 10} ∨
        polygon = {3, 6, 8, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 3, 6, 8, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 3, 6, 8, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 3, 6, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 3, 6, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 3, 6, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 3, 6, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 3, 6, 8, 9, 10} \ {x, y} := by
    calc
      polygon = {0, 2, 3, 6, 8, 9, 10} \ ({0, 2, 3, 6, 8, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 3, 6, 8, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4941 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 3, 6, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 3, 6, 8} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 8, 9} ∨
        polygon = {0, 2, 3, 8, 12} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 6, 8, 9} ∨
        polygon = {0, 2, 6, 8, 12} ∨
        polygon = {0, 2, 6, 9, 12} ∨
        polygon = {0, 2, 8, 9, 12} ∨
        polygon = {0, 3, 6, 8, 9} ∨
        polygon = {0, 3, 6, 8, 12} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 8, 9, 12} ∨
        polygon = {0, 6, 8, 9, 12} ∨
        polygon = {2, 3, 6, 8, 9} ∨
        polygon = {2, 3, 6, 8, 12} ∨
        polygon = {2, 3, 6, 9, 12} ∨
        polygon = {2, 3, 8, 9, 12} ∨
        polygon = {2, 6, 8, 9, 12} ∨
        polygon = {3, 6, 8, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 3, 6, 8, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 3, 6, 8, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 3, 6, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 3, 6, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 3, 6, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 3, 6, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 3, 6, 8, 9, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 3, 6, 8, 9, 12} \ ({0, 2, 3, 6, 8, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 3, 6, 8, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5453 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 3, 6, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 3, 6, 8} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 8, 10} ∨
        polygon = {0, 2, 3, 8, 12} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 6, 8, 10} ∨
        polygon = {0, 2, 6, 8, 12} ∨
        polygon = {0, 2, 6, 10, 12} ∨
        polygon = {0, 2, 8, 10, 12} ∨
        polygon = {0, 3, 6, 8, 10} ∨
        polygon = {0, 3, 6, 8, 12} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 8, 10, 12} ∨
        polygon = {0, 6, 8, 10, 12} ∨
        polygon = {2, 3, 6, 8, 10} ∨
        polygon = {2, 3, 6, 8, 12} ∨
        polygon = {2, 3, 6, 10, 12} ∨
        polygon = {2, 3, 8, 10, 12} ∨
        polygon = {2, 6, 8, 10, 12} ∨
        polygon = {3, 6, 8, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 3, 6, 8, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 3, 6, 8, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 3, 6, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 3, 6, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 3, 6, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 3, 6, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 3, 6, 8, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 3, 6, 8, 10, 12} \ ({0, 2, 3, 6, 8, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 3, 6, 8, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5709 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 3, 6, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 6, 9, 10} ∨
        polygon = {0, 2, 6, 9, 12} ∨
        polygon = {0, 2, 6, 10, 12} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 6, 9, 10, 12} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {2, 3, 6, 9, 12} ∨
        polygon = {2, 3, 6, 10, 12} ∨
        polygon = {2, 3, 9, 10, 12} ∨
        polygon = {2, 6, 9, 10, 12} ∨
        polygon = {3, 6, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 3, 6, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 3, 6, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 3, 6, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 3, 6, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 3, 6, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 3, 6, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 3, 6, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 3, 6, 9, 10, 12} \ ({0, 2, 3, 6, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 3, 6, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1933 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 3, 7, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {0, 2, 3, 7, 8} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 8, 9} ∨
        polygon = {0, 2, 3, 8, 10} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 7, 8, 9} ∨
        polygon = {0, 2, 7, 8, 10} ∨
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 2, 8, 9, 10} ∨
        polygon = {0, 3, 7, 8, 9} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 7, 8, 9, 10} ∨
        polygon = {2, 3, 7, 8, 9} ∨
        polygon = {2, 3, 7, 8, 10} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 3, 8, 9, 10} ∨
        polygon = {2, 7, 8, 9, 10} ∨
        polygon = {3, 7, 8, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 3, 7, 8, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 3, 7, 8, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 3, 7, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 3, 7, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 3, 7, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 3, 7, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 3, 7, 8, 9, 10} \ {x, y} := by
    calc
      polygon = {0, 2, 3, 7, 8, 9, 10} \ ({0, 2, 3, 7, 8, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 3, 7, 8, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5005 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 3, 7, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 3, 7, 8} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 8, 9} ∨
        polygon = {0, 2, 3, 8, 12} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 7, 8, 9} ∨
        polygon = {0, 2, 7, 8, 12} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 2, 8, 9, 12} ∨
        polygon = {0, 3, 7, 8, 9} ∨
        polygon = {0, 3, 7, 8, 12} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 8, 9, 12} ∨
        polygon = {0, 7, 8, 9, 12} ∨
        polygon = {2, 3, 7, 8, 9} ∨
        polygon = {2, 3, 7, 8, 12} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 3, 8, 9, 12} ∨
        polygon = {2, 7, 8, 9, 12} ∨
        polygon = {3, 7, 8, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 3, 7, 8, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 3, 7, 8, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 3, 7, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 3, 7, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 3, 7, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 3, 7, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 3, 7, 8, 9, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 3, 7, 8, 9, 12} \ ({0, 2, 3, 7, 8, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 3, 7, 8, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5517 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 3, 7, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 3, 7, 8} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 8, 10} ∨
        polygon = {0, 2, 3, 8, 12} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 7, 8, 10} ∨
        polygon = {0, 2, 7, 8, 12} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 2, 8, 10, 12} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 3, 7, 8, 12} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 8, 10, 12} ∨
        polygon = {0, 7, 8, 10, 12} ∨
        polygon = {2, 3, 7, 8, 10} ∨
        polygon = {2, 3, 7, 8, 12} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {2, 3, 8, 10, 12} ∨
        polygon = {2, 7, 8, 10, 12} ∨
        polygon = {3, 7, 8, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 3, 7, 8, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 3, 7, 8, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 3, 7, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 3, 7, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 3, 7, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 3, 7, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 3, 7, 8, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 3, 7, 8, 10, 12} \ ({0, 2, 3, 7, 8, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 3, 7, 8, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5773 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 3, 7, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 7, 9, 10, 12} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {2, 3, 9, 10, 12} ∨
        polygon = {2, 7, 9, 10, 12} ∨
        polygon = {3, 7, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 3, 7, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 3, 7, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 3, 7, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 3, 7, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 3, 7, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 3, 7, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 3, 7, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 3, 7, 9, 10, 12} \ ({0, 2, 3, 7, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 3, 7, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5901 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 3, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 3, 8, 9} ∨
        polygon = {0, 2, 3, 8, 10} ∨
        polygon = {0, 2, 3, 8, 12} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 8, 9, 10} ∨
        polygon = {0, 2, 8, 9, 12} ∨
        polygon = {0, 2, 8, 10, 12} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 3, 8, 9, 12} ∨
        polygon = {0, 3, 8, 10, 12} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 8, 9, 10, 12} ∨
        polygon = {2, 3, 8, 9, 10} ∨
        polygon = {2, 3, 8, 9, 12} ∨
        polygon = {2, 3, 8, 10, 12} ∨
        polygon = {2, 3, 9, 10, 12} ∨
        polygon = {2, 8, 9, 10, 12} ∨
        polygon = {3, 8, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 3, 8, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 3, 8, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 3, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 3, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 3, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 3, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 3, 8, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 3, 8, 9, 10, 12} \ ({0, 2, 3, 8, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 3, 8, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask0501 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 4, 5, 6, 7, 8} →
      polygon.card = 5 →
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 2, 4, 5, 8} ∨
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 2, 4, 6, 8} ∨
        polygon = {0, 2, 4, 7, 8} ∨
        polygon = {0, 2, 5, 6, 7} ∨
        polygon = {0, 2, 5, 6, 8} ∨
        polygon = {0, 2, 5, 7, 8} ∨
        polygon = {0, 2, 6, 7, 8} ∨
        polygon = {0, 4, 5, 6, 7} ∨
        polygon = {0, 4, 5, 6, 8} ∨
        polygon = {0, 4, 5, 7, 8} ∨
        polygon = {0, 4, 6, 7, 8} ∨
        polygon = {0, 5, 6, 7, 8} ∨
        polygon = {2, 4, 5, 6, 7} ∨
        polygon = {2, 4, 5, 6, 8} ∨
        polygon = {2, 4, 5, 7, 8} ∨
        polygon = {2, 4, 6, 7, 8} ∨
        polygon = {2, 5, 6, 7, 8} ∨
        polygon = {4, 5, 6, 7, 8} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 4, 5, 6, 7, 8} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 4, 5, 6, 7, 8} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 4, 5, 6, 7, 8} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 4, 5, 6, 7, 8} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 4, 5, 6, 7, 8} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 4, 5, 6, 7, 8} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 4, 5, 6, 7, 8} \ {x, y} := by
    calc
      polygon = {0, 2, 4, 5, 6, 7, 8} \ ({0, 2, 4, 5, 6, 7, 8} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 4, 5, 6, 7, 8} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask0757 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 4, 5, 6, 7, 9} →
      polygon.card = 5 →
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 2, 4, 6, 9} ∨
        polygon = {0, 2, 4, 7, 9} ∨
        polygon = {0, 2, 5, 6, 7} ∨
        polygon = {0, 2, 5, 6, 9} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 6, 7, 9} ∨
        polygon = {0, 4, 5, 6, 7} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 4, 6, 7, 9} ∨
        polygon = {0, 5, 6, 7, 9} ∨
        polygon = {2, 4, 5, 6, 7} ∨
        polygon = {2, 4, 5, 6, 9} ∨
        polygon = {2, 4, 5, 7, 9} ∨
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {2, 5, 6, 7, 9} ∨
        polygon = {4, 5, 6, 7, 9} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 4, 5, 6, 7, 9} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 4, 5, 6, 7, 9} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 4, 5, 6, 7, 9} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 4, 5, 6, 7, 9} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 4, 5, 6, 7, 9} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 4, 5, 6, 7, 9} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 4, 5, 6, 7, 9} \ {x, y} := by
    calc
      polygon = {0, 2, 4, 5, 6, 7, 9} \ ({0, 2, 4, 5, 6, 7, 9} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 4, 5, 6, 7, 9} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1269 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 4, 5, 6, 7, 10} →
      polygon.card = 5 →
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 2, 4, 6, 10} ∨
        polygon = {0, 2, 4, 7, 10} ∨
        polygon = {0, 2, 5, 6, 7} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 6, 7, 10} ∨
        polygon = {0, 4, 5, 6, 7} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {2, 4, 5, 6, 7} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {2, 5, 6, 7, 10} ∨
        polygon = {4, 5, 6, 7, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 4, 5, 6, 7, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 4, 5, 6, 7, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 4, 5, 6, 7, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 4, 5, 6, 7, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 4, 5, 6, 7, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 4, 5, 6, 7, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 4, 5, 6, 7, 10} \ {x, y} := by
    calc
      polygon = {0, 2, 4, 5, 6, 7, 10} \ ({0, 2, 4, 5, 6, 7, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 4, 5, 6, 7, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4341 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 4, 5, 6, 7, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 2, 4, 6, 12} ∨
        polygon = {0, 2, 4, 7, 12} ∨
        polygon = {0, 2, 5, 6, 7} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 6, 7, 12} ∨
        polygon = {0, 4, 5, 6, 7} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 6, 7, 12} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {2, 4, 5, 6, 7} ∨
        polygon = {2, 4, 5, 6, 12} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {2, 4, 6, 7, 12} ∨
        polygon = {2, 5, 6, 7, 12} ∨
        polygon = {4, 5, 6, 7, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 4, 5, 6, 7, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 4, 5, 6, 7, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 4, 5, 6, 7, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 4, 5, 6, 7, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 4, 5, 6, 7, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 4, 5, 6, 7, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 4, 5, 6, 7, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 4, 5, 6, 7, 12} \ ({0, 2, 4, 5, 6, 7, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 4, 5, 6, 7, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask0885 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 4, 5, 6, 8, 9} →
      polygon.card = 5 →
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 2, 4, 5, 8} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 2, 4, 6, 8} ∨
        polygon = {0, 2, 4, 6, 9} ∨
        polygon = {0, 2, 4, 8, 9} ∨
        polygon = {0, 2, 5, 6, 8} ∨
        polygon = {0, 2, 5, 6, 9} ∨
        polygon = {0, 2, 5, 8, 9} ∨
        polygon = {0, 2, 6, 8, 9} ∨
        polygon = {0, 4, 5, 6, 8} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 4, 6, 8, 9} ∨
        polygon = {0, 5, 6, 8, 9} ∨
        polygon = {2, 4, 5, 6, 8} ∨
        polygon = {2, 4, 5, 6, 9} ∨
        polygon = {2, 4, 5, 8, 9} ∨
        polygon = {2, 4, 6, 8, 9} ∨
        polygon = {2, 5, 6, 8, 9} ∨
        polygon = {4, 5, 6, 8, 9} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 4, 5, 6, 8, 9} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 4, 5, 6, 8, 9} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 4, 5, 6, 8, 9} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 4, 5, 6, 8, 9} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 4, 5, 6, 8, 9} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 4, 5, 6, 8, 9} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 4, 5, 6, 8, 9} \ {x, y} := by
    calc
      polygon = {0, 2, 4, 5, 6, 8, 9} \ ({0, 2, 4, 5, 6, 8, 9} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 4, 5, 6, 8, 9} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1397 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 4, 5, 6, 8, 10} →
      polygon.card = 5 →
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 2, 4, 5, 8} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 4, 6, 8} ∨
        polygon = {0, 2, 4, 6, 10} ∨
        polygon = {0, 2, 4, 8, 10} ∨
        polygon = {0, 2, 5, 6, 8} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 5, 8, 10} ∨
        polygon = {0, 2, 6, 8, 10} ∨
        polygon = {0, 4, 5, 6, 8} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 4, 6, 8, 10} ∨
        polygon = {0, 5, 6, 8, 10} ∨
        polygon = {2, 4, 5, 6, 8} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {2, 4, 5, 8, 10} ∨
        polygon = {2, 4, 6, 8, 10} ∨
        polygon = {2, 5, 6, 8, 10} ∨
        polygon = {4, 5, 6, 8, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 4, 5, 6, 8, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 4, 5, 6, 8, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 4, 5, 6, 8, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 4, 5, 6, 8, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 4, 5, 6, 8, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 4, 5, 6, 8, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 4, 5, 6, 8, 10} \ {x, y} := by
    calc
      polygon = {0, 2, 4, 5, 6, 8, 10} \ ({0, 2, 4, 5, 6, 8, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 4, 5, 6, 8, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4469 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 4, 5, 6, 8, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 2, 4, 5, 8} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 6, 8} ∨
        polygon = {0, 2, 4, 6, 12} ∨
        polygon = {0, 2, 4, 8, 12} ∨
        polygon = {0, 2, 5, 6, 8} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 5, 8, 12} ∨
        polygon = {0, 2, 6, 8, 12} ∨
        polygon = {0, 4, 5, 6, 8} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 8, 12} ∨
        polygon = {0, 4, 6, 8, 12} ∨
        polygon = {0, 5, 6, 8, 12} ∨
        polygon = {2, 4, 5, 6, 8} ∨
        polygon = {2, 4, 5, 6, 12} ∨
        polygon = {2, 4, 5, 8, 12} ∨
        polygon = {2, 4, 6, 8, 12} ∨
        polygon = {2, 5, 6, 8, 12} ∨
        polygon = {4, 5, 6, 8, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 4, 5, 6, 8, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 4, 5, 6, 8, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 4, 5, 6, 8, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 4, 5, 6, 8, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 4, 5, 6, 8, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 4, 5, 6, 8, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 4, 5, 6, 8, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 4, 5, 6, 8, 12} \ ({0, 2, 4, 5, 6, 8, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 4, 5, 6, 8, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1653 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 4, 5, 6, 9, 10} →
      polygon.card = 5 →
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 4, 6, 9} ∨
        polygon = {0, 2, 4, 6, 10} ∨
        polygon = {0, 2, 4, 9, 10} ∨
        polygon = {0, 2, 5, 6, 9} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 6, 9, 10} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 6, 9, 10} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {2, 4, 5, 6, 9} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {2, 5, 6, 9, 10} ∨
        polygon = {4, 5, 6, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 4, 5, 6, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 4, 5, 6, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 4, 5, 6, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 4, 5, 6, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 4, 5, 6, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 4, 5, 6, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 4, 5, 6, 9, 10} \ {x, y} := by
    calc
      polygon = {0, 2, 4, 5, 6, 9, 10} \ ({0, 2, 4, 5, 6, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 4, 5, 6, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4725 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 4, 5, 6, 9, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 6, 9} ∨
        polygon = {0, 2, 4, 6, 12} ∨
        polygon = {0, 2, 4, 9, 12} ∨
        polygon = {0, 2, 5, 6, 9} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 6, 9, 12} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 6, 9, 12} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {2, 4, 5, 6, 9} ∨
        polygon = {2, 4, 5, 6, 12} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {2, 4, 6, 9, 12} ∨
        polygon = {2, 5, 6, 9, 12} ∨
        polygon = {4, 5, 6, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 4, 5, 6, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 4, 5, 6, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 4, 5, 6, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 4, 5, 6, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 4, 5, 6, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 4, 5, 6, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 4, 5, 6, 9, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 4, 5, 6, 9, 12} \ ({0, 2, 4, 5, 6, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 4, 5, 6, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5237 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 4, 5, 6, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 6, 10} ∨
        polygon = {0, 2, 4, 6, 12} ∨
        polygon = {0, 2, 4, 10, 12} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 6, 10, 12} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {2, 4, 5, 6, 12} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {2, 4, 6, 10, 12} ∨
        polygon = {2, 5, 6, 10, 12} ∨
        polygon = {4, 5, 6, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 4, 5, 6, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 4, 5, 6, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 4, 5, 6, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 4, 5, 6, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 4, 5, 6, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 4, 5, 6, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 4, 5, 6, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 4, 5, 6, 10, 12} \ ({0, 2, 4, 5, 6, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 4, 5, 6, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask0949 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 4, 5, 7, 8, 9} →
      polygon.card = 5 →
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 2, 4, 5, 8} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 2, 4, 7, 8} ∨
        polygon = {0, 2, 4, 7, 9} ∨
        polygon = {0, 2, 4, 8, 9} ∨
        polygon = {0, 2, 5, 7, 8} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 5, 8, 9} ∨
        polygon = {0, 2, 7, 8, 9} ∨
        polygon = {0, 4, 5, 7, 8} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 4, 7, 8, 9} ∨
        polygon = {0, 5, 7, 8, 9} ∨
        polygon = {2, 4, 5, 7, 8} ∨
        polygon = {2, 4, 5, 7, 9} ∨
        polygon = {2, 4, 5, 8, 9} ∨
        polygon = {2, 4, 7, 8, 9} ∨
        polygon = {2, 5, 7, 8, 9} ∨
        polygon = {4, 5, 7, 8, 9} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 4, 5, 7, 8, 9} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 4, 5, 7, 8, 9} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 4, 5, 7, 8, 9} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 4, 5, 7, 8, 9} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 4, 5, 7, 8, 9} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 4, 5, 7, 8, 9} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 4, 5, 7, 8, 9} \ {x, y} := by
    calc
      polygon = {0, 2, 4, 5, 7, 8, 9} \ ({0, 2, 4, 5, 7, 8, 9} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 4, 5, 7, 8, 9} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1461 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 4, 5, 7, 8, 10} →
      polygon.card = 5 →
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 2, 4, 5, 8} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 4, 7, 8} ∨
        polygon = {0, 2, 4, 7, 10} ∨
        polygon = {0, 2, 4, 8, 10} ∨
        polygon = {0, 2, 5, 7, 8} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 5, 8, 10} ∨
        polygon = {0, 2, 7, 8, 10} ∨
        polygon = {0, 4, 5, 7, 8} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 4, 7, 8, 10} ∨
        polygon = {0, 5, 7, 8, 10} ∨
        polygon = {2, 4, 5, 7, 8} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {2, 4, 5, 8, 10} ∨
        polygon = {2, 4, 7, 8, 10} ∨
        polygon = {2, 5, 7, 8, 10} ∨
        polygon = {4, 5, 7, 8, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 4, 5, 7, 8, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 4, 5, 7, 8, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 4, 5, 7, 8, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 4, 5, 7, 8, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 4, 5, 7, 8, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 4, 5, 7, 8, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 4, 5, 7, 8, 10} \ {x, y} := by
    calc
      polygon = {0, 2, 4, 5, 7, 8, 10} \ ({0, 2, 4, 5, 7, 8, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 4, 5, 7, 8, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4533 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 4, 5, 7, 8, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 2, 4, 5, 8} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 7, 8} ∨
        polygon = {0, 2, 4, 7, 12} ∨
        polygon = {0, 2, 4, 8, 12} ∨
        polygon = {0, 2, 5, 7, 8} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 5, 8, 12} ∨
        polygon = {0, 2, 7, 8, 12} ∨
        polygon = {0, 4, 5, 7, 8} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 8, 12} ∨
        polygon = {0, 4, 7, 8, 12} ∨
        polygon = {0, 5, 7, 8, 12} ∨
        polygon = {2, 4, 5, 7, 8} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {2, 4, 5, 8, 12} ∨
        polygon = {2, 4, 7, 8, 12} ∨
        polygon = {2, 5, 7, 8, 12} ∨
        polygon = {4, 5, 7, 8, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 4, 5, 7, 8, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 4, 5, 7, 8, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 4, 5, 7, 8, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 4, 5, 7, 8, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 4, 5, 7, 8, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 4, 5, 7, 8, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 4, 5, 7, 8, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 4, 5, 7, 8, 12} \ ({0, 2, 4, 5, 7, 8, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 4, 5, 7, 8, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1717 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 4, 5, 7, 9, 10} →
      polygon.card = 5 →
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 4, 7, 9} ∨
        polygon = {0, 2, 4, 7, 10} ∨
        polygon = {0, 2, 4, 9, 10} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 7, 9, 10} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {2, 4, 5, 7, 9} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {4, 5, 7, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 4, 5, 7, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 4, 5, 7, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 4, 5, 7, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 4, 5, 7, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 4, 5, 7, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 4, 5, 7, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 4, 5, 7, 9, 10} \ {x, y} := by
    calc
      polygon = {0, 2, 4, 5, 7, 9, 10} \ ({0, 2, 4, 5, 7, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 4, 5, 7, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4789 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 4, 5, 7, 9, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 7, 9} ∨
        polygon = {0, 2, 4, 7, 12} ∨
        polygon = {0, 2, 4, 9, 12} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 7, 9, 12} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {2, 4, 5, 7, 9} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {2, 4, 7, 9, 12} ∨
        polygon = {2, 5, 7, 9, 12} ∨
        polygon = {4, 5, 7, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 4, 5, 7, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 4, 5, 7, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 4, 5, 7, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 4, 5, 7, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 4, 5, 7, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 4, 5, 7, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 4, 5, 7, 9, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 4, 5, 7, 9, 12} \ ({0, 2, 4, 5, 7, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 4, 5, 7, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5301 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 4, 5, 7, 10, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 7, 10} ∨
        polygon = {0, 2, 4, 7, 12} ∨
        polygon = {0, 2, 4, 10, 12} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 7, 10, 12} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {2, 4, 7, 10, 12} ∨
        polygon = {2, 5, 7, 10, 12} ∨
        polygon = {4, 5, 7, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 4, 5, 7, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 4, 5, 7, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 4, 5, 7, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 4, 5, 7, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 4, 5, 7, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 4, 5, 7, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 4, 5, 7, 10, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 4, 5, 7, 10, 12} \ ({0, 2, 4, 5, 7, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 4, 5, 7, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1845 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 4, 5, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {0, 2, 4, 5, 8} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 4, 8, 9} ∨
        polygon = {0, 2, 4, 8, 10} ∨
        polygon = {0, 2, 4, 9, 10} ∨
        polygon = {0, 2, 5, 8, 9} ∨
        polygon = {0, 2, 5, 8, 10} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 8, 9, 10} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 8, 9, 10} ∨
        polygon = {0, 5, 8, 9, 10} ∨
        polygon = {2, 4, 5, 8, 9} ∨
        polygon = {2, 4, 5, 8, 10} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {2, 4, 8, 9, 10} ∨
        polygon = {2, 5, 8, 9, 10} ∨
        polygon = {4, 5, 8, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 4, 5, 8, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 4, 5, 8, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 4, 5, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 4, 5, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 4, 5, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 4, 5, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 4, 5, 8, 9, 10} \ {x, y} := by
    calc
      polygon = {0, 2, 4, 5, 8, 9, 10} \ ({0, 2, 4, 5, 8, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 4, 5, 8, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4917 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {0, 2, 4, 5, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {0, 2, 4, 5, 8} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 8, 9} ∨
        polygon = {0, 2, 4, 8, 12} ∨
        polygon = {0, 2, 4, 9, 12} ∨
        polygon = {0, 2, 5, 8, 9} ∨
        polygon = {0, 2, 5, 8, 12} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 8, 9, 12} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 4, 5, 8, 12} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 8, 9, 12} ∨
        polygon = {0, 5, 8, 9, 12} ∨
        polygon = {2, 4, 5, 8, 9} ∨
        polygon = {2, 4, 5, 8, 12} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {2, 4, 8, 9, 12} ∨
        polygon = {2, 5, 8, 9, 12} ∨
        polygon = {4, 5, 8, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({0, 2, 4, 5, 8, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({0, 2, 4, 5, 8, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {0, 2, 4, 5, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {0, 2, 4, 5, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({0, 2, 4, 5, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({0, 2, 4, 5, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {0, 2, 4, 5, 8, 9, 12} \ {x, y} := by
    calc
      polygon = {0, 2, 4, 5, 8, 9, 12} \ ({0, 2, 4, 5, 8, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {0, 2, 4, 5, 8, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

end ErdosSzekeres

end
