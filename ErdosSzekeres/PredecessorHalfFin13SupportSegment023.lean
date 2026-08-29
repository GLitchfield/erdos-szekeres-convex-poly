module

public import ErdosSzekeres.PredecessorHalfFin13Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 023. -/

theorem predecessorHalfFin13_fiveSubset_mask4572 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 6, 7, 8, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {2, 3, 4, 6, 8} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 7, 8} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 8, 12} ∨
        polygon = {2, 3, 6, 7, 8} ∨
        polygon = {2, 3, 6, 7, 12} ∨
        polygon = {2, 3, 6, 8, 12} ∨
        polygon = {2, 3, 7, 8, 12} ∨
        polygon = {2, 4, 6, 7, 8} ∨
        polygon = {2, 4, 6, 7, 12} ∨
        polygon = {2, 4, 6, 8, 12} ∨
        polygon = {2, 4, 7, 8, 12} ∨
        polygon = {2, 6, 7, 8, 12} ∨
        polygon = {3, 4, 6, 7, 8} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 4, 6, 8, 12} ∨
        polygon = {3, 4, 7, 8, 12} ∨
        polygon = {3, 6, 7, 8, 12} ∨
        polygon = {4, 6, 7, 8, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 6, 7, 8, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 6, 7, 8, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 6, 7, 8, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 6, 7, 8, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 6, 7, 8, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 6, 7, 8, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 6, 7, 8, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 6, 7, 8, 12} \ ({2, 3, 4, 6, 7, 8, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 6, 7, 8, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1756 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 6, 7, 9, 10} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {2, 6, 7, 9, 10} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {4, 6, 7, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 6, 7, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 6, 7, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 6, 7, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 6, 7, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 6, 7, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 6, 7, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 6, 7, 9, 10} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 6, 7, 9, 10} \ ({2, 3, 4, 6, 7, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 6, 7, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask2780 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 6, 7, 9, 11} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 6, 11} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 7, 11} ∨
        polygon = {2, 3, 4, 9, 11} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {2, 3, 6, 7, 11} ∨
        polygon = {2, 3, 6, 9, 11} ∨
        polygon = {2, 3, 7, 9, 11} ∨
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {2, 4, 6, 7, 11} ∨
        polygon = {2, 4, 6, 9, 11} ∨
        polygon = {2, 4, 7, 9, 11} ∨
        polygon = {2, 6, 7, 9, 11} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {3, 4, 6, 7, 11} ∨
        polygon = {3, 4, 6, 9, 11} ∨
        polygon = {3, 4, 7, 9, 11} ∨
        polygon = {3, 6, 7, 9, 11} ∨
        polygon = {4, 6, 7, 9, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 6, 7, 9, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 6, 7, 9, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 6, 7, 9, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 6, 7, 9, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 6, 7, 9, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 6, 7, 9, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 6, 7, 9, 11} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 6, 7, 9, 11} \ ({2, 3, 4, 6, 7, 9, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 6, 7, 9, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4828 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 6, 7, 9, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {2, 3, 6, 7, 12} ∨
        polygon = {2, 3, 6, 9, 12} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {2, 4, 6, 7, 12} ∨
        polygon = {2, 4, 6, 9, 12} ∨
        polygon = {2, 4, 7, 9, 12} ∨
        polygon = {2, 6, 7, 9, 12} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {4, 6, 7, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 6, 7, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 6, 7, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 6, 7, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 6, 7, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 6, 7, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 6, 7, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 6, 7, 9, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 6, 7, 9, 12} \ ({2, 3, 4, 6, 7, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 6, 7, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3292 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 6, 7, 10, 11} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 6, 11} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 7, 11} ∨
        polygon = {2, 3, 4, 10, 11} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {2, 3, 6, 7, 11} ∨
        polygon = {2, 3, 6, 10, 11} ∨
        polygon = {2, 3, 7, 10, 11} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {2, 4, 6, 7, 11} ∨
        polygon = {2, 4, 6, 10, 11} ∨
        polygon = {2, 4, 7, 10, 11} ∨
        polygon = {2, 6, 7, 10, 11} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {3, 4, 6, 7, 11} ∨
        polygon = {3, 4, 6, 10, 11} ∨
        polygon = {3, 4, 7, 10, 11} ∨
        polygon = {3, 6, 7, 10, 11} ∨
        polygon = {4, 6, 7, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 6, 7, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 6, 7, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 6, 7, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 6, 7, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 6, 7, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 6, 7, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 6, 7, 10, 11} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 6, 7, 10, 11} \ ({2, 3, 4, 6, 7, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 6, 7, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5340 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 6, 7, 10, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {2, 3, 6, 7, 12} ∨
        polygon = {2, 3, 6, 10, 12} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {2, 4, 6, 7, 12} ∨
        polygon = {2, 4, 6, 10, 12} ∨
        polygon = {2, 4, 7, 10, 12} ∨
        polygon = {2, 6, 7, 10, 12} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {4, 6, 7, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 6, 7, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 6, 7, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 6, 7, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 6, 7, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 6, 7, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 6, 7, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 6, 7, 10, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 6, 7, 10, 12} \ ({2, 3, 4, 6, 7, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 6, 7, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1884 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 6, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 6, 8} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 8, 9} ∨
        polygon = {2, 3, 4, 8, 10} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 6, 8, 9} ∨
        polygon = {2, 3, 6, 8, 10} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {2, 3, 8, 9, 10} ∨
        polygon = {2, 4, 6, 8, 9} ∨
        polygon = {2, 4, 6, 8, 10} ∨
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {2, 4, 8, 9, 10} ∨
        polygon = {2, 6, 8, 9, 10} ∨
        polygon = {3, 4, 6, 8, 9} ∨
        polygon = {3, 4, 6, 8, 10} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 4, 8, 9, 10} ∨
        polygon = {3, 6, 8, 9, 10} ∨
        polygon = {4, 6, 8, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 6, 8, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 6, 8, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 6, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 6, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 6, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 6, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 6, 8, 9, 10} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 6, 8, 9, 10} \ ({2, 3, 4, 6, 8, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 6, 8, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4956 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 6, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 6, 8} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 8, 9} ∨
        polygon = {2, 3, 4, 8, 12} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 6, 8, 9} ∨
        polygon = {2, 3, 6, 8, 12} ∨
        polygon = {2, 3, 6, 9, 12} ∨
        polygon = {2, 3, 8, 9, 12} ∨
        polygon = {2, 4, 6, 8, 9} ∨
        polygon = {2, 4, 6, 8, 12} ∨
        polygon = {2, 4, 6, 9, 12} ∨
        polygon = {2, 4, 8, 9, 12} ∨
        polygon = {2, 6, 8, 9, 12} ∨
        polygon = {3, 4, 6, 8, 9} ∨
        polygon = {3, 4, 6, 8, 12} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 8, 9, 12} ∨
        polygon = {3, 6, 8, 9, 12} ∨
        polygon = {4, 6, 8, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 6, 8, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 6, 8, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 6, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 6, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 6, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 6, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 6, 8, 9, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 6, 8, 9, 12} \ ({2, 3, 4, 6, 8, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 6, 8, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3420 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 6, 8, 10, 11} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 6, 8} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 6, 11} ∨
        polygon = {2, 3, 4, 8, 10} ∨
        polygon = {2, 3, 4, 8, 11} ∨
        polygon = {2, 3, 4, 10, 11} ∨
        polygon = {2, 3, 6, 8, 10} ∨
        polygon = {2, 3, 6, 8, 11} ∨
        polygon = {2, 3, 6, 10, 11} ∨
        polygon = {2, 3, 8, 10, 11} ∨
        polygon = {2, 4, 6, 8, 10} ∨
        polygon = {2, 4, 6, 8, 11} ∨
        polygon = {2, 4, 6, 10, 11} ∨
        polygon = {2, 4, 8, 10, 11} ∨
        polygon = {2, 6, 8, 10, 11} ∨
        polygon = {3, 4, 6, 8, 10} ∨
        polygon = {3, 4, 6, 8, 11} ∨
        polygon = {3, 4, 6, 10, 11} ∨
        polygon = {3, 4, 8, 10, 11} ∨
        polygon = {3, 6, 8, 10, 11} ∨
        polygon = {4, 6, 8, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 6, 8, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 6, 8, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 6, 8, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 6, 8, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 6, 8, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 6, 8, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 6, 8, 10, 11} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 6, 8, 10, 11} \ ({2, 3, 4, 6, 8, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 6, 8, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5468 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 6, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 6, 8} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 8, 10} ∨
        polygon = {2, 3, 4, 8, 12} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 6, 8, 10} ∨
        polygon = {2, 3, 6, 8, 12} ∨
        polygon = {2, 3, 6, 10, 12} ∨
        polygon = {2, 3, 8, 10, 12} ∨
        polygon = {2, 4, 6, 8, 10} ∨
        polygon = {2, 4, 6, 8, 12} ∨
        polygon = {2, 4, 6, 10, 12} ∨
        polygon = {2, 4, 8, 10, 12} ∨
        polygon = {2, 6, 8, 10, 12} ∨
        polygon = {3, 4, 6, 8, 10} ∨
        polygon = {3, 4, 6, 8, 12} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 8, 10, 12} ∨
        polygon = {3, 6, 8, 10, 12} ∨
        polygon = {4, 6, 8, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 6, 8, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 6, 8, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 6, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 6, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 6, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 6, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 6, 8, 10, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 6, 8, 10, 12} \ ({2, 3, 4, 6, 8, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 6, 8, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3676 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 6, 9, 10, 11} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 6, 11} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 4, 9, 11} ∨
        polygon = {2, 3, 4, 10, 11} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {2, 3, 6, 9, 11} ∨
        polygon = {2, 3, 6, 10, 11} ∨
        polygon = {2, 3, 9, 10, 11} ∨
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {2, 4, 6, 9, 11} ∨
        polygon = {2, 4, 6, 10, 11} ∨
        polygon = {2, 4, 9, 10, 11} ∨
        polygon = {2, 6, 9, 10, 11} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 4, 6, 9, 11} ∨
        polygon = {3, 4, 6, 10, 11} ∨
        polygon = {3, 4, 9, 10, 11} ∨
        polygon = {3, 6, 9, 10, 11} ∨
        polygon = {4, 6, 9, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 6, 9, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 6, 9, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 6, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 6, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 6, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 6, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 6, 9, 10, 11} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 6, 9, 10, 11} \ ({2, 3, 4, 6, 9, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 6, 9, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5724 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 6, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {2, 3, 6, 9, 12} ∨
        polygon = {2, 3, 6, 10, 12} ∨
        polygon = {2, 3, 9, 10, 12} ∨
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {2, 4, 6, 9, 12} ∨
        polygon = {2, 4, 6, 10, 12} ∨
        polygon = {2, 4, 9, 10, 12} ∨
        polygon = {2, 6, 9, 10, 12} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {4, 6, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 6, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 6, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 6, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 6, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 6, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 6, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 6, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 6, 9, 10, 12} \ ({2, 3, 4, 6, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 6, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1948 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 7, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 7, 8} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 8, 9} ∨
        polygon = {2, 3, 4, 8, 10} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 7, 8, 9} ∨
        polygon = {2, 3, 7, 8, 10} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 3, 8, 9, 10} ∨
        polygon = {2, 4, 7, 8, 9} ∨
        polygon = {2, 4, 7, 8, 10} ∨
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {2, 4, 8, 9, 10} ∨
        polygon = {2, 7, 8, 9, 10} ∨
        polygon = {3, 4, 7, 8, 9} ∨
        polygon = {3, 4, 7, 8, 10} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {3, 4, 8, 9, 10} ∨
        polygon = {3, 7, 8, 9, 10} ∨
        polygon = {4, 7, 8, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 7, 8, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 7, 8, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 7, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 7, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 7, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 7, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 7, 8, 9, 10} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 7, 8, 9, 10} \ ({2, 3, 4, 7, 8, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 7, 8, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask2972 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 7, 8, 9, 11} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 7, 8} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 7, 11} ∨
        polygon = {2, 3, 4, 8, 9} ∨
        polygon = {2, 3, 4, 8, 11} ∨
        polygon = {2, 3, 4, 9, 11} ∨
        polygon = {2, 3, 7, 8, 9} ∨
        polygon = {2, 3, 7, 8, 11} ∨
        polygon = {2, 3, 7, 9, 11} ∨
        polygon = {2, 3, 8, 9, 11} ∨
        polygon = {2, 4, 7, 8, 9} ∨
        polygon = {2, 4, 7, 8, 11} ∨
        polygon = {2, 4, 7, 9, 11} ∨
        polygon = {2, 4, 8, 9, 11} ∨
        polygon = {2, 7, 8, 9, 11} ∨
        polygon = {3, 4, 7, 8, 9} ∨
        polygon = {3, 4, 7, 8, 11} ∨
        polygon = {3, 4, 7, 9, 11} ∨
        polygon = {3, 4, 8, 9, 11} ∨
        polygon = {3, 7, 8, 9, 11} ∨
        polygon = {4, 7, 8, 9, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 7, 8, 9, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 7, 8, 9, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 7, 8, 9, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 7, 8, 9, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 7, 8, 9, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 7, 8, 9, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 7, 8, 9, 11} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 7, 8, 9, 11} \ ({2, 3, 4, 7, 8, 9, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 7, 8, 9, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5020 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 7, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 7, 8} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 8, 9} ∨
        polygon = {2, 3, 4, 8, 12} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 7, 8, 9} ∨
        polygon = {2, 3, 7, 8, 12} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 3, 8, 9, 12} ∨
        polygon = {2, 4, 7, 8, 9} ∨
        polygon = {2, 4, 7, 8, 12} ∨
        polygon = {2, 4, 7, 9, 12} ∨
        polygon = {2, 4, 8, 9, 12} ∨
        polygon = {2, 7, 8, 9, 12} ∨
        polygon = {3, 4, 7, 8, 9} ∨
        polygon = {3, 4, 7, 8, 12} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 4, 8, 9, 12} ∨
        polygon = {3, 7, 8, 9, 12} ∨
        polygon = {4, 7, 8, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 7, 8, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 7, 8, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 7, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 7, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 7, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 7, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 7, 8, 9, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 7, 8, 9, 12} \ ({2, 3, 4, 7, 8, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 7, 8, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3484 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 7, 8, 10, 11} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 7, 8} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 7, 11} ∨
        polygon = {2, 3, 4, 8, 10} ∨
        polygon = {2, 3, 4, 8, 11} ∨
        polygon = {2, 3, 4, 10, 11} ∨
        polygon = {2, 3, 7, 8, 10} ∨
        polygon = {2, 3, 7, 8, 11} ∨
        polygon = {2, 3, 7, 10, 11} ∨
        polygon = {2, 3, 8, 10, 11} ∨
        polygon = {2, 4, 7, 8, 10} ∨
        polygon = {2, 4, 7, 8, 11} ∨
        polygon = {2, 4, 7, 10, 11} ∨
        polygon = {2, 4, 8, 10, 11} ∨
        polygon = {2, 7, 8, 10, 11} ∨
        polygon = {3, 4, 7, 8, 10} ∨
        polygon = {3, 4, 7, 8, 11} ∨
        polygon = {3, 4, 7, 10, 11} ∨
        polygon = {3, 4, 8, 10, 11} ∨
        polygon = {3, 7, 8, 10, 11} ∨
        polygon = {4, 7, 8, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 7, 8, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 7, 8, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 7, 8, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 7, 8, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 7, 8, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 7, 8, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 7, 8, 10, 11} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 7, 8, 10, 11} \ ({2, 3, 4, 7, 8, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 7, 8, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5532 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 7, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 7, 8} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 8, 10} ∨
        polygon = {2, 3, 4, 8, 12} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 7, 8, 10} ∨
        polygon = {2, 3, 7, 8, 12} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {2, 3, 8, 10, 12} ∨
        polygon = {2, 4, 7, 8, 10} ∨
        polygon = {2, 4, 7, 8, 12} ∨
        polygon = {2, 4, 7, 10, 12} ∨
        polygon = {2, 4, 8, 10, 12} ∨
        polygon = {2, 7, 8, 10, 12} ∨
        polygon = {3, 4, 7, 8, 10} ∨
        polygon = {3, 4, 7, 8, 12} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {3, 4, 8, 10, 12} ∨
        polygon = {3, 7, 8, 10, 12} ∨
        polygon = {4, 7, 8, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 7, 8, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 7, 8, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 7, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 7, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 7, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 7, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 7, 8, 10, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 7, 8, 10, 12} \ ({2, 3, 4, 7, 8, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 7, 8, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3740 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 7, 9, 10, 11} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 7, 11} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 4, 9, 11} ∨
        polygon = {2, 3, 4, 10, 11} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 3, 7, 9, 11} ∨
        polygon = {2, 3, 7, 10, 11} ∨
        polygon = {2, 3, 9, 10, 11} ∨
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {2, 4, 7, 9, 11} ∨
        polygon = {2, 4, 7, 10, 11} ∨
        polygon = {2, 4, 9, 10, 11} ∨
        polygon = {2, 7, 9, 10, 11} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {3, 4, 7, 9, 11} ∨
        polygon = {3, 4, 7, 10, 11} ∨
        polygon = {3, 4, 9, 10, 11} ∨
        polygon = {3, 7, 9, 10, 11} ∨
        polygon = {4, 7, 9, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 7, 9, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 7, 9, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 7, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 7, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 7, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 7, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 7, 9, 10, 11} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 7, 9, 10, 11} \ ({2, 3, 4, 7, 9, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 7, 9, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5788 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 7, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {2, 3, 9, 10, 12} ∨
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {2, 4, 7, 9, 12} ∨
        polygon = {2, 4, 7, 10, 12} ∨
        polygon = {2, 4, 9, 10, 12} ∨
        polygon = {2, 7, 9, 10, 12} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {4, 7, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 7, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 7, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 7, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 7, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 7, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 7, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 7, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 7, 9, 10, 12} \ ({2, 3, 4, 7, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 7, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask7324 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 7, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 7, 11} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 10, 11} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 4, 11, 12} ∨
        polygon = {2, 3, 7, 10, 11} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {2, 3, 7, 11, 12} ∨
        polygon = {2, 3, 10, 11, 12} ∨
        polygon = {2, 4, 7, 10, 11} ∨
        polygon = {2, 4, 7, 10, 12} ∨
        polygon = {2, 4, 7, 11, 12} ∨
        polygon = {2, 4, 10, 11, 12} ∨
        polygon = {2, 7, 10, 11, 12} ∨
        polygon = {3, 4, 7, 10, 11} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {3, 4, 7, 11, 12} ∨
        polygon = {3, 4, 10, 11, 12} ∨
        polygon = {3, 7, 10, 11, 12} ∨
        polygon = {4, 7, 10, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 7, 10, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 7, 10, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 7, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 7, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 7, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 7, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 7, 10, 11, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 7, 10, 11, 12} \ ({2, 3, 4, 7, 10, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 7, 10, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5916 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 8, 9} ∨
        polygon = {2, 3, 4, 8, 10} ∨
        polygon = {2, 3, 4, 8, 12} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 8, 9, 10} ∨
        polygon = {2, 3, 8, 9, 12} ∨
        polygon = {2, 3, 8, 10, 12} ∨
        polygon = {2, 3, 9, 10, 12} ∨
        polygon = {2, 4, 8, 9, 10} ∨
        polygon = {2, 4, 8, 9, 12} ∨
        polygon = {2, 4, 8, 10, 12} ∨
        polygon = {2, 4, 9, 10, 12} ∨
        polygon = {2, 8, 9, 10, 12} ∨
        polygon = {3, 4, 8, 9, 10} ∨
        polygon = {3, 4, 8, 9, 12} ∨
        polygon = {3, 4, 8, 10, 12} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 8, 9, 10, 12} ∨
        polygon = {4, 8, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 8, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 8, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 8, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 8, 9, 10, 12} \ ({2, 3, 4, 8, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 8, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask7452 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 4, 8, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 4, 8, 10} ∨
        polygon = {2, 3, 4, 8, 11} ∨
        polygon = {2, 3, 4, 8, 12} ∨
        polygon = {2, 3, 4, 10, 11} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 4, 11, 12} ∨
        polygon = {2, 3, 8, 10, 11} ∨
        polygon = {2, 3, 8, 10, 12} ∨
        polygon = {2, 3, 8, 11, 12} ∨
        polygon = {2, 3, 10, 11, 12} ∨
        polygon = {2, 4, 8, 10, 11} ∨
        polygon = {2, 4, 8, 10, 12} ∨
        polygon = {2, 4, 8, 11, 12} ∨
        polygon = {2, 4, 10, 11, 12} ∨
        polygon = {2, 8, 10, 11, 12} ∨
        polygon = {3, 4, 8, 10, 11} ∨
        polygon = {3, 4, 8, 10, 12} ∨
        polygon = {3, 4, 8, 11, 12} ∨
        polygon = {3, 4, 10, 11, 12} ∨
        polygon = {3, 8, 10, 11, 12} ∨
        polygon = {4, 8, 10, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 4, 8, 10, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 4, 8, 10, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 4, 8, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 4, 8, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 4, 8, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 4, 8, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 4, 8, 10, 11, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 4, 8, 10, 11, 12} \ ({2, 3, 4, 8, 10, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 4, 8, 10, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1004 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 5, 6, 7, 8, 9} →
      polygon.card = 5 →
        polygon = {2, 3, 5, 6, 7} ∨
        polygon = {2, 3, 5, 6, 8} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {2, 3, 5, 7, 8} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {2, 3, 5, 8, 9} ∨
        polygon = {2, 3, 6, 7, 8} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {2, 3, 6, 8, 9} ∨
        polygon = {2, 3, 7, 8, 9} ∨
        polygon = {2, 5, 6, 7, 8} ∨
        polygon = {2, 5, 6, 7, 9} ∨
        polygon = {2, 5, 6, 8, 9} ∨
        polygon = {2, 5, 7, 8, 9} ∨
        polygon = {2, 6, 7, 8, 9} ∨
        polygon = {3, 5, 6, 7, 8} ∨
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {3, 5, 6, 8, 9} ∨
        polygon = {3, 5, 7, 8, 9} ∨
        polygon = {3, 6, 7, 8, 9} ∨
        polygon = {5, 6, 7, 8, 9} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 5, 6, 7, 8, 9} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 5, 6, 7, 8, 9} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 5, 6, 7, 8, 9} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 5, 6, 7, 8, 9} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 5, 6, 7, 8, 9} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 5, 6, 7, 8, 9} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 5, 6, 7, 8, 9} \ {x, y} := by
    calc
      polygon = {2, 3, 5, 6, 7, 8, 9} \ ({2, 3, 5, 6, 7, 8, 9} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 5, 6, 7, 8, 9} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1516 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 5, 6, 7, 8, 10} →
      polygon.card = 5 →
        polygon = {2, 3, 5, 6, 7} ∨
        polygon = {2, 3, 5, 6, 8} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {2, 3, 5, 7, 8} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 5, 8, 10} ∨
        polygon = {2, 3, 6, 7, 8} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {2, 3, 6, 8, 10} ∨
        polygon = {2, 3, 7, 8, 10} ∨
        polygon = {2, 5, 6, 7, 8} ∨
        polygon = {2, 5, 6, 7, 10} ∨
        polygon = {2, 5, 6, 8, 10} ∨
        polygon = {2, 5, 7, 8, 10} ∨
        polygon = {2, 6, 7, 8, 10} ∨
        polygon = {3, 5, 6, 7, 8} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {3, 5, 6, 8, 10} ∨
        polygon = {3, 5, 7, 8, 10} ∨
        polygon = {3, 6, 7, 8, 10} ∨
        polygon = {5, 6, 7, 8, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 5, 6, 7, 8, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 5, 6, 7, 8, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 5, 6, 7, 8, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 5, 6, 7, 8, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 5, 6, 7, 8, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 5, 6, 7, 8, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 5, 6, 7, 8, 10} \ {x, y} := by
    calc
      polygon = {2, 3, 5, 6, 7, 8, 10} \ ({2, 3, 5, 6, 7, 8, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 5, 6, 7, 8, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask2540 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 5, 6, 7, 8, 11} →
      polygon.card = 5 →
        polygon = {2, 3, 5, 6, 7} ∨
        polygon = {2, 3, 5, 6, 8} ∨
        polygon = {2, 3, 5, 6, 11} ∨
        polygon = {2, 3, 5, 7, 8} ∨
        polygon = {2, 3, 5, 7, 11} ∨
        polygon = {2, 3, 5, 8, 11} ∨
        polygon = {2, 3, 6, 7, 8} ∨
        polygon = {2, 3, 6, 7, 11} ∨
        polygon = {2, 3, 6, 8, 11} ∨
        polygon = {2, 3, 7, 8, 11} ∨
        polygon = {2, 5, 6, 7, 8} ∨
        polygon = {2, 5, 6, 7, 11} ∨
        polygon = {2, 5, 6, 8, 11} ∨
        polygon = {2, 5, 7, 8, 11} ∨
        polygon = {2, 6, 7, 8, 11} ∨
        polygon = {3, 5, 6, 7, 8} ∨
        polygon = {3, 5, 6, 7, 11} ∨
        polygon = {3, 5, 6, 8, 11} ∨
        polygon = {3, 5, 7, 8, 11} ∨
        polygon = {3, 6, 7, 8, 11} ∨
        polygon = {5, 6, 7, 8, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 5, 6, 7, 8, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 5, 6, 7, 8, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 5, 6, 7, 8, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 5, 6, 7, 8, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 5, 6, 7, 8, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 5, 6, 7, 8, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 5, 6, 7, 8, 11} \ {x, y} := by
    calc
      polygon = {2, 3, 5, 6, 7, 8, 11} \ ({2, 3, 5, 6, 7, 8, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 5, 6, 7, 8, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4588 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 5, 6, 7, 8, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 5, 6, 7} ∨
        polygon = {2, 3, 5, 6, 8} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {2, 3, 5, 7, 8} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 5, 8, 12} ∨
        polygon = {2, 3, 6, 7, 8} ∨
        polygon = {2, 3, 6, 7, 12} ∨
        polygon = {2, 3, 6, 8, 12} ∨
        polygon = {2, 3, 7, 8, 12} ∨
        polygon = {2, 5, 6, 7, 8} ∨
        polygon = {2, 5, 6, 7, 12} ∨
        polygon = {2, 5, 6, 8, 12} ∨
        polygon = {2, 5, 7, 8, 12} ∨
        polygon = {2, 6, 7, 8, 12} ∨
        polygon = {3, 5, 6, 7, 8} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {3, 5, 6, 8, 12} ∨
        polygon = {3, 5, 7, 8, 12} ∨
        polygon = {3, 6, 7, 8, 12} ∨
        polygon = {5, 6, 7, 8, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 5, 6, 7, 8, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 5, 6, 7, 8, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 5, 6, 7, 8, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 5, 6, 7, 8, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 5, 6, 7, 8, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 5, 6, 7, 8, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 5, 6, 7, 8, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 5, 6, 7, 8, 12} \ ({2, 3, 5, 6, 7, 8, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 5, 6, 7, 8, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1772 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 5, 6, 7, 9, 10} →
      polygon.card = 5 →
        polygon = {2, 3, 5, 6, 7} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 5, 6, 7, 9} ∨
        polygon = {2, 5, 6, 7, 10} ∨
        polygon = {2, 5, 6, 9, 10} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {2, 6, 7, 9, 10} ∨
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {5, 6, 7, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 5, 6, 7, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 5, 6, 7, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 5, 6, 7, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 5, 6, 7, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 5, 6, 7, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 5, 6, 7, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 5, 6, 7, 9, 10} \ {x, y} := by
    calc
      polygon = {2, 3, 5, 6, 7, 9, 10} \ ({2, 3, 5, 6, 7, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 5, 6, 7, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask2796 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 5, 6, 7, 9, 11} →
      polygon.card = 5 →
        polygon = {2, 3, 5, 6, 7} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {2, 3, 5, 6, 11} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {2, 3, 5, 7, 11} ∨
        polygon = {2, 3, 5, 9, 11} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {2, 3, 6, 7, 11} ∨
        polygon = {2, 3, 6, 9, 11} ∨
        polygon = {2, 3, 7, 9, 11} ∨
        polygon = {2, 5, 6, 7, 9} ∨
        polygon = {2, 5, 6, 7, 11} ∨
        polygon = {2, 5, 6, 9, 11} ∨
        polygon = {2, 5, 7, 9, 11} ∨
        polygon = {2, 6, 7, 9, 11} ∨
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {3, 5, 6, 7, 11} ∨
        polygon = {3, 5, 6, 9, 11} ∨
        polygon = {3, 5, 7, 9, 11} ∨
        polygon = {3, 6, 7, 9, 11} ∨
        polygon = {5, 6, 7, 9, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 5, 6, 7, 9, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 5, 6, 7, 9, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 5, 6, 7, 9, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 5, 6, 7, 9, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 5, 6, 7, 9, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 5, 6, 7, 9, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 5, 6, 7, 9, 11} \ {x, y} := by
    calc
      polygon = {2, 3, 5, 6, 7, 9, 11} \ ({2, 3, 5, 6, 7, 9, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 5, 6, 7, 9, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4844 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 5, 6, 7, 9, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 5, 6, 7} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {2, 3, 6, 7, 12} ∨
        polygon = {2, 3, 6, 9, 12} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 5, 6, 7, 9} ∨
        polygon = {2, 5, 6, 7, 12} ∨
        polygon = {2, 5, 6, 9, 12} ∨
        polygon = {2, 5, 7, 9, 12} ∨
        polygon = {2, 6, 7, 9, 12} ∨
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {5, 6, 7, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 5, 6, 7, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 5, 6, 7, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 5, 6, 7, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 5, 6, 7, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 5, 6, 7, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 5, 6, 7, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 5, 6, 7, 9, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 5, 6, 7, 9, 12} \ ({2, 3, 5, 6, 7, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 5, 6, 7, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3308 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 5, 6, 7, 10, 11} →
      polygon.card = 5 →
        polygon = {2, 3, 5, 6, 7} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {2, 3, 5, 6, 11} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 5, 7, 11} ∨
        polygon = {2, 3, 5, 10, 11} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {2, 3, 6, 7, 11} ∨
        polygon = {2, 3, 6, 10, 11} ∨
        polygon = {2, 3, 7, 10, 11} ∨
        polygon = {2, 5, 6, 7, 10} ∨
        polygon = {2, 5, 6, 7, 11} ∨
        polygon = {2, 5, 6, 10, 11} ∨
        polygon = {2, 5, 7, 10, 11} ∨
        polygon = {2, 6, 7, 10, 11} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {3, 5, 6, 7, 11} ∨
        polygon = {3, 5, 6, 10, 11} ∨
        polygon = {3, 5, 7, 10, 11} ∨
        polygon = {3, 6, 7, 10, 11} ∨
        polygon = {5, 6, 7, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 5, 6, 7, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 5, 6, 7, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 5, 6, 7, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 5, 6, 7, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 5, 6, 7, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 5, 6, 7, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 5, 6, 7, 10, 11} \ {x, y} := by
    calc
      polygon = {2, 3, 5, 6, 7, 10, 11} \ ({2, 3, 5, 6, 7, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 5, 6, 7, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5356 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 5, 6, 7, 10, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 5, 6, 7} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {2, 3, 6, 7, 12} ∨
        polygon = {2, 3, 6, 10, 12} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {2, 5, 6, 7, 10} ∨
        polygon = {2, 5, 6, 7, 12} ∨
        polygon = {2, 5, 6, 10, 12} ∨
        polygon = {2, 5, 7, 10, 12} ∨
        polygon = {2, 6, 7, 10, 12} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {5, 6, 7, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 5, 6, 7, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 5, 6, 7, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 5, 6, 7, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 5, 6, 7, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 5, 6, 7, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 5, 6, 7, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 5, 6, 7, 10, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 5, 6, 7, 10, 12} \ ({2, 3, 5, 6, 7, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 5, 6, 7, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1900 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 5, 6, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {2, 3, 5, 6, 8} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {2, 3, 5, 8, 9} ∨
        polygon = {2, 3, 5, 8, 10} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 6, 8, 9} ∨
        polygon = {2, 3, 6, 8, 10} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {2, 3, 8, 9, 10} ∨
        polygon = {2, 5, 6, 8, 9} ∨
        polygon = {2, 5, 6, 8, 10} ∨
        polygon = {2, 5, 6, 9, 10} ∨
        polygon = {2, 5, 8, 9, 10} ∨
        polygon = {2, 6, 8, 9, 10} ∨
        polygon = {3, 5, 6, 8, 9} ∨
        polygon = {3, 5, 6, 8, 10} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {3, 5, 8, 9, 10} ∨
        polygon = {3, 6, 8, 9, 10} ∨
        polygon = {5, 6, 8, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 5, 6, 8, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 5, 6, 8, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 5, 6, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 5, 6, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 5, 6, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 5, 6, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 5, 6, 8, 9, 10} \ {x, y} := by
    calc
      polygon = {2, 3, 5, 6, 8, 9, 10} \ ({2, 3, 5, 6, 8, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 5, 6, 8, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask2924 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 5, 6, 8, 9, 11} →
      polygon.card = 5 →
        polygon = {2, 3, 5, 6, 8} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {2, 3, 5, 6, 11} ∨
        polygon = {2, 3, 5, 8, 9} ∨
        polygon = {2, 3, 5, 8, 11} ∨
        polygon = {2, 3, 5, 9, 11} ∨
        polygon = {2, 3, 6, 8, 9} ∨
        polygon = {2, 3, 6, 8, 11} ∨
        polygon = {2, 3, 6, 9, 11} ∨
        polygon = {2, 3, 8, 9, 11} ∨
        polygon = {2, 5, 6, 8, 9} ∨
        polygon = {2, 5, 6, 8, 11} ∨
        polygon = {2, 5, 6, 9, 11} ∨
        polygon = {2, 5, 8, 9, 11} ∨
        polygon = {2, 6, 8, 9, 11} ∨
        polygon = {3, 5, 6, 8, 9} ∨
        polygon = {3, 5, 6, 8, 11} ∨
        polygon = {3, 5, 6, 9, 11} ∨
        polygon = {3, 5, 8, 9, 11} ∨
        polygon = {3, 6, 8, 9, 11} ∨
        polygon = {5, 6, 8, 9, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 5, 6, 8, 9, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 5, 6, 8, 9, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 5, 6, 8, 9, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 5, 6, 8, 9, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 5, 6, 8, 9, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 5, 6, 8, 9, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 5, 6, 8, 9, 11} \ {x, y} := by
    calc
      polygon = {2, 3, 5, 6, 8, 9, 11} \ ({2, 3, 5, 6, 8, 9, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 5, 6, 8, 9, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4972 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 5, 6, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 5, 6, 8} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {2, 3, 5, 8, 9} ∨
        polygon = {2, 3, 5, 8, 12} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 6, 8, 9} ∨
        polygon = {2, 3, 6, 8, 12} ∨
        polygon = {2, 3, 6, 9, 12} ∨
        polygon = {2, 3, 8, 9, 12} ∨
        polygon = {2, 5, 6, 8, 9} ∨
        polygon = {2, 5, 6, 8, 12} ∨
        polygon = {2, 5, 6, 9, 12} ∨
        polygon = {2, 5, 8, 9, 12} ∨
        polygon = {2, 6, 8, 9, 12} ∨
        polygon = {3, 5, 6, 8, 9} ∨
        polygon = {3, 5, 6, 8, 12} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {3, 5, 8, 9, 12} ∨
        polygon = {3, 6, 8, 9, 12} ∨
        polygon = {5, 6, 8, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 5, 6, 8, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 5, 6, 8, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 5, 6, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 5, 6, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 5, 6, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 5, 6, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 5, 6, 8, 9, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 5, 6, 8, 9, 12} \ ({2, 3, 5, 6, 8, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 5, 6, 8, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3436 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 5, 6, 8, 10, 11} →
      polygon.card = 5 →
        polygon = {2, 3, 5, 6, 8} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {2, 3, 5, 6, 11} ∨
        polygon = {2, 3, 5, 8, 10} ∨
        polygon = {2, 3, 5, 8, 11} ∨
        polygon = {2, 3, 5, 10, 11} ∨
        polygon = {2, 3, 6, 8, 10} ∨
        polygon = {2, 3, 6, 8, 11} ∨
        polygon = {2, 3, 6, 10, 11} ∨
        polygon = {2, 3, 8, 10, 11} ∨
        polygon = {2, 5, 6, 8, 10} ∨
        polygon = {2, 5, 6, 8, 11} ∨
        polygon = {2, 5, 6, 10, 11} ∨
        polygon = {2, 5, 8, 10, 11} ∨
        polygon = {2, 6, 8, 10, 11} ∨
        polygon = {3, 5, 6, 8, 10} ∨
        polygon = {3, 5, 6, 8, 11} ∨
        polygon = {3, 5, 6, 10, 11} ∨
        polygon = {3, 5, 8, 10, 11} ∨
        polygon = {3, 6, 8, 10, 11} ∨
        polygon = {5, 6, 8, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 5, 6, 8, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 5, 6, 8, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 5, 6, 8, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 5, 6, 8, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 5, 6, 8, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 5, 6, 8, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 5, 6, 8, 10, 11} \ {x, y} := by
    calc
      polygon = {2, 3, 5, 6, 8, 10, 11} \ ({2, 3, 5, 6, 8, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 5, 6, 8, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5484 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 5, 6, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 5, 6, 8} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {2, 3, 5, 8, 10} ∨
        polygon = {2, 3, 5, 8, 12} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 6, 8, 10} ∨
        polygon = {2, 3, 6, 8, 12} ∨
        polygon = {2, 3, 6, 10, 12} ∨
        polygon = {2, 3, 8, 10, 12} ∨
        polygon = {2, 5, 6, 8, 10} ∨
        polygon = {2, 5, 6, 8, 12} ∨
        polygon = {2, 5, 6, 10, 12} ∨
        polygon = {2, 5, 8, 10, 12} ∨
        polygon = {2, 6, 8, 10, 12} ∨
        polygon = {3, 5, 6, 8, 10} ∨
        polygon = {3, 5, 6, 8, 12} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {3, 5, 8, 10, 12} ∨
        polygon = {3, 6, 8, 10, 12} ∨
        polygon = {5, 6, 8, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 5, 6, 8, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 5, 6, 8, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 5, 6, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 5, 6, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 5, 6, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 5, 6, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 5, 6, 8, 10, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 5, 6, 8, 10, 12} \ ({2, 3, 5, 6, 8, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 5, 6, 8, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask6508 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 5, 6, 8, 11, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 5, 6, 8} ∨
        polygon = {2, 3, 5, 6, 11} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {2, 3, 5, 8, 11} ∨
        polygon = {2, 3, 5, 8, 12} ∨
        polygon = {2, 3, 5, 11, 12} ∨
        polygon = {2, 3, 6, 8, 11} ∨
        polygon = {2, 3, 6, 8, 12} ∨
        polygon = {2, 3, 6, 11, 12} ∨
        polygon = {2, 3, 8, 11, 12} ∨
        polygon = {2, 5, 6, 8, 11} ∨
        polygon = {2, 5, 6, 8, 12} ∨
        polygon = {2, 5, 6, 11, 12} ∨
        polygon = {2, 5, 8, 11, 12} ∨
        polygon = {2, 6, 8, 11, 12} ∨
        polygon = {3, 5, 6, 8, 11} ∨
        polygon = {3, 5, 6, 8, 12} ∨
        polygon = {3, 5, 6, 11, 12} ∨
        polygon = {3, 5, 8, 11, 12} ∨
        polygon = {3, 6, 8, 11, 12} ∨
        polygon = {5, 6, 8, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 5, 6, 8, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 5, 6, 8, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 5, 6, 8, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 5, 6, 8, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 5, 6, 8, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 5, 6, 8, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 5, 6, 8, 11, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 5, 6, 8, 11, 12} \ ({2, 3, 5, 6, 8, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 5, 6, 8, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3692 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 5, 6, 9, 10, 11} →
      polygon.card = 5 →
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {2, 3, 5, 6, 11} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 5, 9, 11} ∨
        polygon = {2, 3, 5, 10, 11} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {2, 3, 6, 9, 11} ∨
        polygon = {2, 3, 6, 10, 11} ∨
        polygon = {2, 3, 9, 10, 11} ∨
        polygon = {2, 5, 6, 9, 10} ∨
        polygon = {2, 5, 6, 9, 11} ∨
        polygon = {2, 5, 6, 10, 11} ∨
        polygon = {2, 5, 9, 10, 11} ∨
        polygon = {2, 6, 9, 10, 11} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {3, 5, 6, 9, 11} ∨
        polygon = {3, 5, 6, 10, 11} ∨
        polygon = {3, 5, 9, 10, 11} ∨
        polygon = {3, 6, 9, 10, 11} ∨
        polygon = {5, 6, 9, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 5, 6, 9, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 5, 6, 9, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 5, 6, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 5, 6, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 5, 6, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 5, 6, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 5, 6, 9, 10, 11} \ {x, y} := by
    calc
      polygon = {2, 3, 5, 6, 9, 10, 11} \ ({2, 3, 5, 6, 9, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 5, 6, 9, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5740 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 5, 6, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {2, 3, 6, 9, 12} ∨
        polygon = {2, 3, 6, 10, 12} ∨
        polygon = {2, 3, 9, 10, 12} ∨
        polygon = {2, 5, 6, 9, 10} ∨
        polygon = {2, 5, 6, 9, 12} ∨
        polygon = {2, 5, 6, 10, 12} ∨
        polygon = {2, 5, 9, 10, 12} ∨
        polygon = {2, 6, 9, 10, 12} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {5, 6, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 5, 6, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 5, 6, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 5, 6, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 5, 6, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 5, 6, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 5, 6, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 5, 6, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 5, 6, 9, 10, 12} \ ({2, 3, 5, 6, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 5, 6, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask7276 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 3, 5, 6, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {2, 3, 5, 6, 11} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {2, 3, 5, 10, 11} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 5, 11, 12} ∨
        polygon = {2, 3, 6, 10, 11} ∨
        polygon = {2, 3, 6, 10, 12} ∨
        polygon = {2, 3, 6, 11, 12} ∨
        polygon = {2, 3, 10, 11, 12} ∨
        polygon = {2, 5, 6, 10, 11} ∨
        polygon = {2, 5, 6, 10, 12} ∨
        polygon = {2, 5, 6, 11, 12} ∨
        polygon = {2, 5, 10, 11, 12} ∨
        polygon = {2, 6, 10, 11, 12} ∨
        polygon = {3, 5, 6, 10, 11} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {3, 5, 6, 11, 12} ∨
        polygon = {3, 5, 10, 11, 12} ∨
        polygon = {3, 6, 10, 11, 12} ∨
        polygon = {5, 6, 10, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 3, 5, 6, 10, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 3, 5, 6, 10, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 3, 5, 6, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 3, 5, 6, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 3, 5, 6, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 3, 5, 6, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 3, 5, 6, 10, 11, 12} \ {x, y} := by
    calc
      polygon = {2, 3, 5, 6, 10, 11, 12} \ ({2, 3, 5, 6, 10, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 3, 5, 6, 10, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

end ErdosSzekeres

end
