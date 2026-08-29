module

public import ErdosSzekeres.PredecessorHalfFin13Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 026. -/

theorem predecessorHalfFin13_fiveSubset_mask6628 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 5, 6, 7, 8, 11, 12} →
      polygon.card = 5 →
        polygon = {2, 5, 6, 7, 8} ∨
        polygon = {2, 5, 6, 7, 11} ∨
        polygon = {2, 5, 6, 7, 12} ∨
        polygon = {2, 5, 6, 8, 11} ∨
        polygon = {2, 5, 6, 8, 12} ∨
        polygon = {2, 5, 6, 11, 12} ∨
        polygon = {2, 5, 7, 8, 11} ∨
        polygon = {2, 5, 7, 8, 12} ∨
        polygon = {2, 5, 7, 11, 12} ∨
        polygon = {2, 5, 8, 11, 12} ∨
        polygon = {2, 6, 7, 8, 11} ∨
        polygon = {2, 6, 7, 8, 12} ∨
        polygon = {2, 6, 7, 11, 12} ∨
        polygon = {2, 6, 8, 11, 12} ∨
        polygon = {2, 7, 8, 11, 12} ∨
        polygon = {5, 6, 7, 8, 11} ∨
        polygon = {5, 6, 7, 8, 12} ∨
        polygon = {5, 6, 7, 11, 12} ∨
        polygon = {5, 6, 8, 11, 12} ∨
        polygon = {5, 7, 8, 11, 12} ∨
        polygon = {6, 7, 8, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 5, 6, 7, 8, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 5, 6, 7, 8, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 5, 6, 7, 8, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 5, 6, 7, 8, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 5, 6, 7, 8, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 5, 6, 7, 8, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 5, 6, 7, 8, 11, 12} \ {x, y} := by
    calc
      polygon = {2, 5, 6, 7, 8, 11, 12} \ ({2, 5, 6, 7, 8, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 5, 6, 7, 8, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3812 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 5, 6, 7, 9, 10, 11} →
      polygon.card = 5 →
        polygon = {2, 5, 6, 7, 9} ∨
        polygon = {2, 5, 6, 7, 10} ∨
        polygon = {2, 5, 6, 7, 11} ∨
        polygon = {2, 5, 6, 9, 10} ∨
        polygon = {2, 5, 6, 9, 11} ∨
        polygon = {2, 5, 6, 10, 11} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {2, 5, 7, 9, 11} ∨
        polygon = {2, 5, 7, 10, 11} ∨
        polygon = {2, 5, 9, 10, 11} ∨
        polygon = {2, 6, 7, 9, 10} ∨
        polygon = {2, 6, 7, 9, 11} ∨
        polygon = {2, 6, 7, 10, 11} ∨
        polygon = {2, 6, 9, 10, 11} ∨
        polygon = {2, 7, 9, 10, 11} ∨
        polygon = {5, 6, 7, 9, 10} ∨
        polygon = {5, 6, 7, 9, 11} ∨
        polygon = {5, 6, 7, 10, 11} ∨
        polygon = {5, 6, 9, 10, 11} ∨
        polygon = {5, 7, 9, 10, 11} ∨
        polygon = {6, 7, 9, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 5, 6, 7, 9, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 5, 6, 7, 9, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 5, 6, 7, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 5, 6, 7, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 5, 6, 7, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 5, 6, 7, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 5, 6, 7, 9, 10, 11} \ {x, y} := by
    calc
      polygon = {2, 5, 6, 7, 9, 10, 11} \ ({2, 5, 6, 7, 9, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 5, 6, 7, 9, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5860 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 5, 6, 7, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {2, 5, 6, 7, 9} ∨
        polygon = {2, 5, 6, 7, 10} ∨
        polygon = {2, 5, 6, 7, 12} ∨
        polygon = {2, 5, 6, 9, 10} ∨
        polygon = {2, 5, 6, 9, 12} ∨
        polygon = {2, 5, 6, 10, 12} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {2, 5, 7, 9, 12} ∨
        polygon = {2, 5, 7, 10, 12} ∨
        polygon = {2, 5, 9, 10, 12} ∨
        polygon = {2, 6, 7, 9, 10} ∨
        polygon = {2, 6, 7, 9, 12} ∨
        polygon = {2, 6, 7, 10, 12} ∨
        polygon = {2, 6, 9, 10, 12} ∨
        polygon = {2, 7, 9, 10, 12} ∨
        polygon = {5, 6, 7, 9, 10} ∨
        polygon = {5, 6, 7, 9, 12} ∨
        polygon = {5, 6, 7, 10, 12} ∨
        polygon = {5, 6, 9, 10, 12} ∨
        polygon = {5, 7, 9, 10, 12} ∨
        polygon = {6, 7, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 5, 6, 7, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 5, 6, 7, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 5, 6, 7, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 5, 6, 7, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 5, 6, 7, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 5, 6, 7, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 5, 6, 7, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {2, 5, 6, 7, 9, 10, 12} \ ({2, 5, 6, 7, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 5, 6, 7, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask6884 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 5, 6, 7, 9, 11, 12} →
      polygon.card = 5 →
        polygon = {2, 5, 6, 7, 9} ∨
        polygon = {2, 5, 6, 7, 11} ∨
        polygon = {2, 5, 6, 7, 12} ∨
        polygon = {2, 5, 6, 9, 11} ∨
        polygon = {2, 5, 6, 9, 12} ∨
        polygon = {2, 5, 6, 11, 12} ∨
        polygon = {2, 5, 7, 9, 11} ∨
        polygon = {2, 5, 7, 9, 12} ∨
        polygon = {2, 5, 7, 11, 12} ∨
        polygon = {2, 5, 9, 11, 12} ∨
        polygon = {2, 6, 7, 9, 11} ∨
        polygon = {2, 6, 7, 9, 12} ∨
        polygon = {2, 6, 7, 11, 12} ∨
        polygon = {2, 6, 9, 11, 12} ∨
        polygon = {2, 7, 9, 11, 12} ∨
        polygon = {5, 6, 7, 9, 11} ∨
        polygon = {5, 6, 7, 9, 12} ∨
        polygon = {5, 6, 7, 11, 12} ∨
        polygon = {5, 6, 9, 11, 12} ∨
        polygon = {5, 7, 9, 11, 12} ∨
        polygon = {6, 7, 9, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 5, 6, 7, 9, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 5, 6, 7, 9, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 5, 6, 7, 9, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 5, 6, 7, 9, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 5, 6, 7, 9, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 5, 6, 7, 9, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 5, 6, 7, 9, 11, 12} \ {x, y} := by
    calc
      polygon = {2, 5, 6, 7, 9, 11, 12} \ ({2, 5, 6, 7, 9, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 5, 6, 7, 9, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask7396 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 5, 6, 7, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {2, 5, 6, 7, 10} ∨
        polygon = {2, 5, 6, 7, 11} ∨
        polygon = {2, 5, 6, 7, 12} ∨
        polygon = {2, 5, 6, 10, 11} ∨
        polygon = {2, 5, 6, 10, 12} ∨
        polygon = {2, 5, 6, 11, 12} ∨
        polygon = {2, 5, 7, 10, 11} ∨
        polygon = {2, 5, 7, 10, 12} ∨
        polygon = {2, 5, 7, 11, 12} ∨
        polygon = {2, 5, 10, 11, 12} ∨
        polygon = {2, 6, 7, 10, 11} ∨
        polygon = {2, 6, 7, 10, 12} ∨
        polygon = {2, 6, 7, 11, 12} ∨
        polygon = {2, 6, 10, 11, 12} ∨
        polygon = {2, 7, 10, 11, 12} ∨
        polygon = {5, 6, 7, 10, 11} ∨
        polygon = {5, 6, 7, 10, 12} ∨
        polygon = {5, 6, 7, 11, 12} ∨
        polygon = {5, 6, 10, 11, 12} ∨
        polygon = {5, 7, 10, 11, 12} ∨
        polygon = {6, 7, 10, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 5, 6, 7, 10, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 5, 6, 7, 10, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 5, 6, 7, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 5, 6, 7, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 5, 6, 7, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 5, 6, 7, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 5, 6, 7, 10, 11, 12} \ {x, y} := by
    calc
      polygon = {2, 5, 6, 7, 10, 11, 12} \ ({2, 5, 6, 7, 10, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 5, 6, 7, 10, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3940 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 5, 6, 8, 9, 10, 11} →
      polygon.card = 5 →
        polygon = {2, 5, 6, 8, 9} ∨
        polygon = {2, 5, 6, 8, 10} ∨
        polygon = {2, 5, 6, 8, 11} ∨
        polygon = {2, 5, 6, 9, 10} ∨
        polygon = {2, 5, 6, 9, 11} ∨
        polygon = {2, 5, 6, 10, 11} ∨
        polygon = {2, 5, 8, 9, 10} ∨
        polygon = {2, 5, 8, 9, 11} ∨
        polygon = {2, 5, 8, 10, 11} ∨
        polygon = {2, 5, 9, 10, 11} ∨
        polygon = {2, 6, 8, 9, 10} ∨
        polygon = {2, 6, 8, 9, 11} ∨
        polygon = {2, 6, 8, 10, 11} ∨
        polygon = {2, 6, 9, 10, 11} ∨
        polygon = {2, 8, 9, 10, 11} ∨
        polygon = {5, 6, 8, 9, 10} ∨
        polygon = {5, 6, 8, 9, 11} ∨
        polygon = {5, 6, 8, 10, 11} ∨
        polygon = {5, 6, 9, 10, 11} ∨
        polygon = {5, 8, 9, 10, 11} ∨
        polygon = {6, 8, 9, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 5, 6, 8, 9, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 5, 6, 8, 9, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 5, 6, 8, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 5, 6, 8, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 5, 6, 8, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 5, 6, 8, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 5, 6, 8, 9, 10, 11} \ {x, y} := by
    calc
      polygon = {2, 5, 6, 8, 9, 10, 11} \ ({2, 5, 6, 8, 9, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 5, 6, 8, 9, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5988 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 5, 6, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {2, 5, 6, 8, 9} ∨
        polygon = {2, 5, 6, 8, 10} ∨
        polygon = {2, 5, 6, 8, 12} ∨
        polygon = {2, 5, 6, 9, 10} ∨
        polygon = {2, 5, 6, 9, 12} ∨
        polygon = {2, 5, 6, 10, 12} ∨
        polygon = {2, 5, 8, 9, 10} ∨
        polygon = {2, 5, 8, 9, 12} ∨
        polygon = {2, 5, 8, 10, 12} ∨
        polygon = {2, 5, 9, 10, 12} ∨
        polygon = {2, 6, 8, 9, 10} ∨
        polygon = {2, 6, 8, 9, 12} ∨
        polygon = {2, 6, 8, 10, 12} ∨
        polygon = {2, 6, 9, 10, 12} ∨
        polygon = {2, 8, 9, 10, 12} ∨
        polygon = {5, 6, 8, 9, 10} ∨
        polygon = {5, 6, 8, 9, 12} ∨
        polygon = {5, 6, 8, 10, 12} ∨
        polygon = {5, 6, 9, 10, 12} ∨
        polygon = {5, 8, 9, 10, 12} ∨
        polygon = {6, 8, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 5, 6, 8, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 5, 6, 8, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 5, 6, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 5, 6, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 5, 6, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 5, 6, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 5, 6, 8, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {2, 5, 6, 8, 9, 10, 12} \ ({2, 5, 6, 8, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 5, 6, 8, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask7524 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 5, 6, 8, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {2, 5, 6, 8, 10} ∨
        polygon = {2, 5, 6, 8, 11} ∨
        polygon = {2, 5, 6, 8, 12} ∨
        polygon = {2, 5, 6, 10, 11} ∨
        polygon = {2, 5, 6, 10, 12} ∨
        polygon = {2, 5, 6, 11, 12} ∨
        polygon = {2, 5, 8, 10, 11} ∨
        polygon = {2, 5, 8, 10, 12} ∨
        polygon = {2, 5, 8, 11, 12} ∨
        polygon = {2, 5, 10, 11, 12} ∨
        polygon = {2, 6, 8, 10, 11} ∨
        polygon = {2, 6, 8, 10, 12} ∨
        polygon = {2, 6, 8, 11, 12} ∨
        polygon = {2, 6, 10, 11, 12} ∨
        polygon = {2, 8, 10, 11, 12} ∨
        polygon = {5, 6, 8, 10, 11} ∨
        polygon = {5, 6, 8, 10, 12} ∨
        polygon = {5, 6, 8, 11, 12} ∨
        polygon = {5, 6, 10, 11, 12} ∨
        polygon = {5, 8, 10, 11, 12} ∨
        polygon = {6, 8, 10, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 5, 6, 8, 10, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 5, 6, 8, 10, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 5, 6, 8, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 5, 6, 8, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 5, 6, 8, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 5, 6, 8, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 5, 6, 8, 10, 11, 12} \ {x, y} := by
    calc
      polygon = {2, 5, 6, 8, 10, 11, 12} \ ({2, 5, 6, 8, 10, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 5, 6, 8, 10, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4004 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 5, 7, 8, 9, 10, 11} →
      polygon.card = 5 →
        polygon = {2, 5, 7, 8, 9} ∨
        polygon = {2, 5, 7, 8, 10} ∨
        polygon = {2, 5, 7, 8, 11} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {2, 5, 7, 9, 11} ∨
        polygon = {2, 5, 7, 10, 11} ∨
        polygon = {2, 5, 8, 9, 10} ∨
        polygon = {2, 5, 8, 9, 11} ∨
        polygon = {2, 5, 8, 10, 11} ∨
        polygon = {2, 5, 9, 10, 11} ∨
        polygon = {2, 7, 8, 9, 10} ∨
        polygon = {2, 7, 8, 9, 11} ∨
        polygon = {2, 7, 8, 10, 11} ∨
        polygon = {2, 7, 9, 10, 11} ∨
        polygon = {2, 8, 9, 10, 11} ∨
        polygon = {5, 7, 8, 9, 10} ∨
        polygon = {5, 7, 8, 9, 11} ∨
        polygon = {5, 7, 8, 10, 11} ∨
        polygon = {5, 7, 9, 10, 11} ∨
        polygon = {5, 8, 9, 10, 11} ∨
        polygon = {7, 8, 9, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 5, 7, 8, 9, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 5, 7, 8, 9, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 5, 7, 8, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 5, 7, 8, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 5, 7, 8, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 5, 7, 8, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 5, 7, 8, 9, 10, 11} \ {x, y} := by
    calc
      polygon = {2, 5, 7, 8, 9, 10, 11} \ ({2, 5, 7, 8, 9, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 5, 7, 8, 9, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask6052 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 5, 7, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {2, 5, 7, 8, 9} ∨
        polygon = {2, 5, 7, 8, 10} ∨
        polygon = {2, 5, 7, 8, 12} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {2, 5, 7, 9, 12} ∨
        polygon = {2, 5, 7, 10, 12} ∨
        polygon = {2, 5, 8, 9, 10} ∨
        polygon = {2, 5, 8, 9, 12} ∨
        polygon = {2, 5, 8, 10, 12} ∨
        polygon = {2, 5, 9, 10, 12} ∨
        polygon = {2, 7, 8, 9, 10} ∨
        polygon = {2, 7, 8, 9, 12} ∨
        polygon = {2, 7, 8, 10, 12} ∨
        polygon = {2, 7, 9, 10, 12} ∨
        polygon = {2, 8, 9, 10, 12} ∨
        polygon = {5, 7, 8, 9, 10} ∨
        polygon = {5, 7, 8, 9, 12} ∨
        polygon = {5, 7, 8, 10, 12} ∨
        polygon = {5, 7, 9, 10, 12} ∨
        polygon = {5, 8, 9, 10, 12} ∨
        polygon = {7, 8, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 5, 7, 8, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 5, 7, 8, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 5, 7, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 5, 7, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 5, 7, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 5, 7, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 5, 7, 8, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {2, 5, 7, 8, 9, 10, 12} \ ({2, 5, 7, 8, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 5, 7, 8, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask7844 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 5, 7, 9, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {2, 5, 7, 9, 11} ∨
        polygon = {2, 5, 7, 9, 12} ∨
        polygon = {2, 5, 7, 10, 11} ∨
        polygon = {2, 5, 7, 10, 12} ∨
        polygon = {2, 5, 7, 11, 12} ∨
        polygon = {2, 5, 9, 10, 11} ∨
        polygon = {2, 5, 9, 10, 12} ∨
        polygon = {2, 5, 9, 11, 12} ∨
        polygon = {2, 5, 10, 11, 12} ∨
        polygon = {2, 7, 9, 10, 11} ∨
        polygon = {2, 7, 9, 10, 12} ∨
        polygon = {2, 7, 9, 11, 12} ∨
        polygon = {2, 7, 10, 11, 12} ∨
        polygon = {2, 9, 10, 11, 12} ∨
        polygon = {5, 7, 9, 10, 11} ∨
        polygon = {5, 7, 9, 10, 12} ∨
        polygon = {5, 7, 9, 11, 12} ∨
        polygon = {5, 7, 10, 11, 12} ∨
        polygon = {5, 9, 10, 11, 12} ∨
        polygon = {7, 9, 10, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 5, 7, 9, 10, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 5, 7, 9, 10, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 5, 7, 9, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 5, 7, 9, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 5, 7, 9, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 5, 7, 9, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 5, 7, 9, 10, 11, 12} \ {x, y} := by
    calc
      polygon = {2, 5, 7, 9, 10, 11, 12} \ ({2, 5, 7, 9, 10, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 5, 7, 9, 10, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4036 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 6, 7, 8, 9, 10, 11} →
      polygon.card = 5 →
        polygon = {2, 6, 7, 8, 9} ∨
        polygon = {2, 6, 7, 8, 10} ∨
        polygon = {2, 6, 7, 8, 11} ∨
        polygon = {2, 6, 7, 9, 10} ∨
        polygon = {2, 6, 7, 9, 11} ∨
        polygon = {2, 6, 7, 10, 11} ∨
        polygon = {2, 6, 8, 9, 10} ∨
        polygon = {2, 6, 8, 9, 11} ∨
        polygon = {2, 6, 8, 10, 11} ∨
        polygon = {2, 6, 9, 10, 11} ∨
        polygon = {2, 7, 8, 9, 10} ∨
        polygon = {2, 7, 8, 9, 11} ∨
        polygon = {2, 7, 8, 10, 11} ∨
        polygon = {2, 7, 9, 10, 11} ∨
        polygon = {2, 8, 9, 10, 11} ∨
        polygon = {6, 7, 8, 9, 10} ∨
        polygon = {6, 7, 8, 9, 11} ∨
        polygon = {6, 7, 8, 10, 11} ∨
        polygon = {6, 7, 9, 10, 11} ∨
        polygon = {6, 8, 9, 10, 11} ∨
        polygon = {7, 8, 9, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 6, 7, 8, 9, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 6, 7, 8, 9, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 6, 7, 8, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 6, 7, 8, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 6, 7, 8, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 6, 7, 8, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 6, 7, 8, 9, 10, 11} \ {x, y} := by
    calc
      polygon = {2, 6, 7, 8, 9, 10, 11} \ ({2, 6, 7, 8, 9, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 6, 7, 8, 9, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask6084 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 6, 7, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {2, 6, 7, 8, 9} ∨
        polygon = {2, 6, 7, 8, 10} ∨
        polygon = {2, 6, 7, 8, 12} ∨
        polygon = {2, 6, 7, 9, 10} ∨
        polygon = {2, 6, 7, 9, 12} ∨
        polygon = {2, 6, 7, 10, 12} ∨
        polygon = {2, 6, 8, 9, 10} ∨
        polygon = {2, 6, 8, 9, 12} ∨
        polygon = {2, 6, 8, 10, 12} ∨
        polygon = {2, 6, 9, 10, 12} ∨
        polygon = {2, 7, 8, 9, 10} ∨
        polygon = {2, 7, 8, 9, 12} ∨
        polygon = {2, 7, 8, 10, 12} ∨
        polygon = {2, 7, 9, 10, 12} ∨
        polygon = {2, 8, 9, 10, 12} ∨
        polygon = {6, 7, 8, 9, 10} ∨
        polygon = {6, 7, 8, 9, 12} ∨
        polygon = {6, 7, 8, 10, 12} ∨
        polygon = {6, 7, 9, 10, 12} ∨
        polygon = {6, 8, 9, 10, 12} ∨
        polygon = {7, 8, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 6, 7, 8, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 6, 7, 8, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 6, 7, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 6, 7, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 6, 7, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 6, 7, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 6, 7, 8, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {2, 6, 7, 8, 9, 10, 12} \ ({2, 6, 7, 8, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 6, 7, 8, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask8004 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 6, 8, 9, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {2, 6, 8, 9, 10} ∨
        polygon = {2, 6, 8, 9, 11} ∨
        polygon = {2, 6, 8, 9, 12} ∨
        polygon = {2, 6, 8, 10, 11} ∨
        polygon = {2, 6, 8, 10, 12} ∨
        polygon = {2, 6, 8, 11, 12} ∨
        polygon = {2, 6, 9, 10, 11} ∨
        polygon = {2, 6, 9, 10, 12} ∨
        polygon = {2, 6, 9, 11, 12} ∨
        polygon = {2, 6, 10, 11, 12} ∨
        polygon = {2, 8, 9, 10, 11} ∨
        polygon = {2, 8, 9, 10, 12} ∨
        polygon = {2, 8, 9, 11, 12} ∨
        polygon = {2, 8, 10, 11, 12} ∨
        polygon = {2, 9, 10, 11, 12} ∨
        polygon = {6, 8, 9, 10, 11} ∨
        polygon = {6, 8, 9, 10, 12} ∨
        polygon = {6, 8, 9, 11, 12} ∨
        polygon = {6, 8, 10, 11, 12} ∨
        polygon = {6, 9, 10, 11, 12} ∨
        polygon = {8, 9, 10, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 6, 8, 9, 10, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 6, 8, 9, 10, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 6, 8, 9, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 6, 8, 9, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 6, 8, 9, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 6, 8, 9, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 6, 8, 9, 10, 11, 12} \ {x, y} := by
    calc
      polygon = {2, 6, 8, 9, 10, 11, 12} \ ({2, 6, 8, 9, 10, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 6, 8, 9, 10, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask8068 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {2, 7, 8, 9, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {2, 7, 8, 9, 10} ∨
        polygon = {2, 7, 8, 9, 11} ∨
        polygon = {2, 7, 8, 9, 12} ∨
        polygon = {2, 7, 8, 10, 11} ∨
        polygon = {2, 7, 8, 10, 12} ∨
        polygon = {2, 7, 8, 11, 12} ∨
        polygon = {2, 7, 9, 10, 11} ∨
        polygon = {2, 7, 9, 10, 12} ∨
        polygon = {2, 7, 9, 11, 12} ∨
        polygon = {2, 7, 10, 11, 12} ∨
        polygon = {2, 8, 9, 10, 11} ∨
        polygon = {2, 8, 9, 10, 12} ∨
        polygon = {2, 8, 9, 11, 12} ∨
        polygon = {2, 8, 10, 11, 12} ∨
        polygon = {2, 9, 10, 11, 12} ∨
        polygon = {7, 8, 9, 10, 11} ∨
        polygon = {7, 8, 9, 10, 12} ∨
        polygon = {7, 8, 9, 11, 12} ∨
        polygon = {7, 8, 10, 11, 12} ∨
        polygon = {7, 9, 10, 11, 12} ∨
        polygon = {8, 9, 10, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({2, 7, 8, 9, 10, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({2, 7, 8, 9, 10, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {2, 7, 8, 9, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {2, 7, 8, 9, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({2, 7, 8, 9, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({2, 7, 8, 9, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {2, 7, 8, 9, 10, 11, 12} \ {x, y} := by
    calc
      polygon = {2, 7, 8, 9, 10, 11, 12} \ ({2, 7, 8, 9, 10, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {2, 7, 8, 9, 10, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1016 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 5, 6, 7, 8, 9} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 6, 7} ∨
        polygon = {3, 4, 5, 6, 8} ∨
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {3, 4, 5, 7, 8} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {3, 4, 5, 8, 9} ∨
        polygon = {3, 4, 6, 7, 8} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {3, 4, 6, 8, 9} ∨
        polygon = {3, 4, 7, 8, 9} ∨
        polygon = {3, 5, 6, 7, 8} ∨
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {3, 5, 6, 8, 9} ∨
        polygon = {3, 5, 7, 8, 9} ∨
        polygon = {3, 6, 7, 8, 9} ∨
        polygon = {4, 5, 6, 7, 8} ∨
        polygon = {4, 5, 6, 7, 9} ∨
        polygon = {4, 5, 6, 8, 9} ∨
        polygon = {4, 5, 7, 8, 9} ∨
        polygon = {4, 6, 7, 8, 9} ∨
        polygon = {5, 6, 7, 8, 9} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 5, 6, 7, 8, 9} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 5, 6, 7, 8, 9} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 5, 6, 7, 8, 9} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 5, 6, 7, 8, 9} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 5, 6, 7, 8, 9} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 5, 6, 7, 8, 9} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 5, 6, 7, 8, 9} \ {x, y} := by
    calc
      polygon = {3, 4, 5, 6, 7, 8, 9} \ ({3, 4, 5, 6, 7, 8, 9} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 5, 6, 7, 8, 9} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1528 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 5, 6, 7, 8, 10} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 6, 7} ∨
        polygon = {3, 4, 5, 6, 8} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {3, 4, 5, 7, 8} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {3, 4, 5, 8, 10} ∨
        polygon = {3, 4, 6, 7, 8} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {3, 4, 6, 8, 10} ∨
        polygon = {3, 4, 7, 8, 10} ∨
        polygon = {3, 5, 6, 7, 8} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {3, 5, 6, 8, 10} ∨
        polygon = {3, 5, 7, 8, 10} ∨
        polygon = {3, 6, 7, 8, 10} ∨
        polygon = {4, 5, 6, 7, 8} ∨
        polygon = {4, 5, 6, 7, 10} ∨
        polygon = {4, 5, 6, 8, 10} ∨
        polygon = {4, 5, 7, 8, 10} ∨
        polygon = {4, 6, 7, 8, 10} ∨
        polygon = {5, 6, 7, 8, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 5, 6, 7, 8, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 5, 6, 7, 8, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 5, 6, 7, 8, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 5, 6, 7, 8, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 5, 6, 7, 8, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 5, 6, 7, 8, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 5, 6, 7, 8, 10} \ {x, y} := by
    calc
      polygon = {3, 4, 5, 6, 7, 8, 10} \ ({3, 4, 5, 6, 7, 8, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 5, 6, 7, 8, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask2552 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 5, 6, 7, 8, 11} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 6, 7} ∨
        polygon = {3, 4, 5, 6, 8} ∨
        polygon = {3, 4, 5, 6, 11} ∨
        polygon = {3, 4, 5, 7, 8} ∨
        polygon = {3, 4, 5, 7, 11} ∨
        polygon = {3, 4, 5, 8, 11} ∨
        polygon = {3, 4, 6, 7, 8} ∨
        polygon = {3, 4, 6, 7, 11} ∨
        polygon = {3, 4, 6, 8, 11} ∨
        polygon = {3, 4, 7, 8, 11} ∨
        polygon = {3, 5, 6, 7, 8} ∨
        polygon = {3, 5, 6, 7, 11} ∨
        polygon = {3, 5, 6, 8, 11} ∨
        polygon = {3, 5, 7, 8, 11} ∨
        polygon = {3, 6, 7, 8, 11} ∨
        polygon = {4, 5, 6, 7, 8} ∨
        polygon = {4, 5, 6, 7, 11} ∨
        polygon = {4, 5, 6, 8, 11} ∨
        polygon = {4, 5, 7, 8, 11} ∨
        polygon = {4, 6, 7, 8, 11} ∨
        polygon = {5, 6, 7, 8, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 5, 6, 7, 8, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 5, 6, 7, 8, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 5, 6, 7, 8, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 5, 6, 7, 8, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 5, 6, 7, 8, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 5, 6, 7, 8, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 5, 6, 7, 8, 11} \ {x, y} := by
    calc
      polygon = {3, 4, 5, 6, 7, 8, 11} \ ({3, 4, 5, 6, 7, 8, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 5, 6, 7, 8, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4600 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 5, 6, 7, 8, 12} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 6, 7} ∨
        polygon = {3, 4, 5, 6, 8} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {3, 4, 5, 7, 8} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {3, 4, 5, 8, 12} ∨
        polygon = {3, 4, 6, 7, 8} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 4, 6, 8, 12} ∨
        polygon = {3, 4, 7, 8, 12} ∨
        polygon = {3, 5, 6, 7, 8} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {3, 5, 6, 8, 12} ∨
        polygon = {3, 5, 7, 8, 12} ∨
        polygon = {3, 6, 7, 8, 12} ∨
        polygon = {4, 5, 6, 7, 8} ∨
        polygon = {4, 5, 6, 7, 12} ∨
        polygon = {4, 5, 6, 8, 12} ∨
        polygon = {4, 5, 7, 8, 12} ∨
        polygon = {4, 6, 7, 8, 12} ∨
        polygon = {5, 6, 7, 8, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 5, 6, 7, 8, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 5, 6, 7, 8, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 5, 6, 7, 8, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 5, 6, 7, 8, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 5, 6, 7, 8, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 5, 6, 7, 8, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 5, 6, 7, 8, 12} \ {x, y} := by
    calc
      polygon = {3, 4, 5, 6, 7, 8, 12} \ ({3, 4, 5, 6, 7, 8, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 5, 6, 7, 8, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1784 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 5, 6, 7, 9, 10} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 6, 7} ∨
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {4, 5, 6, 7, 9} ∨
        polygon = {4, 5, 6, 7, 10} ∨
        polygon = {4, 5, 6, 9, 10} ∨
        polygon = {4, 5, 7, 9, 10} ∨
        polygon = {4, 6, 7, 9, 10} ∨
        polygon = {5, 6, 7, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 5, 6, 7, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 5, 6, 7, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 5, 6, 7, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 5, 6, 7, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 5, 6, 7, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 5, 6, 7, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 5, 6, 7, 9, 10} \ {x, y} := by
    calc
      polygon = {3, 4, 5, 6, 7, 9, 10} \ ({3, 4, 5, 6, 7, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 5, 6, 7, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask2808 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 5, 6, 7, 9, 11} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 6, 7} ∨
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {3, 4, 5, 6, 11} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {3, 4, 5, 7, 11} ∨
        polygon = {3, 4, 5, 9, 11} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {3, 4, 6, 7, 11} ∨
        polygon = {3, 4, 6, 9, 11} ∨
        polygon = {3, 4, 7, 9, 11} ∨
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {3, 5, 6, 7, 11} ∨
        polygon = {3, 5, 6, 9, 11} ∨
        polygon = {3, 5, 7, 9, 11} ∨
        polygon = {3, 6, 7, 9, 11} ∨
        polygon = {4, 5, 6, 7, 9} ∨
        polygon = {4, 5, 6, 7, 11} ∨
        polygon = {4, 5, 6, 9, 11} ∨
        polygon = {4, 5, 7, 9, 11} ∨
        polygon = {4, 6, 7, 9, 11} ∨
        polygon = {5, 6, 7, 9, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 5, 6, 7, 9, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 5, 6, 7, 9, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 5, 6, 7, 9, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 5, 6, 7, 9, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 5, 6, 7, 9, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 5, 6, 7, 9, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 5, 6, 7, 9, 11} \ {x, y} := by
    calc
      polygon = {3, 4, 5, 6, 7, 9, 11} \ ({3, 4, 5, 6, 7, 9, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 5, 6, 7, 9, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4856 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 5, 6, 7, 9, 12} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 6, 7} ∨
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {4, 5, 6, 7, 9} ∨
        polygon = {4, 5, 6, 7, 12} ∨
        polygon = {4, 5, 6, 9, 12} ∨
        polygon = {4, 5, 7, 9, 12} ∨
        polygon = {4, 6, 7, 9, 12} ∨
        polygon = {5, 6, 7, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 5, 6, 7, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 5, 6, 7, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 5, 6, 7, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 5, 6, 7, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 5, 6, 7, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 5, 6, 7, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 5, 6, 7, 9, 12} \ {x, y} := by
    calc
      polygon = {3, 4, 5, 6, 7, 9, 12} \ ({3, 4, 5, 6, 7, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 5, 6, 7, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3320 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 5, 6, 7, 10, 11} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 6, 7} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {3, 4, 5, 6, 11} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {3, 4, 5, 7, 11} ∨
        polygon = {3, 4, 5, 10, 11} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {3, 4, 6, 7, 11} ∨
        polygon = {3, 4, 6, 10, 11} ∨
        polygon = {3, 4, 7, 10, 11} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {3, 5, 6, 7, 11} ∨
        polygon = {3, 5, 6, 10, 11} ∨
        polygon = {3, 5, 7, 10, 11} ∨
        polygon = {3, 6, 7, 10, 11} ∨
        polygon = {4, 5, 6, 7, 10} ∨
        polygon = {4, 5, 6, 7, 11} ∨
        polygon = {4, 5, 6, 10, 11} ∨
        polygon = {4, 5, 7, 10, 11} ∨
        polygon = {4, 6, 7, 10, 11} ∨
        polygon = {5, 6, 7, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 5, 6, 7, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 5, 6, 7, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 5, 6, 7, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 5, 6, 7, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 5, 6, 7, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 5, 6, 7, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 5, 6, 7, 10, 11} \ {x, y} := by
    calc
      polygon = {3, 4, 5, 6, 7, 10, 11} \ ({3, 4, 5, 6, 7, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 5, 6, 7, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5368 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 5, 6, 7, 10, 12} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 6, 7} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {4, 5, 6, 7, 10} ∨
        polygon = {4, 5, 6, 7, 12} ∨
        polygon = {4, 5, 6, 10, 12} ∨
        polygon = {4, 5, 7, 10, 12} ∨
        polygon = {4, 6, 7, 10, 12} ∨
        polygon = {5, 6, 7, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 5, 6, 7, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 5, 6, 7, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 5, 6, 7, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 5, 6, 7, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 5, 6, 7, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 5, 6, 7, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 5, 6, 7, 10, 12} \ {x, y} := by
    calc
      polygon = {3, 4, 5, 6, 7, 10, 12} \ ({3, 4, 5, 6, 7, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 5, 6, 7, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1912 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 5, 6, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 6, 8} ∨
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {3, 4, 5, 8, 9} ∨
        polygon = {3, 4, 5, 8, 10} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {3, 4, 6, 8, 9} ∨
        polygon = {3, 4, 6, 8, 10} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 4, 8, 9, 10} ∨
        polygon = {3, 5, 6, 8, 9} ∨
        polygon = {3, 5, 6, 8, 10} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {3, 5, 8, 9, 10} ∨
        polygon = {3, 6, 8, 9, 10} ∨
        polygon = {4, 5, 6, 8, 9} ∨
        polygon = {4, 5, 6, 8, 10} ∨
        polygon = {4, 5, 6, 9, 10} ∨
        polygon = {4, 5, 8, 9, 10} ∨
        polygon = {4, 6, 8, 9, 10} ∨
        polygon = {5, 6, 8, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 5, 6, 8, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 5, 6, 8, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 5, 6, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 5, 6, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 5, 6, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 5, 6, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 5, 6, 8, 9, 10} \ {x, y} := by
    calc
      polygon = {3, 4, 5, 6, 8, 9, 10} \ ({3, 4, 5, 6, 8, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 5, 6, 8, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask2936 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 5, 6, 8, 9, 11} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 6, 8} ∨
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {3, 4, 5, 6, 11} ∨
        polygon = {3, 4, 5, 8, 9} ∨
        polygon = {3, 4, 5, 8, 11} ∨
        polygon = {3, 4, 5, 9, 11} ∨
        polygon = {3, 4, 6, 8, 9} ∨
        polygon = {3, 4, 6, 8, 11} ∨
        polygon = {3, 4, 6, 9, 11} ∨
        polygon = {3, 4, 8, 9, 11} ∨
        polygon = {3, 5, 6, 8, 9} ∨
        polygon = {3, 5, 6, 8, 11} ∨
        polygon = {3, 5, 6, 9, 11} ∨
        polygon = {3, 5, 8, 9, 11} ∨
        polygon = {3, 6, 8, 9, 11} ∨
        polygon = {4, 5, 6, 8, 9} ∨
        polygon = {4, 5, 6, 8, 11} ∨
        polygon = {4, 5, 6, 9, 11} ∨
        polygon = {4, 5, 8, 9, 11} ∨
        polygon = {4, 6, 8, 9, 11} ∨
        polygon = {5, 6, 8, 9, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 5, 6, 8, 9, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 5, 6, 8, 9, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 5, 6, 8, 9, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 5, 6, 8, 9, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 5, 6, 8, 9, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 5, 6, 8, 9, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 5, 6, 8, 9, 11} \ {x, y} := by
    calc
      polygon = {3, 4, 5, 6, 8, 9, 11} \ ({3, 4, 5, 6, 8, 9, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 5, 6, 8, 9, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4984 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 5, 6, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 6, 8} ∨
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {3, 4, 5, 8, 9} ∨
        polygon = {3, 4, 5, 8, 12} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 6, 8, 9} ∨
        polygon = {3, 4, 6, 8, 12} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 8, 9, 12} ∨
        polygon = {3, 5, 6, 8, 9} ∨
        polygon = {3, 5, 6, 8, 12} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {3, 5, 8, 9, 12} ∨
        polygon = {3, 6, 8, 9, 12} ∨
        polygon = {4, 5, 6, 8, 9} ∨
        polygon = {4, 5, 6, 8, 12} ∨
        polygon = {4, 5, 6, 9, 12} ∨
        polygon = {4, 5, 8, 9, 12} ∨
        polygon = {4, 6, 8, 9, 12} ∨
        polygon = {5, 6, 8, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 5, 6, 8, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 5, 6, 8, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 5, 6, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 5, 6, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 5, 6, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 5, 6, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 5, 6, 8, 9, 12} \ {x, y} := by
    calc
      polygon = {3, 4, 5, 6, 8, 9, 12} \ ({3, 4, 5, 6, 8, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 5, 6, 8, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3448 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 5, 6, 8, 10, 11} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 6, 8} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {3, 4, 5, 6, 11} ∨
        polygon = {3, 4, 5, 8, 10} ∨
        polygon = {3, 4, 5, 8, 11} ∨
        polygon = {3, 4, 5, 10, 11} ∨
        polygon = {3, 4, 6, 8, 10} ∨
        polygon = {3, 4, 6, 8, 11} ∨
        polygon = {3, 4, 6, 10, 11} ∨
        polygon = {3, 4, 8, 10, 11} ∨
        polygon = {3, 5, 6, 8, 10} ∨
        polygon = {3, 5, 6, 8, 11} ∨
        polygon = {3, 5, 6, 10, 11} ∨
        polygon = {3, 5, 8, 10, 11} ∨
        polygon = {3, 6, 8, 10, 11} ∨
        polygon = {4, 5, 6, 8, 10} ∨
        polygon = {4, 5, 6, 8, 11} ∨
        polygon = {4, 5, 6, 10, 11} ∨
        polygon = {4, 5, 8, 10, 11} ∨
        polygon = {4, 6, 8, 10, 11} ∨
        polygon = {5, 6, 8, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 5, 6, 8, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 5, 6, 8, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 5, 6, 8, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 5, 6, 8, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 5, 6, 8, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 5, 6, 8, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 5, 6, 8, 10, 11} \ {x, y} := by
    calc
      polygon = {3, 4, 5, 6, 8, 10, 11} \ ({3, 4, 5, 6, 8, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 5, 6, 8, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5496 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 5, 6, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 6, 8} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {3, 4, 5, 8, 10} ∨
        polygon = {3, 4, 5, 8, 12} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 6, 8, 10} ∨
        polygon = {3, 4, 6, 8, 12} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 8, 10, 12} ∨
        polygon = {3, 5, 6, 8, 10} ∨
        polygon = {3, 5, 6, 8, 12} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {3, 5, 8, 10, 12} ∨
        polygon = {3, 6, 8, 10, 12} ∨
        polygon = {4, 5, 6, 8, 10} ∨
        polygon = {4, 5, 6, 8, 12} ∨
        polygon = {4, 5, 6, 10, 12} ∨
        polygon = {4, 5, 8, 10, 12} ∨
        polygon = {4, 6, 8, 10, 12} ∨
        polygon = {5, 6, 8, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 5, 6, 8, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 5, 6, 8, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 5, 6, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 5, 6, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 5, 6, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 5, 6, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 5, 6, 8, 10, 12} \ {x, y} := by
    calc
      polygon = {3, 4, 5, 6, 8, 10, 12} \ ({3, 4, 5, 6, 8, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 5, 6, 8, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3704 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 5, 6, 9, 10, 11} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {3, 4, 5, 6, 11} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {3, 4, 5, 9, 11} ∨
        polygon = {3, 4, 5, 10, 11} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 4, 6, 9, 11} ∨
        polygon = {3, 4, 6, 10, 11} ∨
        polygon = {3, 4, 9, 10, 11} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {3, 5, 6, 9, 11} ∨
        polygon = {3, 5, 6, 10, 11} ∨
        polygon = {3, 5, 9, 10, 11} ∨
        polygon = {3, 6, 9, 10, 11} ∨
        polygon = {4, 5, 6, 9, 10} ∨
        polygon = {4, 5, 6, 9, 11} ∨
        polygon = {4, 5, 6, 10, 11} ∨
        polygon = {4, 5, 9, 10, 11} ∨
        polygon = {4, 6, 9, 10, 11} ∨
        polygon = {5, 6, 9, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 5, 6, 9, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 5, 6, 9, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 5, 6, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 5, 6, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 5, 6, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 5, 6, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 5, 6, 9, 10, 11} \ {x, y} := by
    calc
      polygon = {3, 4, 5, 6, 9, 10, 11} \ ({3, 4, 5, 6, 9, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 5, 6, 9, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5752 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 5, 6, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {4, 5, 6, 9, 10} ∨
        polygon = {4, 5, 6, 9, 12} ∨
        polygon = {4, 5, 6, 10, 12} ∨
        polygon = {4, 5, 9, 10, 12} ∨
        polygon = {4, 6, 9, 10, 12} ∨
        polygon = {5, 6, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 5, 6, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 5, 6, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 5, 6, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 5, 6, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 5, 6, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 5, 6, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 5, 6, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {3, 4, 5, 6, 9, 10, 12} \ ({3, 4, 5, 6, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 5, 6, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask6776 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 5, 6, 9, 11, 12} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {3, 4, 5, 6, 11} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {3, 4, 5, 9, 11} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 5, 11, 12} ∨
        polygon = {3, 4, 6, 9, 11} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 6, 11, 12} ∨
        polygon = {3, 4, 9, 11, 12} ∨
        polygon = {3, 5, 6, 9, 11} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {3, 5, 6, 11, 12} ∨
        polygon = {3, 5, 9, 11, 12} ∨
        polygon = {3, 6, 9, 11, 12} ∨
        polygon = {4, 5, 6, 9, 11} ∨
        polygon = {4, 5, 6, 9, 12} ∨
        polygon = {4, 5, 6, 11, 12} ∨
        polygon = {4, 5, 9, 11, 12} ∨
        polygon = {4, 6, 9, 11, 12} ∨
        polygon = {5, 6, 9, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 5, 6, 9, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 5, 6, 9, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 5, 6, 9, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 5, 6, 9, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 5, 6, 9, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 5, 6, 9, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 5, 6, 9, 11, 12} \ {x, y} := by
    calc
      polygon = {3, 4, 5, 6, 9, 11, 12} \ ({3, 4, 5, 6, 9, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 5, 6, 9, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask7288 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 5, 6, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {3, 4, 5, 6, 11} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {3, 4, 5, 10, 11} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 5, 11, 12} ∨
        polygon = {3, 4, 6, 10, 11} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 6, 11, 12} ∨
        polygon = {3, 4, 10, 11, 12} ∨
        polygon = {3, 5, 6, 10, 11} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {3, 5, 6, 11, 12} ∨
        polygon = {3, 5, 10, 11, 12} ∨
        polygon = {3, 6, 10, 11, 12} ∨
        polygon = {4, 5, 6, 10, 11} ∨
        polygon = {4, 5, 6, 10, 12} ∨
        polygon = {4, 5, 6, 11, 12} ∨
        polygon = {4, 5, 10, 11, 12} ∨
        polygon = {4, 6, 10, 11, 12} ∨
        polygon = {5, 6, 10, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 5, 6, 10, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 5, 6, 10, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 5, 6, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 5, 6, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 5, 6, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 5, 6, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 5, 6, 10, 11, 12} \ {x, y} := by
    calc
      polygon = {3, 4, 5, 6, 10, 11, 12} \ ({3, 4, 5, 6, 10, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 5, 6, 10, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask1976 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 5, 7, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 7, 8} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {3, 4, 5, 8, 9} ∨
        polygon = {3, 4, 5, 8, 10} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {3, 4, 7, 8, 9} ∨
        polygon = {3, 4, 7, 8, 10} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {3, 4, 8, 9, 10} ∨
        polygon = {3, 5, 7, 8, 9} ∨
        polygon = {3, 5, 7, 8, 10} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {3, 5, 8, 9, 10} ∨
        polygon = {3, 7, 8, 9, 10} ∨
        polygon = {4, 5, 7, 8, 9} ∨
        polygon = {4, 5, 7, 8, 10} ∨
        polygon = {4, 5, 7, 9, 10} ∨
        polygon = {4, 5, 8, 9, 10} ∨
        polygon = {4, 7, 8, 9, 10} ∨
        polygon = {5, 7, 8, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 5, 7, 8, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 5, 7, 8, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 5, 7, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 5, 7, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 5, 7, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 5, 7, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 5, 7, 8, 9, 10} \ {x, y} := by
    calc
      polygon = {3, 4, 5, 7, 8, 9, 10} \ ({3, 4, 5, 7, 8, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 5, 7, 8, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3000 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 5, 7, 8, 9, 11} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 7, 8} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {3, 4, 5, 7, 11} ∨
        polygon = {3, 4, 5, 8, 9} ∨
        polygon = {3, 4, 5, 8, 11} ∨
        polygon = {3, 4, 5, 9, 11} ∨
        polygon = {3, 4, 7, 8, 9} ∨
        polygon = {3, 4, 7, 8, 11} ∨
        polygon = {3, 4, 7, 9, 11} ∨
        polygon = {3, 4, 8, 9, 11} ∨
        polygon = {3, 5, 7, 8, 9} ∨
        polygon = {3, 5, 7, 8, 11} ∨
        polygon = {3, 5, 7, 9, 11} ∨
        polygon = {3, 5, 8, 9, 11} ∨
        polygon = {3, 7, 8, 9, 11} ∨
        polygon = {4, 5, 7, 8, 9} ∨
        polygon = {4, 5, 7, 8, 11} ∨
        polygon = {4, 5, 7, 9, 11} ∨
        polygon = {4, 5, 8, 9, 11} ∨
        polygon = {4, 7, 8, 9, 11} ∨
        polygon = {5, 7, 8, 9, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 5, 7, 8, 9, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 5, 7, 8, 9, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 5, 7, 8, 9, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 5, 7, 8, 9, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 5, 7, 8, 9, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 5, 7, 8, 9, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 5, 7, 8, 9, 11} \ {x, y} := by
    calc
      polygon = {3, 4, 5, 7, 8, 9, 11} \ ({3, 4, 5, 7, 8, 9, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 5, 7, 8, 9, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5048 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 5, 7, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 7, 8} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {3, 4, 5, 8, 9} ∨
        polygon = {3, 4, 5, 8, 12} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 7, 8, 9} ∨
        polygon = {3, 4, 7, 8, 12} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 4, 8, 9, 12} ∨
        polygon = {3, 5, 7, 8, 9} ∨
        polygon = {3, 5, 7, 8, 12} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {3, 5, 8, 9, 12} ∨
        polygon = {3, 7, 8, 9, 12} ∨
        polygon = {4, 5, 7, 8, 9} ∨
        polygon = {4, 5, 7, 8, 12} ∨
        polygon = {4, 5, 7, 9, 12} ∨
        polygon = {4, 5, 8, 9, 12} ∨
        polygon = {4, 7, 8, 9, 12} ∨
        polygon = {5, 7, 8, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 5, 7, 8, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 5, 7, 8, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 5, 7, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 5, 7, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 5, 7, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 5, 7, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 5, 7, 8, 9, 12} \ {x, y} := by
    calc
      polygon = {3, 4, 5, 7, 8, 9, 12} \ ({3, 4, 5, 7, 8, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 5, 7, 8, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3512 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 5, 7, 8, 10, 11} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 7, 8} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {3, 4, 5, 7, 11} ∨
        polygon = {3, 4, 5, 8, 10} ∨
        polygon = {3, 4, 5, 8, 11} ∨
        polygon = {3, 4, 5, 10, 11} ∨
        polygon = {3, 4, 7, 8, 10} ∨
        polygon = {3, 4, 7, 8, 11} ∨
        polygon = {3, 4, 7, 10, 11} ∨
        polygon = {3, 4, 8, 10, 11} ∨
        polygon = {3, 5, 7, 8, 10} ∨
        polygon = {3, 5, 7, 8, 11} ∨
        polygon = {3, 5, 7, 10, 11} ∨
        polygon = {3, 5, 8, 10, 11} ∨
        polygon = {3, 7, 8, 10, 11} ∨
        polygon = {4, 5, 7, 8, 10} ∨
        polygon = {4, 5, 7, 8, 11} ∨
        polygon = {4, 5, 7, 10, 11} ∨
        polygon = {4, 5, 8, 10, 11} ∨
        polygon = {4, 7, 8, 10, 11} ∨
        polygon = {5, 7, 8, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 5, 7, 8, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 5, 7, 8, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 5, 7, 8, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 5, 7, 8, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 5, 7, 8, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 5, 7, 8, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 5, 7, 8, 10, 11} \ {x, y} := by
    calc
      polygon = {3, 4, 5, 7, 8, 10, 11} \ ({3, 4, 5, 7, 8, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 5, 7, 8, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5560 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 5, 7, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 7, 8} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {3, 4, 5, 8, 10} ∨
        polygon = {3, 4, 5, 8, 12} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 7, 8, 10} ∨
        polygon = {3, 4, 7, 8, 12} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {3, 4, 8, 10, 12} ∨
        polygon = {3, 5, 7, 8, 10} ∨
        polygon = {3, 5, 7, 8, 12} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {3, 5, 8, 10, 12} ∨
        polygon = {3, 7, 8, 10, 12} ∨
        polygon = {4, 5, 7, 8, 10} ∨
        polygon = {4, 5, 7, 8, 12} ∨
        polygon = {4, 5, 7, 10, 12} ∨
        polygon = {4, 5, 8, 10, 12} ∨
        polygon = {4, 7, 8, 10, 12} ∨
        polygon = {5, 7, 8, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 5, 7, 8, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 5, 7, 8, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 5, 7, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 5, 7, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 5, 7, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 5, 7, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 5, 7, 8, 10, 12} \ {x, y} := by
    calc
      polygon = {3, 4, 5, 7, 8, 10, 12} \ ({3, 4, 5, 7, 8, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 5, 7, 8, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3768 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 5, 7, 9, 10, 11} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {3, 4, 5, 7, 11} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {3, 4, 5, 9, 11} ∨
        polygon = {3, 4, 5, 10, 11} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {3, 4, 7, 9, 11} ∨
        polygon = {3, 4, 7, 10, 11} ∨
        polygon = {3, 4, 9, 10, 11} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {3, 5, 7, 9, 11} ∨
        polygon = {3, 5, 7, 10, 11} ∨
        polygon = {3, 5, 9, 10, 11} ∨
        polygon = {3, 7, 9, 10, 11} ∨
        polygon = {4, 5, 7, 9, 10} ∨
        polygon = {4, 5, 7, 9, 11} ∨
        polygon = {4, 5, 7, 10, 11} ∨
        polygon = {4, 5, 9, 10, 11} ∨
        polygon = {4, 7, 9, 10, 11} ∨
        polygon = {5, 7, 9, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 5, 7, 9, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 5, 7, 9, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 5, 7, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 5, 7, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 5, 7, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 5, 7, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 5, 7, 9, 10, 11} \ {x, y} := by
    calc
      polygon = {3, 4, 5, 7, 9, 10, 11} \ ({3, 4, 5, 7, 9, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 5, 7, 9, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5816 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 5, 7, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {4, 5, 7, 9, 10} ∨
        polygon = {4, 5, 7, 9, 12} ∨
        polygon = {4, 5, 7, 10, 12} ∨
        polygon = {4, 5, 9, 10, 12} ∨
        polygon = {4, 7, 9, 10, 12} ∨
        polygon = {5, 7, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 5, 7, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 5, 7, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 5, 7, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 5, 7, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 5, 7, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 5, 7, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 5, 7, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {3, 4, 5, 7, 9, 10, 12} \ ({3, 4, 5, 7, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 5, 7, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

end ErdosSzekeres

end
