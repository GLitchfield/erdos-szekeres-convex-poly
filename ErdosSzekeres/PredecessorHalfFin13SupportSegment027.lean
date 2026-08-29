module

public import ErdosSzekeres.PredecessorHalfFin13Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 027. -/

theorem predecessorHalfFin13_fiveSubset_mask6840 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 5, 7, 9, 11, 12} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {3, 4, 5, 7, 11} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {3, 4, 5, 9, 11} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 5, 11, 12} ∨
        polygon = {3, 4, 7, 9, 11} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 4, 7, 11, 12} ∨
        polygon = {3, 4, 9, 11, 12} ∨
        polygon = {3, 5, 7, 9, 11} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {3, 5, 7, 11, 12} ∨
        polygon = {3, 5, 9, 11, 12} ∨
        polygon = {3, 7, 9, 11, 12} ∨
        polygon = {4, 5, 7, 9, 11} ∨
        polygon = {4, 5, 7, 9, 12} ∨
        polygon = {4, 5, 7, 11, 12} ∨
        polygon = {4, 5, 9, 11, 12} ∨
        polygon = {4, 7, 9, 11, 12} ∨
        polygon = {5, 7, 9, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 5, 7, 9, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 5, 7, 9, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 5, 7, 9, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 5, 7, 9, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 5, 7, 9, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 5, 7, 9, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 5, 7, 9, 11, 12} \ {x, y} := by
    calc
      polygon = {3, 4, 5, 7, 9, 11, 12} \ ({3, 4, 5, 7, 9, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 5, 7, 9, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3896 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 5, 8, 9, 10, 11} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 8, 9} ∨
        polygon = {3, 4, 5, 8, 10} ∨
        polygon = {3, 4, 5, 8, 11} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {3, 4, 5, 9, 11} ∨
        polygon = {3, 4, 5, 10, 11} ∨
        polygon = {3, 4, 8, 9, 10} ∨
        polygon = {3, 4, 8, 9, 11} ∨
        polygon = {3, 4, 8, 10, 11} ∨
        polygon = {3, 4, 9, 10, 11} ∨
        polygon = {3, 5, 8, 9, 10} ∨
        polygon = {3, 5, 8, 9, 11} ∨
        polygon = {3, 5, 8, 10, 11} ∨
        polygon = {3, 5, 9, 10, 11} ∨
        polygon = {3, 8, 9, 10, 11} ∨
        polygon = {4, 5, 8, 9, 10} ∨
        polygon = {4, 5, 8, 9, 11} ∨
        polygon = {4, 5, 8, 10, 11} ∨
        polygon = {4, 5, 9, 10, 11} ∨
        polygon = {4, 8, 9, 10, 11} ∨
        polygon = {5, 8, 9, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 5, 8, 9, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 5, 8, 9, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 5, 8, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 5, 8, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 5, 8, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 5, 8, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 5, 8, 9, 10, 11} \ {x, y} := by
    calc
      polygon = {3, 4, 5, 8, 9, 10, 11} \ ({3, 4, 5, 8, 9, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 5, 8, 9, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5944 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 5, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 8, 9} ∨
        polygon = {3, 4, 5, 8, 10} ∨
        polygon = {3, 4, 5, 8, 12} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 8, 9, 10} ∨
        polygon = {3, 4, 8, 9, 12} ∨
        polygon = {3, 4, 8, 10, 12} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 5, 8, 9, 10} ∨
        polygon = {3, 5, 8, 9, 12} ∨
        polygon = {3, 5, 8, 10, 12} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 8, 9, 10, 12} ∨
        polygon = {4, 5, 8, 9, 10} ∨
        polygon = {4, 5, 8, 9, 12} ∨
        polygon = {4, 5, 8, 10, 12} ∨
        polygon = {4, 5, 9, 10, 12} ∨
        polygon = {4, 8, 9, 10, 12} ∨
        polygon = {5, 8, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 5, 8, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 5, 8, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 5, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 5, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 5, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 5, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 5, 8, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {3, 4, 5, 8, 9, 10, 12} \ ({3, 4, 5, 8, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 5, 8, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask6968 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 5, 8, 9, 11, 12} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 8, 9} ∨
        polygon = {3, 4, 5, 8, 11} ∨
        polygon = {3, 4, 5, 8, 12} ∨
        polygon = {3, 4, 5, 9, 11} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 5, 11, 12} ∨
        polygon = {3, 4, 8, 9, 11} ∨
        polygon = {3, 4, 8, 9, 12} ∨
        polygon = {3, 4, 8, 11, 12} ∨
        polygon = {3, 4, 9, 11, 12} ∨
        polygon = {3, 5, 8, 9, 11} ∨
        polygon = {3, 5, 8, 9, 12} ∨
        polygon = {3, 5, 8, 11, 12} ∨
        polygon = {3, 5, 9, 11, 12} ∨
        polygon = {3, 8, 9, 11, 12} ∨
        polygon = {4, 5, 8, 9, 11} ∨
        polygon = {4, 5, 8, 9, 12} ∨
        polygon = {4, 5, 8, 11, 12} ∨
        polygon = {4, 5, 9, 11, 12} ∨
        polygon = {4, 8, 9, 11, 12} ∨
        polygon = {5, 8, 9, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 5, 8, 9, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 5, 8, 9, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 5, 8, 9, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 5, 8, 9, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 5, 8, 9, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 5, 8, 9, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 5, 8, 9, 11, 12} \ {x, y} := by
    calc
      polygon = {3, 4, 5, 8, 9, 11, 12} \ ({3, 4, 5, 8, 9, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 5, 8, 9, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask7736 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 5, 9, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {3, 4, 5, 9, 11} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 5, 10, 11} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 5, 11, 12} ∨
        polygon = {3, 4, 9, 10, 11} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 4, 9, 11, 12} ∨
        polygon = {3, 4, 10, 11, 12} ∨
        polygon = {3, 5, 9, 10, 11} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 5, 9, 11, 12} ∨
        polygon = {3, 5, 10, 11, 12} ∨
        polygon = {3, 9, 10, 11, 12} ∨
        polygon = {4, 5, 9, 10, 11} ∨
        polygon = {4, 5, 9, 10, 12} ∨
        polygon = {4, 5, 9, 11, 12} ∨
        polygon = {4, 5, 10, 11, 12} ∨
        polygon = {4, 9, 10, 11, 12} ∨
        polygon = {5, 9, 10, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 5, 9, 10, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 5, 9, 10, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 5, 9, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 5, 9, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 5, 9, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 5, 9, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 5, 9, 10, 11, 12} \ {x, y} := by
    calc
      polygon = {3, 4, 5, 9, 10, 11, 12} \ ({3, 4, 5, 9, 10, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 5, 9, 10, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask2008 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 6, 7, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {3, 4, 6, 7, 8} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {3, 4, 6, 8, 9} ∨
        polygon = {3, 4, 6, 8, 10} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 4, 7, 8, 9} ∨
        polygon = {3, 4, 7, 8, 10} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {3, 4, 8, 9, 10} ∨
        polygon = {3, 6, 7, 8, 9} ∨
        polygon = {3, 6, 7, 8, 10} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {3, 6, 8, 9, 10} ∨
        polygon = {3, 7, 8, 9, 10} ∨
        polygon = {4, 6, 7, 8, 9} ∨
        polygon = {4, 6, 7, 8, 10} ∨
        polygon = {4, 6, 7, 9, 10} ∨
        polygon = {4, 6, 8, 9, 10} ∨
        polygon = {4, 7, 8, 9, 10} ∨
        polygon = {6, 7, 8, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 6, 7, 8, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 6, 7, 8, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 6, 7, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 6, 7, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 6, 7, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 6, 7, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 6, 7, 8, 9, 10} \ {x, y} := by
    calc
      polygon = {3, 4, 6, 7, 8, 9, 10} \ ({3, 4, 6, 7, 8, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 6, 7, 8, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3032 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 6, 7, 8, 9, 11} →
      polygon.card = 5 →
        polygon = {3, 4, 6, 7, 8} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {3, 4, 6, 7, 11} ∨
        polygon = {3, 4, 6, 8, 9} ∨
        polygon = {3, 4, 6, 8, 11} ∨
        polygon = {3, 4, 6, 9, 11} ∨
        polygon = {3, 4, 7, 8, 9} ∨
        polygon = {3, 4, 7, 8, 11} ∨
        polygon = {3, 4, 7, 9, 11} ∨
        polygon = {3, 4, 8, 9, 11} ∨
        polygon = {3, 6, 7, 8, 9} ∨
        polygon = {3, 6, 7, 8, 11} ∨
        polygon = {3, 6, 7, 9, 11} ∨
        polygon = {3, 6, 8, 9, 11} ∨
        polygon = {3, 7, 8, 9, 11} ∨
        polygon = {4, 6, 7, 8, 9} ∨
        polygon = {4, 6, 7, 8, 11} ∨
        polygon = {4, 6, 7, 9, 11} ∨
        polygon = {4, 6, 8, 9, 11} ∨
        polygon = {4, 7, 8, 9, 11} ∨
        polygon = {6, 7, 8, 9, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 6, 7, 8, 9, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 6, 7, 8, 9, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 6, 7, 8, 9, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 6, 7, 8, 9, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 6, 7, 8, 9, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 6, 7, 8, 9, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 6, 7, 8, 9, 11} \ {x, y} := by
    calc
      polygon = {3, 4, 6, 7, 8, 9, 11} \ ({3, 4, 6, 7, 8, 9, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 6, 7, 8, 9, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5080 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 6, 7, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {3, 4, 6, 7, 8} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 4, 6, 8, 9} ∨
        polygon = {3, 4, 6, 8, 12} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 7, 8, 9} ∨
        polygon = {3, 4, 7, 8, 12} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 4, 8, 9, 12} ∨
        polygon = {3, 6, 7, 8, 9} ∨
        polygon = {3, 6, 7, 8, 12} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {3, 6, 8, 9, 12} ∨
        polygon = {3, 7, 8, 9, 12} ∨
        polygon = {4, 6, 7, 8, 9} ∨
        polygon = {4, 6, 7, 8, 12} ∨
        polygon = {4, 6, 7, 9, 12} ∨
        polygon = {4, 6, 8, 9, 12} ∨
        polygon = {4, 7, 8, 9, 12} ∨
        polygon = {6, 7, 8, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 6, 7, 8, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 6, 7, 8, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 6, 7, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 6, 7, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 6, 7, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 6, 7, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 6, 7, 8, 9, 12} \ {x, y} := by
    calc
      polygon = {3, 4, 6, 7, 8, 9, 12} \ ({3, 4, 6, 7, 8, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 6, 7, 8, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3544 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 6, 7, 8, 10, 11} →
      polygon.card = 5 →
        polygon = {3, 4, 6, 7, 8} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {3, 4, 6, 7, 11} ∨
        polygon = {3, 4, 6, 8, 10} ∨
        polygon = {3, 4, 6, 8, 11} ∨
        polygon = {3, 4, 6, 10, 11} ∨
        polygon = {3, 4, 7, 8, 10} ∨
        polygon = {3, 4, 7, 8, 11} ∨
        polygon = {3, 4, 7, 10, 11} ∨
        polygon = {3, 4, 8, 10, 11} ∨
        polygon = {3, 6, 7, 8, 10} ∨
        polygon = {3, 6, 7, 8, 11} ∨
        polygon = {3, 6, 7, 10, 11} ∨
        polygon = {3, 6, 8, 10, 11} ∨
        polygon = {3, 7, 8, 10, 11} ∨
        polygon = {4, 6, 7, 8, 10} ∨
        polygon = {4, 6, 7, 8, 11} ∨
        polygon = {4, 6, 7, 10, 11} ∨
        polygon = {4, 6, 8, 10, 11} ∨
        polygon = {4, 7, 8, 10, 11} ∨
        polygon = {6, 7, 8, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 6, 7, 8, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 6, 7, 8, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 6, 7, 8, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 6, 7, 8, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 6, 7, 8, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 6, 7, 8, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 6, 7, 8, 10, 11} \ {x, y} := by
    calc
      polygon = {3, 4, 6, 7, 8, 10, 11} \ ({3, 4, 6, 7, 8, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 6, 7, 8, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5592 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 6, 7, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {3, 4, 6, 7, 8} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 4, 6, 8, 10} ∨
        polygon = {3, 4, 6, 8, 12} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 7, 8, 10} ∨
        polygon = {3, 4, 7, 8, 12} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {3, 4, 8, 10, 12} ∨
        polygon = {3, 6, 7, 8, 10} ∨
        polygon = {3, 6, 7, 8, 12} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {3, 6, 8, 10, 12} ∨
        polygon = {3, 7, 8, 10, 12} ∨
        polygon = {4, 6, 7, 8, 10} ∨
        polygon = {4, 6, 7, 8, 12} ∨
        polygon = {4, 6, 7, 10, 12} ∨
        polygon = {4, 6, 8, 10, 12} ∨
        polygon = {4, 7, 8, 10, 12} ∨
        polygon = {6, 7, 8, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 6, 7, 8, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 6, 7, 8, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 6, 7, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 6, 7, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 6, 7, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 6, 7, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 6, 7, 8, 10, 12} \ {x, y} := by
    calc
      polygon = {3, 4, 6, 7, 8, 10, 12} \ ({3, 4, 6, 7, 8, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 6, 7, 8, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask6616 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 6, 7, 8, 11, 12} →
      polygon.card = 5 →
        polygon = {3, 4, 6, 7, 8} ∨
        polygon = {3, 4, 6, 7, 11} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 4, 6, 8, 11} ∨
        polygon = {3, 4, 6, 8, 12} ∨
        polygon = {3, 4, 6, 11, 12} ∨
        polygon = {3, 4, 7, 8, 11} ∨
        polygon = {3, 4, 7, 8, 12} ∨
        polygon = {3, 4, 7, 11, 12} ∨
        polygon = {3, 4, 8, 11, 12} ∨
        polygon = {3, 6, 7, 8, 11} ∨
        polygon = {3, 6, 7, 8, 12} ∨
        polygon = {3, 6, 7, 11, 12} ∨
        polygon = {3, 6, 8, 11, 12} ∨
        polygon = {3, 7, 8, 11, 12} ∨
        polygon = {4, 6, 7, 8, 11} ∨
        polygon = {4, 6, 7, 8, 12} ∨
        polygon = {4, 6, 7, 11, 12} ∨
        polygon = {4, 6, 8, 11, 12} ∨
        polygon = {4, 7, 8, 11, 12} ∨
        polygon = {6, 7, 8, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 6, 7, 8, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 6, 7, 8, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 6, 7, 8, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 6, 7, 8, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 6, 7, 8, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 6, 7, 8, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 6, 7, 8, 11, 12} \ {x, y} := by
    calc
      polygon = {3, 4, 6, 7, 8, 11, 12} \ ({3, 4, 6, 7, 8, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 6, 7, 8, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3800 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 6, 7, 9, 10, 11} →
      polygon.card = 5 →
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {3, 4, 6, 7, 11} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 4, 6, 9, 11} ∨
        polygon = {3, 4, 6, 10, 11} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {3, 4, 7, 9, 11} ∨
        polygon = {3, 4, 7, 10, 11} ∨
        polygon = {3, 4, 9, 10, 11} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {3, 6, 7, 9, 11} ∨
        polygon = {3, 6, 7, 10, 11} ∨
        polygon = {3, 6, 9, 10, 11} ∨
        polygon = {3, 7, 9, 10, 11} ∨
        polygon = {4, 6, 7, 9, 10} ∨
        polygon = {4, 6, 7, 9, 11} ∨
        polygon = {4, 6, 7, 10, 11} ∨
        polygon = {4, 6, 9, 10, 11} ∨
        polygon = {4, 7, 9, 10, 11} ∨
        polygon = {6, 7, 9, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 6, 7, 9, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 6, 7, 9, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 6, 7, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 6, 7, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 6, 7, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 6, 7, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 6, 7, 9, 10, 11} \ {x, y} := by
    calc
      polygon = {3, 4, 6, 7, 9, 10, 11} \ ({3, 4, 6, 7, 9, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 6, 7, 9, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5848 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 6, 7, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {4, 6, 7, 9, 10} ∨
        polygon = {4, 6, 7, 9, 12} ∨
        polygon = {4, 6, 7, 10, 12} ∨
        polygon = {4, 6, 9, 10, 12} ∨
        polygon = {4, 7, 9, 10, 12} ∨
        polygon = {6, 7, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 6, 7, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 6, 7, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 6, 7, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 6, 7, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 6, 7, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 6, 7, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 6, 7, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {3, 4, 6, 7, 9, 10, 12} \ ({3, 4, 6, 7, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 6, 7, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask6872 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 6, 7, 9, 11, 12} →
      polygon.card = 5 →
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {3, 4, 6, 7, 11} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 4, 6, 9, 11} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 6, 11, 12} ∨
        polygon = {3, 4, 7, 9, 11} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 4, 7, 11, 12} ∨
        polygon = {3, 4, 9, 11, 12} ∨
        polygon = {3, 6, 7, 9, 11} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {3, 6, 7, 11, 12} ∨
        polygon = {3, 6, 9, 11, 12} ∨
        polygon = {3, 7, 9, 11, 12} ∨
        polygon = {4, 6, 7, 9, 11} ∨
        polygon = {4, 6, 7, 9, 12} ∨
        polygon = {4, 6, 7, 11, 12} ∨
        polygon = {4, 6, 9, 11, 12} ∨
        polygon = {4, 7, 9, 11, 12} ∨
        polygon = {6, 7, 9, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 6, 7, 9, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 6, 7, 9, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 6, 7, 9, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 6, 7, 9, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 6, 7, 9, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 6, 7, 9, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 6, 7, 9, 11, 12} \ {x, y} := by
    calc
      polygon = {3, 4, 6, 7, 9, 11, 12} \ ({3, 4, 6, 7, 9, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 6, 7, 9, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask7384 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 6, 7, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {3, 4, 6, 7, 11} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 4, 6, 10, 11} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 6, 11, 12} ∨
        polygon = {3, 4, 7, 10, 11} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {3, 4, 7, 11, 12} ∨
        polygon = {3, 4, 10, 11, 12} ∨
        polygon = {3, 6, 7, 10, 11} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {3, 6, 7, 11, 12} ∨
        polygon = {3, 6, 10, 11, 12} ∨
        polygon = {3, 7, 10, 11, 12} ∨
        polygon = {4, 6, 7, 10, 11} ∨
        polygon = {4, 6, 7, 10, 12} ∨
        polygon = {4, 6, 7, 11, 12} ∨
        polygon = {4, 6, 10, 11, 12} ∨
        polygon = {4, 7, 10, 11, 12} ∨
        polygon = {6, 7, 10, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 6, 7, 10, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 6, 7, 10, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 6, 7, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 6, 7, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 6, 7, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 6, 7, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 6, 7, 10, 11, 12} \ {x, y} := by
    calc
      polygon = {3, 4, 6, 7, 10, 11, 12} \ ({3, 4, 6, 7, 10, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 6, 7, 10, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3928 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 6, 8, 9, 10, 11} →
      polygon.card = 5 →
        polygon = {3, 4, 6, 8, 9} ∨
        polygon = {3, 4, 6, 8, 10} ∨
        polygon = {3, 4, 6, 8, 11} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 4, 6, 9, 11} ∨
        polygon = {3, 4, 6, 10, 11} ∨
        polygon = {3, 4, 8, 9, 10} ∨
        polygon = {3, 4, 8, 9, 11} ∨
        polygon = {3, 4, 8, 10, 11} ∨
        polygon = {3, 4, 9, 10, 11} ∨
        polygon = {3, 6, 8, 9, 10} ∨
        polygon = {3, 6, 8, 9, 11} ∨
        polygon = {3, 6, 8, 10, 11} ∨
        polygon = {3, 6, 9, 10, 11} ∨
        polygon = {3, 8, 9, 10, 11} ∨
        polygon = {4, 6, 8, 9, 10} ∨
        polygon = {4, 6, 8, 9, 11} ∨
        polygon = {4, 6, 8, 10, 11} ∨
        polygon = {4, 6, 9, 10, 11} ∨
        polygon = {4, 8, 9, 10, 11} ∨
        polygon = {6, 8, 9, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 6, 8, 9, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 6, 8, 9, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 6, 8, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 6, 8, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 6, 8, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 6, 8, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 6, 8, 9, 10, 11} \ {x, y} := by
    calc
      polygon = {3, 4, 6, 8, 9, 10, 11} \ ({3, 4, 6, 8, 9, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 6, 8, 9, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5976 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 6, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {3, 4, 6, 8, 9} ∨
        polygon = {3, 4, 6, 8, 10} ∨
        polygon = {3, 4, 6, 8, 12} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 8, 9, 10} ∨
        polygon = {3, 4, 8, 9, 12} ∨
        polygon = {3, 4, 8, 10, 12} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 6, 8, 9, 10} ∨
        polygon = {3, 6, 8, 9, 12} ∨
        polygon = {3, 6, 8, 10, 12} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {3, 8, 9, 10, 12} ∨
        polygon = {4, 6, 8, 9, 10} ∨
        polygon = {4, 6, 8, 9, 12} ∨
        polygon = {4, 6, 8, 10, 12} ∨
        polygon = {4, 6, 9, 10, 12} ∨
        polygon = {4, 8, 9, 10, 12} ∨
        polygon = {6, 8, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 6, 8, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 6, 8, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 6, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 6, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 6, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 6, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 6, 8, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {3, 4, 6, 8, 9, 10, 12} \ ({3, 4, 6, 8, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 6, 8, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask7000 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 6, 8, 9, 11, 12} →
      polygon.card = 5 →
        polygon = {3, 4, 6, 8, 9} ∨
        polygon = {3, 4, 6, 8, 11} ∨
        polygon = {3, 4, 6, 8, 12} ∨
        polygon = {3, 4, 6, 9, 11} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 6, 11, 12} ∨
        polygon = {3, 4, 8, 9, 11} ∨
        polygon = {3, 4, 8, 9, 12} ∨
        polygon = {3, 4, 8, 11, 12} ∨
        polygon = {3, 4, 9, 11, 12} ∨
        polygon = {3, 6, 8, 9, 11} ∨
        polygon = {3, 6, 8, 9, 12} ∨
        polygon = {3, 6, 8, 11, 12} ∨
        polygon = {3, 6, 9, 11, 12} ∨
        polygon = {3, 8, 9, 11, 12} ∨
        polygon = {4, 6, 8, 9, 11} ∨
        polygon = {4, 6, 8, 9, 12} ∨
        polygon = {4, 6, 8, 11, 12} ∨
        polygon = {4, 6, 9, 11, 12} ∨
        polygon = {4, 8, 9, 11, 12} ∨
        polygon = {6, 8, 9, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 6, 8, 9, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 6, 8, 9, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 6, 8, 9, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 6, 8, 9, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 6, 8, 9, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 6, 8, 9, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 6, 8, 9, 11, 12} \ {x, y} := by
    calc
      polygon = {3, 4, 6, 8, 9, 11, 12} \ ({3, 4, 6, 8, 9, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 6, 8, 9, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask7512 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 6, 8, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {3, 4, 6, 8, 10} ∨
        polygon = {3, 4, 6, 8, 11} ∨
        polygon = {3, 4, 6, 8, 12} ∨
        polygon = {3, 4, 6, 10, 11} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 6, 11, 12} ∨
        polygon = {3, 4, 8, 10, 11} ∨
        polygon = {3, 4, 8, 10, 12} ∨
        polygon = {3, 4, 8, 11, 12} ∨
        polygon = {3, 4, 10, 11, 12} ∨
        polygon = {3, 6, 8, 10, 11} ∨
        polygon = {3, 6, 8, 10, 12} ∨
        polygon = {3, 6, 8, 11, 12} ∨
        polygon = {3, 6, 10, 11, 12} ∨
        polygon = {3, 8, 10, 11, 12} ∨
        polygon = {4, 6, 8, 10, 11} ∨
        polygon = {4, 6, 8, 10, 12} ∨
        polygon = {4, 6, 8, 11, 12} ∨
        polygon = {4, 6, 10, 11, 12} ∨
        polygon = {4, 8, 10, 11, 12} ∨
        polygon = {6, 8, 10, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 6, 8, 10, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 6, 8, 10, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 6, 8, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 6, 8, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 6, 8, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 6, 8, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 6, 8, 10, 11, 12} \ {x, y} := by
    calc
      polygon = {3, 4, 6, 8, 10, 11, 12} \ ({3, 4, 6, 8, 10, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 6, 8, 10, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask7768 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 6, 9, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 4, 6, 9, 11} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 6, 10, 11} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 6, 11, 12} ∨
        polygon = {3, 4, 9, 10, 11} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 4, 9, 11, 12} ∨
        polygon = {3, 4, 10, 11, 12} ∨
        polygon = {3, 6, 9, 10, 11} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {3, 6, 9, 11, 12} ∨
        polygon = {3, 6, 10, 11, 12} ∨
        polygon = {3, 9, 10, 11, 12} ∨
        polygon = {4, 6, 9, 10, 11} ∨
        polygon = {4, 6, 9, 10, 12} ∨
        polygon = {4, 6, 9, 11, 12} ∨
        polygon = {4, 6, 10, 11, 12} ∨
        polygon = {4, 9, 10, 11, 12} ∨
        polygon = {6, 9, 10, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 6, 9, 10, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 6, 9, 10, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 6, 9, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 6, 9, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 6, 9, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 6, 9, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 6, 9, 10, 11, 12} \ {x, y} := by
    calc
      polygon = {3, 4, 6, 9, 10, 11, 12} \ ({3, 4, 6, 9, 10, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 6, 9, 10, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3992 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 7, 8, 9, 10, 11} →
      polygon.card = 5 →
        polygon = {3, 4, 7, 8, 9} ∨
        polygon = {3, 4, 7, 8, 10} ∨
        polygon = {3, 4, 7, 8, 11} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {3, 4, 7, 9, 11} ∨
        polygon = {3, 4, 7, 10, 11} ∨
        polygon = {3, 4, 8, 9, 10} ∨
        polygon = {3, 4, 8, 9, 11} ∨
        polygon = {3, 4, 8, 10, 11} ∨
        polygon = {3, 4, 9, 10, 11} ∨
        polygon = {3, 7, 8, 9, 10} ∨
        polygon = {3, 7, 8, 9, 11} ∨
        polygon = {3, 7, 8, 10, 11} ∨
        polygon = {3, 7, 9, 10, 11} ∨
        polygon = {3, 8, 9, 10, 11} ∨
        polygon = {4, 7, 8, 9, 10} ∨
        polygon = {4, 7, 8, 9, 11} ∨
        polygon = {4, 7, 8, 10, 11} ∨
        polygon = {4, 7, 9, 10, 11} ∨
        polygon = {4, 8, 9, 10, 11} ∨
        polygon = {7, 8, 9, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 7, 8, 9, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 7, 8, 9, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 7, 8, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 7, 8, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 7, 8, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 7, 8, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 7, 8, 9, 10, 11} \ {x, y} := by
    calc
      polygon = {3, 4, 7, 8, 9, 10, 11} \ ({3, 4, 7, 8, 9, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 7, 8, 9, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask6040 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 7, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {3, 4, 7, 8, 9} ∨
        polygon = {3, 4, 7, 8, 10} ∨
        polygon = {3, 4, 7, 8, 12} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {3, 4, 8, 9, 10} ∨
        polygon = {3, 4, 8, 9, 12} ∨
        polygon = {3, 4, 8, 10, 12} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 7, 8, 9, 10} ∨
        polygon = {3, 7, 8, 9, 12} ∨
        polygon = {3, 7, 8, 10, 12} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {3, 8, 9, 10, 12} ∨
        polygon = {4, 7, 8, 9, 10} ∨
        polygon = {4, 7, 8, 9, 12} ∨
        polygon = {4, 7, 8, 10, 12} ∨
        polygon = {4, 7, 9, 10, 12} ∨
        polygon = {4, 8, 9, 10, 12} ∨
        polygon = {7, 8, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 7, 8, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 7, 8, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 7, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 7, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 7, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 7, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 7, 8, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {3, 4, 7, 8, 9, 10, 12} \ ({3, 4, 7, 8, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 7, 8, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask7064 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 7, 8, 9, 11, 12} →
      polygon.card = 5 →
        polygon = {3, 4, 7, 8, 9} ∨
        polygon = {3, 4, 7, 8, 11} ∨
        polygon = {3, 4, 7, 8, 12} ∨
        polygon = {3, 4, 7, 9, 11} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 4, 7, 11, 12} ∨
        polygon = {3, 4, 8, 9, 11} ∨
        polygon = {3, 4, 8, 9, 12} ∨
        polygon = {3, 4, 8, 11, 12} ∨
        polygon = {3, 4, 9, 11, 12} ∨
        polygon = {3, 7, 8, 9, 11} ∨
        polygon = {3, 7, 8, 9, 12} ∨
        polygon = {3, 7, 8, 11, 12} ∨
        polygon = {3, 7, 9, 11, 12} ∨
        polygon = {3, 8, 9, 11, 12} ∨
        polygon = {4, 7, 8, 9, 11} ∨
        polygon = {4, 7, 8, 9, 12} ∨
        polygon = {4, 7, 8, 11, 12} ∨
        polygon = {4, 7, 9, 11, 12} ∨
        polygon = {4, 8, 9, 11, 12} ∨
        polygon = {7, 8, 9, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 7, 8, 9, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 7, 8, 9, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 7, 8, 9, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 7, 8, 9, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 7, 8, 9, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 7, 8, 9, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 7, 8, 9, 11, 12} \ {x, y} := by
    calc
      polygon = {3, 4, 7, 8, 9, 11, 12} \ ({3, 4, 7, 8, 9, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 7, 8, 9, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask7832 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 7, 9, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {3, 4, 7, 9, 11} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 4, 7, 10, 11} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {3, 4, 7, 11, 12} ∨
        polygon = {3, 4, 9, 10, 11} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 4, 9, 11, 12} ∨
        polygon = {3, 4, 10, 11, 12} ∨
        polygon = {3, 7, 9, 10, 11} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {3, 7, 9, 11, 12} ∨
        polygon = {3, 7, 10, 11, 12} ∨
        polygon = {3, 9, 10, 11, 12} ∨
        polygon = {4, 7, 9, 10, 11} ∨
        polygon = {4, 7, 9, 10, 12} ∨
        polygon = {4, 7, 9, 11, 12} ∨
        polygon = {4, 7, 10, 11, 12} ∨
        polygon = {4, 9, 10, 11, 12} ∨
        polygon = {7, 9, 10, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 7, 9, 10, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 7, 9, 10, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 7, 9, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 7, 9, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 7, 9, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 7, 9, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 7, 9, 10, 11, 12} \ {x, y} := by
    calc
      polygon = {3, 4, 7, 9, 10, 11, 12} \ ({3, 4, 7, 9, 10, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 7, 9, 10, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask7960 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 4, 8, 9, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {3, 4, 8, 9, 10} ∨
        polygon = {3, 4, 8, 9, 11} ∨
        polygon = {3, 4, 8, 9, 12} ∨
        polygon = {3, 4, 8, 10, 11} ∨
        polygon = {3, 4, 8, 10, 12} ∨
        polygon = {3, 4, 8, 11, 12} ∨
        polygon = {3, 4, 9, 10, 11} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 4, 9, 11, 12} ∨
        polygon = {3, 4, 10, 11, 12} ∨
        polygon = {3, 8, 9, 10, 11} ∨
        polygon = {3, 8, 9, 10, 12} ∨
        polygon = {3, 8, 9, 11, 12} ∨
        polygon = {3, 8, 10, 11, 12} ∨
        polygon = {3, 9, 10, 11, 12} ∨
        polygon = {4, 8, 9, 10, 11} ∨
        polygon = {4, 8, 9, 10, 12} ∨
        polygon = {4, 8, 9, 11, 12} ∨
        polygon = {4, 8, 10, 11, 12} ∨
        polygon = {4, 9, 10, 11, 12} ∨
        polygon = {8, 9, 10, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 4, 8, 9, 10, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 4, 8, 9, 10, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 4, 8, 9, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 4, 8, 9, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 4, 8, 9, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 4, 8, 9, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 4, 8, 9, 10, 11, 12} \ {x, y} := by
    calc
      polygon = {3, 4, 8, 9, 10, 11, 12} \ ({3, 4, 8, 9, 10, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 4, 8, 9, 10, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask2024 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 5, 6, 7, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {3, 5, 6, 7, 8} ∨
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {3, 5, 6, 8, 9} ∨
        polygon = {3, 5, 6, 8, 10} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {3, 5, 7, 8, 9} ∨
        polygon = {3, 5, 7, 8, 10} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {3, 5, 8, 9, 10} ∨
        polygon = {3, 6, 7, 8, 9} ∨
        polygon = {3, 6, 7, 8, 10} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {3, 6, 8, 9, 10} ∨
        polygon = {3, 7, 8, 9, 10} ∨
        polygon = {5, 6, 7, 8, 9} ∨
        polygon = {5, 6, 7, 8, 10} ∨
        polygon = {5, 6, 7, 9, 10} ∨
        polygon = {5, 6, 8, 9, 10} ∨
        polygon = {5, 7, 8, 9, 10} ∨
        polygon = {6, 7, 8, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 5, 6, 7, 8, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 5, 6, 7, 8, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 5, 6, 7, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 5, 6, 7, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 5, 6, 7, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 5, 6, 7, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 5, 6, 7, 8, 9, 10} \ {x, y} := by
    calc
      polygon = {3, 5, 6, 7, 8, 9, 10} \ ({3, 5, 6, 7, 8, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 5, 6, 7, 8, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3048 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 5, 6, 7, 8, 9, 11} →
      polygon.card = 5 →
        polygon = {3, 5, 6, 7, 8} ∨
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {3, 5, 6, 7, 11} ∨
        polygon = {3, 5, 6, 8, 9} ∨
        polygon = {3, 5, 6, 8, 11} ∨
        polygon = {3, 5, 6, 9, 11} ∨
        polygon = {3, 5, 7, 8, 9} ∨
        polygon = {3, 5, 7, 8, 11} ∨
        polygon = {3, 5, 7, 9, 11} ∨
        polygon = {3, 5, 8, 9, 11} ∨
        polygon = {3, 6, 7, 8, 9} ∨
        polygon = {3, 6, 7, 8, 11} ∨
        polygon = {3, 6, 7, 9, 11} ∨
        polygon = {3, 6, 8, 9, 11} ∨
        polygon = {3, 7, 8, 9, 11} ∨
        polygon = {5, 6, 7, 8, 9} ∨
        polygon = {5, 6, 7, 8, 11} ∨
        polygon = {5, 6, 7, 9, 11} ∨
        polygon = {5, 6, 8, 9, 11} ∨
        polygon = {5, 7, 8, 9, 11} ∨
        polygon = {6, 7, 8, 9, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 5, 6, 7, 8, 9, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 5, 6, 7, 8, 9, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 5, 6, 7, 8, 9, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 5, 6, 7, 8, 9, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 5, 6, 7, 8, 9, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 5, 6, 7, 8, 9, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 5, 6, 7, 8, 9, 11} \ {x, y} := by
    calc
      polygon = {3, 5, 6, 7, 8, 9, 11} \ ({3, 5, 6, 7, 8, 9, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 5, 6, 7, 8, 9, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5096 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 5, 6, 7, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {3, 5, 6, 7, 8} ∨
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {3, 5, 6, 8, 9} ∨
        polygon = {3, 5, 6, 8, 12} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {3, 5, 7, 8, 9} ∨
        polygon = {3, 5, 7, 8, 12} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {3, 5, 8, 9, 12} ∨
        polygon = {3, 6, 7, 8, 9} ∨
        polygon = {3, 6, 7, 8, 12} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {3, 6, 8, 9, 12} ∨
        polygon = {3, 7, 8, 9, 12} ∨
        polygon = {5, 6, 7, 8, 9} ∨
        polygon = {5, 6, 7, 8, 12} ∨
        polygon = {5, 6, 7, 9, 12} ∨
        polygon = {5, 6, 8, 9, 12} ∨
        polygon = {5, 7, 8, 9, 12} ∨
        polygon = {6, 7, 8, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 5, 6, 7, 8, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 5, 6, 7, 8, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 5, 6, 7, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 5, 6, 7, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 5, 6, 7, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 5, 6, 7, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 5, 6, 7, 8, 9, 12} \ {x, y} := by
    calc
      polygon = {3, 5, 6, 7, 8, 9, 12} \ ({3, 5, 6, 7, 8, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 5, 6, 7, 8, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3560 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 5, 6, 7, 8, 10, 11} →
      polygon.card = 5 →
        polygon = {3, 5, 6, 7, 8} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {3, 5, 6, 7, 11} ∨
        polygon = {3, 5, 6, 8, 10} ∨
        polygon = {3, 5, 6, 8, 11} ∨
        polygon = {3, 5, 6, 10, 11} ∨
        polygon = {3, 5, 7, 8, 10} ∨
        polygon = {3, 5, 7, 8, 11} ∨
        polygon = {3, 5, 7, 10, 11} ∨
        polygon = {3, 5, 8, 10, 11} ∨
        polygon = {3, 6, 7, 8, 10} ∨
        polygon = {3, 6, 7, 8, 11} ∨
        polygon = {3, 6, 7, 10, 11} ∨
        polygon = {3, 6, 8, 10, 11} ∨
        polygon = {3, 7, 8, 10, 11} ∨
        polygon = {5, 6, 7, 8, 10} ∨
        polygon = {5, 6, 7, 8, 11} ∨
        polygon = {5, 6, 7, 10, 11} ∨
        polygon = {5, 6, 8, 10, 11} ∨
        polygon = {5, 7, 8, 10, 11} ∨
        polygon = {6, 7, 8, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 5, 6, 7, 8, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 5, 6, 7, 8, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 5, 6, 7, 8, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 5, 6, 7, 8, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 5, 6, 7, 8, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 5, 6, 7, 8, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 5, 6, 7, 8, 10, 11} \ {x, y} := by
    calc
      polygon = {3, 5, 6, 7, 8, 10, 11} \ ({3, 5, 6, 7, 8, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 5, 6, 7, 8, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5608 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 5, 6, 7, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {3, 5, 6, 7, 8} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {3, 5, 6, 8, 10} ∨
        polygon = {3, 5, 6, 8, 12} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {3, 5, 7, 8, 10} ∨
        polygon = {3, 5, 7, 8, 12} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {3, 5, 8, 10, 12} ∨
        polygon = {3, 6, 7, 8, 10} ∨
        polygon = {3, 6, 7, 8, 12} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {3, 6, 8, 10, 12} ∨
        polygon = {3, 7, 8, 10, 12} ∨
        polygon = {5, 6, 7, 8, 10} ∨
        polygon = {5, 6, 7, 8, 12} ∨
        polygon = {5, 6, 7, 10, 12} ∨
        polygon = {5, 6, 8, 10, 12} ∨
        polygon = {5, 7, 8, 10, 12} ∨
        polygon = {6, 7, 8, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 5, 6, 7, 8, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 5, 6, 7, 8, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 5, 6, 7, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 5, 6, 7, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 5, 6, 7, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 5, 6, 7, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 5, 6, 7, 8, 10, 12} \ {x, y} := by
    calc
      polygon = {3, 5, 6, 7, 8, 10, 12} \ ({3, 5, 6, 7, 8, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 5, 6, 7, 8, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3816 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 5, 6, 7, 9, 10, 11} →
      polygon.card = 5 →
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {3, 5, 6, 7, 11} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {3, 5, 6, 9, 11} ∨
        polygon = {3, 5, 6, 10, 11} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {3, 5, 7, 9, 11} ∨
        polygon = {3, 5, 7, 10, 11} ∨
        polygon = {3, 5, 9, 10, 11} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {3, 6, 7, 9, 11} ∨
        polygon = {3, 6, 7, 10, 11} ∨
        polygon = {3, 6, 9, 10, 11} ∨
        polygon = {3, 7, 9, 10, 11} ∨
        polygon = {5, 6, 7, 9, 10} ∨
        polygon = {5, 6, 7, 9, 11} ∨
        polygon = {5, 6, 7, 10, 11} ∨
        polygon = {5, 6, 9, 10, 11} ∨
        polygon = {5, 7, 9, 10, 11} ∨
        polygon = {6, 7, 9, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 5, 6, 7, 9, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 5, 6, 7, 9, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 5, 6, 7, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 5, 6, 7, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 5, 6, 7, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 5, 6, 7, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 5, 6, 7, 9, 10, 11} \ {x, y} := by
    calc
      polygon = {3, 5, 6, 7, 9, 10, 11} \ ({3, 5, 6, 7, 9, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 5, 6, 7, 9, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5864 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 5, 6, 7, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {5, 6, 7, 9, 10} ∨
        polygon = {5, 6, 7, 9, 12} ∨
        polygon = {5, 6, 7, 10, 12} ∨
        polygon = {5, 6, 9, 10, 12} ∨
        polygon = {5, 7, 9, 10, 12} ∨
        polygon = {6, 7, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 5, 6, 7, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 5, 6, 7, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 5, 6, 7, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 5, 6, 7, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 5, 6, 7, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 5, 6, 7, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 5, 6, 7, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {3, 5, 6, 7, 9, 10, 12} \ ({3, 5, 6, 7, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 5, 6, 7, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask6888 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 5, 6, 7, 9, 11, 12} →
      polygon.card = 5 →
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {3, 5, 6, 7, 11} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {3, 5, 6, 9, 11} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {3, 5, 6, 11, 12} ∨
        polygon = {3, 5, 7, 9, 11} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {3, 5, 7, 11, 12} ∨
        polygon = {3, 5, 9, 11, 12} ∨
        polygon = {3, 6, 7, 9, 11} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {3, 6, 7, 11, 12} ∨
        polygon = {3, 6, 9, 11, 12} ∨
        polygon = {3, 7, 9, 11, 12} ∨
        polygon = {5, 6, 7, 9, 11} ∨
        polygon = {5, 6, 7, 9, 12} ∨
        polygon = {5, 6, 7, 11, 12} ∨
        polygon = {5, 6, 9, 11, 12} ∨
        polygon = {5, 7, 9, 11, 12} ∨
        polygon = {6, 7, 9, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 5, 6, 7, 9, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 5, 6, 7, 9, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 5, 6, 7, 9, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 5, 6, 7, 9, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 5, 6, 7, 9, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 5, 6, 7, 9, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 5, 6, 7, 9, 11, 12} \ {x, y} := by
    calc
      polygon = {3, 5, 6, 7, 9, 11, 12} \ ({3, 5, 6, 7, 9, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 5, 6, 7, 9, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask7400 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 5, 6, 7, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {3, 5, 6, 7, 11} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {3, 5, 6, 10, 11} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {3, 5, 6, 11, 12} ∨
        polygon = {3, 5, 7, 10, 11} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {3, 5, 7, 11, 12} ∨
        polygon = {3, 5, 10, 11, 12} ∨
        polygon = {3, 6, 7, 10, 11} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {3, 6, 7, 11, 12} ∨
        polygon = {3, 6, 10, 11, 12} ∨
        polygon = {3, 7, 10, 11, 12} ∨
        polygon = {5, 6, 7, 10, 11} ∨
        polygon = {5, 6, 7, 10, 12} ∨
        polygon = {5, 6, 7, 11, 12} ∨
        polygon = {5, 6, 10, 11, 12} ∨
        polygon = {5, 7, 10, 11, 12} ∨
        polygon = {6, 7, 10, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 5, 6, 7, 10, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 5, 6, 7, 10, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 5, 6, 7, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 5, 6, 7, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 5, 6, 7, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 5, 6, 7, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 5, 6, 7, 10, 11, 12} \ {x, y} := by
    calc
      polygon = {3, 5, 6, 7, 10, 11, 12} \ ({3, 5, 6, 7, 10, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 5, 6, 7, 10, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3944 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 5, 6, 8, 9, 10, 11} →
      polygon.card = 5 →
        polygon = {3, 5, 6, 8, 9} ∨
        polygon = {3, 5, 6, 8, 10} ∨
        polygon = {3, 5, 6, 8, 11} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {3, 5, 6, 9, 11} ∨
        polygon = {3, 5, 6, 10, 11} ∨
        polygon = {3, 5, 8, 9, 10} ∨
        polygon = {3, 5, 8, 9, 11} ∨
        polygon = {3, 5, 8, 10, 11} ∨
        polygon = {3, 5, 9, 10, 11} ∨
        polygon = {3, 6, 8, 9, 10} ∨
        polygon = {3, 6, 8, 9, 11} ∨
        polygon = {3, 6, 8, 10, 11} ∨
        polygon = {3, 6, 9, 10, 11} ∨
        polygon = {3, 8, 9, 10, 11} ∨
        polygon = {5, 6, 8, 9, 10} ∨
        polygon = {5, 6, 8, 9, 11} ∨
        polygon = {5, 6, 8, 10, 11} ∨
        polygon = {5, 6, 9, 10, 11} ∨
        polygon = {5, 8, 9, 10, 11} ∨
        polygon = {6, 8, 9, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 5, 6, 8, 9, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 5, 6, 8, 9, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 5, 6, 8, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 5, 6, 8, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 5, 6, 8, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 5, 6, 8, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 5, 6, 8, 9, 10, 11} \ {x, y} := by
    calc
      polygon = {3, 5, 6, 8, 9, 10, 11} \ ({3, 5, 6, 8, 9, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 5, 6, 8, 9, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5992 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 5, 6, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {3, 5, 6, 8, 9} ∨
        polygon = {3, 5, 6, 8, 10} ∨
        polygon = {3, 5, 6, 8, 12} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {3, 5, 8, 9, 10} ∨
        polygon = {3, 5, 8, 9, 12} ∨
        polygon = {3, 5, 8, 10, 12} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 6, 8, 9, 10} ∨
        polygon = {3, 6, 8, 9, 12} ∨
        polygon = {3, 6, 8, 10, 12} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {3, 8, 9, 10, 12} ∨
        polygon = {5, 6, 8, 9, 10} ∨
        polygon = {5, 6, 8, 9, 12} ∨
        polygon = {5, 6, 8, 10, 12} ∨
        polygon = {5, 6, 9, 10, 12} ∨
        polygon = {5, 8, 9, 10, 12} ∨
        polygon = {6, 8, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 5, 6, 8, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 5, 6, 8, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 5, 6, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 5, 6, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 5, 6, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 5, 6, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 5, 6, 8, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {3, 5, 6, 8, 9, 10, 12} \ ({3, 5, 6, 8, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 5, 6, 8, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask7016 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 5, 6, 8, 9, 11, 12} →
      polygon.card = 5 →
        polygon = {3, 5, 6, 8, 9} ∨
        polygon = {3, 5, 6, 8, 11} ∨
        polygon = {3, 5, 6, 8, 12} ∨
        polygon = {3, 5, 6, 9, 11} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {3, 5, 6, 11, 12} ∨
        polygon = {3, 5, 8, 9, 11} ∨
        polygon = {3, 5, 8, 9, 12} ∨
        polygon = {3, 5, 8, 11, 12} ∨
        polygon = {3, 5, 9, 11, 12} ∨
        polygon = {3, 6, 8, 9, 11} ∨
        polygon = {3, 6, 8, 9, 12} ∨
        polygon = {3, 6, 8, 11, 12} ∨
        polygon = {3, 6, 9, 11, 12} ∨
        polygon = {3, 8, 9, 11, 12} ∨
        polygon = {5, 6, 8, 9, 11} ∨
        polygon = {5, 6, 8, 9, 12} ∨
        polygon = {5, 6, 8, 11, 12} ∨
        polygon = {5, 6, 9, 11, 12} ∨
        polygon = {5, 8, 9, 11, 12} ∨
        polygon = {6, 8, 9, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 5, 6, 8, 9, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 5, 6, 8, 9, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 5, 6, 8, 9, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 5, 6, 8, 9, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 5, 6, 8, 9, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 5, 6, 8, 9, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 5, 6, 8, 9, 11, 12} \ {x, y} := by
    calc
      polygon = {3, 5, 6, 8, 9, 11, 12} \ ({3, 5, 6, 8, 9, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 5, 6, 8, 9, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask7528 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 5, 6, 8, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {3, 5, 6, 8, 10} ∨
        polygon = {3, 5, 6, 8, 11} ∨
        polygon = {3, 5, 6, 8, 12} ∨
        polygon = {3, 5, 6, 10, 11} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {3, 5, 6, 11, 12} ∨
        polygon = {3, 5, 8, 10, 11} ∨
        polygon = {3, 5, 8, 10, 12} ∨
        polygon = {3, 5, 8, 11, 12} ∨
        polygon = {3, 5, 10, 11, 12} ∨
        polygon = {3, 6, 8, 10, 11} ∨
        polygon = {3, 6, 8, 10, 12} ∨
        polygon = {3, 6, 8, 11, 12} ∨
        polygon = {3, 6, 10, 11, 12} ∨
        polygon = {3, 8, 10, 11, 12} ∨
        polygon = {5, 6, 8, 10, 11} ∨
        polygon = {5, 6, 8, 10, 12} ∨
        polygon = {5, 6, 8, 11, 12} ∨
        polygon = {5, 6, 10, 11, 12} ∨
        polygon = {5, 8, 10, 11, 12} ∨
        polygon = {6, 8, 10, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 5, 6, 8, 10, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 5, 6, 8, 10, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 5, 6, 8, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 5, 6, 8, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 5, 6, 8, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 5, 6, 8, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 5, 6, 8, 10, 11, 12} \ {x, y} := by
    calc
      polygon = {3, 5, 6, 8, 10, 11, 12} \ ({3, 5, 6, 8, 10, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 5, 6, 8, 10, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4008 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 5, 7, 8, 9, 10, 11} →
      polygon.card = 5 →
        polygon = {3, 5, 7, 8, 9} ∨
        polygon = {3, 5, 7, 8, 10} ∨
        polygon = {3, 5, 7, 8, 11} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {3, 5, 7, 9, 11} ∨
        polygon = {3, 5, 7, 10, 11} ∨
        polygon = {3, 5, 8, 9, 10} ∨
        polygon = {3, 5, 8, 9, 11} ∨
        polygon = {3, 5, 8, 10, 11} ∨
        polygon = {3, 5, 9, 10, 11} ∨
        polygon = {3, 7, 8, 9, 10} ∨
        polygon = {3, 7, 8, 9, 11} ∨
        polygon = {3, 7, 8, 10, 11} ∨
        polygon = {3, 7, 9, 10, 11} ∨
        polygon = {3, 8, 9, 10, 11} ∨
        polygon = {5, 7, 8, 9, 10} ∨
        polygon = {5, 7, 8, 9, 11} ∨
        polygon = {5, 7, 8, 10, 11} ∨
        polygon = {5, 7, 9, 10, 11} ∨
        polygon = {5, 8, 9, 10, 11} ∨
        polygon = {7, 8, 9, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 5, 7, 8, 9, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 5, 7, 8, 9, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 5, 7, 8, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 5, 7, 8, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 5, 7, 8, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 5, 7, 8, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 5, 7, 8, 9, 10, 11} \ {x, y} := by
    calc
      polygon = {3, 5, 7, 8, 9, 10, 11} \ ({3, 5, 7, 8, 9, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 5, 7, 8, 9, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask6056 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 5, 7, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {3, 5, 7, 8, 9} ∨
        polygon = {3, 5, 7, 8, 10} ∨
        polygon = {3, 5, 7, 8, 12} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {3, 5, 8, 9, 10} ∨
        polygon = {3, 5, 8, 9, 12} ∨
        polygon = {3, 5, 8, 10, 12} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 7, 8, 9, 10} ∨
        polygon = {3, 7, 8, 9, 12} ∨
        polygon = {3, 7, 8, 10, 12} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {3, 8, 9, 10, 12} ∨
        polygon = {5, 7, 8, 9, 10} ∨
        polygon = {5, 7, 8, 9, 12} ∨
        polygon = {5, 7, 8, 10, 12} ∨
        polygon = {5, 7, 9, 10, 12} ∨
        polygon = {5, 8, 9, 10, 12} ∨
        polygon = {7, 8, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 5, 7, 8, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 5, 7, 8, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 5, 7, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 5, 7, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 5, 7, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 5, 7, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 5, 7, 8, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {3, 5, 7, 8, 9, 10, 12} \ ({3, 5, 7, 8, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 5, 7, 8, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

end ErdosSzekeres

end
