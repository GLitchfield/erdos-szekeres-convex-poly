module

public import ErdosSzekeres.PredecessorHalfFin13Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 028. -/

theorem predecessorHalfFin13_fiveSubset_mask7592 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 5, 7, 8, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {3, 5, 7, 8, 10} ∨
        polygon = {3, 5, 7, 8, 11} ∨
        polygon = {3, 5, 7, 8, 12} ∨
        polygon = {3, 5, 7, 10, 11} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {3, 5, 7, 11, 12} ∨
        polygon = {3, 5, 8, 10, 11} ∨
        polygon = {3, 5, 8, 10, 12} ∨
        polygon = {3, 5, 8, 11, 12} ∨
        polygon = {3, 5, 10, 11, 12} ∨
        polygon = {3, 7, 8, 10, 11} ∨
        polygon = {3, 7, 8, 10, 12} ∨
        polygon = {3, 7, 8, 11, 12} ∨
        polygon = {3, 7, 10, 11, 12} ∨
        polygon = {3, 8, 10, 11, 12} ∨
        polygon = {5, 7, 8, 10, 11} ∨
        polygon = {5, 7, 8, 10, 12} ∨
        polygon = {5, 7, 8, 11, 12} ∨
        polygon = {5, 7, 10, 11, 12} ∨
        polygon = {5, 8, 10, 11, 12} ∨
        polygon = {7, 8, 10, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 5, 7, 8, 10, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 5, 7, 8, 10, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 5, 7, 8, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 5, 7, 8, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 5, 7, 8, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 5, 7, 8, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 5, 7, 8, 10, 11, 12} \ {x, y} := by
    calc
      polygon = {3, 5, 7, 8, 10, 11, 12} \ ({3, 5, 7, 8, 10, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 5, 7, 8, 10, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask7848 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 5, 7, 9, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {3, 5, 7, 9, 11} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {3, 5, 7, 10, 11} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {3, 5, 7, 11, 12} ∨
        polygon = {3, 5, 9, 10, 11} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 5, 9, 11, 12} ∨
        polygon = {3, 5, 10, 11, 12} ∨
        polygon = {3, 7, 9, 10, 11} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {3, 7, 9, 11, 12} ∨
        polygon = {3, 7, 10, 11, 12} ∨
        polygon = {3, 9, 10, 11, 12} ∨
        polygon = {5, 7, 9, 10, 11} ∨
        polygon = {5, 7, 9, 10, 12} ∨
        polygon = {5, 7, 9, 11, 12} ∨
        polygon = {5, 7, 10, 11, 12} ∨
        polygon = {5, 9, 10, 11, 12} ∨
        polygon = {7, 9, 10, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 5, 7, 9, 10, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 5, 7, 9, 10, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 5, 7, 9, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 5, 7, 9, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 5, 7, 9, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 5, 7, 9, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 5, 7, 9, 10, 11, 12} \ {x, y} := by
    calc
      polygon = {3, 5, 7, 9, 10, 11, 12} \ ({3, 5, 7, 9, 10, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 5, 7, 9, 10, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask7976 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 5, 8, 9, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {3, 5, 8, 9, 10} ∨
        polygon = {3, 5, 8, 9, 11} ∨
        polygon = {3, 5, 8, 9, 12} ∨
        polygon = {3, 5, 8, 10, 11} ∨
        polygon = {3, 5, 8, 10, 12} ∨
        polygon = {3, 5, 8, 11, 12} ∨
        polygon = {3, 5, 9, 10, 11} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 5, 9, 11, 12} ∨
        polygon = {3, 5, 10, 11, 12} ∨
        polygon = {3, 8, 9, 10, 11} ∨
        polygon = {3, 8, 9, 10, 12} ∨
        polygon = {3, 8, 9, 11, 12} ∨
        polygon = {3, 8, 10, 11, 12} ∨
        polygon = {3, 9, 10, 11, 12} ∨
        polygon = {5, 8, 9, 10, 11} ∨
        polygon = {5, 8, 9, 10, 12} ∨
        polygon = {5, 8, 9, 11, 12} ∨
        polygon = {5, 8, 10, 11, 12} ∨
        polygon = {5, 9, 10, 11, 12} ∨
        polygon = {8, 9, 10, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 5, 8, 9, 10, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 5, 8, 9, 10, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 5, 8, 9, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 5, 8, 9, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 5, 8, 9, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 5, 8, 9, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 5, 8, 9, 10, 11, 12} \ {x, y} := by
    calc
      polygon = {3, 5, 8, 9, 10, 11, 12} \ ({3, 5, 8, 9, 10, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 5, 8, 9, 10, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4040 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 6, 7, 8, 9, 10, 11} →
      polygon.card = 5 →
        polygon = {3, 6, 7, 8, 9} ∨
        polygon = {3, 6, 7, 8, 10} ∨
        polygon = {3, 6, 7, 8, 11} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {3, 6, 7, 9, 11} ∨
        polygon = {3, 6, 7, 10, 11} ∨
        polygon = {3, 6, 8, 9, 10} ∨
        polygon = {3, 6, 8, 9, 11} ∨
        polygon = {3, 6, 8, 10, 11} ∨
        polygon = {3, 6, 9, 10, 11} ∨
        polygon = {3, 7, 8, 9, 10} ∨
        polygon = {3, 7, 8, 9, 11} ∨
        polygon = {3, 7, 8, 10, 11} ∨
        polygon = {3, 7, 9, 10, 11} ∨
        polygon = {3, 8, 9, 10, 11} ∨
        polygon = {6, 7, 8, 9, 10} ∨
        polygon = {6, 7, 8, 9, 11} ∨
        polygon = {6, 7, 8, 10, 11} ∨
        polygon = {6, 7, 9, 10, 11} ∨
        polygon = {6, 8, 9, 10, 11} ∨
        polygon = {7, 8, 9, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 6, 7, 8, 9, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 6, 7, 8, 9, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 6, 7, 8, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 6, 7, 8, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 6, 7, 8, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 6, 7, 8, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 6, 7, 8, 9, 10, 11} \ {x, y} := by
    calc
      polygon = {3, 6, 7, 8, 9, 10, 11} \ ({3, 6, 7, 8, 9, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 6, 7, 8, 9, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask6088 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 6, 7, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {3, 6, 7, 8, 9} ∨
        polygon = {3, 6, 7, 8, 10} ∨
        polygon = {3, 6, 7, 8, 12} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {3, 6, 8, 9, 10} ∨
        polygon = {3, 6, 8, 9, 12} ∨
        polygon = {3, 6, 8, 10, 12} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {3, 7, 8, 9, 10} ∨
        polygon = {3, 7, 8, 9, 12} ∨
        polygon = {3, 7, 8, 10, 12} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {3, 8, 9, 10, 12} ∨
        polygon = {6, 7, 8, 9, 10} ∨
        polygon = {6, 7, 8, 9, 12} ∨
        polygon = {6, 7, 8, 10, 12} ∨
        polygon = {6, 7, 9, 10, 12} ∨
        polygon = {6, 8, 9, 10, 12} ∨
        polygon = {7, 8, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 6, 7, 8, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 6, 7, 8, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 6, 7, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 6, 7, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 6, 7, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 6, 7, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 6, 7, 8, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {3, 6, 7, 8, 9, 10, 12} \ ({3, 6, 7, 8, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 6, 7, 8, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask7624 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 6, 7, 8, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {3, 6, 7, 8, 10} ∨
        polygon = {3, 6, 7, 8, 11} ∨
        polygon = {3, 6, 7, 8, 12} ∨
        polygon = {3, 6, 7, 10, 11} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {3, 6, 7, 11, 12} ∨
        polygon = {3, 6, 8, 10, 11} ∨
        polygon = {3, 6, 8, 10, 12} ∨
        polygon = {3, 6, 8, 11, 12} ∨
        polygon = {3, 6, 10, 11, 12} ∨
        polygon = {3, 7, 8, 10, 11} ∨
        polygon = {3, 7, 8, 10, 12} ∨
        polygon = {3, 7, 8, 11, 12} ∨
        polygon = {3, 7, 10, 11, 12} ∨
        polygon = {3, 8, 10, 11, 12} ∨
        polygon = {6, 7, 8, 10, 11} ∨
        polygon = {6, 7, 8, 10, 12} ∨
        polygon = {6, 7, 8, 11, 12} ∨
        polygon = {6, 7, 10, 11, 12} ∨
        polygon = {6, 8, 10, 11, 12} ∨
        polygon = {7, 8, 10, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 6, 7, 8, 10, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 6, 7, 8, 10, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 6, 7, 8, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 6, 7, 8, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 6, 7, 8, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 6, 7, 8, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 6, 7, 8, 10, 11, 12} \ {x, y} := by
    calc
      polygon = {3, 6, 7, 8, 10, 11, 12} \ ({3, 6, 7, 8, 10, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 6, 7, 8, 10, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask8008 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {3, 6, 8, 9, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {3, 6, 8, 9, 10} ∨
        polygon = {3, 6, 8, 9, 11} ∨
        polygon = {3, 6, 8, 9, 12} ∨
        polygon = {3, 6, 8, 10, 11} ∨
        polygon = {3, 6, 8, 10, 12} ∨
        polygon = {3, 6, 8, 11, 12} ∨
        polygon = {3, 6, 9, 10, 11} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {3, 6, 9, 11, 12} ∨
        polygon = {3, 6, 10, 11, 12} ∨
        polygon = {3, 8, 9, 10, 11} ∨
        polygon = {3, 8, 9, 10, 12} ∨
        polygon = {3, 8, 9, 11, 12} ∨
        polygon = {3, 8, 10, 11, 12} ∨
        polygon = {3, 9, 10, 11, 12} ∨
        polygon = {6, 8, 9, 10, 11} ∨
        polygon = {6, 8, 9, 10, 12} ∨
        polygon = {6, 8, 9, 11, 12} ∨
        polygon = {6, 8, 10, 11, 12} ∨
        polygon = {6, 9, 10, 11, 12} ∨
        polygon = {8, 9, 10, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({3, 6, 8, 9, 10, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({3, 6, 8, 9, 10, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {3, 6, 8, 9, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {3, 6, 8, 9, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({3, 6, 8, 9, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({3, 6, 8, 9, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {3, 6, 8, 9, 10, 11, 12} \ {x, y} := by
    calc
      polygon = {3, 6, 8, 9, 10, 11, 12} \ ({3, 6, 8, 9, 10, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {3, 6, 8, 9, 10, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask2032 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {4, 5, 6, 7, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 7, 8} ∨
        polygon = {4, 5, 6, 7, 9} ∨
        polygon = {4, 5, 6, 7, 10} ∨
        polygon = {4, 5, 6, 8, 9} ∨
        polygon = {4, 5, 6, 8, 10} ∨
        polygon = {4, 5, 6, 9, 10} ∨
        polygon = {4, 5, 7, 8, 9} ∨
        polygon = {4, 5, 7, 8, 10} ∨
        polygon = {4, 5, 7, 9, 10} ∨
        polygon = {4, 5, 8, 9, 10} ∨
        polygon = {4, 6, 7, 8, 9} ∨
        polygon = {4, 6, 7, 8, 10} ∨
        polygon = {4, 6, 7, 9, 10} ∨
        polygon = {4, 6, 8, 9, 10} ∨
        polygon = {4, 7, 8, 9, 10} ∨
        polygon = {5, 6, 7, 8, 9} ∨
        polygon = {5, 6, 7, 8, 10} ∨
        polygon = {5, 6, 7, 9, 10} ∨
        polygon = {5, 6, 8, 9, 10} ∨
        polygon = {5, 7, 8, 9, 10} ∨
        polygon = {6, 7, 8, 9, 10} := by
  intro polygon hsubset hcard
  have hdiffcard : ({4, 5, 6, 7, 8, 9, 10} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({4, 5, 6, 7, 8, 9, 10} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {4, 5, 6, 7, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {4, 5, 6, 7, 8, 9, 10} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({4, 5, 6, 7, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({4, 5, 6, 7, 8, 9, 10} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {4, 5, 6, 7, 8, 9, 10} \ {x, y} := by
    calc
      polygon = {4, 5, 6, 7, 8, 9, 10} \ ({4, 5, 6, 7, 8, 9, 10} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {4, 5, 6, 7, 8, 9, 10} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3056 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {4, 5, 6, 7, 8, 9, 11} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 7, 8} ∨
        polygon = {4, 5, 6, 7, 9} ∨
        polygon = {4, 5, 6, 7, 11} ∨
        polygon = {4, 5, 6, 8, 9} ∨
        polygon = {4, 5, 6, 8, 11} ∨
        polygon = {4, 5, 6, 9, 11} ∨
        polygon = {4, 5, 7, 8, 9} ∨
        polygon = {4, 5, 7, 8, 11} ∨
        polygon = {4, 5, 7, 9, 11} ∨
        polygon = {4, 5, 8, 9, 11} ∨
        polygon = {4, 6, 7, 8, 9} ∨
        polygon = {4, 6, 7, 8, 11} ∨
        polygon = {4, 6, 7, 9, 11} ∨
        polygon = {4, 6, 8, 9, 11} ∨
        polygon = {4, 7, 8, 9, 11} ∨
        polygon = {5, 6, 7, 8, 9} ∨
        polygon = {5, 6, 7, 8, 11} ∨
        polygon = {5, 6, 7, 9, 11} ∨
        polygon = {5, 6, 8, 9, 11} ∨
        polygon = {5, 7, 8, 9, 11} ∨
        polygon = {6, 7, 8, 9, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({4, 5, 6, 7, 8, 9, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({4, 5, 6, 7, 8, 9, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {4, 5, 6, 7, 8, 9, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {4, 5, 6, 7, 8, 9, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({4, 5, 6, 7, 8, 9, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({4, 5, 6, 7, 8, 9, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {4, 5, 6, 7, 8, 9, 11} \ {x, y} := by
    calc
      polygon = {4, 5, 6, 7, 8, 9, 11} \ ({4, 5, 6, 7, 8, 9, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {4, 5, 6, 7, 8, 9, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5104 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {4, 5, 6, 7, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 7, 8} ∨
        polygon = {4, 5, 6, 7, 9} ∨
        polygon = {4, 5, 6, 7, 12} ∨
        polygon = {4, 5, 6, 8, 9} ∨
        polygon = {4, 5, 6, 8, 12} ∨
        polygon = {4, 5, 6, 9, 12} ∨
        polygon = {4, 5, 7, 8, 9} ∨
        polygon = {4, 5, 7, 8, 12} ∨
        polygon = {4, 5, 7, 9, 12} ∨
        polygon = {4, 5, 8, 9, 12} ∨
        polygon = {4, 6, 7, 8, 9} ∨
        polygon = {4, 6, 7, 8, 12} ∨
        polygon = {4, 6, 7, 9, 12} ∨
        polygon = {4, 6, 8, 9, 12} ∨
        polygon = {4, 7, 8, 9, 12} ∨
        polygon = {5, 6, 7, 8, 9} ∨
        polygon = {5, 6, 7, 8, 12} ∨
        polygon = {5, 6, 7, 9, 12} ∨
        polygon = {5, 6, 8, 9, 12} ∨
        polygon = {5, 7, 8, 9, 12} ∨
        polygon = {6, 7, 8, 9, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({4, 5, 6, 7, 8, 9, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({4, 5, 6, 7, 8, 9, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {4, 5, 6, 7, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {4, 5, 6, 7, 8, 9, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({4, 5, 6, 7, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({4, 5, 6, 7, 8, 9, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {4, 5, 6, 7, 8, 9, 12} \ {x, y} := by
    calc
      polygon = {4, 5, 6, 7, 8, 9, 12} \ ({4, 5, 6, 7, 8, 9, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {4, 5, 6, 7, 8, 9, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3568 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {4, 5, 6, 7, 8, 10, 11} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 7, 8} ∨
        polygon = {4, 5, 6, 7, 10} ∨
        polygon = {4, 5, 6, 7, 11} ∨
        polygon = {4, 5, 6, 8, 10} ∨
        polygon = {4, 5, 6, 8, 11} ∨
        polygon = {4, 5, 6, 10, 11} ∨
        polygon = {4, 5, 7, 8, 10} ∨
        polygon = {4, 5, 7, 8, 11} ∨
        polygon = {4, 5, 7, 10, 11} ∨
        polygon = {4, 5, 8, 10, 11} ∨
        polygon = {4, 6, 7, 8, 10} ∨
        polygon = {4, 6, 7, 8, 11} ∨
        polygon = {4, 6, 7, 10, 11} ∨
        polygon = {4, 6, 8, 10, 11} ∨
        polygon = {4, 7, 8, 10, 11} ∨
        polygon = {5, 6, 7, 8, 10} ∨
        polygon = {5, 6, 7, 8, 11} ∨
        polygon = {5, 6, 7, 10, 11} ∨
        polygon = {5, 6, 8, 10, 11} ∨
        polygon = {5, 7, 8, 10, 11} ∨
        polygon = {6, 7, 8, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({4, 5, 6, 7, 8, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({4, 5, 6, 7, 8, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {4, 5, 6, 7, 8, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {4, 5, 6, 7, 8, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({4, 5, 6, 7, 8, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({4, 5, 6, 7, 8, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {4, 5, 6, 7, 8, 10, 11} \ {x, y} := by
    calc
      polygon = {4, 5, 6, 7, 8, 10, 11} \ ({4, 5, 6, 7, 8, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {4, 5, 6, 7, 8, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5616 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {4, 5, 6, 7, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 7, 8} ∨
        polygon = {4, 5, 6, 7, 10} ∨
        polygon = {4, 5, 6, 7, 12} ∨
        polygon = {4, 5, 6, 8, 10} ∨
        polygon = {4, 5, 6, 8, 12} ∨
        polygon = {4, 5, 6, 10, 12} ∨
        polygon = {4, 5, 7, 8, 10} ∨
        polygon = {4, 5, 7, 8, 12} ∨
        polygon = {4, 5, 7, 10, 12} ∨
        polygon = {4, 5, 8, 10, 12} ∨
        polygon = {4, 6, 7, 8, 10} ∨
        polygon = {4, 6, 7, 8, 12} ∨
        polygon = {4, 6, 7, 10, 12} ∨
        polygon = {4, 6, 8, 10, 12} ∨
        polygon = {4, 7, 8, 10, 12} ∨
        polygon = {5, 6, 7, 8, 10} ∨
        polygon = {5, 6, 7, 8, 12} ∨
        polygon = {5, 6, 7, 10, 12} ∨
        polygon = {5, 6, 8, 10, 12} ∨
        polygon = {5, 7, 8, 10, 12} ∨
        polygon = {6, 7, 8, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({4, 5, 6, 7, 8, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({4, 5, 6, 7, 8, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {4, 5, 6, 7, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {4, 5, 6, 7, 8, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({4, 5, 6, 7, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({4, 5, 6, 7, 8, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {4, 5, 6, 7, 8, 10, 12} \ {x, y} := by
    calc
      polygon = {4, 5, 6, 7, 8, 10, 12} \ ({4, 5, 6, 7, 8, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {4, 5, 6, 7, 8, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask6640 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {4, 5, 6, 7, 8, 11, 12} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 7, 8} ∨
        polygon = {4, 5, 6, 7, 11} ∨
        polygon = {4, 5, 6, 7, 12} ∨
        polygon = {4, 5, 6, 8, 11} ∨
        polygon = {4, 5, 6, 8, 12} ∨
        polygon = {4, 5, 6, 11, 12} ∨
        polygon = {4, 5, 7, 8, 11} ∨
        polygon = {4, 5, 7, 8, 12} ∨
        polygon = {4, 5, 7, 11, 12} ∨
        polygon = {4, 5, 8, 11, 12} ∨
        polygon = {4, 6, 7, 8, 11} ∨
        polygon = {4, 6, 7, 8, 12} ∨
        polygon = {4, 6, 7, 11, 12} ∨
        polygon = {4, 6, 8, 11, 12} ∨
        polygon = {4, 7, 8, 11, 12} ∨
        polygon = {5, 6, 7, 8, 11} ∨
        polygon = {5, 6, 7, 8, 12} ∨
        polygon = {5, 6, 7, 11, 12} ∨
        polygon = {5, 6, 8, 11, 12} ∨
        polygon = {5, 7, 8, 11, 12} ∨
        polygon = {6, 7, 8, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({4, 5, 6, 7, 8, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({4, 5, 6, 7, 8, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {4, 5, 6, 7, 8, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {4, 5, 6, 7, 8, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({4, 5, 6, 7, 8, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({4, 5, 6, 7, 8, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {4, 5, 6, 7, 8, 11, 12} \ {x, y} := by
    calc
      polygon = {4, 5, 6, 7, 8, 11, 12} \ ({4, 5, 6, 7, 8, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {4, 5, 6, 7, 8, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask3824 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {4, 5, 6, 7, 9, 10, 11} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 7, 9} ∨
        polygon = {4, 5, 6, 7, 10} ∨
        polygon = {4, 5, 6, 7, 11} ∨
        polygon = {4, 5, 6, 9, 10} ∨
        polygon = {4, 5, 6, 9, 11} ∨
        polygon = {4, 5, 6, 10, 11} ∨
        polygon = {4, 5, 7, 9, 10} ∨
        polygon = {4, 5, 7, 9, 11} ∨
        polygon = {4, 5, 7, 10, 11} ∨
        polygon = {4, 5, 9, 10, 11} ∨
        polygon = {4, 6, 7, 9, 10} ∨
        polygon = {4, 6, 7, 9, 11} ∨
        polygon = {4, 6, 7, 10, 11} ∨
        polygon = {4, 6, 9, 10, 11} ∨
        polygon = {4, 7, 9, 10, 11} ∨
        polygon = {5, 6, 7, 9, 10} ∨
        polygon = {5, 6, 7, 9, 11} ∨
        polygon = {5, 6, 7, 10, 11} ∨
        polygon = {5, 6, 9, 10, 11} ∨
        polygon = {5, 7, 9, 10, 11} ∨
        polygon = {6, 7, 9, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({4, 5, 6, 7, 9, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({4, 5, 6, 7, 9, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {4, 5, 6, 7, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {4, 5, 6, 7, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({4, 5, 6, 7, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({4, 5, 6, 7, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {4, 5, 6, 7, 9, 10, 11} \ {x, y} := by
    calc
      polygon = {4, 5, 6, 7, 9, 10, 11} \ ({4, 5, 6, 7, 9, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {4, 5, 6, 7, 9, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask5872 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {4, 5, 6, 7, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 7, 9} ∨
        polygon = {4, 5, 6, 7, 10} ∨
        polygon = {4, 5, 6, 7, 12} ∨
        polygon = {4, 5, 6, 9, 10} ∨
        polygon = {4, 5, 6, 9, 12} ∨
        polygon = {4, 5, 6, 10, 12} ∨
        polygon = {4, 5, 7, 9, 10} ∨
        polygon = {4, 5, 7, 9, 12} ∨
        polygon = {4, 5, 7, 10, 12} ∨
        polygon = {4, 5, 9, 10, 12} ∨
        polygon = {4, 6, 7, 9, 10} ∨
        polygon = {4, 6, 7, 9, 12} ∨
        polygon = {4, 6, 7, 10, 12} ∨
        polygon = {4, 6, 9, 10, 12} ∨
        polygon = {4, 7, 9, 10, 12} ∨
        polygon = {5, 6, 7, 9, 10} ∨
        polygon = {5, 6, 7, 9, 12} ∨
        polygon = {5, 6, 7, 10, 12} ∨
        polygon = {5, 6, 9, 10, 12} ∨
        polygon = {5, 7, 9, 10, 12} ∨
        polygon = {6, 7, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({4, 5, 6, 7, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({4, 5, 6, 7, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {4, 5, 6, 7, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {4, 5, 6, 7, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({4, 5, 6, 7, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({4, 5, 6, 7, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {4, 5, 6, 7, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {4, 5, 6, 7, 9, 10, 12} \ ({4, 5, 6, 7, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {4, 5, 6, 7, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask6000 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {4, 5, 6, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 8, 9} ∨
        polygon = {4, 5, 6, 8, 10} ∨
        polygon = {4, 5, 6, 8, 12} ∨
        polygon = {4, 5, 6, 9, 10} ∨
        polygon = {4, 5, 6, 9, 12} ∨
        polygon = {4, 5, 6, 10, 12} ∨
        polygon = {4, 5, 8, 9, 10} ∨
        polygon = {4, 5, 8, 9, 12} ∨
        polygon = {4, 5, 8, 10, 12} ∨
        polygon = {4, 5, 9, 10, 12} ∨
        polygon = {4, 6, 8, 9, 10} ∨
        polygon = {4, 6, 8, 9, 12} ∨
        polygon = {4, 6, 8, 10, 12} ∨
        polygon = {4, 6, 9, 10, 12} ∨
        polygon = {4, 8, 9, 10, 12} ∨
        polygon = {5, 6, 8, 9, 10} ∨
        polygon = {5, 6, 8, 9, 12} ∨
        polygon = {5, 6, 8, 10, 12} ∨
        polygon = {5, 6, 9, 10, 12} ∨
        polygon = {5, 8, 9, 10, 12} ∨
        polygon = {6, 8, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({4, 5, 6, 8, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({4, 5, 6, 8, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {4, 5, 6, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {4, 5, 6, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({4, 5, 6, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({4, 5, 6, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {4, 5, 6, 8, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {4, 5, 6, 8, 9, 10, 12} \ ({4, 5, 6, 8, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {4, 5, 6, 8, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask7536 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {4, 5, 6, 8, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 8, 10} ∨
        polygon = {4, 5, 6, 8, 11} ∨
        polygon = {4, 5, 6, 8, 12} ∨
        polygon = {4, 5, 6, 10, 11} ∨
        polygon = {4, 5, 6, 10, 12} ∨
        polygon = {4, 5, 6, 11, 12} ∨
        polygon = {4, 5, 8, 10, 11} ∨
        polygon = {4, 5, 8, 10, 12} ∨
        polygon = {4, 5, 8, 11, 12} ∨
        polygon = {4, 5, 10, 11, 12} ∨
        polygon = {4, 6, 8, 10, 11} ∨
        polygon = {4, 6, 8, 10, 12} ∨
        polygon = {4, 6, 8, 11, 12} ∨
        polygon = {4, 6, 10, 11, 12} ∨
        polygon = {4, 8, 10, 11, 12} ∨
        polygon = {5, 6, 8, 10, 11} ∨
        polygon = {5, 6, 8, 10, 12} ∨
        polygon = {5, 6, 8, 11, 12} ∨
        polygon = {5, 6, 10, 11, 12} ∨
        polygon = {5, 8, 10, 11, 12} ∨
        polygon = {6, 8, 10, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({4, 5, 6, 8, 10, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({4, 5, 6, 8, 10, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {4, 5, 6, 8, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {4, 5, 6, 8, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({4, 5, 6, 8, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({4, 5, 6, 8, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {4, 5, 6, 8, 10, 11, 12} \ {x, y} := by
    calc
      polygon = {4, 5, 6, 8, 10, 11, 12} \ ({4, 5, 6, 8, 10, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {4, 5, 6, 8, 10, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4016 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {4, 5, 7, 8, 9, 10, 11} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 8, 9} ∨
        polygon = {4, 5, 7, 8, 10} ∨
        polygon = {4, 5, 7, 8, 11} ∨
        polygon = {4, 5, 7, 9, 10} ∨
        polygon = {4, 5, 7, 9, 11} ∨
        polygon = {4, 5, 7, 10, 11} ∨
        polygon = {4, 5, 8, 9, 10} ∨
        polygon = {4, 5, 8, 9, 11} ∨
        polygon = {4, 5, 8, 10, 11} ∨
        polygon = {4, 5, 9, 10, 11} ∨
        polygon = {4, 7, 8, 9, 10} ∨
        polygon = {4, 7, 8, 9, 11} ∨
        polygon = {4, 7, 8, 10, 11} ∨
        polygon = {4, 7, 9, 10, 11} ∨
        polygon = {4, 8, 9, 10, 11} ∨
        polygon = {5, 7, 8, 9, 10} ∨
        polygon = {5, 7, 8, 9, 11} ∨
        polygon = {5, 7, 8, 10, 11} ∨
        polygon = {5, 7, 9, 10, 11} ∨
        polygon = {5, 8, 9, 10, 11} ∨
        polygon = {7, 8, 9, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({4, 5, 7, 8, 9, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({4, 5, 7, 8, 9, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {4, 5, 7, 8, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {4, 5, 7, 8, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({4, 5, 7, 8, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({4, 5, 7, 8, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {4, 5, 7, 8, 9, 10, 11} \ {x, y} := by
    calc
      polygon = {4, 5, 7, 8, 9, 10, 11} \ ({4, 5, 7, 8, 9, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {4, 5, 7, 8, 9, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask6064 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {4, 5, 7, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 8, 9} ∨
        polygon = {4, 5, 7, 8, 10} ∨
        polygon = {4, 5, 7, 8, 12} ∨
        polygon = {4, 5, 7, 9, 10} ∨
        polygon = {4, 5, 7, 9, 12} ∨
        polygon = {4, 5, 7, 10, 12} ∨
        polygon = {4, 5, 8, 9, 10} ∨
        polygon = {4, 5, 8, 9, 12} ∨
        polygon = {4, 5, 8, 10, 12} ∨
        polygon = {4, 5, 9, 10, 12} ∨
        polygon = {4, 7, 8, 9, 10} ∨
        polygon = {4, 7, 8, 9, 12} ∨
        polygon = {4, 7, 8, 10, 12} ∨
        polygon = {4, 7, 9, 10, 12} ∨
        polygon = {4, 8, 9, 10, 12} ∨
        polygon = {5, 7, 8, 9, 10} ∨
        polygon = {5, 7, 8, 9, 12} ∨
        polygon = {5, 7, 8, 10, 12} ∨
        polygon = {5, 7, 9, 10, 12} ∨
        polygon = {5, 8, 9, 10, 12} ∨
        polygon = {7, 8, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({4, 5, 7, 8, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({4, 5, 7, 8, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {4, 5, 7, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {4, 5, 7, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({4, 5, 7, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({4, 5, 7, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {4, 5, 7, 8, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {4, 5, 7, 8, 9, 10, 12} \ ({4, 5, 7, 8, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {4, 5, 7, 8, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4048 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {4, 6, 7, 8, 9, 10, 11} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 8, 9} ∨
        polygon = {4, 6, 7, 8, 10} ∨
        polygon = {4, 6, 7, 8, 11} ∨
        polygon = {4, 6, 7, 9, 10} ∨
        polygon = {4, 6, 7, 9, 11} ∨
        polygon = {4, 6, 7, 10, 11} ∨
        polygon = {4, 6, 8, 9, 10} ∨
        polygon = {4, 6, 8, 9, 11} ∨
        polygon = {4, 6, 8, 10, 11} ∨
        polygon = {4, 6, 9, 10, 11} ∨
        polygon = {4, 7, 8, 9, 10} ∨
        polygon = {4, 7, 8, 9, 11} ∨
        polygon = {4, 7, 8, 10, 11} ∨
        polygon = {4, 7, 9, 10, 11} ∨
        polygon = {4, 8, 9, 10, 11} ∨
        polygon = {6, 7, 8, 9, 10} ∨
        polygon = {6, 7, 8, 9, 11} ∨
        polygon = {6, 7, 8, 10, 11} ∨
        polygon = {6, 7, 9, 10, 11} ∨
        polygon = {6, 8, 9, 10, 11} ∨
        polygon = {7, 8, 9, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({4, 6, 7, 8, 9, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({4, 6, 7, 8, 9, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {4, 6, 7, 8, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {4, 6, 7, 8, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({4, 6, 7, 8, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({4, 6, 7, 8, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {4, 6, 7, 8, 9, 10, 11} \ {x, y} := by
    calc
      polygon = {4, 6, 7, 8, 9, 10, 11} \ ({4, 6, 7, 8, 9, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {4, 6, 7, 8, 9, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask6096 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {4, 6, 7, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 8, 9} ∨
        polygon = {4, 6, 7, 8, 10} ∨
        polygon = {4, 6, 7, 8, 12} ∨
        polygon = {4, 6, 7, 9, 10} ∨
        polygon = {4, 6, 7, 9, 12} ∨
        polygon = {4, 6, 7, 10, 12} ∨
        polygon = {4, 6, 8, 9, 10} ∨
        polygon = {4, 6, 8, 9, 12} ∨
        polygon = {4, 6, 8, 10, 12} ∨
        polygon = {4, 6, 9, 10, 12} ∨
        polygon = {4, 7, 8, 9, 10} ∨
        polygon = {4, 7, 8, 9, 12} ∨
        polygon = {4, 7, 8, 10, 12} ∨
        polygon = {4, 7, 9, 10, 12} ∨
        polygon = {4, 8, 9, 10, 12} ∨
        polygon = {6, 7, 8, 9, 10} ∨
        polygon = {6, 7, 8, 9, 12} ∨
        polygon = {6, 7, 8, 10, 12} ∨
        polygon = {6, 7, 9, 10, 12} ∨
        polygon = {6, 8, 9, 10, 12} ∨
        polygon = {7, 8, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({4, 6, 7, 8, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({4, 6, 7, 8, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {4, 6, 7, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {4, 6, 7, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({4, 6, 7, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({4, 6, 7, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {4, 6, 7, 8, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {4, 6, 7, 8, 9, 10, 12} \ ({4, 6, 7, 8, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {4, 6, 7, 8, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask7888 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {4, 6, 7, 9, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 9, 10} ∨
        polygon = {4, 6, 7, 9, 11} ∨
        polygon = {4, 6, 7, 9, 12} ∨
        polygon = {4, 6, 7, 10, 11} ∨
        polygon = {4, 6, 7, 10, 12} ∨
        polygon = {4, 6, 7, 11, 12} ∨
        polygon = {4, 6, 9, 10, 11} ∨
        polygon = {4, 6, 9, 10, 12} ∨
        polygon = {4, 6, 9, 11, 12} ∨
        polygon = {4, 6, 10, 11, 12} ∨
        polygon = {4, 7, 9, 10, 11} ∨
        polygon = {4, 7, 9, 10, 12} ∨
        polygon = {4, 7, 9, 11, 12} ∨
        polygon = {4, 7, 10, 11, 12} ∨
        polygon = {4, 9, 10, 11, 12} ∨
        polygon = {6, 7, 9, 10, 11} ∨
        polygon = {6, 7, 9, 10, 12} ∨
        polygon = {6, 7, 9, 11, 12} ∨
        polygon = {6, 7, 10, 11, 12} ∨
        polygon = {6, 9, 10, 11, 12} ∨
        polygon = {7, 9, 10, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({4, 6, 7, 9, 10, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({4, 6, 7, 9, 10, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {4, 6, 7, 9, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {4, 6, 7, 9, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({4, 6, 7, 9, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({4, 6, 7, 9, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {4, 6, 7, 9, 10, 11, 12} \ {x, y} := by
    calc
      polygon = {4, 6, 7, 9, 10, 11, 12} \ ({4, 6, 7, 9, 10, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {4, 6, 7, 9, 10, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask8080 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {4, 7, 8, 9, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {4, 7, 8, 9, 10} ∨
        polygon = {4, 7, 8, 9, 11} ∨
        polygon = {4, 7, 8, 9, 12} ∨
        polygon = {4, 7, 8, 10, 11} ∨
        polygon = {4, 7, 8, 10, 12} ∨
        polygon = {4, 7, 8, 11, 12} ∨
        polygon = {4, 7, 9, 10, 11} ∨
        polygon = {4, 7, 9, 10, 12} ∨
        polygon = {4, 7, 9, 11, 12} ∨
        polygon = {4, 7, 10, 11, 12} ∨
        polygon = {4, 8, 9, 10, 11} ∨
        polygon = {4, 8, 9, 10, 12} ∨
        polygon = {4, 8, 9, 11, 12} ∨
        polygon = {4, 8, 10, 11, 12} ∨
        polygon = {4, 9, 10, 11, 12} ∨
        polygon = {7, 8, 9, 10, 11} ∨
        polygon = {7, 8, 9, 10, 12} ∨
        polygon = {7, 8, 9, 11, 12} ∨
        polygon = {7, 8, 10, 11, 12} ∨
        polygon = {7, 9, 10, 11, 12} ∨
        polygon = {8, 9, 10, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({4, 7, 8, 9, 10, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({4, 7, 8, 9, 10, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {4, 7, 8, 9, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {4, 7, 8, 9, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({4, 7, 8, 9, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({4, 7, 8, 9, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {4, 7, 8, 9, 10, 11, 12} \ {x, y} := by
    calc
      polygon = {4, 7, 8, 9, 10, 11, 12} \ ({4, 7, 8, 9, 10, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {4, 7, 8, 9, 10, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask4064 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {5, 6, 7, 8, 9, 10, 11} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 8, 9} ∨
        polygon = {5, 6, 7, 8, 10} ∨
        polygon = {5, 6, 7, 8, 11} ∨
        polygon = {5, 6, 7, 9, 10} ∨
        polygon = {5, 6, 7, 9, 11} ∨
        polygon = {5, 6, 7, 10, 11} ∨
        polygon = {5, 6, 8, 9, 10} ∨
        polygon = {5, 6, 8, 9, 11} ∨
        polygon = {5, 6, 8, 10, 11} ∨
        polygon = {5, 6, 9, 10, 11} ∨
        polygon = {5, 7, 8, 9, 10} ∨
        polygon = {5, 7, 8, 9, 11} ∨
        polygon = {5, 7, 8, 10, 11} ∨
        polygon = {5, 7, 9, 10, 11} ∨
        polygon = {5, 8, 9, 10, 11} ∨
        polygon = {6, 7, 8, 9, 10} ∨
        polygon = {6, 7, 8, 9, 11} ∨
        polygon = {6, 7, 8, 10, 11} ∨
        polygon = {6, 7, 9, 10, 11} ∨
        polygon = {6, 8, 9, 10, 11} ∨
        polygon = {7, 8, 9, 10, 11} := by
  intro polygon hsubset hcard
  have hdiffcard : ({5, 6, 7, 8, 9, 10, 11} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({5, 6, 7, 8, 9, 10, 11} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {5, 6, 7, 8, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {5, 6, 7, 8, 9, 10, 11} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({5, 6, 7, 8, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({5, 6, 7, 8, 9, 10, 11} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {5, 6, 7, 8, 9, 10, 11} \ {x, y} := by
    calc
      polygon = {5, 6, 7, 8, 9, 10, 11} \ ({5, 6, 7, 8, 9, 10, 11} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {5, 6, 7, 8, 9, 10, 11} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask6112 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {5, 6, 7, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 8, 9} ∨
        polygon = {5, 6, 7, 8, 10} ∨
        polygon = {5, 6, 7, 8, 12} ∨
        polygon = {5, 6, 7, 9, 10} ∨
        polygon = {5, 6, 7, 9, 12} ∨
        polygon = {5, 6, 7, 10, 12} ∨
        polygon = {5, 6, 8, 9, 10} ∨
        polygon = {5, 6, 8, 9, 12} ∨
        polygon = {5, 6, 8, 10, 12} ∨
        polygon = {5, 6, 9, 10, 12} ∨
        polygon = {5, 7, 8, 9, 10} ∨
        polygon = {5, 7, 8, 9, 12} ∨
        polygon = {5, 7, 8, 10, 12} ∨
        polygon = {5, 7, 9, 10, 12} ∨
        polygon = {5, 8, 9, 10, 12} ∨
        polygon = {6, 7, 8, 9, 10} ∨
        polygon = {6, 7, 8, 9, 12} ∨
        polygon = {6, 7, 8, 10, 12} ∨
        polygon = {6, 7, 9, 10, 12} ∨
        polygon = {6, 8, 9, 10, 12} ∨
        polygon = {7, 8, 9, 10, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({5, 6, 7, 8, 9, 10, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({5, 6, 7, 8, 9, 10, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {5, 6, 7, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {5, 6, 7, 8, 9, 10, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({5, 6, 7, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({5, 6, 7, 8, 9, 10, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {5, 6, 7, 8, 9, 10, 12} \ {x, y} := by
    calc
      polygon = {5, 6, 7, 8, 9, 10, 12} \ ({5, 6, 7, 8, 9, 10, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {5, 6, 7, 8, 9, 10, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

theorem predecessorHalfFin13_fiveSubset_mask8032 :
    ∀ polygon : Finset (Fin 13), polygon ⊆ {5, 6, 8, 9, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {5, 6, 8, 9, 10} ∨
        polygon = {5, 6, 8, 9, 11} ∨
        polygon = {5, 6, 8, 9, 12} ∨
        polygon = {5, 6, 8, 10, 11} ∨
        polygon = {5, 6, 8, 10, 12} ∨
        polygon = {5, 6, 8, 11, 12} ∨
        polygon = {5, 6, 9, 10, 11} ∨
        polygon = {5, 6, 9, 10, 12} ∨
        polygon = {5, 6, 9, 11, 12} ∨
        polygon = {5, 6, 10, 11, 12} ∨
        polygon = {5, 8, 9, 10, 11} ∨
        polygon = {5, 8, 9, 10, 12} ∨
        polygon = {5, 8, 9, 11, 12} ∨
        polygon = {5, 8, 10, 11, 12} ∨
        polygon = {5, 9, 10, 11, 12} ∨
        polygon = {6, 8, 9, 10, 11} ∨
        polygon = {6, 8, 9, 10, 12} ∨
        polygon = {6, 8, 9, 11, 12} ∨
        polygon = {6, 8, 10, 11, 12} ∨
        polygon = {6, 9, 10, 11, 12} ∨
        polygon = {8, 9, 10, 11, 12} := by
  intro polygon hsubset hcard
  have hdiffcard : ({5, 6, 8, 9, 10, 11, 12} \ polygon).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsubset, hcard]
    have hsevenCard : ({5, 6, 8, 9, 10, 11, 12} : Finset (Fin 13)).card = 7 := by decide
    omega
  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard
  have hxDiff : x ∈ {5, 6, 8, 9, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hyDiff : y ∈ {5, 6, 8, 9, 10, 11, 12} \ polygon := by
    rw [hdiff]
    simp
  have hx : x ∈ ({5, 6, 8, 9, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hxDiff).1
  have hy : y ∈ ({5, 6, 8, 9, 10, 11, 12} : Finset (Fin 13)) :=
    (Finset.mem_sdiff.mp hyDiff).1
  have heq : polygon = {5, 6, 8, 9, 10, 11, 12} \ {x, y} := by
    calc
      polygon = {5, 6, 8, 9, 10, 11, 12} \ ({5, 6, 8, 9, 10, 11, 12} \ polygon) :=
        (Finset.sdiff_sdiff_eq_self hsubset).symm
      _ = {5, 6, 8, 9, 10, 11, 12} \ {x, y} := by rw [hdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> decide

end ErdosSzekeres

end
