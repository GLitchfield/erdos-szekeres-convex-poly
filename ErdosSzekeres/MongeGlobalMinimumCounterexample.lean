module

public import ErdosSzekeres.MongeRealizableCounterexample

@[expose] public section

/-!
# The global anchored minimum of the realizable Monge witness

This file checks all Boolean labelings with the frozen extreme anchors. The crossing-mismatch
energy is at least two, and its unique energy-two labeling is the frozen base labeling.
-/

namespace ErdosSzekeres
namespace CrossingMismatch

noncomputable section

/-- The two anchors determine the endpoint entries of an arbitrary labeling. -/
private theorem mongeN8_anchoredLabel_eq
    (label : Fin 8 → Bool)
    (h0 : label 0 = false)
    (h7 : label 7 = true) :
    label = ![false, label 1, label 2, label 3, label 4, label 5, label 6, true] := by
  funext i
  fin_cases i <;> simp_all

set_option maxHeartbeats 4000000 in
/-- The complete six-bit calculation underlying the arbitrary-label theorems. -/
private theorem mongeN8_anchoredEnergy_finite
    (b1 b2 b3 b4 b5 b6 : Bool) :
    2 ≤ mismatchEnergy mongeN8Coloring ![false, b1, b2, b3, b4, b5, b6, true] ∧
      (mismatchEnergy mongeN8Coloring ![false, b1, b2, b3, b4, b5, b6, true] = 2 ↔
        b1 = false ∧ b2 = false ∧ b3 = false ∧ b4 = false ∧ b5 = false ∧ b6 = false) := by
  fin_cases b1 <;> fin_cases b2 <;> fin_cases b3 <;> fin_cases b4 <;>
    fin_cases b5 <;> fin_cases b6
  all_goals rw [mongeN8_mismatchEnergy_eq_sum, mongeN8Coloring_eq_table]
  all_goals decide

/-- Every labeling with the frozen extreme anchors has mismatch energy at least two. -/
theorem mongeN8_anchoredEnergy_ge_two
    (label : Fin 8 → Bool)
    (h0 : label 0 = false)
    (h7 : label 7 = true) :
    2 ≤ mismatchEnergy mongeN8Coloring label := by
  rw [mongeN8_anchoredLabel_eq label h0 h7]
  exact (mongeN8_anchoredEnergy_finite
    (label 1) (label 2) (label 3) (label 4) (label 5) (label 6)).1

/-- Among anchored labelings, energy two characterizes the frozen base labeling exactly. -/
theorem mongeN8_anchoredEnergy_eq_two_iff
    (label : Fin 8 → Bool)
    (h0 : label 0 = false)
    (h7 : label 7 = true) :
    mismatchEnergy mongeN8Coloring label = 2 ↔ label = mongeN8BaseLabel := by
  constructor
  · intro henergy
    have hlabel := mongeN8_anchoredLabel_eq label h0 h7
    rw [hlabel] at henergy
    have hfree := (mongeN8_anchoredEnergy_finite
      (label 1) (label 2) (label 3) (label 4) (label 5) (label 6)).2.mp henergy
    rcases hfree with ⟨h1, h2, h3, h4, h5, h6⟩
    calc
      label = ![false, label 1, label 2, label 3, label 4, label 5, label 6, true] := hlabel
      _ = mongeN8BaseLabel := by
        rw [h1, h2, h3, h4, h5, h6]
        rfl
  · intro hlabel
    rw [hlabel]
    exact mongeN8_baseEnergy

/-- No labeling with the frozen extreme anchors has zero mismatch energy. -/
theorem mongeN8_noAnchoredZeroEnergy
    (label : Fin 8 → Bool)
    (h0 : label 0 = false)
    (h7 : label 7 = true) :
    mismatchEnergy mongeN8Coloring label ≠ 0 := by
  have hge := mongeN8_anchoredEnergy_ge_two label h0 h7
  omega

/--
The realizable strong-five-free witness is a strict local minimum and the unique global minimum
among all labelings with the frozen extreme anchors; its positive minimum rules out energy zero.
-/
theorem mongeN8_realizable_globalMinimum_counterexample :
    (mongeN8Configuration.point = ordinatePoint mongeN8Heights ∧
      mongeN8Configuration.tripleColoring = mongeN8Coloring ∧
      (∀ ⦃i j k : Fin 8⦄, i ≠ j → i ≠ k → j ≠ k →
        orientation (mongeN8Configuration.point i) (mongeN8Configuration.point j)
          (mongeN8Configuration.point k) ≠ 0) ∧
      (∀ f : Fin 5 ↪o Fin 8, ¬IsStrongPolygonOn mongeN8Coloring f) ∧
      mismatchEnergy mongeN8Coloring mongeN8BaseLabel = 2 ∧
      mismatchEnergy mongeN8Coloring mongeN8Flip1 = 15 ∧
      mismatchEnergy mongeN8Coloring mongeN8Flip2 = 12 ∧
      mismatchEnergy mongeN8Coloring mongeN8Flip3 = 3 ∧
      mismatchEnergy mongeN8Coloring mongeN8Flip4 = 11 ∧
      mismatchEnergy mongeN8Coloring mongeN8Flip5 = 19 ∧
      mismatchEnergy mongeN8Coloring mongeN8Flip6 = 21) ∧
    (∀ label : Fin 8 → Bool, label 0 = false → label 7 = true →
      2 ≤ mismatchEnergy mongeN8Coloring label) ∧
    (∀ label : Fin 8 → Bool, label 0 = false → label 7 = true →
      (mismatchEnergy mongeN8Coloring label = 2 ↔ label = mongeN8BaseLabel)) ∧
    (∀ label : Fin 8 → Bool, label 0 = false → label 7 = true →
      mismatchEnergy mongeN8Coloring label ≠ 0) := by
  exact ⟨mongeN8_realizable_strictLocalMinimum_counterexample,
    mongeN8_anchoredEnergy_ge_two, mongeN8_anchoredEnergy_eq_two_iff,
    mongeN8_noAnchoredZeroEnergy⟩

end

end CrossingMismatch
end ErdosSzekeres

end
