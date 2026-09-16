import ESBlueprint.B.CtxTwoActualMarkerCompanionMaximumBound
import ESBlueprint.B.CtxBoundLeOppositeWidthOfSiblingMaximumGeKMinusThree

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- At k six, any two-actual-marker internal-complement cut with complement maximum three has independent-fuel and full sums at most twelve, without a positional, convexity, or clear-history assumption. The complement costs at most four by sibling-maximum normalization and the retained double complement costs at most eight by the sharp companion theorem.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_bound_le_opposite_width_of_sibling_maximum_ge_k_minus_three, ErdosSzekeres.ctx_two_actual_marker_companion_maximum_bound, ErdosSzekeres.ctx_part_positive_letters
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_marker_internal_complement_cut_six_bound_of_maximum_three (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (keep : List ℕ) (q₀ l m n : ℕ) (hq₀ : q₀ ∈ keep) (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions) (hl : l ∈ σ.childPositions) (hlnot : l ∉ keep) (hk : σ.k = 6) (hcoupling : m + n = σ.k - 1) (hmThree : m = 3) : let rest := σ.childPositions.filter (· ∉ keep); (∀ f g, Ctx.Context.boundFuel f (σ.part rest s m) + Ctx.Context.boundFuel g (σ.part keep t n) ≤ 12) ∧ (σ.part rest s m).bound + (σ.part keep t n).bound ≤ 12 := by
  classical
  let rest := σ.childPositions.filter (· ∉ keep)
  let α := σ.part rest s m
  let β := σ.part keep t n
  change (∀ f g, boundFuel f α + boundFuel g β ≤ 12) ∧ α.bound + β.bound ≤ 12
  have hRest (p : ℕ) : p ∈ rest ↔ p ∈ σ.childPositions ∧ p ∉ keep := by
    simp only [rest, List.mem_filter, decide_eq_true_eq]
  have hChildα (p : ℕ) : p ∈ α.childPositions ↔ p ∈ rest := by
    simp only [α, part_childPositions, rest, List.mem_filter, decide_eq_true_eq]
    tauto
  have hExtα (p : ℕ) : p ∈ α.extPositions 1 ↔
      p ∈ σ.childPositions ∧ p ∈ keep := by
    rw [part_extPositions_one hpositive]
    simp only [rest, List.mem_filter, decide_eq_true_eq]
    tauto
  have hQα : q₀ ∈ α.extPositions 1 :=
    (hExtα q₀).mpr ⟨hkeep q₀ hq₀, hq₀⟩
  have hSideα : α.sideAt 1 = s :=
    part_sideAt_one_of_mem hpositive rest s m hQα
  have hPosα := ctx_part_positive_letters σ rest s m
  have hOneα : 1 ∈ α.levels := by
    simp only [α, part_levels, List.mem_cons, true_or]
  have hMaximumα : α.k - 3 ≤ α.maximumAt 1 := by
    rw [part_maximumAt_one]
    change σ.k - 3 ≤ m
    omega
  have hAlpha := ctx_bound_le_opposite_width_of_sibling_maximum_ge_k_minus_three
    α hPosα s t hne 1 hOneα hSideα hMaximumα
  have hAlphaFour : (∀ fuel, boundFuel fuel α ≤ 4) ∧ α.bound ≤ 4 := by
    cases s <;> cases t
    · exact False.elim (hne rfl)
    · have hcap : α.a - 1 ≤ 4 := by
        change σ.a - 1 ≤ 4
        simp only at hopposite
        omega
      exact ⟨fun fuel => (hAlpha.1 fuel).trans hcap, hAlpha.2.trans hcap⟩
    · have hcap : α.u - 1 ≤ 4 := by
        change σ.u - 1 ≤ 4
        simp only at hopposite
        omega
      exact ⟨fun fuel => (hAlpha.1 fuel).trans hcap, hAlpha.2.trans hcap⟩
    · exact False.elim (hne rfl)
  have hDouble (v : Side) (c : ℕ) :
      σ.part (σ.childPositions.filter (· ∉ rest)) v c = σ.part keep v c := by
    apply part_congr
    intro p hp
    simp only [rest, List.mem_filter, decide_eq_true_eq, hp, true_and, not_not]
  have hCompanion := ctx_two_actual_marker_companion_maximum_bound σ hpositive s t hne
    N M x y hN hM hNM hNs hMs hx hy hglobal rest m n l q₀
    ((hChildα l).mpr ((hRest l).mpr ⟨hl, hlnot⟩)) (hkeep q₀ hq₀)
    (by simp only [rest, List.mem_filter, decide_eq_true_eq, hkeep q₀ hq₀,
      true_and, not_true_eq_false, not_false_eq_true, hq₀])
  rw [hDouble t n] at hCompanion
  have hnTwo : n = 2 := by omega
  have hbudget : σ.k - n - 1 = 3 := by omega
  have hBetaEight : (∀ fuel, boundFuel fuel β ≤ 8) ∧ β.bound ≤ 8 := by
    change (∀ fuel, boundFuel fuel (σ.part keep t n) ≤ 8) ∧
      (σ.part keep t n).bound ≤ 8
    simpa only [hbudget] using hCompanion
  exact ⟨
    fun f g => (Nat.add_le_add (hAlphaFour.1 f) (hBetaEight.1 g)).trans (by omega),
    (Nat.add_le_add hAlphaFour.2 hBetaEight.2).trans (by omega)⟩

end ErdosSzekeres
