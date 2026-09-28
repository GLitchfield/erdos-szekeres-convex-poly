import ESBlueprint.B.CtxTwoMarkerYoungerExteriorInternalComplementCutComponentBounds
import ESBlueprint.B.CtxChosenSiblingMaximumOppositeBinomialBound

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- At k six, the unique younger-exterior internal-complement residual with complement maximum two has independent-fuel and full sums at most twelve. Sibling-maximum normalization bounds the complement by choose five two, while the geometric component theorem bounds the retained part by two.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_two_marker_younger_exterior_internal_complement_cut_component_bounds, ErdosSzekeres.ctx_chosen_sibling_maximum_opposite_binomial_bound, ErdosSzekeres.ctx_part_positive_letters
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_marker_younger_exterior_internal_complement_cut_six_bound_of_maximum_two (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hclear : σ.levelsOn t 0 = []) (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ p ∈ σ.extPositions j, p = x ∨ p = y) (hwidth : 2 ≤ (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1) (keep : List ℕ) (q₀ l r m n : ℕ) (hq₀ : q₀ ∈ keep) (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions) (hl : l ∈ σ.childPositions) (hr : r ∈ σ.childPositions) (hlnot : l ∉ keep) (hrnot : r ∉ keep) (hinside : ∀ p ∈ keep, l < p ∧ p < r) (houtside : (x < y ∧ ∀ p ∈ keep, p < x) ∨ (y < x ∧ ∀ p ∈ keep, x < p)) (hk : σ.k = 6) (hmTwo : m = 2) : let rest := σ.childPositions.filter (· ∉ keep); (∀ f g, Ctx.Context.boundFuel f (σ.part rest s m) + Ctx.Context.boundFuel g (σ.part keep t n) ≤ 12) ∧ (σ.part rest s m).bound + (σ.part keep t n).bound ≤ 12 := by
  classical
  let w := (match t with | Side.lower => σ.u | Side.upper => σ.a) - 1
  let rest := σ.childPositions.filter (· ∉ keep)
  let α := σ.part rest s m
  let β := σ.part keep t n
  change (∀ f g, boundFuel f α + boundFuel g β ≤ 12) ∧
    α.bound + β.bound ≤ 12
  have hComponent :=
    ctx_two_marker_younger_exterior_internal_complement_cut_component_bounds
      σ hpositive s t hne N M x y hN hM hNM hNs hMs hx hy hglobal hclear hchosen
      hwidth keep q₀ l r m n hq₀ hkeep hl hr hlnot hrnot hinside houtside
  change ((∀ f, boundFuel f α ≤ (w + 1).choose 2 + 1) ∧
      α.bound ≤ (w + 1).choose 2 + 1) ∧
    ((∀ g, boundFuel g β ≤ w - 2) ∧ β.bound ≤ w - 2) at hComponent
  have hPosα := ctx_part_positive_letters σ rest s m
  have hOneα : 1 ∈ α.levels := by
    simp only [α, part_levels, List.mem_cons, true_or]
  have hExtα (p : ℕ) : p ∈ α.extPositions 1 ↔
      p ∈ σ.childPositions ∧ p ∈ keep := by
    rw [part_extPositions_one hpositive]
    simp only [rest, List.mem_filter, decide_eq_true_eq]
    tauto
  have hQα : q₀ ∈ α.extPositions 1 :=
    (hExtα q₀).mpr ⟨hkeep q₀ hq₀, hq₀⟩
  have hSideα : α.sideAt 1 = s :=
    part_sideAt_one_of_mem hpositive rest s m hQα
  have hMaximumα : α.k - 4 ≤ α.maximumAt 1 := by
    rw [part_maximumAt_one]
    change σ.k - 4 ≤ m
    omega
  have hAlpha := ctx_chosen_sibling_maximum_opposite_binomial_bound
    α hPosα s t hne 1 hOneα hSideα hMaximumα
  have hChooseTen :
      (match t with | Side.lower => α.u | Side.upper => α.a).choose 2 ≤ 10 := by
    cases t <;> simp only at hopposite ⊢
    · change σ.u.choose 2 ≤ 10
      have hh := Nat.choose_le_choose 2 hopposite
      norm_num at hh ⊢
      exact hh
    · change σ.a.choose 2 ≤ 10
      have hh := Nat.choose_le_choose 2 hopposite
      norm_num at hh ⊢
      exact hh
  change (∀ fuel, boundFuel fuel α ≤
      (match t with | Side.lower => α.u | Side.upper => α.a).choose 2) ∧
    α.bound ≤ (match t with | Side.lower => α.u | Side.upper => α.a).choose 2 at hAlpha
  have hwUpper : w ≤ 4 := by
    dsimp only [w]
    cases t <;> simp only at hopposite ⊢ <;> omega
  exact ⟨
    fun f g => (Nat.add_le_add ((hAlpha.1 f).trans hChooseTen)
      (hComponent.2.1 g)).trans (by omega),
    (Nat.add_le_add (hAlpha.2.trans hChooseTen) hComponent.2.2).trans (by omega)⟩

end ErdosSzekeres
