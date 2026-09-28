import ESBlueprint.B.CtxTwoMarkerYoungerExteriorInternalComplementCutComponentBounds
import ESBlueprint.B.CtxBoundLeOneOfLargeSiblingMaximum
import ESBlueprint.B.CtxPartPositiveLetters

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- At k six, the younger-exterior internal-complement cut has independent-fuel and full sums at most twelve when the complement maximum is extreme. For m=1 the legal coupling makes the retained maximum four and hence its bound one; for m=4 the complement bound is one. The component theorem supplies the other exact charge. All classifier hypotheses, arbitrary original maxima, inactive children, and both legal maxima remain explicit.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_two_marker_younger_exterior_internal_complement_cut_component_bounds, ErdosSzekeres.ctx_bound_le_one_of_large_sibling_maximum, ErdosSzekeres.ctx_part_positive_letters
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_marker_younger_exterior_internal_complement_cut_six_bound_of_extreme_maximum (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hclear : σ.levelsOn t 0 = []) (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ p ∈ σ.extPositions j, p = x ∨ p = y) (hwidth : 2 ≤ (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1) (keep : List ℕ) (q₀ l r m n : ℕ) (hq₀ : q₀ ∈ keep) (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions) (hl : l ∈ σ.childPositions) (hr : r ∈ σ.childPositions) (hlnot : l ∉ keep) (hrnot : r ∉ keep) (hinside : ∀ p ∈ keep, l < p ∧ p < r) (houtside : (x < y ∧ ∀ p ∈ keep, p < x) ∨ (y < x ∧ ∀ p ∈ keep, x < p)) (hconvex : ∀ p ∈ keep, ∀ q ∈ keep, ∀ z ∈ σ.childPositions, p ≤ z → z ≤ q → z ∈ keep) (hk : σ.k = 6) (hm : 1 ≤ m) (hn : 1 ≤ n) (hcoupling : m + n = σ.k - 1) (hextreme : m = 1 ∨ m = 4) : let rest := σ.childPositions.filter (· ∉ keep); (∀ f g, Ctx.Context.boundFuel f (σ.part rest s m) + Ctx.Context.boundFuel g (σ.part keep t n) ≤ 12) ∧ (σ.part rest s m).bound + (σ.part keep t n).bound ≤ 12 := by
  classical
  let w := (match t with | Side.lower => σ.u | Side.upper => σ.a) - 1
  let rest := σ.childPositions.filter (· ∉ keep)
  let α := σ.part rest s m
  let β := σ.part keep t n
  change (∀ f g, boundFuel f α + boundFuel g β ≤ 12) ∧ α.bound + β.bound ≤ 12
  have hComponent :=
    ctx_two_marker_younger_exterior_internal_complement_cut_component_bounds
      σ hpositive s t hne N M x y hN hM hNM hNs hMs hx hy hglobal hclear hchosen
      hwidth keep q₀ l r m n hq₀ hkeep hl hr hlnot hrnot hinside houtside
  change ((∀ f, boundFuel f α ≤ (w + 1).choose 2 + 1) ∧
      α.bound ≤ (w + 1).choose 2 + 1) ∧
    ((∀ g, boundFuel g β ≤ w - 2) ∧ β.bound ≤ w - 2) at hComponent
  have hPosα := ctx_part_positive_letters σ rest s m
  have hPosβ := ctx_part_positive_letters σ keep t n
  have hOneα : 1 ∈ α.levels := by simp only [α, part_levels, List.mem_cons, true_or]
  have hOneβ : 1 ∈ β.levels := by simp only [β, part_levels, List.mem_cons, true_or]
  have hwUpper : w ≤ 4 := by
    dsimp only [w]
    cases t <;> simp only at hopposite ⊢ <;> omega
  have hChoose : (w + 1).choose 2 ≤ 10 := by
    have hh := Nat.choose_le_choose 2 (show w + 1 ≤ 5 by omega)
    norm_num at hh ⊢
    exact hh
  rcases hextreme with hmOne | hmFour
  · have hMaximumβ : β.maximumAt 1 = n := part_maximumAt_one σ keep t n
    have hLargeβ : β.k - 2 ≤ β.maximumAt 1 := by
      rw [hMaximumβ]
      change σ.k - 2 ≤ n
      omega
    have hβOne := ctx_bound_le_one_of_large_sibling_maximum β hPosβ 1 hOneβ hLargeβ
    exact ⟨
      fun f g => by
        have ha := hComponent.1.1 f
        have hb := hβOne.1 g
        omega,
      by
        have ha := hComponent.1.2
        have hb := hβOne.2
        omega⟩
  · have hMaximumα : α.maximumAt 1 = m := part_maximumAt_one σ rest s m
    have hLargeα : α.k - 2 ≤ α.maximumAt 1 := by
      rw [hMaximumα]
      change σ.k - 2 ≤ m
      omega
    have hαOne := ctx_bound_le_one_of_large_sibling_maximum α hPosα 1 hOneα hLargeα
    exact ⟨
      fun f g => by
        have ha := hαOne.1 f
        have hb := hComponent.2.1 g
        omega,
      by
        have ha := hαOne.2
        have hb := hComponent.2.2
        omega⟩

end ErdosSzekeres
