import ESBlueprint.B.CtxTwoMarkerInternalComplementCutSixResidualClassification
import ESBlueprint.B.CtxTwoMarkerOlderSurroundingInternalComplementCutSixBoundOfExtremeMaximum

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- At k six, sharpen the exact two-marker internal-complement classifier so that every cut has sum at most twelve unless either the opposite kept interval surrounds the older marker with middle complement maximum m=2 or m=3, or the block lies exterior to the younger marker away from the older marker. The extreme older-surround maxima m=1 and m=4 are discharged by the coupled sibling-bound theorem. All original positivity, history, convexity, maxima, inactivity, and legal coupling hypotheses remain explicit.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_two_marker_internal_complement_cut_six_residual_classification, ErdosSzekeres.ctx_two_marker_older_surrounding_internal_complement_cut_six_bound_of_extreme_maximum
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_marker_internal_complement_cut_six_middle_residual_classification (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hclear : σ.levelsOn t 0 = []) (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ p ∈ σ.extPositions j, p = x ∨ p = y) (hwidth : 2 ≤ (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1) (keep : List ℕ) (q₀ l r m n : ℕ) (hq₀ : q₀ ∈ keep) (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions) (hl : l ∈ σ.childPositions) (hr : r ∈ σ.childPositions) (hlnot : l ∉ keep) (hrnot : r ∉ keep) (hinside : ∀ p ∈ keep, l < p ∧ p < r) (hconvex : ∀ p ∈ keep, ∀ q ∈ keep, ∀ z ∈ σ.childPositions, p ≤ z → z ≤ q → z ∈ keep) (hk : σ.k = 6) (hm : 1 ≤ m) (hn : 1 ≤ n) (hcoupling : m + n = σ.k - 1) : let rest := σ.childPositions.filter (· ∉ keep); ((∀ f g, Ctx.Context.boundFuel f (σ.part rest s m) + Ctx.Context.boundFuel g (σ.part keep t n) ≤ 12) ∧ (σ.part rest s m).bound + (σ.part keep t n).bound ≤ 12) ∨ (((m = 2 ∨ m = 3) ∧ ∃ a ∈ keep, ∃ b ∈ keep, a < y ∧ y < b)) ∨ ((x < y ∧ ∀ p ∈ keep, p < x) ∨ (y < x ∧ ∀ p ∈ keep, x < p)) := by
  classical
  let rest := σ.childPositions.filter (· ∉ keep)
  let Result : Prop :=
    (∀ f g, boundFuel f (σ.part rest s m) + boundFuel g (σ.part keep t n) ≤ 12) ∧
      (σ.part rest s m).bound + (σ.part keep t n).bound ≤ 12
  change Result ∨ (((m = 2 ∨ m = 3) ∧
    ∃ a ∈ keep, ∃ b ∈ keep, a < y ∧ y < b)) ∨
    ((x < y ∧ ∀ p ∈ keep, p < x) ∨ (y < x ∧ ∀ p ∈ keep, x < p))
  have hClass := ctx_two_marker_internal_complement_cut_six_residual_classification
    σ hpositive s t hne N M x y hN hM hNM hNs hMs hx hy hglobal hopposite
    hclear hchosen hwidth keep q₀ l r m n hq₀ hkeep hl hr hlnot hrnot hinside
    hconvex hk hm hn hcoupling
  change Result ∨ (∃ a ∈ keep, ∃ b ∈ keep, a < y ∧ y < b) ∨
    ((x < y ∧ ∀ p ∈ keep, p < x) ∨ (y < x ∧ ∀ p ∈ keep, x < p)) at hClass
  rcases hClass with hExact | hOld | hYoungExterior
  · exact Or.inl hExact
  · by_cases hextreme : m = 1 ∨ m = 4
    · obtain ⟨a, ha, b, hb, hay, hyb⟩ := hOld
      have hh :=
        ctx_two_marker_older_surrounding_internal_complement_cut_six_bound_of_extreme_maximum
          σ hpositive s t hne N M x y hN hM hNM hNs hMs hx hy hglobal hopposite
          hchosen hwidth keep a b l r m n ha hb hay hyb hkeep hl hr hlnot hrnot
          hinside hconvex hk hm hn hcoupling hextreme
      exact Or.inl (by simpa only [Result, rest] using hh)
    · have hmUpper : m ≤ 4 := by omega
      have hMiddle : m = 2 ∨ m = 3 := by omega
      exact Or.inr (Or.inl ⟨hMiddle, hOld⟩)
  · exact Or.inr (Or.inr hYoungExterior)

end ErdosSzekeres
