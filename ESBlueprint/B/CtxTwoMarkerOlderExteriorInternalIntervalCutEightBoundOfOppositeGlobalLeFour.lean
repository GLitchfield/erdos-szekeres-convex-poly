import ESBlueprint.B.CtxTwoMarkerOlderExteriorInternalIntervalCutPotentialBound

namespace ErdosSzekeres

/-- For a convex internally bracketed chosen-kept interval exterior beyond the older of two actual chosen markers, opposite global at most four and opposite width at least two sharpen the full and independent-fuel cut sum to eight. This closes the nonsaturated opposite-global portion of the remaining k-six older-exterior obstruction.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_two_marker_older_exterior_internal_interval_cut_potential_bound
@consumer ErdosSzekeres.ctx_two_actual_marker_small_history_internal_chosen_kept_cut_six_bound -/
theorem ctx_two_marker_older_exterior_internal_interval_cut_eight_bound_of_opposite_global_le_four (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j, z = x ∨ z = y) (hwidth : 2 ≤ (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1) (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 4) (keep : List ℕ) (q₀ l r m n : ℕ) (hq₀ : q₀ ∈ keep) (hexterior : (x < y ∧ ∀ p ∈ keep, y < p) ∨ (y < x ∧ ∀ p ∈ keep, p < y)) (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions) (hl : l ∈ σ.childPositions) (hr : r ∈ σ.childPositions) (hlnot : l ∉ keep) (hrnot : r ∉ keep) (hinside : ∀ p ∈ keep, l < p ∧ p < r) (hconvex : ∀ p ∈ keep, ∀ q ∈ keep, ∀ z ∈ σ.childPositions, p ≤ z → z ≤ q → z ∈ keep) : let rest := σ.childPositions.filter (· ∉ keep); (∀ f g, Ctx.Context.boundFuel f (σ.part keep s m) + Ctx.Context.boundFuel g (σ.part rest t n) ≤ 8) ∧ (σ.part keep s m).bound + (σ.part rest t n).bound ≤ 8 := by
  classical
  let w := (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1
  let rest := σ.childPositions.filter (· ∉ keep)
  have hw : w ≤ 3 := by
    dsimp only [w]
    omega
  have hchoose : (w + 1).choose 2 ≤ 6 := by
    have hh := Nat.choose_le_choose 2 (show w + 1 ≤ 4 by omega)
    norm_num at hh ⊢
    exact hh
  have hbudget : (w + 1).choose 2 + w - 1 ≤ 8 := by omega
  have hOld := ctx_two_marker_older_exterior_internal_interval_cut_potential_bound
    σ hpositive s t hne N M x y hN hM hNM hNs hMs hx hy
    hglobal hchosen hwidth keep q₀ l r m n hq₀ hexterior hkeep hl hr
    hlnot hrnot hinside hconvex
  change (∀ f g, Ctx.Context.boundFuel f (σ.part keep s m) +
      Ctx.Context.boundFuel g (σ.part rest t n) ≤
        (w + 1).choose 2 + w - 1) ∧
      (σ.part keep s m).bound + (σ.part rest t n).bound ≤
        (w + 1).choose 2 + w - 1 at hOld
  change (∀ f g, Ctx.Context.boundFuel f (σ.part keep s m) +
      Ctx.Context.boundFuel g (σ.part rest t n) ≤ 8) ∧
      (σ.part keep s m).bound + (σ.part rest t n).bound ≤ 8
  exact ⟨fun f g => (hOld.1 f g).trans hbudget, hOld.2.trans hbudget⟩

end ErdosSzekeres
