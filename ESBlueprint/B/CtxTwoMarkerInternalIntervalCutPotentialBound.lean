import ESBlueprint.B.CtxTwoMarkerSurroundingYoungestInternalIntervalCutPotentialBound
import ESBlueprint.B.CtxTwoMarkerSurroundingOlderInternalIntervalCutPotentialBound
import ESBlueprint.B.CtxTwoMarkerBetweenInternalIntervalCutPotentialBound
import ESBlueprint.B.CtxTwoMarkerYoungerExteriorInternalIntervalCutPotentialBound
import ESBlueprint.B.CtxTwoMarkerOlderExteriorInternalIntervalCutPotentialBound
import ErdosSzekeres.DecomposableContext

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Classify a nonempty internally bracketed convex chosen interval against both actual markers. The surrounding, between, younger-exterior and older-exterior cut estimates cover every case, without a recursive potential premise. Positive external labels, chosen global at most five and opposite width w at least two. Two actual indexed chosen positions at distinct levels N<M, containing all indexed chosen positions. The chosen kept set is a nonempty convex child interval with complementary witnesses bracketing both ends. Arbitrary opposite history, original and new maxima and inactive children are allowed. No recursive potential premise.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_marker_internal_interval_cut_potential_bound (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ)
  (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M)
  (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s)
  (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
  (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ p ∈ σ.extPositions j, p = x ∨ p = y)
  (hwidth : 2 ≤ (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1)
  (keep : List ℕ) (q₀ l r m n : ℕ)
  (hq₀ : q₀ ∈ keep)
  (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions)
  (hl : l ∈ σ.childPositions) (hr : r ∈ σ.childPositions)
  (hlnot : l ∉ keep) (hrnot : r ∉ keep)
  (hinside : ∀ p ∈ keep, l < p ∧ p < r)
  (hconvex : ∀ p ∈ keep, ∀ q ∈ keep, ∀ z ∈ σ.childPositions,
    p ≤ z → z ≤ q → z ∈ keep) :
  let w := (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1
  let rest := σ.childPositions.filter (· ∉ keep)
  (∀ f g, Ctx.Context.boundFuel f (σ.part keep s m) +
    Ctx.Context.boundFuel g (σ.part rest t n) ≤ (w + 1).choose 2 + w - 1) ∧
    (σ.part keep s m).bound + (σ.part rest t n).bound ≤ (w + 1).choose 2 + w - 1 := by
  classical
  by_cases hYoung : ∃ a ∈ keep, ∃ b ∈ keep, a < x ∧ x < b
  · obtain ⟨a, ha, b, hb, hab⟩ := hYoung
    exact (ctx_two_marker_surrounding_youngest_internal_interval_cut_potential_bound
      σ hpositive s t hne N M x y hN hM hNM hNs hMs hx hy hglobal hchosen (Nat.le_trans (by decide : 1 ≤ 2) hwidth)
      keep a b l r m n ha hb hab hkeep hl hr hlnot hrnot hinside hconvex)
  by_cases hOld : ∃ a ∈ keep, ∃ b ∈ keep, a < y ∧ y < b
  · obtain ⟨a, ha, b, hb, hab⟩ := hOld
    exact (ctx_two_marker_surrounding_older_internal_interval_cut_potential_bound
      σ hpositive s t hne N M x y hN hM hNM hNs hMs hx hy hglobal hchosen hwidth
      keep a b l r m n ha hb hab hkeep hl hr hlnot hrnot hinside hconvex)
  have hChildNe (p j z : ℕ) (hp : p ∈ σ.childPositions)
      (hz : z ∈ σ.extPositions j) : p ≠ z := by
    have hc := of_decide_eq_true (List.mem_filter.mp hp).2
    have he := (List.mem_filter.mp hz).2
    intro h
    subst z
    simp [hc] at he
  have hAvoid (z : ℕ) (hNe : ∀ p ∈ keep, p ≠ z)
      (hNoCut : ¬∃ a ∈ keep, ∃ b ∈ keep, a < z ∧ z < b) :
      (∀ p ∈ keep, p < z) ∨ (∀ p ∈ keep, z < p) := by
    by_cases hq : q₀ < z
    · left
      intro p hp
      have hn := hNe p hp
      by_contra hh
      exact hNoCut ⟨q₀, hq₀, p, hp, hq, by omega⟩
    · right
      have hnq := hNe q₀ hq₀
      have hzq : z < q₀ := by omega
      intro p hp
      have hn := hNe p hp
      by_contra hh
      exact hNoCut ⟨p, hp, q₀, hq₀, by omega, hzq⟩
  have hAvoidX := hAvoid x (fun p hp ↦ hChildNe p N x (hkeep p hp) hx) hYoung
  have hAvoidY := hAvoid y (fun p hp ↦ hChildNe p M y (hkeep p hp) hy) hOld
  have hXY : x ≠ y := by
    intro he
    have hxn := (List.mem_filter.mp hx).2
    have hym := (List.mem_filter.mp hy).2
    rw [← he] at hym
    cases hletter : σ.letterAt x <;> simp [hletter] at hxn hym
    omega
  rcases hAvoidX with hLX | hRX <;> rcases hAvoidY with hLY | hRY
  · by_cases hxy : x < y
    · exact (ctx_two_marker_younger_exterior_internal_interval_cut_potential_bound
        σ hpositive s t hne N M x y hN hM hNM hNs hMs hx hy hglobal hchosen hwidth
        keep q₀ l r m n hq₀ (Or.inl ⟨hxy, hLX⟩) hkeep hl hr hlnot hrnot hinside hconvex)
    · exact ctx_two_marker_older_exterior_internal_interval_cut_potential_bound
        σ hpositive s t hne N M x y hN hM hNM hNs hMs hx hy hglobal hchosen hwidth
        keep q₀ l r m n hq₀ (Or.inr ⟨by omega, hLY⟩) hkeep hl hr hlnot hrnot hinside hconvex
  · exact (ctx_two_marker_between_internal_interval_cut_potential_bound
      σ hpositive s t hne N M x y hN hM hNM hNs hMs hx hy hglobal hchosen hwidth
      keep q₀ l r m n hq₀ (Or.inr (fun p hp ↦ ⟨hRY p hp, hLX p hp⟩))
      hkeep hl hr hlnot hrnot hinside hconvex)
  · exact (ctx_two_marker_between_internal_interval_cut_potential_bound
      σ hpositive s t hne N M x y hN hM hNM hNs hMs hx hy hglobal hchosen hwidth
      keep q₀ l r m n hq₀ (Or.inl (fun p hp ↦ ⟨hRX p hp, hLY p hp⟩))
      hkeep hl hr hlnot hrnot hinside hconvex)
  · by_cases hxy : x < y
    · exact ctx_two_marker_older_exterior_internal_interval_cut_potential_bound
        σ hpositive s t hne N M x y hN hM hNM hNs hMs hx hy hglobal hchosen hwidth
        keep q₀ l r m n hq₀ (Or.inl ⟨hxy, hRY⟩) hkeep hl hr hlnot hrnot hinside hconvex
    · exact (ctx_two_marker_younger_exterior_internal_interval_cut_potential_bound
        σ hpositive s t hne N M x y hN hM hNM hNs hMs hx hy hglobal hchosen hwidth
        keep q₀ l r m n hq₀ (Or.inr ⟨by omega, hRX⟩) hkeep hl hr hlnot hrnot hinside hconvex)

end ErdosSzekeres
