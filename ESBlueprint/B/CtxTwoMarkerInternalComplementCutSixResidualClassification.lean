import ESBlueprint.B.CtxTwoMarkerYoungerSurroundingInternalComplementCutTenBound
import ESBlueprint.B.CtxTwoMarkerBetweenInternalComplementCutTenBound
import ESBlueprint.B.CtxOlderExteriorInternalComplementCutSixBound

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- At k six, classify every legal two-marker internal opposite-kept interval cut into an exact independent-fuel/full sum bound of twelve or one of two explicit saturated residual geometries: the kept interval surrounds the older marker, or it lies exterior to the younger marker away from the older marker. Younger surrounds and between-marker blocks are bounded by ten, while the older-exterior alternative is discharged by the coupled exact theorem. Positive labels, clear opposite history, convexity, arbitrary maxima, inactive children, and the legal coupling remain explicit.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_two_marker_younger_surrounding_internal_complement_cut_ten_bound, ErdosSzekeres.ctx_two_marker_between_internal_complement_cut_ten_bound, ErdosSzekeres.ctx_older_exterior_internal_complement_cut_six_bound
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_marker_internal_complement_cut_six_residual_classification (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hclear : σ.levelsOn t 0 = []) (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ p ∈ σ.extPositions j, p = x ∨ p = y) (hwidth : 2 ≤ (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1) (keep : List ℕ) (q₀ l r m n : ℕ) (hq₀ : q₀ ∈ keep) (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions) (hl : l ∈ σ.childPositions) (hr : r ∈ σ.childPositions) (hlnot : l ∉ keep) (hrnot : r ∉ keep) (hinside : ∀ p ∈ keep, l < p ∧ p < r) (hconvex : ∀ p ∈ keep, ∀ q ∈ keep, ∀ z ∈ σ.childPositions, p ≤ z → z ≤ q → z ∈ keep) (hk : σ.k = 6) (hm : 1 ≤ m) (hn : 1 ≤ n) (hcoupling : m + n = σ.k - 1) : let rest := σ.childPositions.filter (· ∉ keep); ((∀ f g, Ctx.Context.boundFuel f (σ.part rest s m) + Ctx.Context.boundFuel g (σ.part keep t n) ≤ 12) ∧ (σ.part rest s m).bound + (σ.part keep t n).bound ≤ 12) ∨ (∃ a ∈ keep, ∃ b ∈ keep, a < y ∧ y < b) ∨ ((x < y ∧ ∀ p ∈ keep, p < x) ∨ (y < x ∧ ∀ p ∈ keep, x < p)) := by
  classical
  let rest := σ.childPositions.filter (· ∉ keep)
  let Result (T : ℕ) : Prop :=
    (∀ f g, boundFuel f (σ.part rest s m) + boundFuel g (σ.part keep t n) ≤ T) ∧
      (σ.part rest s m).bound + (σ.part keep t n).bound ≤ T
  change Result 12 ∨ (∃ a ∈ keep, ∃ b ∈ keep, a < y ∧ y < b) ∨
    ((x < y ∧ ∀ p ∈ keep, p < x) ∨ (y < x ∧ ∀ p ∈ keep, x < p))
  have hLift (hh : Result 10) : Result 12 :=
    ⟨fun f g => (hh.1 f g).trans (by omega), hh.2.trans (by omega)⟩
  have hAtLevel (j i p : ℕ) (hp : p ∈ σ.extPositions j)
      (hp' : p ∈ σ.extPositions i) : j = i := by
    have hj := (List.mem_filter.mp hp).2
    have hi := (List.mem_filter.mp hp').2
    cases hletter : σ.letterAt p <;> simp [hletter] at hj hi
    omega
  have hNpos := one_le_of_mem_levels hN
  have hYoungHistory : ∀ j ∈ σ.levelsOn s N, σ.extPositions j = [] := by
    intro j hj
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro p hp
    have hh := List.mem_filter.mp hj
    have hPred := of_decide_eq_true hh.2
    have hOn : j ∈ σ.levelsOn s 0 :=
      List.mem_filter.mpr ⟨hh.1, by simp [hPred.1]⟩
    rcases hchosen j hOn p hp with hpx | hpy
    · have he := hAtLevel j N x (by simpa only [hpx] using hp) hx
      omega
    · have he := hAtLevel j M y (by simpa only [hpy] using hp) hy
      omega
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
  by_cases hYoung : ∃ a ∈ keep, ∃ b ∈ keep, a < x ∧ x < b
  · obtain ⟨a, ha, b, hb, hab⟩ := hYoung
    have hh := ctx_two_marker_younger_surrounding_internal_complement_cut_ten_bound
      σ hpositive s t hne N M x y hN hM hNM hNs hMs hx hy hglobal hopposite
      hchosen hwidth keep a b l r m n ha hb hab.1 hab.2 hkeep hl hr hlnot hrnot
      hinside hconvex
    have hten : Result 10 := by simpa only [Result, rest] using hh
    exact Or.inl (hLift hten)
  by_cases hOld : ∃ a ∈ keep, ∃ b ∈ keep, a < y ∧ y < b
  · exact Or.inr (Or.inl hOld)
  have hAvoidX := hAvoid x (fun p hp => hChildNe p N x (hkeep p hp) hx) hYoung
  have hAvoidY := hAvoid y (fun p hp => hChildNe p M y (hkeep p hp) hy) hOld
  have hXY : x ≠ y := by
    intro he
    have hxn := (List.mem_filter.mp hx).2
    have hym := (List.mem_filter.mp hy).2
    rw [← he] at hym
    cases hletter : σ.letterAt x <;> simp [hletter] at hxn hym
    omega
  rcases hAvoidX with hLX | hRX <;> rcases hAvoidY with hLY | hRY
  · by_cases hxy : x < y
    · exact Or.inr (Or.inr (Or.inl ⟨hxy, hLX⟩))
    · have hExterior : (x < y ∧ ∀ p ∈ keep, y < p) ∨
          (y < x ∧ ∀ p ∈ keep, p < y) := Or.inr ⟨by omega, hLY⟩
      have hh := ctx_older_exterior_internal_complement_cut_six_bound σ hpositive
        s t hne N M x y hN hM hNM hNs hMs hx hy hYoungHistory hglobal hopposite
        hwidth keep q₀ l r m n hq₀ hkeep hl hr hlnot hrnot hinside hExterior
        hk hm hn hcoupling
      exact Or.inl (by simpa only [Result, rest] using hh)
  · have hh := ctx_two_marker_between_internal_complement_cut_ten_bound
      σ hpositive s t hne N M x y hN hM hNM hNs hMs hx hy hglobal hopposite
      hclear hchosen hwidth keep q₀ l r m n hq₀ hkeep hl hr hlnot hrnot hinside
      (Or.inr (fun p hp => ⟨hRY p hp, hLX p hp⟩))
    have hten : Result 10 := by simpa only [Result, rest] using hh
    exact Or.inl (hLift hten)
  · have hh := ctx_two_marker_between_internal_complement_cut_ten_bound
      σ hpositive s t hne N M x y hN hM hNM hNs hMs hx hy hglobal hopposite
      hclear hchosen hwidth keep q₀ l r m n hq₀ hkeep hl hr hlnot hrnot hinside
      (Or.inl (fun p hp => ⟨hRX p hp, hLY p hp⟩))
    have hten : Result 10 := by simpa only [Result, rest] using hh
    exact Or.inl (hLift hten)
  · by_cases hxy : x < y
    · have hExterior : (x < y ∧ ∀ p ∈ keep, y < p) ∨
          (y < x ∧ ∀ p ∈ keep, p < y) := Or.inl ⟨hxy, hRY⟩
      have hh := ctx_older_exterior_internal_complement_cut_six_bound σ hpositive
        s t hne N M x y hN hM hNM hNs hMs hx hy hYoungHistory hglobal hopposite
        hwidth keep q₀ l r m n hq₀ hkeep hl hr hlnot hrnot hinside hExterior
        hk hm hn hcoupling
      exact Or.inl (by simpa only [Result, rest] using hh)
    · exact Or.inr (Or.inr (Or.inr ⟨by omega, hRX⟩))

end ErdosSzekeres
