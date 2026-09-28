import ESBlueprint.B.CtxSmallGlobalAxisOppositeBinomialBound
import ESBlueprint.B.CtxSiblingMaximumUpperNormalize

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- An indexed chosen-side sibling maximum at least k-4 forces the full opposite-binomial bound. Upper normalization at that level caps the chosen global by four while preserving the opposite global, and the checked global-four triangle theorem then bounds every fuel approximation and the full context. No original global bound, marker occurrence, terminal-level, or well-formedness hypothesis is needed.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_sibling_maximum_upper_normalize, ErdosSzekeres.ctx_small_global_axis_opposite_binomial_bound
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_chosen_sibling_maximum_opposite_binomial_bound (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N : ℕ) (hN : N ∈ σ.levels) (hNs : σ.sideAt N = s) (hmaximum : σ.k - 4 ≤ σ.maximumAt N) : let oppositeGlobal := match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a; (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ oppositeGlobal.choose 2) ∧ σ.bound ≤ oppositeGlobal.choose 2 := by
  let G (ρ : Context) (v : Side) := match v with
    | Side.lower => ρ.u
    | Side.upper => ρ.a
  let τ : Context := match σ.sideAt N with
    | Side.lower => { σ with
        u := min σ.u (σ.k - σ.maximumAt N)
        maxima := σ.maxima.take (N - 1) }
    | Side.upper => { σ with
        a := min σ.a (σ.k - σ.maximumAt N)
        maxima := σ.maxima.take (N - 1) }
  change (∀ fuel, boundFuel fuel σ ≤ (G σ t).choose 2) ∧
    σ.bound ≤ (G σ t).choose 2
  have hFuel : ∀ fuel, boundFuel fuel σ ≤ boundFuel fuel τ := by
    simpa only [τ] using
      (ctx_sibling_maximum_upper_normalize σ N hN).2.1
  have hFull : σ.bound ≤ τ.bound := by
    simpa only [τ] using
      (ctx_sibling_maximum_upper_normalize σ N hN).2.2
  have hWord : τ.word = σ.word := by
    cases hside : σ.sideAt N <;> simp only [τ, hside]
  have hLetter (p : ℕ) : τ.letterAt p = σ.letterAt p := by
    simp only [letterAt, hWord]
  have hPositive : ∀ p j v, τ.letterAt p = Letter.ext j v → 1 ≤ j := by
    intro p j v hp
    rw [hLetter] at hp
    exact hpositive p j v hp
  have hChosen : G τ s ≤ 4 := by
    rw [← hNs]
    cases hside : σ.sideAt N <;> simp only [G, τ, hside]
    all_goals exact (Nat.min_le_right _ _).trans (by omega)
  have hOpposite : G τ t = G σ t := by
    cases s <;> cases t
    · exact False.elim (hne rfl)
    · simp only [G, τ, hNs]
    · simp only [G, τ, hNs]
    · exact False.elim (hne rfl)
  have hTriangle :=
    ctx_small_global_axis_opposite_binomial_bound τ hPositive s t hne hChosen
  change (∀ fuel, boundFuel fuel τ ≤ (G τ t).choose 2) ∧
    τ.bound ≤ (G τ t).choose 2 at hTriangle
  rw [hOpposite] at hTriangle
  exact ⟨fun fuel => (hFuel fuel).trans (hTriangle.1 fuel),
    hFull.trans hTriangle.2⟩

end ErdosSzekeres
