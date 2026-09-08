import ESBlueprint.B.CtxPartLimitsLe

namespace ErdosSzekeres

/-- The recursive context bound is at most the sum of the pointwise classical base bounds. This unconditional separable upper bound transports through every recursive partition using part-limit monotonicity. In particular, zero pointwise capacity at every child position forces the full recursive bound to vanish.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_single_run -/
theorem ctx_bound_le_sum_point_bases (σ : Ctx.Context) :
  σ.bound ≤ (σ.childPositions.map
    (fun p ↦ Ctx.Context.baseOf (σ.cupLimit p p) (σ.capLimit p p) σ.k)).sum := by
  let w (c : Ctx.Context) (p : ℕ) := Ctx.Context.baseOf (c.cupLimit p p) (c.capLimit p p) c.k
  let total (c : Ctx.Context) := (c.childPositions.map (w c)).sum
  have hsum : ∀ (xs : List ℕ) (f g : ℕ → ℕ), (∀ p ∈ xs, f p ≤ g p) →
      (xs.map f).sum ≤ (xs.map g).sum := by
    intro xs f g h
    induction xs with
    | nil => simp
    | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (h x (by simp)) (ih (fun p hp => h p (by simp [hp])))
  have hpartition (xs : List ℕ) (keep : List ℕ) (f : ℕ → ℕ) :
      ((xs.filter (· ∈ keep)).map f).sum + ((xs.filter (· ∉ keep)).map f).sum =
        (xs.map f).sum := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      by_cases hx : x ∈ keep <;>
        simp [hx, Nat.add_assoc, Nat.add_left_comm] <;>
        simpa only [decide_not] using ih
  have hbase (c : Ctx.Context) : c.base ≤ total c := by
    rw [Ctx.Context.base_eq_baseOf]
    dsimp [total]
    cases hps : c.childPositions with
    | nil => simp
    | cons p ps => simp [w]
  have hpart (c : Ctx.Context) (keep : List ℕ) (t : Ctx.Side) (m : ℕ) :
      total (c.part keep t m) ≤ ((c.childPositions.filter (· ∈ keep)).map (w c)).sum := by
    dsimp [total]
    rw [Ctx.Context.part_childPositions]
    apply hsum
    intro p hp
    have h := ctx_part_limits_le c keep t m p p
    exact Ctx.Context.baseOf_mono h.1 h.2
  have hcut (c : Ctx.Context) (keep : List ℕ) (s t : Ctx.Side) (m n : ℕ) :
      total (c.part keep s m) + total (c.part (c.childPositions.filter (· ∉ keep)) t n) ≤ total c := by
    have hrest : c.childPositions.filter (· ∈ c.childPositions.filter (· ∉ keep)) =
        c.childPositions.filter (· ∉ keep) := by
      apply List.filter_congr
      intro p hp
      simp [hp]
    have h := Nat.add_le_add (hpart c keep s m) (hpart c (c.childPositions.filter (· ∉ keep)) t n)
    rw [hrest, hpartition] at h
    exact h
  have hfuel : ∀ fuel (c : Ctx.Context), Ctx.Context.boundFuel fuel c ≤ total c := by
    intro fuel
    induction fuel with
    | zero => intro c; exact Nat.zero_le _
    | succ fuel ih =>
      intro c
      rw [Ctx.Context.boundFuel]
      split
      · exact hbase c
      · apply Ctx.getD_max?_le
        intro x hx
        simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hx
        obtain ⟨keep, _, d, _, hx⟩ := hx
        rcases hx with rfl | rfl
        · exact (Nat.add_le_add (ih _) (ih _)).trans (hcut c keep _ _ _ _)
        · exact (Nat.add_le_add (ih _) (ih _)).trans (hcut c keep _ _ _ _)
  exact hfuel _ σ

end ErdosSzekeres
