import ESBlueprint.B.CtxPartPruningHistoryTransport

namespace ErdosSzekeres

/-- For the canonical binary pruning of source children at chosen capacity two, every ordered pair shared by the active low and high pair unions has explicit source-active witnesses on both sides of the capacity split. Pruning transport identifies their point limits and opposite-rank intervals with the source, so both pair coordinates lie in both original-history intervals. This removes the pruning abstraction from the mixed-capacity collision residual.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_part_pruning_history_transport
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_binary_capacity_pair_intersection_source_witnesses (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) : let capacity : ℕ → ℕ := fun q => match s with | Ctx.Side.lower => σ.cupLimit q q | Ctx.Side.upper => σ.capLimit q q; let color : ℕ → ℕ := fun q => if capacity q ≤ 2 then 0 else 1; let support : ℕ → List ℕ := fun c => σ.childPositions.filter (fun q => color q = c); let group : ℕ → Ctx.Context := fun c => ({ σ with word := (List.range σ.word.length).map (fun q => match σ.letterAt q with | Ctx.Letter.child => if q ∈ support c then Ctx.Letter.child else Ctx.Letter.ext (σ.maxima.length + 1) Ctx.Side.lower | Ctx.Letter.ext j v => Ctx.Letter.ext j v) } : Ctx.Context); let global : ℕ := match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a; let active : ℕ → Finset ℕ := fun c => (group c).childPositions.toFinset.filter (fun q => 0 < (group c).cupLimit q q ∧ 0 < (group c).capLimit q q); let interval : ℕ → ℕ → Finset ℕ := fun c q => Finset.Icc ((group c).leftExt t 0 q + 1) (global - 1 - (group c).rightExt t 0 q); let pairs : ℕ → Finset (ℕ × ℕ) := fun c => (active c).biUnion (fun q => (((interval c q).product (interval c q)).filter (fun z => z.1 ≤ z.2))); let sourceInterval : ℕ → Finset ℕ := fun q => Finset.Icc (σ.leftExt t 0 q + 1) (global - 1 - σ.rightExt t 0 q); ∀ z ∈ (pairs 0) ∩ (pairs 1), ∃ low high, low ∈ σ.childPositions ∧ 0 < σ.cupLimit low low ∧ 0 < σ.capLimit low low ∧ capacity low ≤ 2 ∧ high ∈ σ.childPositions ∧ 0 < σ.cupLimit high high ∧ 0 < σ.capLimit high high ∧ 3 ≤ capacity high ∧ z.1 ≤ z.2 ∧ z.1 ∈ sourceInterval low ∧ z.2 ∈ sourceInterval low ∧ z.1 ∈ sourceInterval high ∧ z.2 ∈ sourceInterval high := by
  classical
  let capacity : ℕ → ℕ := fun q => match s with
    | Ctx.Side.lower => σ.cupLimit q q
    | Ctx.Side.upper => σ.capLimit q q
  let color : ℕ → ℕ := fun q => if capacity q ≤ 2 then 0 else 1
  let support : ℕ → List ℕ := fun c =>
    σ.childPositions.filter (fun q => color q = c)
  let group : ℕ → Ctx.Context := fun c => ({ σ with
    word := (List.range σ.word.length).map (fun q => match σ.letterAt q with
      | Ctx.Letter.child => if q ∈ support c then Ctx.Letter.child
          else Ctx.Letter.ext (σ.maxima.length + 1) Ctx.Side.lower
      | Ctx.Letter.ext j v => Ctx.Letter.ext j v) } : Ctx.Context)
  let global : ℕ := match t with
    | Ctx.Side.lower => σ.u
    | Ctx.Side.upper => σ.a
  let active : ℕ → Finset ℕ := fun c =>
    (group c).childPositions.toFinset.filter
      (fun q => 0 < (group c).cupLimit q q ∧ 0 < (group c).capLimit q q)
  let interval : ℕ → ℕ → Finset ℕ := fun c q =>
    Finset.Icc ((group c).leftExt t 0 q + 1)
      (global - 1 - (group c).rightExt t 0 q)
  let pairs : ℕ → Finset (ℕ × ℕ) := fun c =>
    (active c).biUnion (fun q =>
      (((interval c q).product (interval c q)).filter (fun z => z.1 ≤ z.2)))
  let sourceInterval : ℕ → Finset ℕ := fun q =>
    Finset.Icc (σ.leftExt t 0 q + 1) (global - 1 - σ.rightExt t 0 q)
  have hChild (c q : ℕ) : q ∈ (group c).childPositions ↔
      q ∈ σ.childPositions ∧ color q = c := by
    have hh : (group c).childPositions =
        σ.childPositions.filter (· ∈ support c) :=
      (ctx_part_pruning_history_transport σ hpositive
        (support c) Ctx.Side.lower 0).2.1
    rw [hh]
    simp [support]
  have hLimits (c p q : ℕ) :
      (group c).cupLimit p q = σ.cupLimit p q ∧
        (group c).capLimit p q = σ.capLimit p q :=
    (ctx_part_pruning_history_transport σ hpositive
      (support c) Ctx.Side.lower 0).2.2.2.2.2.1 p q
  have hPure (c : ℕ) (v : Ctx.Side) (top q : ℕ) :
      (group c).leftExt v top q = σ.leftExt v top q ∧
        (group c).rightExt v top q = σ.rightExt v top q :=
    (ctx_part_pruning_history_transport σ hpositive
      (support c) Ctx.Side.lower 0).2.2.2.2.1 v top q
  have hActive (c q : ℕ) : q ∈ active c ↔
      q ∈ σ.childPositions ∧ 0 < σ.cupLimit q q ∧
        0 < σ.capLimit q q ∧ color q = c := by
    simp only [active, Finset.mem_filter, List.mem_toFinset, hChild,
      (hLimits c q q).1, (hLimits c q q).2]
    tauto
  have hInterval (c q : ℕ) : interval c q = sourceInterval q := by
    simp only [interval, sourceInterval, (hPure c t 0 q).1, (hPure c t 0 q).2]
  change ∀ z ∈ (pairs 0) ∩ (pairs 1), ∃ low high,
    low ∈ σ.childPositions ∧ 0 < σ.cupLimit low low ∧
      0 < σ.capLimit low low ∧ capacity low ≤ 2 ∧
    high ∈ σ.childPositions ∧ 0 < σ.cupLimit high high ∧
      0 < σ.capLimit high high ∧ 3 ≤ capacity high ∧
    z.1 ≤ z.2 ∧ z.1 ∈ sourceInterval low ∧ z.2 ∈ sourceInterval low ∧
      z.1 ∈ sourceInterval high ∧ z.2 ∈ sourceInterval high
  intro z hz
  have hz' := Finset.mem_inter.mp hz
  obtain ⟨low, hlowActive, hzLow⟩ := Finset.mem_biUnion.mp hz'.1
  obtain ⟨high, hhighActive, hzHigh⟩ := Finset.mem_biUnion.mp hz'.2
  have hlow := (hActive 0 low).mp hlowActive
  have hhigh := (hActive 1 high).mp hhighActive
  have hlowCapacity : capacity low ≤ 2 := by
    have hc := hlow.2.2.2
    dsimp only [color] at hc
    by_cases h : capacity low ≤ 2
    · exact h
    · simp [h] at hc
  have hhighCapacity : 3 ≤ capacity high := by
    have hc := hhigh.2.2.2
    dsimp only [color] at hc
    by_cases h : capacity high ≤ 2
    · simp [h] at hc
    · omega
  have hzLow' := Finset.mem_filter.mp hzLow
  have hzHigh' := Finset.mem_filter.mp hzHigh
  have hzLowProduct := Finset.mem_product.mp hzLow'.1
  have hzHighProduct := Finset.mem_product.mp hzHigh'.1
  rw [hInterval 0 low] at hzLowProduct
  rw [hInterval 1 high] at hzHighProduct
  exact ⟨low, high, hlow.1, hlow.2.1, hlow.2.2.1, hlowCapacity,
    hhigh.1, hhigh.2.1, hhigh.2.2.1, hhighCapacity, hzLow'.2,
    hzLowProduct.1, hzLowProduct.2, hzHighProduct.1, hzHighProduct.2⟩

end ErdosSzekeres
