import ESBlueprint.B.CtxUnitAxisActiveRegionPotential

namespace ErdosSzekeres

/-- A context with unit pointwise capacity on one axis has bound at most one when every pair of children has a clear interval on that axis. Allows arbitrarily many physical runs separated on the opposite side, empty child sets, and unused levels; positive external labels suffice. Consumes the active-region potential: all child marker labels agree, so there is at most one active region. Supplies the degenerate opposite-axis case in small-capacity interval-complement additivity.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_bound_le_one_of_clear_unit_axis (σ : Ctx.Context)
  (hpositive : ∀ x l t, σ.letterAt x = Ctx.Letter.ext l t → 1 ≤ l)
  (s : Ctx.Side)
  (hunit : ∀ p ∈ σ.childPositions,
    (match s with
      | Ctx.Side.lower => σ.cupLimit p p
      | Ctx.Side.upper => σ.capLimit p p) ≤ 1)
  (hclear : ∀ p ∈ σ.childPositions, ∀ q ∈ σ.childPositions,
    ∀ l ∈ σ.levelsOn s 0, ∀ x ∈ σ.extPositions l,
      x < min p q ∨ max p q < x) :
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ 1) ∧ σ.bound ≤ 1 := by
  classical
  let markers : Finset ℕ := (σ.levelsOn s 0).toFinset.biUnion
    (fun l => (σ.extPositions l).toFinset)
  let active : Finset ℕ := σ.childPositions.toFinset.filter
    (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
  let label (p : ℕ) := (markers.filter (· < p)).card
  have hlabel (p q : ℕ) (hp : p ∈ σ.childPositions) (hq : q ∈ σ.childPositions) :
      label p = label q := by
    apply congrArg Finset.card
    apply Finset.ext
    intro x
    simp only [Finset.mem_filter]
    have hout (hx : x ∈ markers) : x < min p q ∨ max p q < x := by
      obtain ⟨l, hl, hx⟩ := Finset.mem_biUnion.mp hx
      exact hclear p hp q hq l (List.mem_toFinset.mp hl) x (List.mem_toFinset.mp hx)
    constructor <;> intro hx
    · exact ⟨hx.1, by have := hout hx.1; omega⟩
    · exact ⟨hx.1, by have := hout hx.1; omega⟩
  have hcard : (active.image label).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
    exact hlabel p q
      (List.mem_toFinset.mp (Finset.mem_filter.mp hp).1)
      (List.mem_toFinset.mp (Finset.mem_filter.mp hq).1)
  have h := ctx_unit_axis_active_region_potential σ hpositive s hunit
  change (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ (active.image label).card) ∧
    σ.bound ≤ (active.image label).card ∧ (active.image label).card ≤ σ.numRuns at h
  exact ⟨fun fuel => (h.1 fuel).trans hcard, h.2.1.trans hcard⟩

end ErdosSzekeres
