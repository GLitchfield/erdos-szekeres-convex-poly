import ESBlueprint.B.CtxMixedCapacityChildrenMarkerSeparatedGlobalFive

namespace ErdosSzekeres

/-- When exactly two actual chosen positions occur on two ordered levels at global at most five, the older position separates any chosen-capacity-three child from any chosen-capacity-at-most-two child. The high child lies beyond every chosen marker, and the general mixed-capacity separator plus the two-occurrence classification puts the low child on the other side of the older marker. This makes the high and low supports simultaneously boundary-ready for a coupled potential. Exact searches in runs/sol-12h/search-mixed-capacity-older-marker.json found no duplicate.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_mixed_capacity_children_marker_separated_global_five, ErdosSzekeres.ctx_capacity_three_children_exterior_of_two_levels_global_five
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_mixed_capacity_children_separated_by_older_marker_global_five (σ : Ctx.Context) (s : Ctx.Side) (N M x y p q : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j, z = x ∨ z = y) (hp : p ∈ σ.childPositions) (hq : q ∈ σ.childPositions) (hhigh : 3 ≤ (match s with | Ctx.Side.lower => σ.cupLimit p p | Ctx.Side.upper => σ.capLimit p p)) (hlow : (match s with | Ctx.Side.lower => σ.cupLimit q q | Ctx.Side.upper => σ.capLimit q q) ≤ 2) : (x < y ∧ q < y ∧ y < p) ∨ (y < x ∧ p < y ∧ y < q) := by
  have hMOn : M ∈ σ.levelsOn s 0 :=
    List.mem_filter.mpr ⟨hM, by simp [hMs]⟩
  have hsep := ctx_mixed_capacity_children_marker_separated_global_five
    σ s N M x y p q hN hM hNM hNs hMs hx hy hglobal hp hq hhigh hlow
  rcases ctx_capacity_three_children_exterior_of_two_levels_global_five
      σ s N M x y hN hM hNM hNs hMs hx hy hglobal with hl | hr
  · refine Or.inl ⟨hl.1, ?_, hl.2 p hp hhigh M hMOn y hy⟩
    obtain ⟨j, hj, z, hz, hbetween⟩ := hsep
    rcases hbetween with hpz | hqz
    · have hzp := hl.2 p hp hhigh j hj z hz
      omega
    · rcases hchosen j hj z hz with hzx | hzy
      · omega
      · omega
  · refine Or.inr ⟨hr.1, hr.2 p hp hhigh M hMOn y hy, ?_⟩
    obtain ⟨j, hj, z, hz, hbetween⟩ := hsep
    rcases hbetween with hpz | hqz
    · rcases hchosen j hj z hz with hzx | hzy
      · omega
      · omega
    · have hpz := hr.2 p hp hhigh j hj z hz
      omega


end ErdosSzekeres
