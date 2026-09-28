import ESBlueprint.B.CtxCapacityThreeChildrenExteriorOfTwoLevelsGlobalFive
import ESBlueprint.B.CtxAxisRegionLimitsExact

namespace ErdosSzekeres

/-- A chosen-capacity-three child and a chosen-capacity-at-most-two child are separated by an actual indexed marker when two actual chosen levels occur at global at most five. Capacity-three exterior geometry places every chosen marker on one side of the high child; exact marker-region capacity constancy then forces the low child across at least one marker. This provides an explicit split marker for the remaining mixed-capacity companion obstruction. Exact searches in runs/sol-12h/search-mixed-capacity-marker-separation.json found no duplicate.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_capacity_three_children_exterior_of_two_levels_global_five, ErdosSzekeres.ctx_axis_region_limits_exact
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_mixed_capacity_children_marker_separated_global_five (σ : Ctx.Context) (s : Ctx.Side) (N M x y p q : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hp : p ∈ σ.childPositions) (hq : q ∈ σ.childPositions) (hhigh : 3 ≤ (match s with | Ctx.Side.lower => σ.cupLimit p p | Ctx.Side.upper => σ.capLimit p p)) (hlow : (match s with | Ctx.Side.lower => σ.cupLimit q q | Ctx.Side.upper => σ.capLimit q q) ≤ 2) : ∃ j, j ∈ σ.levelsOn s 0 ∧ ∃ z, z ∈ σ.extPositions j ∧ ((p < z ∧ z < q) ∨ (q < z ∧ z < p)) := by
  classical
  have hChildNe (r j z : ℕ) (hr : r ∈ σ.childPositions)
      (hz : z ∈ σ.extPositions j) : r ≠ z := by
    have hc := of_decide_eq_true (List.mem_filter.mp hr).2
    have he := (List.mem_filter.mp hz).2
    intro h
    subst z
    simp [hc] at he
  have hDifferentRegion : ¬(∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j,
      (z < p ↔ z < q) ∧ (p < z ↔ q < z)) := by
    intro hregion
    have heq := (ctx_axis_region_limits_exact σ s p q hregion).2.2.2
    cases s <;> simp only at hhigh hlow heq <;> omega
  rcases ctx_capacity_three_children_exterior_of_two_levels_global_five
      σ s N M x y hN hM hNM hNs hMs hx hy hglobal with hl | hr
  · have hsep : ∃ j, j ∈ σ.levelsOn s 0 ∧ ∃ z, z ∈ σ.extPositions j ∧
        q < z ∧ z < p := by
      by_contra hn
      apply hDifferentRegion
      intro j hj z hz
      have hzp := hl.2 p hp hhigh j hj z hz
      have hnqz : ¬q < z := by
        intro hqz
        exact hn ⟨j, hj, z, hz, hqz, hzp⟩
      have hzq : z < q := by
        have hne := hChildNe q j z hq hz
        omega
      constructor <;> constructor <;> intro <;> omega
    obtain ⟨j, hj, z, hz, hqz, hzp⟩ := hsep
    exact ⟨j, hj, z, hz, Or.inr ⟨hqz, hzp⟩⟩
  · have hsep : ∃ j, j ∈ σ.levelsOn s 0 ∧ ∃ z, z ∈ σ.extPositions j ∧
        p < z ∧ z < q := by
      by_contra hn
      apply hDifferentRegion
      intro j hj z hz
      have hpz := hr.2 p hp hhigh j hj z hz
      have hnzq : ¬z < q := by
        intro hzq
        exact hn ⟨j, hj, z, hz, hpz, hzq⟩
      have hqz : q < z := by
        have hne := hChildNe q j z hq hz
        omega
      constructor <;> constructor <;> intro <;> omega
    obtain ⟨j, hj, z, hz, hpz, hzq⟩ := hsep
    exact ⟨j, hj, z, hz, Or.inl ⟨hpz, hzq⟩⟩


end ErdosSzekeres
