import ErdosSzekeres.DecomposableContext
import ESBlueprint.B.CtxThinRankRectangleContextCoverPotential

set_option maxHeartbeats 8000000
set_option maxRecDepth 15000
open ErdosSzekeres.Ctx ErdosSzekeres.Ctx.Context


namespace ErdosSzekeres

/-- Bound every fuel approximation and the full context by three opposite widths minus two when chosen global is at most five, every chosen maximum is at most k-5, and active chosen point capacities are at most two. Cutoff inclusion proves that these capacities equal their pure chain capacities; the thin rectangle cover then applies. Positive physical labels, distinct axes, chosen global at most five, k at least five and opposite width at least one. Every indexed chosen-axis maximum is at most k-5, and every active chosen point capacity is at most two. Arbitrary history depth, marker positions, inactive children and opposite maxima. No actual-marker, recursive-potential or cut-bound premise.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_small_maxima_active_capacity_two_linear_potential (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
  (hk : 5 ≤ σ.k)
  (hmax : ∀ j ∈ σ.levelsOn s 0, σ.maximumAt j ≤ σ.k-5)
  (hsmall : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p → 0 < σ.capLimit p p →
    (match s with | Ctx.Side.lower => σ.cupLimit p p | Ctx.Side.upper => σ.capLimit p p) ≤ 2)
  (hwidth : 1 ≤ (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1) :
  let w := (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ 3*w-2) ∧ σ.bound ≤ 3*w-2 := by
  classical
  let G (v : Side) := match v with | Side.lower => σ.u | Side.upper => σ.a
  let w := G t - 1
  let active := σ.childPositions.toFinset.filter (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
  let ranks (v : Side) (p : ℕ) := Finset.Icc (σ.leftExt v 0 p + 1) (G v - 1 - σ.rightExt v 0 p)
  let cost (I : Finset ℕ) := if I = ∅ then 0 else
    ((I.biUnion (ranks s)).card - 1) * ((I.biUnion (ranks t)).card - 1) + 1
  change (∀ fuel, boundFuel fuel σ ≤ 3 * w - 2) ∧ σ.bound ≤ 3 * w - 2
  have hw : 1 ≤ w := hwidth
  have hg : G s ≤ 5 := hglobal
  have hCutoff (ρ : Context) (v : Side) (top : ℕ) :
      (ρ.levelsOn v top).Sublist (ρ.levelsOn v 0) := by
    have he : ρ.levelsOn v top =
        (ρ.levelsOn v 0).filter (fun j => decide (top = 0 ∨ j < top)) := by
      simp only [levelsOn, List.filter_filter]
      apply List.filter_congr
      intro j _
      simp [Bool.and_comm]
    rw [he]
    exact List.filter_sublist
  have hLeftCutoff (ρ : Context) (v : Side) (top z : ℕ) :
      ρ.leftExt v top z ≤ ρ.leftExt v 0 z := by
    simp only [leftExt_eq]
    apply getD_max?_le_of_forall
    intro value hv
    obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hv
    exact ⟨_, List.mem_map.mpr ⟨ls,
      List.mem_sublists.mpr ((List.mem_sublists.mp hls).trans (hCutoff ρ v top)), rfl⟩, le_rfl⟩
  have hRightCutoff (ρ : Context) (v : Side) (top z : ℕ) :
      ρ.rightExt v top z ≤ ρ.rightExt v 0 z := by
    simp only [rightExt_eq]
    apply getD_max?_le_of_forall
    intro value hv
    obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hv
    exact ⟨_, List.mem_map.mpr ⟨ls,
      List.mem_sublists.mpr ((List.mem_sublists.mp hls).trans (hCutoff ρ v top)), rfl⟩, le_rfl⟩
  have hJoin (p : ℕ) : σ.joinExt s p p ≤ σ.chainExt s p p + (σ.k-5) := by
    unfold joinExt
    apply max_le
    · omega
    · apply getD_max?_le
      intro value hv
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hv
      have hl := hLeftCutoff σ s j p
      have hr := hRightCutoff σ s j p
      have hm := hmax j hj
      dsimp only [chainExt]
      omega
  have hPureCapacity (p : ℕ) :
      (match s with | Side.lower => σ.cupLimit p p | Side.upper => σ.capLimit p p) =
        G s - 1 - σ.chainExt s p p := by
    have hj := hJoin p
    cases s <;> simp only [cupLimit, capLimit, G] at hg ⊢ <;> omega
  have hThin : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p → 0 < σ.capLimit p p →
      G s - 1 - σ.rightExt s 0 p ≤ σ.leftExt s 0 p + 2 := by
    intro p hp hc hu
    have hh := hsmall p hp hc hu
    have he := hPureCapacity p
    cases s <;> simp only [G, chainExt] at he hh ⊢ <;> omega
  have hCover := ctx_thin_rank_rectangle_context_cover_potential σ hpositive s t hne
    (by cases s <;> exact hThin)
    [active] (fun p hp => ⟨active, by simp, hp⟩)
    (by intro I hI; have he := List.mem_singleton.mp hI; subst I; exact Finset.Subset.refl _)
  change (∀ fuel, boundFuel fuel σ ≤ ([active].map cost).sum) ∧
    σ.bound ≤ ([active].map cost).sum at hCover
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at hCover
  have hBudget : cost active ≤ 3 * w - 2 := by
    by_cases hEmpty : active = ∅
    · simp only [cost, if_pos hEmpty]
      exact Nat.zero_le _
    have hRankSub (v : Side) : active.biUnion (ranks v) ⊆ Finset.Icc 1 (G v - 1) := by
      intro z hz
      obtain ⟨p, _, hz⟩ := Finset.mem_biUnion.mp hz
      have hh := Finset.mem_Icc.mp hz
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hRankCard (v : Side) : (active.biUnion (ranks v)).card ≤ G v - 1 := by
      simpa only [Nat.card_Icc, Nat.add_sub_cancel] using Finset.card_le_card (hRankSub v)
    have hxCard : (active.biUnion (ranks s)).card - 1 ≤ 3 := by
      have hh := hRankCard s
      omega
    have hyCard : (active.biUnion (ranks t)).card - 1 ≤ w - 1 := by
      have hh := hRankCard t
      dsimp only [w]
      omega
    have hh := Nat.mul_le_mul hxCard hyCard
    have he : 3 * (w - 1) + 1 = 3 * w - 2 := by omega
    simp only [cost, if_neg hEmpty]
    omega
  exact ⟨fun fuel => (hCover.1 fuel).trans hBudget, hCover.2.trans hBudget⟩


end ErdosSzekeres
