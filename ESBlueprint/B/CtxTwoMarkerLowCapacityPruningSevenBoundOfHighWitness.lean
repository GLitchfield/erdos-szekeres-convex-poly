import ESBlueprint.B.CtxBoundaryRetainedDoubledRankBudget
import ESBlueprint.B.CtxMixedCapacityChildrenSeparatedByOlderMarkerGlobalFive
import ESBlueprint.B.CtxPartPruningHistoryTransport

set_option maxHeartbeats 4000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

/-- With two exact chosen markers at global at most five and one chosen-capacity-three child, the canonical original-history pruning to all chosen-capacity-at-most-two children is bounded by seven when the opposite global is at most five. The older marker separates the entire low support from the high witness; absorbing that boundary leaves the younger actual marker in a chosen-global-four context, so the refined one-level doubled-rank budget applies. This exports a strict low-arm charge for the sole mixed-support k-six extreme residual.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_mixed_capacity_children_separated_by_older_marker_global_five, ErdosSzekeres.ctx_boundary_retained_doubled_rank_budget, ErdosSzekeres.ctx_part_pruning_history_transport
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_marker_low_capacity_pruning_seven_bound_of_high_witness (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N M x y high : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hchosenGlobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j, z = x ∨ z = y) (hhighmem : high ∈ σ.childPositions) (hhigh : 3 ≤ (match s with | Ctx.Side.lower => σ.cupLimit high high | Ctx.Side.upper => σ.capLimit high high)) : let capacity := fun p => match s with | Ctx.Side.lower => σ.cupLimit p p | Ctx.Side.upper => σ.capLimit p p; let support := σ.childPositions.filter (fun p => capacity p ≤ 2); let low := ({ σ with word := (List.range σ.word.length).map (fun p => match σ.letterAt p with | Ctx.Letter.child => if p ∈ support then Ctx.Letter.child else Ctx.Letter.ext (σ.maxima.length + 1) Ctx.Side.lower | Ctx.Letter.ext j v => Ctx.Letter.ext j v) } : Ctx.Context); (∀ fuel, Ctx.Context.boundFuel fuel low ≤ 7) ∧ low.bound ≤ 7 := by
  classical
  let C (p : ℕ) := match s with
    | Ctx.Side.lower => σ.cupLimit p p
    | Ctx.Side.upper => σ.capLimit p p
  let support := σ.childPositions.filter (fun p => C p ≤ 2)
  let low : Ctx.Context := { σ with
    word := (List.range σ.word.length).map (fun p => match σ.letterAt p with
      | Ctx.Letter.child => if p ∈ support then Ctx.Letter.child
          else Ctx.Letter.ext (σ.maxima.length + 1) Ctx.Side.lower
      | Ctx.Letter.ext j v => Ctx.Letter.ext j v) }
  change (∀ fuel, Ctx.Context.boundFuel fuel low ≤ 7) ∧ low.bound ≤ 7
  have ht := ctx_part_pruning_history_transport σ hpositive support
    Ctx.Side.lower 0
  change (∀ p j v, low.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) ∧
      low.childPositions = σ.childPositions.filter (· ∈ support) ∧
      (∀ j ∈ σ.levels,
        low.extPositions j = σ.extPositions j ∧ low.sideAt j = σ.sideAt j) ∧
      (∀ v top, low.levelsOn v top = σ.levelsOn v top) ∧
      (∀ v top p, low.leftExt v top p = σ.leftExt v top p ∧
        low.rightExt v top p = σ.rightExt v top p) ∧
      (∀ p q, low.cupLimit p q = σ.cupLimit p q ∧
        low.capLimit p q = σ.capLimit p q) ∧ _ at ht
  have hPos := ht.1
  have hChildEq := ht.2.1
  have hHist := ht.2.2.1
  have hLevels := ht.2.2.2.1
  have hChild (p : ℕ) : p ∈ low.childPositions ↔
      p ∈ σ.childPositions ∧ C p ≤ 2 := by
    rw [hChildEq]
    simp [support]
  have hNlow : N ∈ low.levels := hN
  have hMlow : M ∈ low.levels := hM
  have hNslow : low.sideAt N = s := (hHist N hN).2.trans hNs
  have hMslow : low.sideAt M = s := (hHist M hM).2.trans hMs
  have hxlow : x ∈ low.extPositions N := by
    rw [(hHist N hN).1]
    exact hx
  have hylow : y ∈ low.extPositions M := by
    rw [(hHist M hM).1]
    exact hy
  have hAtLevel (j i z : ℕ) (hz : z ∈ σ.extPositions j)
      (hz' : z ∈ σ.extPositions i) : j = i := by
    have hj := (List.mem_filter.mp hz).2
    have hi := (List.mem_filter.mp hz').2
    cases he : σ.letterAt z <;> simp [he] at hj hi
    omega
  have hBound (direction : Bool)
      (hxy : if direction then x < y else y < x)
      (hlow : ∀ p ∈ low.childPositions,
        if direction then p < y else y < p) :
      (∀ fuel, Ctx.Context.boundFuel fuel low ≤ 7) ∧ low.bound ≤ 7 := by
    have hYoung : ∀ j ∈ low.levelsOn (low.sideAt M) M,
        ∀ z ∈ low.extPositions j,
          if direction then z < y else y < z := by
      rw [hMslow]
      intro j hj z hz
      rw [hLevels s M] at hj
      have hh := List.mem_filter.mp hj
      have hpred := of_decide_eq_true hh.2
      have hj0 : j ∈ σ.levelsOn s 0 :=
        List.mem_filter.mpr ⟨hh.1, by simp [hpred.1]⟩
      rw [(hHist j hh.1).1] at hz
      rcases hchosen j hj0 z hz with hzx | hzy
      · simpa only [hzx] using hxy
      · have he := hAtLevel j M y (by simpa only [hzy] using hz) hy
        omega
    have hb := ctx_boundary_retained_doubled_rank_budget low hPos M N y x
      hMlow hNlow hNM hylow hxlow (hNslow.trans hMslow.symm) direction
      hlow hYoung t (hMslow.trans_ne hne) (by
        rw [hMslow]
        cases s <;> exact hchosenGlobal) 0 0 (by intros; omega) (by intros; omega)
    have hSeven : 2 * ((match t with
        | Ctx.Side.lower => low.u
        | Ctx.Side.upper => low.a) - 1) - 1 ≤ 7 := by
      cases t <;> simp only [low] at hopposite ⊢ <;> omega
    simpa only [Nat.sub_zero] using
      And.intro (fun fuel => (hb.1 fuel).trans hSeven) (hb.2.trans hSeven)
  rcases ctx_capacity_three_children_exterior_of_two_levels_global_five
      σ s N M x y hN hM hNM hNs hMs hx hy hchosenGlobal with horient | horient
  · apply hBound true
    · simpa only [if_true] using horient.1
    · intro q hq
      have hqData := (hChild q).mp hq
      have hsep := ctx_mixed_capacity_children_separated_by_older_marker_global_five
        σ s N M x y high q hN hM hNM hNs hMs hx hy hchosenGlobal hchosen
        hhighmem hqData.1 hhigh hqData.2
      rcases hsep with hh | hh
      · simpa only [if_true] using hh.2.1
      · omega
  · apply hBound false
    · simpa only [if_false] using horient.1
    · intro q hq
      have hqData := (hChild q).mp hq
      have hsep := ctx_mixed_capacity_children_separated_by_older_marker_global_five
        σ s N M x y high q hN hM hNM hNs hMs hx hy hchosenGlobal hchosen
        hhighmem hqData.1 hhigh hqData.2
      rcases hsep with hh | hh
      · omega
      · simpa only [if_false] using hh.2.2

end ErdosSzekeres
