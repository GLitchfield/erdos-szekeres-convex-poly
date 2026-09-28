import ESBlueprint.B.CtxTwoMarkerLowCapacityPruningSevenBoundOfHighWitness

namespace ErdosSzekeres

/-- With two exact chosen markers at global at most five and a capacity-three witness, prune to chosen capacity at most two. If an actual opposite-axis marker below the older chosen level lies strictly to one side of the entire low support, its endpoint reservation sharpens the retained-boundary doubled-rank budget from seven to five. Positive labels, arbitrary other history, both orientations, inactive children, multiple marker occurrences, and every fuel remain explicit.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_mixed_capacity_children_separated_by_older_marker_global_five, ErdosSzekeres.ctx_boundary_retained_doubled_rank_budget, ErdosSzekeres.ctx_part_pruning_history_transport
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_marker_low_capacity_pruning_five_bound_of_opposite_boundary (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N M x y high L z : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hchosenGlobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ w ∈ σ.extPositions j, w = x ∨ w = y) (hhighmem : high ∈ σ.childPositions) (hhigh : 3 ≤ (match s with | Ctx.Side.lower => σ.cupLimit high high | Ctx.Side.upper => σ.capLimit high high)) (hL : L ∈ σ.levels) (hLt : σ.sideAt L = t) (hz : z ∈ σ.extPositions L) (hLM : L < M) : let capacity := fun p => match s with | Ctx.Side.lower => σ.cupLimit p p | Ctx.Side.upper => σ.capLimit p p; let support := σ.childPositions.filter (fun p => capacity p ≤ 2); let low := ({ σ with word := (List.range σ.word.length).map (fun p => match σ.letterAt p with | Ctx.Letter.child => if p ∈ support then Ctx.Letter.child else Ctx.Letter.ext (σ.maxima.length + 1) Ctx.Side.lower | Ctx.Letter.ext j v => Ctx.Letter.ext j v) } : Ctx.Context); ((∀ q ∈ low.childPositions, q < z) ∨ (∀ q ∈ low.childPositions, z < q)) → (∀ fuel, Ctx.Context.boundFuel fuel low ≤ 5) ∧ low.bound ≤ 5 := by
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
  change ((∀ q ∈ low.childPositions, q < z) ∨
      (∀ q ∈ low.childPositions, z < q)) →
    (∀ fuel, Ctx.Context.boundFuel fuel low ≤ 5) ∧ low.bound ≤ 5
  intro hboundary
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
  have hLlow : L ∈ low.levels := hL
  have hNslow : low.sideAt N = s := (hHist N hN).2.trans hNs
  have hMslow : low.sideAt M = s := (hHist M hM).2.trans hMs
  have hLtlow : low.sideAt L = t := (hHist L hL).2.trans hLt
  have hxlow : x ∈ low.extPositions N := by
    rw [(hHist N hN).1]
    exact hx
  have hylow : y ∈ low.extPositions M := by
    rw [(hHist M hM).1]
    exact hy
  have hzlow : z ∈ low.extPositions L := by
    rw [(hHist L hL).1]
    exact hz
  have hOppositeLow : (match t with
      | Ctx.Side.lower => low.u
      | Ctx.Side.upper => low.a) ≤ 5 := by
    cases t <;> exact hopposite
  have hLOn : L ∈ low.levelsOn t M := by
    apply List.mem_filter.mpr
    refine ⟨hLlow, ?_⟩
    simp [hLtlow, hLM]
  have hOneLeft (q : ℕ) (hq : q ∈ low.childPositions) (hzq : z < q) :
      1 ≤ low.leftExt t M q := by
    have hm : z ∈ (low.extPositions L).filter (· < q) := by simp [hzlow, hzq]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := Ctx.le_getD_max?_of_mem
      (L := (low.levelsOn t M).sublists.map
        (fun ls => (ls.foldl (Ctx.Context.leftStep low) (q, 0)).2))
      (List.mem_map.mpr ⟨[L],
        List.mem_sublists.mpr (List.singleton_sublist.mpr hLOn), rfl⟩)
    change _ ≤ low.leftExt t M q at hv
    simpa only [List.foldl_cons, List.foldl_nil, Ctx.Context.leftStep,
      List.getLast?_eq_some_getLast hnonempty] using hv
  have hOneRight (q : ℕ) (hq : q ∈ low.childPositions) (hqz : q < z) :
      1 ≤ low.rightExt t M q := by
    have hm : z ∈ (low.extPositions L).filter (q < ·) := by simp [hzlow, hqz]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := Ctx.le_getD_max?_of_mem
      (L := (low.levelsOn t M).sublists.map
        (fun ls => (ls.foldl (Ctx.Context.rightStep low) (q, 0)).2))
      (List.mem_map.mpr ⟨[L],
        List.mem_sublists.mpr (List.singleton_sublist.mpr hLOn), rfl⟩)
    change _ ≤ low.rightExt t M q at hv
    simpa only [List.foldl_cons, List.foldl_nil, Ctx.Context.rightStep,
      List.head?_eq_some_head hnonempty] using hv
  have hAtLevel (j i w : ℕ) (hw : w ∈ σ.extPositions j)
      (hw' : w ∈ σ.extPositions i) : j = i := by
    have hj := (List.mem_filter.mp hw).2
    have hi := (List.mem_filter.mp hw').2
    cases he : σ.letterAt w <;> simp [he] at hj hi
    omega
  have hBound (direction : Bool)
      (hxy : if direction then x < y else y < x)
      (hlow : ∀ p ∈ low.childPositions,
        if direction then p < y else y < p) :
      (∀ fuel, Ctx.Context.boundFuel fuel low ≤ 5) ∧ low.bound ≤ 5 := by
    have hYoung : ∀ j ∈ low.levelsOn (low.sideAt M) M,
        ∀ w ∈ low.extPositions j,
          if direction then w < y else y < w := by
      rw [hMslow]
      intro j hj w hw
      rw [hLevels s M] at hj
      have hh := List.mem_filter.mp hj
      have hpred := of_decide_eq_true hh.2
      have hj0 : j ∈ σ.levelsOn s 0 :=
        List.mem_filter.mpr ⟨hh.1, by simp [hpred.1]⟩
      rw [(hHist j hh.1).1] at hw
      rcases hchosen j hj0 w hw with hwx | hwy
      · simpa only [hwx] using hxy
      · have he := hAtLevel j M y (by simpa only [hwy] using hw) hy
        omega
    rcases hboundary with hleft | hright
    · have hb := ctx_boundary_retained_doubled_rank_budget low hPos M N y x
        hMlow hNlow hNM hylow hxlow (hNslow.trans hMslow.symm) direction
        hlow hYoung t (hMslow.trans_ne hne) (by
          rw [hMslow]
          cases s <;> exact hchosenGlobal) 0 1 (by intros; omega)
        (fun q hq => hOneRight q hq (hleft q hq))
      cases ht : t with
      | lower =>
          have hb' : (∀ fuel, Ctx.Context.boundFuel fuel low ≤
                2 * (low.u - 1 - 0 - 1) - 1) ∧
              low.bound ≤ 2 * (low.u - 1 - 0 - 1) - 1 := by
            simpa only [ht] using hb
          have hFive : 2 * (low.u - 1 - 0 - 1) - 1 ≤ 5 := by
            have hOpp : low.u ≤ 5 := by simpa only [ht] using hOppositeLow
            omega
          exact ⟨fun fuel => (hb'.1 fuel).trans hFive, hb'.2.trans hFive⟩
      | upper =>
          have hb' : (∀ fuel, Ctx.Context.boundFuel fuel low ≤
                2 * (low.a - 1 - 0 - 1) - 1) ∧
              low.bound ≤ 2 * (low.a - 1 - 0 - 1) - 1 := by
            simpa only [ht] using hb
          have hFive : 2 * (low.a - 1 - 0 - 1) - 1 ≤ 5 := by
            have hOpp : low.a ≤ 5 := by simpa only [ht] using hOppositeLow
            omega
          exact ⟨fun fuel => (hb'.1 fuel).trans hFive, hb'.2.trans hFive⟩
    · have hb := ctx_boundary_retained_doubled_rank_budget low hPos M N y x
        hMlow hNlow hNM hylow hxlow (hNslow.trans hMslow.symm) direction
        hlow hYoung t (hMslow.trans_ne hne) (by
          rw [hMslow]
          cases s <;> exact hchosenGlobal) 1 0
        (fun q hq => hOneLeft q hq (hright q hq)) (by intros; omega)
      cases ht : t with
      | lower =>
          have hb' : (∀ fuel, Ctx.Context.boundFuel fuel low ≤
                2 * (low.u - 1 - 1 - 0) - 1) ∧
              low.bound ≤ 2 * (low.u - 1 - 1 - 0) - 1 := by
            simpa only [ht] using hb
          have hFive : 2 * (low.u - 1 - 1 - 0) - 1 ≤ 5 := by
            have hOpp : low.u ≤ 5 := by simpa only [ht] using hOppositeLow
            omega
          exact ⟨fun fuel => (hb'.1 fuel).trans hFive, hb'.2.trans hFive⟩
      | upper =>
          have hb' : (∀ fuel, Ctx.Context.boundFuel fuel low ≤
                2 * (low.a - 1 - 1 - 0) - 1) ∧
              low.bound ≤ 2 * (low.a - 1 - 1 - 0) - 1 := by
            simpa only [ht] using hb
          have hFive : 2 * (low.a - 1 - 1 - 0) - 1 ≤ 5 := by
            have hOpp : low.a ≤ 5 := by simpa only [ht] using hOppositeLow
            omega
          exact ⟨fun fuel => (hb'.1 fuel).trans hFive, hb'.2.trans hFive⟩
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
