import ESBlueprint.B.CtxTwoMarkerLowCapacityPruningFiveBoundOfOppositeBoundary

set_option maxHeartbeats 20000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

/-- The two-marker low-capacity pruning has bound five when the actual opposite-axis marker lies to one side of every active low child; inactive low children are first removed without decreasing the source bound.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_mixed_capacity_children_separated_by_older_marker_global_five, ErdosSzekeres.ctx_boundary_retained_doubled_rank_budget, ErdosSzekeres.ctx_part_pruning_history_transport, ErdosSzekeres.ctx_bound_le_inactive_prune_capacity_three
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_marker_low_capacity_pruning_five_bound_of_active_opposite_boundary (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N M x y high L z : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hchosenGlobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ w ∈ σ.extPositions j, w = x ∨ w = y) (hhighmem : high ∈ σ.childPositions) (hhigh : 3 ≤ (match s with | Ctx.Side.lower => σ.cupLimit high high | Ctx.Side.upper => σ.capLimit high high)) (hL : L ∈ σ.levels) (hLt : σ.sideAt L = t) (hz : z ∈ σ.extPositions L) (hLM : L < M) : let capacity := fun p => match s with | Ctx.Side.lower => σ.cupLimit p p | Ctx.Side.upper => σ.capLimit p p; let support := σ.childPositions.filter (fun p => capacity p ≤ 2); let low := ({ σ with word := (List.range σ.word.length).map (fun p => match σ.letterAt p with | Ctx.Letter.child => if p ∈ support then Ctx.Letter.child else Ctx.Letter.ext (σ.maxima.length + 1) Ctx.Side.lower | Ctx.Letter.ext j v => Ctx.Letter.ext j v) } : Ctx.Context); ((∀ q ∈ low.childPositions, 0 < low.cupLimit q q ∧ 0 < low.capLimit q q → q < z) ∨ (∀ q ∈ low.childPositions, 0 < low.cupLimit q q ∧ 0 < low.capLimit q q → z < q)) → (∀ fuel, Ctx.Context.boundFuel fuel low ≤ 5) ∧ low.bound ≤ 5 := by
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
  change ((∀ q ∈ low.childPositions,
      0 < low.cupLimit q q ∧ 0 < low.capLimit q q → q < z) ∨
      (∀ q ∈ low.childPositions,
        0 < low.cupLimit q q ∧ 0 < low.capLimit q q → z < q)) →
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
  have hLimits := ht.2.2.2.2.2.1
  have hChild (p : ℕ) : p ∈ low.childPositions ↔
      p ∈ σ.childPositions ∧ C p ≤ 2 := by
    rw [hChildEq]
    simp [support]
  have hSmall : ∀ p ∈ low.childPositions,
      min (low.cupLimit p p) (low.capLimit p p) ≤ 3 := by
    intro p hp
    have hc := (hChild p).mp hp
    have hl := hLimits p p
    cases s <;> simp only [C] at hc <;> omega
  let keep := low.childPositions.filter
    (fun p => 0 < low.cupLimit p p ∧ 0 < low.capLimit p p)
  let live : Ctx.Context := { low with
    word := (List.range low.word.length).map (fun p => match low.letterAt p with
      | Ctx.Letter.child => if p ∈ keep then Ctx.Letter.child
          else Ctx.Letter.ext (low.maxima.length + 1) Ctx.Side.lower
      | Ctx.Letter.ext j v => Ctx.Letter.ext j v) }
  have hm := ctx_bound_le_inactive_prune_capacity_three low hPos hSmall
  change (∀ fuel, Ctx.Context.boundFuel fuel low ≤ live.bound) ∧
    low.bound ≤ live.bound at hm
  have hu := ctx_part_pruning_history_transport low hPos keep
    Ctx.Side.lower 0
  change (∀ p j v, live.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) ∧
      live.childPositions = low.childPositions.filter (· ∈ keep) ∧
      (∀ j ∈ low.levels,
        live.extPositions j = low.extPositions j ∧ live.sideAt j = low.sideAt j) ∧
      (∀ v top, live.levelsOn v top = low.levelsOn v top) ∧
      (∀ v top p, live.leftExt v top p = low.leftExt v top p ∧
        live.rightExt v top p = low.rightExt v top p) ∧
      (∀ p q, live.cupLimit p q = low.cupLimit p q ∧
        live.capLimit p q = low.capLimit p q) ∧ _ at hu
  have hLivePos := hu.1
  have hLiveChildEq := hu.2.1
  have hLiveHist := hu.2.2.1
  have hLiveLevels := hu.2.2.2.1
  have hLiveLimits := hu.2.2.2.2.2.1
  have hLiveChild (p : ℕ) : p ∈ live.childPositions ↔
      p ∈ low.childPositions ∧
        0 < low.cupLimit p p ∧ 0 < low.capLimit p p := by
    rw [hLiveChildEq]
    simp only [keep, List.mem_filter, decide_eq_true_eq]
    tauto
  have hLiveHistSigma (j : ℕ) (hj : j ∈ σ.levels) :
      live.extPositions j = σ.extPositions j ∧
        live.sideAt j = σ.sideAt j := by
    have hjlow : j ∈ low.levels := hj
    exact ⟨(hLiveHist j hjlow).1.trans (hHist j hj).1,
      (hLiveHist j hjlow).2.trans (hHist j hj).2⟩
  have hLiveLevelsSigma (v : Ctx.Side) (top : ℕ) :
      live.levelsOn v top = σ.levelsOn v top :=
    (hLiveLevels v top).trans (hLevels v top)
  have hNlive : N ∈ live.levels := hN
  have hMlive : M ∈ live.levels := hM
  have hLlive : L ∈ live.levels := hL
  have hNslive : live.sideAt N = s :=
    (hLiveHistSigma N hN).2.trans hNs
  have hMslive : live.sideAt M = s :=
    (hLiveHistSigma M hM).2.trans hMs
  have hLtlive : live.sideAt L = t :=
    (hLiveHistSigma L hL).2.trans hLt
  have hxlive : x ∈ live.extPositions N := by
    rw [(hLiveHistSigma N hN).1]
    exact hx
  have hylive : y ∈ live.extPositions M := by
    rw [(hLiveHistSigma M hM).1]
    exact hy
  have hzlive : z ∈ live.extPositions L := by
    rw [(hLiveHistSigma L hL).1]
    exact hz
  have hOppositeLive : (match t with
      | Ctx.Side.lower => live.u
      | Ctx.Side.upper => live.a) ≤ 5 := by
    cases t <;> exact hopposite
  have hLOn : L ∈ live.levelsOn t M := by
    apply List.mem_filter.mpr
    refine ⟨hLlive, ?_⟩
    simp [hLtlive, hLM]
  have hOneLeft (q : ℕ) (hq : q ∈ live.childPositions) (hzq : z < q) :
      1 ≤ live.leftExt t M q := by
    have hmem : z ∈ (live.extPositions L).filter (· < q) := by
      simp [hzlive, hzq]
    have hnonempty := List.ne_nil_of_mem hmem
    have hv := Ctx.le_getD_max?_of_mem
      (L := (live.levelsOn t M).sublists.map
        (fun ls => (ls.foldl (Ctx.Context.leftStep live) (q, 0)).2))
      (List.mem_map.mpr ⟨[L],
        List.mem_sublists.mpr (List.singleton_sublist.mpr hLOn), rfl⟩)
    change _ ≤ live.leftExt t M q at hv
    simpa only [List.foldl_cons, List.foldl_nil, Ctx.Context.leftStep,
      List.getLast?_eq_some_getLast hnonempty] using hv
  have hOneRight (q : ℕ) (hq : q ∈ live.childPositions) (hqz : q < z) :
      1 ≤ live.rightExt t M q := by
    have hmem : z ∈ (live.extPositions L).filter (q < ·) := by
      simp [hzlive, hqz]
    have hnonempty := List.ne_nil_of_mem hmem
    have hv := Ctx.le_getD_max?_of_mem
      (L := (live.levelsOn t M).sublists.map
        (fun ls => (ls.foldl (Ctx.Context.rightStep live) (q, 0)).2))
      (List.mem_map.mpr ⟨[L],
        List.mem_sublists.mpr (List.singleton_sublist.mpr hLOn), rfl⟩)
    change _ ≤ live.rightExt t M q at hv
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
      (hlow : ∀ p ∈ live.childPositions,
        if direction then p < y else y < p) :
      (∀ fuel, Ctx.Context.boundFuel fuel live ≤ 5) ∧ live.bound ≤ 5 := by
    have hYoung : ∀ j ∈ live.levelsOn (live.sideAt M) M,
        ∀ w ∈ live.extPositions j,
          if direction then w < y else y < w := by
      rw [hMslive]
      intro j hj w hw
      rw [hLiveLevelsSigma s M] at hj
      have hh := List.mem_filter.mp hj
      have hpred := of_decide_eq_true hh.2
      have hj0 : j ∈ σ.levelsOn s 0 :=
        List.mem_filter.mpr ⟨hh.1, by simp [hpred.1]⟩
      rw [(hLiveHistSigma j hh.1).1] at hw
      rcases hchosen j hj0 w hw with hwx | hwy
      · simpa only [hwx] using hxy
      · have he := hAtLevel j M y (by simpa only [hwy] using hw) hy
        omega
    rcases hboundary with hleft | hright
    · have hb := ctx_boundary_retained_doubled_rank_budget live hLivePos M N y x
        hMlive hNlive hNM hylive hxlive (hNslive.trans hMslive.symm) direction
        hlow hYoung t (hMslive.trans_ne hne) (by
          rw [hMslive]
          cases s <;> exact hchosenGlobal) 0 1 (by intros; omega)
        (fun q hq => hOneRight q hq (hleft q ((hLiveChild q).mp hq).1
          ((hLiveChild q).mp hq).2))
      cases ht' : t with
      | lower =>
          have hb' : (∀ fuel, Ctx.Context.boundFuel fuel live ≤
                2 * (live.u - 1 - 0 - 1) - 1) ∧
              live.bound ≤ 2 * (live.u - 1 - 0 - 1) - 1 := by
            simpa only [ht'] using hb
          have hFive : 2 * (live.u - 1 - 0 - 1) - 1 ≤ 5 := by
            have hOpp : live.u ≤ 5 := by
              simpa only [ht'] using hOppositeLive
            omega
          exact ⟨fun fuel => (hb'.1 fuel).trans hFive, hb'.2.trans hFive⟩
      | upper =>
          have hb' : (∀ fuel, Ctx.Context.boundFuel fuel live ≤
                2 * (live.a - 1 - 0 - 1) - 1) ∧
              live.bound ≤ 2 * (live.a - 1 - 0 - 1) - 1 := by
            simpa only [ht'] using hb
          have hFive : 2 * (live.a - 1 - 0 - 1) - 1 ≤ 5 := by
            have hOpp : live.a ≤ 5 := by
              simpa only [ht'] using hOppositeLive
            omega
          exact ⟨fun fuel => (hb'.1 fuel).trans hFive, hb'.2.trans hFive⟩
    · have hb := ctx_boundary_retained_doubled_rank_budget live hLivePos M N y x
        hMlive hNlive hNM hylive hxlive (hNslive.trans hMslive.symm) direction
        hlow hYoung t (hMslive.trans_ne hne) (by
          rw [hMslive]
          cases s <;> exact hchosenGlobal) 1 0
        (fun q hq => hOneLeft q hq (hright q ((hLiveChild q).mp hq).1
          ((hLiveChild q).mp hq).2)) (by intros; omega)
      cases ht' : t with
      | lower =>
          have hb' : (∀ fuel, Ctx.Context.boundFuel fuel live ≤
                2 * (live.u - 1 - 1 - 0) - 1) ∧
              live.bound ≤ 2 * (live.u - 1 - 1 - 0) - 1 := by
            simpa only [ht'] using hb
          have hFive : 2 * (live.u - 1 - 1 - 0) - 1 ≤ 5 := by
            have hOpp : live.u ≤ 5 := by
              simpa only [ht'] using hOppositeLive
            omega
          exact ⟨fun fuel => (hb'.1 fuel).trans hFive, hb'.2.trans hFive⟩
      | upper =>
          have hb' : (∀ fuel, Ctx.Context.boundFuel fuel live ≤
                2 * (live.a - 1 - 1 - 0) - 1) ∧
              live.bound ≤ 2 * (live.a - 1 - 1 - 0) - 1 := by
            simpa only [ht'] using hb
          have hFive : 2 * (live.a - 1 - 1 - 0) - 1 ≤ 5 := by
            have hOpp : live.a ≤ 5 := by
              simpa only [ht'] using hOppositeLive
            omega
          exact ⟨fun fuel => (hb'.1 fuel).trans hFive, hb'.2.trans hFive⟩
  have hFinish (direction : Bool)
      (hxy : if direction then x < y else y < x)
      (hlow : ∀ p ∈ live.childPositions,
        if direction then p < y else y < p) :
      (∀ fuel, Ctx.Context.boundFuel fuel low ≤ 5) ∧ low.bound ≤ 5 := by
    have hb := hBound direction hxy hlow
    exact ⟨fun fuel => (hm.1 fuel).trans hb.2, hm.2.trans hb.2⟩
  rcases ctx_capacity_three_children_exterior_of_two_levels_global_five
      σ s N M x y hN hM hNM hNs hMs hx hy hchosenGlobal with horient | horient
  · apply hFinish true
    · simpa only [if_true] using horient.1
    · intro q hq
      have hqLive := (hLiveChild q).mp hq
      have hqData := (hChild q).mp hqLive.1
      have hsep := ctx_mixed_capacity_children_separated_by_older_marker_global_five
        σ s N M x y high q hN hM hNM hNs hMs hx hy hchosenGlobal hchosen
        hhighmem hqData.1 hhigh hqData.2
      rcases hsep with hh | hh
      · simpa only [if_true] using hh.2.1
      · omega
  · apply hFinish false
    · simpa only [if_false] using horient.1
    · intro q hq
      have hqLive := (hLiveChild q).mp hq
      have hqData := (hChild q).mp hqLive.1
      have hsep := ctx_mixed_capacity_children_separated_by_older_marker_global_five
        σ s N M x y high q hN hM hNM hNs hMs hx hy hchosenGlobal hchosen
        hhighmem hqData.1 hhigh hqData.2
      rcases hsep with hh | hh
      · omega
      · simpa only [if_false] using hh.2.2

end ErdosSzekeres
