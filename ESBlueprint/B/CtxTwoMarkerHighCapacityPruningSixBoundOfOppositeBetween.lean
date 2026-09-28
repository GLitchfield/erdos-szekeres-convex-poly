import ESBlueprint.B.CtxTwoMarkerMixedCapacityPairOverlapExcessBound
import ESBlueprint.B.CtxActualMarkerOppositeRankIntervalEndpointExclusion

namespace ErdosSzekeres

/-- In a two-marker chosen-global-five context, prune to children of chosen capacity at least three. If an actual opposite-axis marker lies strictly between the two chosen markers, the common chosen-exterior geometry puts every retained child on one side of it, excluding one opposite endpoint rank. The active boundary rank-pair union therefore occupies only three ranks and every fuel and full high pruning are at most six. Arbitrary other positive history, inactive children, maxima, and both orientations remain explicit.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_capacity_three_children_exterior_of_two_levels_global_five, ErdosSzekeres.ctx_active_boundary_marker_rank_pair_union_bound, ErdosSzekeres.ctx_actual_marker_opposite_rank_interval_endpoint_exclusion, ErdosSzekeres.ctx_part_pruning_history_transport
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_marker_high_capacity_pruning_six_bound_of_opposite_between (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N M x y L z : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hchosenGlobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ w ∈ σ.extPositions j, w = x ∨ w = y) (hL : L ∈ σ.levels) (hLt : σ.sideAt L = t) (hz : z ∈ σ.extPositions L) (hbetween : (x < z ∧ z < y) ∨ (y < z ∧ z < x)) : let capacity := fun p => match s with | Ctx.Side.lower => σ.cupLimit p p | Ctx.Side.upper => σ.capLimit p p; let color := fun p => if capacity p ≤ 2 then (0 : ℕ) else 1; let support := fun c => σ.childPositions.filter (fun p => color p = c); let group := fun c => ({ σ with word := (List.range σ.word.length).map (fun p => match σ.letterAt p with | Ctx.Letter.child => if p ∈ support c then Ctx.Letter.child else Ctx.Letter.ext (σ.maxima.length + 1) Ctx.Side.lower | Ctx.Letter.ext j v => Ctx.Letter.ext j v) } : Ctx.Context); (∀ fuel, Ctx.Context.boundFuel fuel (group 1) ≤ 6) ∧ (group 1).bound ≤ 6 := by
  classical
  let C (p : ℕ) := match s with
    | Ctx.Side.lower => σ.cupLimit p p
    | Ctx.Side.upper => σ.capLimit p p
  let color (p : ℕ) := if C p ≤ 2 then (0 : ℕ) else 1
  let support (c : ℕ) := σ.childPositions.filter (fun p => color p = c)
  let group (c : ℕ) : Ctx.Context := { σ with
    word := (List.range σ.word.length).map (fun p => match σ.letterAt p with
      | Ctx.Letter.child => if p ∈ support c then Ctx.Letter.child
          else Ctx.Letter.ext (σ.maxima.length + 1) Ctx.Side.lower
      | Ctx.Letter.ext j v => Ctx.Letter.ext j v) }
  let G := match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a
  let active (c : ℕ) := (group c).childPositions.toFinset.filter
    (fun p => 0 < (group c).cupLimit p p ∧ 0 < (group c).capLimit p p)
  let I (c p : ℕ) := Finset.Icc ((group c).leftExt t 0 p + 1)
    (G - 1 - (group c).rightExt t 0 p)
  let Q (S : Finset ℕ) := (S.product S).filter (fun w => w.1 ≤ w.2)
  let pairs (c : ℕ) := (active c).biUnion (fun p => Q (I c p))
  change (∀ fuel, Ctx.Context.boundFuel fuel (group 1) ≤ 6) ∧
    (group 1).bound ≤ 6
  have hPos (c : ℕ) : ∀ p j v,
      (group c).letterAt p = Ctx.Letter.ext j v → 1 ≤ j :=
    (ctx_part_pruning_history_transport σ hpositive (support c)
      Ctx.Side.lower 0).1
  have hChild (c p : ℕ) : p ∈ (group c).childPositions ↔
      p ∈ σ.childPositions ∧ color p = c := by
    have hh := (ctx_part_pruning_history_transport σ hpositive (support c)
      Ctx.Side.lower 0).2.1
    change (group c).childPositions = σ.childPositions.filter (· ∈ support c) at hh
    rw [hh]
    simp [support]
  have hHist (c j : ℕ) (hj : j ∈ σ.levels) :
      (group c).extPositions j = σ.extPositions j ∧
        (group c).sideAt j = σ.sideAt j :=
    (ctx_part_pruning_history_transport σ hpositive (support c)
      Ctx.Side.lower 0).2.2.1 j hj
  have hLevels (c : ℕ) (v : Ctx.Side) (top : ℕ) :
      (group c).levelsOn v top = σ.levelsOn v top :=
    (ctx_part_pruning_history_transport σ hpositive (support c)
      Ctx.Side.lower 0).2.2.2.1 v top
  have hAtLevel (j i w : ℕ) (hw : w ∈ σ.extPositions j)
      (hw' : w ∈ σ.extPositions i) : j = i := by
    have hj := (List.mem_filter.mp hw).2
    have hi := (List.mem_filter.mp hw').2
    cases he : σ.letterAt w <;> simp [he] at hj hi
    omega
  have hNOn : N ∈ σ.levelsOn s 0 :=
    List.mem_filter.mpr ⟨hN, by simp [hNs]⟩
  have hNpos : 1 ≤ N := Ctx.Context.one_le_of_mem_levels hN
  have hNgroup : N ∈ (group 1).levels := hN
  have hLgroup : L ∈ (group 1).levels := hL
  have hxgroup : x ∈ (group 1).extPositions N := by
    rw [(hHist 1 N hN).1]
    exact hx
  have hzgroup : z ∈ (group 1).extPositions L := by
    rw [(hHist 1 L hL).1]
    exact hz
  have hNside : (group 1).sideAt N = s := (hHist 1 N hN).2.trans hNs
  have hLside : (group 1).sideAt L = t := (hHist 1 L hL).2.trans hLt
  have hLOn : L ∈ (group 1).levelsOn t 0 :=
    List.mem_filter.mpr ⟨hLgroup, by simp [hLside]⟩
  have hOneLeft (p : ℕ) (hp : p ∈ (group 1).childPositions) (hzp : z < p) :
      1 ≤ (group 1).leftExt t 0 p := by
    have hm : z ∈ ((group 1).extPositions L).filter (· < p) := by
      simp [hzgroup, hzp]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := Ctx.le_getD_max?_of_mem
      (L := ((group 1).levelsOn t 0).sublists.map
        (fun ls => (ls.foldl (Ctx.Context.leftStep (group 1)) (p, 0)).2))
      (List.mem_map.mpr ⟨[L],
        List.mem_sublists.mpr (List.singleton_sublist.mpr hLOn), rfl⟩)
    change _ ≤ (group 1).leftExt t 0 p at hv
    simpa only [List.foldl_cons, List.foldl_nil, Ctx.Context.leftStep,
      List.getLast?_eq_some_getLast hnonempty] using hv
  have hOneRight (p : ℕ) (hp : p ∈ (group 1).childPositions) (hpz : p < z) :
      1 ≤ (group 1).rightExt t 0 p := by
    have hm : z ∈ ((group 1).extPositions L).filter (p < ·) := by
      simp [hzgroup, hpz]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := Ctx.le_getD_max?_of_mem
      (L := ((group 1).levelsOn t 0).sublists.map
        (fun ls => (ls.foldl (Ctx.Context.rightStep (group 1)) (p, 0)).2))
      (List.mem_map.mpr ⟨[L],
        List.mem_sublists.mpr (List.singleton_sublist.mpr hLOn), rfl⟩)
    change _ ≤ (group 1).rightExt t 0 p at hv
    simpa only [List.foldl_cons, List.foldl_nil, Ctx.Context.rightStep,
      List.head?_eq_some_head hnonempty] using hv
  have hSmall : min ((match (group 1).sideAt N with
      | Ctx.Side.lower => (group 1).u
      | Ctx.Side.upper => (group 1).a) - 1)
      ((group 1).k - (group 1).maximumAt N) ≤ 4 := by
    apply (Nat.min_le_left _ _).trans
    rw [hNside]
    cases s <;> simp only [group] at hchosenGlobal ⊢ <;> omega
  have hHigh : (∀ fuel, Ctx.Context.boundFuel fuel (group 1) ≤ (pairs 1).card) ∧
      (group 1).bound ≤ (pairs 1).card := by
    rcases ctx_capacity_three_children_exterior_of_two_levels_global_five
        σ s N M x y hN hM hNM hNs hMs hx hy hchosenGlobal with horient | horient
    · have hb := ctx_active_boundary_marker_rank_pair_union_bound
          (group 1) (hPos 1) N x hNgroup hxgroup false
          (fun p hp _ => by
            have hpData := (hChild 1 p).mp hp
            have hcap : 3 ≤ C p := by
              have hc := hpData.2
              dsimp only [color] at hc
              by_cases hle : C p ≤ 2
              · simp [hle] at hc
              · omega
            have hout := horient.2 p hpData.1 hcap N hNOn x hx
            simpa using hout)
          (fun j hj w hw => by
            rw [hNside, hLevels 1 s N] at hj
            have hh := List.mem_filter.mp hj
            have hpred := of_decide_eq_true hh.2
            have hjN : j < N := by
              rcases hpred.2 with hzero | hlt
              · omega
              · exact hlt
            have hj0 : j ∈ σ.levelsOn s 0 :=
              List.mem_filter.mpr ⟨hh.1, by simp [hpred.1]⟩
            rw [(hHist 1 j hh.1).1] at hw
            rcases hchosen j hj0 w hw with hwx | hwy
            · have he := hAtLevel j N x (by simpa only [hwx] using hw) hx
              omega
            · simpa only [hwy, if_false] using horient.1)
          t (by rw [hNside]; exact hne) hSmall
      simpa only [pairs, active, Q, I, G] using hb
    · have hb := ctx_active_boundary_marker_rank_pair_union_bound
          (group 1) (hPos 1) N x hNgroup hxgroup true
          (fun p hp _ => by
            have hpData := (hChild 1 p).mp hp
            have hcap : 3 ≤ C p := by
              have hc := hpData.2
              dsimp only [color] at hc
              by_cases hle : C p ≤ 2
              · simp [hle] at hc
              · omega
            have hout := horient.2 p hpData.1 hcap N hNOn x hx
            simpa using hout)
          (fun j hj w hw => by
            rw [hNside, hLevels 1 s N] at hj
            have hh := List.mem_filter.mp hj
            have hpred := of_decide_eq_true hh.2
            have hjN : j < N := by
              rcases hpred.2 with hzero | hlt
              · omega
              · exact hlt
            have hj0 : j ∈ σ.levelsOn s 0 :=
              List.mem_filter.mpr ⟨hh.1, by simp [hpred.1]⟩
            rw [(hHist 1 j hh.1).1] at hw
            rcases hchosen j hj0 w hw with hwx | hwy
            · have he := hAtLevel j N x (by simpa only [hwx] using hw) hx
              omega
            · simpa only [hwy, if_true] using horient.1)
          t (by rw [hNside]; exact hne) hSmall
      simpa only [pairs, active, Q, I, G] using hb
  have hOppositeG : G ≤ 5 := by
    cases t <;> exact hopposite
  have hFinish (T : Finset ℕ)
      (hInside : ∀ p ∈ (group 1).childPositions, I 1 p ⊆ T)
      (hCard : (Q T).card ≤ 6) :
      (∀ fuel, Ctx.Context.boundFuel fuel (group 1) ≤ 6) ∧
        (group 1).bound ≤ 6 := by
    have hSub : pairs 1 ⊆ Q T := by
      intro w hw
      obtain ⟨p, hp, hw⟩ := Finset.mem_biUnion.mp hw
      have hpChild : p ∈ (group 1).childPositions :=
        List.mem_toFinset.mp (Finset.mem_filter.mp hp).1
      have hpair := Finset.mem_filter.mp hw
      have hcoords := Finset.mem_product.mp hpair.1
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr
          ⟨hInside p hpChild hcoords.1, hInside p hpChild hcoords.2⟩, hpair.2⟩
    have hCount : (pairs 1).card ≤ 6 :=
      (Finset.card_le_card hSub).trans hCard
    exact ⟨fun fuel => (hHigh.1 fuel).trans hCount, hHigh.2.trans hCount⟩
  rcases ctx_capacity_three_children_exterior_of_two_levels_global_five
      σ s N M x y hN hM hNM hNs hMs hx hy hchosenGlobal with horient | horient
  · have horder : x < z ∧ z < y := by
      rcases hbetween with hb | hb
      · exact hb
      · omega
    let T := Finset.Icc 2 4
    apply hFinish T
    · intro p hp r hr
      have hpData := (hChild 1 p).mp hp
      have hcap : 3 ≤ C p := by
        have hc := hpData.2
        dsimp only [color] at hc
        by_cases hle : C p ≤ 2
        · simp [hle] at hc
        · omega
      have hzp : z < p := by
        have hh := horient.2 p hpData.1 hcap M
          (List.mem_filter.mpr ⟨hM, by simp [hMs]⟩) y hy
        omega
      have hleft := hOneLeft p hp hzp
      have hrData := Finset.mem_Icc.mp hr
      apply Finset.mem_Icc.mpr
      exact ⟨by omega, by omega⟩
    · change ({w ∈ (Finset.Icc 2 4).product (Finset.Icc 2 4) |
        w.1 ≤ w.2} : Finset (ℕ × ℕ)).card ≤ 6
      decide
  · have horder : y < z ∧ z < x := by
      rcases hbetween with hb | hb
      · omega
      · exact hb
    let T := Finset.Icc 1 3
    apply hFinish T
    · intro p hp r hr
      have hpData := (hChild 1 p).mp hp
      have hcap : 3 ≤ C p := by
        have hc := hpData.2
        dsimp only [color] at hc
        by_cases hle : C p ≤ 2
        · simp [hle] at hc
        · omega
      have hpz : p < z := by
        have hh := horient.2 p hpData.1 hcap M
          (List.mem_filter.mpr ⟨hM, by simp [hMs]⟩) y hy
        omega
      have hright := hOneRight p hp hpz
      have hrData := Finset.mem_Icc.mp hr
      apply Finset.mem_Icc.mpr
      exact ⟨by omega, by omega⟩
    · change ({w ∈ (Finset.Icc 1 3).product (Finset.Icc 1 3) |
        w.1 ≤ w.2} : Finset (ℕ × ℕ)).card ≤ 6
      decide

end ErdosSzekeres
