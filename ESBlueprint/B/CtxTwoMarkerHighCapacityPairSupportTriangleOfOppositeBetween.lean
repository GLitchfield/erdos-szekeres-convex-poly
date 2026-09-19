import ESBlueprint.B.CtxTwoMarkerHighCapacityPruningSixBoundOfOppositeBetween

set_option maxHeartbeats 4000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

/-- For the canonical high chosen-capacity pruning, an actual opposite marker between two chosen markers orients every active opposite-rank interval into one explicit three-rank window, so the entire high pair support lies in Q([2,4]) or Q([1,3]).
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_capacity_three_children_exterior_of_two_levels_global_five, ErdosSzekeres.ctx_part_pruning_history_transport
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_marker_high_capacity_pair_support_triangle_of_opposite_between (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N M x y L z : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hchosenGlobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hL : L ∈ σ.levels) (hLt : σ.sideAt L = t) (hz : z ∈ σ.extPositions L) (hbetween : (x < z ∧ z < y) ∨ (y < z ∧ z < x)) : let capacity : ℕ → ℕ := fun p => match s with | Ctx.Side.lower => σ.cupLimit p p | Ctx.Side.upper => σ.capLimit p p; let color : ℕ → ℕ := fun p => if capacity p ≤ 2 then 0 else 1; let support : ℕ → List ℕ := fun c => σ.childPositions.filter (fun p => color p = c); let group : ℕ → Ctx.Context := fun c => ({ σ with word := (List.range σ.word.length).map (fun p => match σ.letterAt p with | Ctx.Letter.child => if p ∈ support c then Ctx.Letter.child else Ctx.Letter.ext (σ.maxima.length + 1) Ctx.Side.lower | Ctx.Letter.ext j v => Ctx.Letter.ext j v) } : Ctx.Context); let global := match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a; let active : ℕ → Finset ℕ := fun c => (group c).childPositions.toFinset.filter (fun p => 0 < (group c).cupLimit p p ∧ 0 < (group c).capLimit p p); let interval : ℕ → ℕ → Finset ℕ := fun c p => Finset.Icc ((group c).leftExt t 0 p + 1) (global - 1 - (group c).rightExt t 0 p); let Q : Finset ℕ → Finset (ℕ × ℕ) := fun S => (S.product S).filter (fun w => w.1 ≤ w.2); let pairs : ℕ → Finset (ℕ × ℕ) := fun c => (active c).biUnion (fun p => Q (interval c p)); (x < z ∧ z < y ∧ pairs 1 ⊆ Q (Finset.Icc 2 4)) ∨ (y < z ∧ z < x ∧ pairs 1 ⊆ Q (Finset.Icc 1 3)) := by
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
  let G := match t, hne, hchosenGlobal, hopposite, hLt with
    | Ctx.Side.lower, _, _, _, _ => σ.u
    | Ctx.Side.upper, _, _, _, _ => σ.a
  let active (c : ℕ) := (group c).childPositions.toFinset.filter
    (fun p => 0 < (group c).cupLimit p p ∧ 0 < (group c).capLimit p p)
  let I (c p : ℕ) := Finset.Icc ((group c).leftExt t 0 p + 1)
    (G - 1 - (group c).rightExt t 0 p)
  let Q (S : Finset ℕ) :=
    (S.product S).filter (fun w => w.1 ≤ w.2)
  let pairs (c : ℕ) := (active c).biUnion (fun p => Q (I c p))
  change (x < z ∧ z < y ∧ pairs 1 ⊆ Q (Finset.Icc 2 4)) ∨
    (y < z ∧ z < x ∧ pairs 1 ⊆ Q (Finset.Icc 1 3))
  have hChild (c p : ℕ) : p ∈ (group c).childPositions ↔
      p ∈ σ.childPositions ∧ color p = c := by
    have hh : (group c).childPositions =
        σ.childPositions.filter (· ∈ support c) :=
      (ctx_part_pruning_history_transport σ hpositive
        (support c) Ctx.Side.lower 0).2.1
    rw [hh]
    simp [support]
  have hHist (c j : ℕ) (hj : j ∈ σ.levels) :
      (group c).extPositions j = σ.extPositions j ∧
        (group c).sideAt j = σ.sideAt j :=
    (ctx_part_pruning_history_transport σ hpositive
      (support c) Ctx.Side.lower 0).2.2.1 j hj
  have hLgroup : L ∈ (group 1).levels := hL
  have hzgroup : z ∈ (group 1).extPositions L := by
    rw [(hHist 1 L hL).1]
    exact hz
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
  have hHigh (p : ℕ) (hp : p ∈ active 1) :
      p ∈ σ.childPositions ∧ 3 ≤ C p := by
    have hpChild : p ∈ (group 1).childPositions :=
      List.mem_toFinset.mp (Finset.mem_filter.mp hp).1
    have hpData := (hChild 1 p).mp hpChild
    refine ⟨hpData.1, ?_⟩
    have hc := hpData.2
    dsimp only [color] at hc
    by_cases hle : C p ≤ 2
    · simp [hle] at hc
    · omega
  have hPairSub (T : Finset ℕ)
      (hInside : ∀ p ∈ active 1, I 1 p ⊆ T) : pairs 1 ⊆ Q T := by
    intro w hw
    obtain ⟨p, hp, hw⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨hwProd, hwOrder⟩ := Finset.mem_filter.mp hw
    obtain ⟨hwLeft, hwRight⟩ := Finset.mem_product.mp hwProd
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr
        ⟨hInside p hp hwLeft, hInside p hp hwRight⟩, hwOrder⟩
  have hOpposite : G ≤ 5 := by
    cases t <;> exact hopposite
  have hChosenGlobal : (match s with
      | Ctx.Side.lower => σ.u
      | Ctx.Side.upper => σ.a) ≤ 5 := by
    cases s <;> exact hchosenGlobal
  rcases ctx_capacity_three_children_exterior_of_two_levels_global_five
      σ s N M x y hN hM hNM hNs hMs hx hy hChosenGlobal with horient | horient
  · have horder : x < z ∧ z < y := by
      rcases hbetween with hb | hb
      · exact hb
      · omega
    apply Or.inl
    refine ⟨horder.1, horder.2, hPairSub (Finset.Icc 2 4) ?_⟩
    intro p hp r hr
    have hpData := hHigh p hp
    have hyp : y < p := horient.2 p hpData.1 hpData.2 M
      (List.mem_filter.mpr ⟨hM, by simp [hMs]⟩) y hy
    have hzp : z < p := by omega
    have hpChild : p ∈ (group 1).childPositions :=
      List.mem_toFinset.mp (Finset.mem_filter.mp hp).1
    have hleft := hOneLeft p hpChild hzp
    have hrRange := Finset.mem_Icc.mp hr
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · have horder : y < z ∧ z < x := by
      rcases hbetween with hb | hb
      · omega
      · exact hb
    apply Or.inr
    refine ⟨horder.1, horder.2, hPairSub (Finset.Icc 1 3) ?_⟩
    intro p hp r hr
    have hpData := hHigh p hp
    have hpy : p < y := horient.2 p hpData.1 hpData.2 M
      (List.mem_filter.mpr ⟨hM, by simp [hMs]⟩) y hy
    have hpz : p < z := by omega
    have hpChild : p ∈ (group 1).childPositions :=
      List.mem_toFinset.mp (Finset.mem_filter.mp hp).1
    have hright := hOneRight p hpChild hpz
    have hrRange := Finset.mem_Icc.mp hr
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩

end ErdosSzekeres
