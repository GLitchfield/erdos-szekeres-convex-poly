import ESBlueprint.B.CtxTwoMarkerLowCapacityPruningRankPairBoundOfHighWitness
import ESBlueprint.B.CtxBoundLeSumRunGroupPruningsOfActualMarkerGlobalFive
import ESBlueprint.B.CtxPointLimitsEqOfChildInterval

set_option maxHeartbeats 8000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

/-- In an exact two-marker chosen-global-five context with a capacity-three witness and opposite global at most five, split physical child runs canonically at chosen capacity two. If the exact active opposite ordered-rank-pair unions of the low and high original-history prunings are disjoint, then every fuel approximation and the full context are at most ten. Binary run decomposition, the low older-boundary pair theorem and the high younger-boundary pair theorem charge the disjoint union, which embeds in the full opposite rank triangle. This isolates pair overlap as the remaining mixed-support obstruction.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_two_marker_low_capacity_pruning_rank_pair_bound_of_high_witness, ErdosSzekeres.ctx_active_boundary_marker_rank_pair_union_bound, ErdosSzekeres.ctx_bound_le_sum_run_group_prunings_of_actual_marker_global_five, ErdosSzekeres.ctx_point_limits_eq_of_child_interval, ErdosSzekeres.ctx_part_pruning_history_transport
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_marker_mixed_capacity_disjoint_pair_support_ten_bound (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N M x y high : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hchosenGlobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j, z = x ∨ z = y) (hhighmem : high ∈ σ.childPositions) (hhigh : 3 ≤ (match s with | Ctx.Side.lower => σ.cupLimit high high | Ctx.Side.upper => σ.capLimit high high)) : let capacity := fun p => match s with | Ctx.Side.lower => σ.cupLimit p p | Ctx.Side.upper => σ.capLimit p p; let color := fun p => if capacity p ≤ 2 then (0 : ℕ) else 1; let support := fun c => σ.childPositions.filter (fun p => color p = c); let group := fun c => ({ σ with word := (List.range σ.word.length).map (fun p => match σ.letterAt p with | Ctx.Letter.child => if p ∈ support c then Ctx.Letter.child else Ctx.Letter.ext (σ.maxima.length + 1) Ctx.Side.lower | Ctx.Letter.ext j v => Ctx.Letter.ext j v) } : Ctx.Context); let global := match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a; let active := fun c => (group c).childPositions.toFinset.filter (fun p => 0 < (group c).cupLimit p p ∧ 0 < (group c).capLimit p p); let interval := fun c p => Finset.Icc ((group c).leftExt t 0 p + 1) (global - 1 - (group c).rightExt t 0 p); let pairs := fun c => (active c).biUnion (fun p => (((interval c p).product (interval c p)).filter (fun z => z.1 ≤ z.2))); Disjoint (pairs 0) (pairs 1) → (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ 10) ∧ σ.bound ≤ 10 := by
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
  let Q (S : Finset ℕ) := (S.product S).filter (fun z => z.1 ≤ z.2)
  let pairs (c : ℕ) := (active c).biUnion (fun p => Q (I c p))
  change Disjoint (pairs 0) (pairs 1) →
    (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ 10) ∧ σ.bound ≤ 10
  intro hdisjoint
  have hCover : ∀ p ∈ σ.childPositions,
      color p ∈ ({0, 1} : Finset ℕ) := by
    intro p hp
    dsimp only [color]
    split_ifs <;> simp
  have hColor : ∀ p ∈ σ.childPositions, ∀ q ∈ σ.childPositions,
      p ≤ q → (∀ r, p ≤ r → r ≤ q → r ∈ σ.childPositions) →
      color p = color q := by
    intro p hp q hq hpq hinterval
    have hh := ctx_point_limits_eq_of_child_interval σ p q hp hq hpq hinterval
    have hC : C p = C q := by
      cases s with
      | lower => simpa only [C] using hh.1
      | upper => simpa only [C] using hh.2
    simp only [color, hC]
  have hDecomp :=
    ctx_bound_le_sum_run_group_prunings_of_actual_marker_global_five
      σ hpositive s N x hN hNs hx hchosenGlobal color ({0, 1} : Finset ℕ)
      hCover hColor
  change (∀ fuel, Ctx.Context.boundFuel fuel σ ≤
      ({0, 1} : Finset ℕ).sum (fun c => (group c).bound)) ∧
      σ.bound ≤ ({0, 1} : Finset ℕ).sum (fun c => (group c).bound) at hDecomp
  have hLow : (∀ fuel, Ctx.Context.boundFuel fuel (group 0) ≤ (pairs 0).card) ∧
      (group 0).bound ≤ (pairs 0).card := by
    have hh := ctx_two_marker_low_capacity_pruning_rank_pair_bound_of_high_witness
      σ hpositive s t hne N M x y high hN hM hNM hNs hMs hx hy
      hchosenGlobal hchosen hhighmem hhigh
    simpa [C, color, support, group, G, active, I, Q, pairs] using hh
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
  have hAtLevel (j i z : ℕ) (hz : z ∈ σ.extPositions j)
      (hz' : z ∈ σ.extPositions i) : j = i := by
    have hj := (List.mem_filter.mp hz).2
    have hi := (List.mem_filter.mp hz').2
    cases he : σ.letterAt z <;> simp [he] at hj hi
    omega
  have hNOn : N ∈ σ.levelsOn s 0 :=
    List.mem_filter.mpr ⟨hN, by simp [hNs]⟩
  have hNpos : 1 ≤ N := Ctx.Context.one_le_of_mem_levels hN
  have hNgroup : N ∈ (group 1).levels := hN
  have hxgroup : x ∈ (group 1).extPositions N := by
    rw [(hHist 1 N hN).1]
    exact hx
  have hNside : (group 1).sideAt N = s := (hHist 1 N hN).2.trans hNs
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
          (fun j hj z hz => by
            rw [hNside, hLevels 1 s N] at hj
            have hh := List.mem_filter.mp hj
            have hpred := of_decide_eq_true hh.2
            have hjN : j < N := by
              rcases hpred.2 with hzero | hlt
              · omega
              · exact hlt
            have hj0 : j ∈ σ.levelsOn s 0 :=
              List.mem_filter.mpr ⟨hh.1, by simp [hpred.1]⟩
            rw [(hHist 1 j hh.1).1] at hz
            rcases hchosen j hj0 z hz with hzx | hzy
            · have he := hAtLevel j N x (by simpa only [hzx] using hz) hx
              omega
            · simpa only [hzy, if_false] using horient.1)
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
          (fun j hj z hz => by
            rw [hNside, hLevels 1 s N] at hj
            have hh := List.mem_filter.mp hj
            have hpred := of_decide_eq_true hh.2
            have hjN : j < N := by
              rcases hpred.2 with hzero | hlt
              · omega
              · exact hlt
            have hj0 : j ∈ σ.levelsOn s 0 :=
              List.mem_filter.mpr ⟨hh.1, by simp [hpred.1]⟩
            rw [(hHist 1 j hh.1).1] at hz
            rcases hchosen j hj0 z hz with hzx | hzy
            · have he := hAtLevel j N x (by simpa only [hzx] using hz) hx
              omega
            · simpa only [hzy, if_true] using horient.1)
          t (by rw [hNside]; exact hne) hSmall
      simpa only [pairs, active, Q, I, G] using hb
  let T := Finset.Icc 1 (G - 1)
  let triangle := Q T
  have hInside (c p : ℕ) : I c p ⊆ T := by
    intro z hz
    have hh := Finset.mem_Icc.mp hz
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hSub (c : ℕ) : pairs c ⊆ triangle := by
    intro z hz
    obtain ⟨p, _, hz⟩ := Finset.mem_biUnion.mp hz
    have hh := Finset.mem_filter.mp hz
    have hp := Finset.mem_product.mp hh.1
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hInside c p hp.1, hInside c p hp.2⟩, hh.2⟩
  have hUnionSub : pairs 0 ∪ pairs 1 ⊆ triangle := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact hSub 0 hz
    · exact hSub 1 hz
  have hCardPairs (S : Finset ℕ) : (Q S).card = (S.card + 1).choose 2 := by
    rw [← Finset.card_sym2]
    apply Finset.card_bij (fun z _ => Sym2.mk z.1 z.2)
    · intro z hz
      exact Finset.mk_mem_sym2_iff.mpr
        (Finset.mem_product.mp (Finset.mem_filter.mp hz).1)
    · intro p hp q hq he
      have hpl := (Finset.mem_filter.mp hp).2
      have hql := (Finset.mem_filter.mp hq).2
      rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Prod.ext h1 h2
      · apply Prod.ext <;> omega
    · intro z hz
      induction z using Sym2.ind with
      | h a b =>
          obtain ⟨ha, hb⟩ := Finset.mk_mem_sym2_iff.mp hz
          by_cases hab : a ≤ b
          · exact ⟨(a, b), Finset.mem_filter.mpr
              ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩, rfl⟩
          · exact ⟨(b, a), Finset.mem_filter.mpr
              ⟨Finset.mem_product.mpr ⟨hb, ha⟩, by omega⟩, Sym2.eq_swap⟩
  have hTriangle : triangle.card = G.choose 2 := by
    change (Q T).card = G.choose 2
    rw [show (Q T).card = (T.card + 1).choose 2 by exact hCardPairs T]
    by_cases hz : G = 0
    · norm_num [T, hz]
    · have hc : T.card + 1 = G := by
        simp only [T, Nat.card_Icc]
        omega
      rw [hc]
  have hPairCount : (pairs 0).card + (pairs 1).card ≤ G.choose 2 := by
    rw [← Finset.card_union_of_disjoint hdisjoint]
    exact (Finset.card_le_card hUnionSub).trans_eq hTriangle
  have hTen : G.choose 2 ≤ 10 := by
    have hh := Nat.choose_le_choose 2 hopposite
    simpa only [G] using hh
  have hGroups : (group 0).bound + (group 1).bound ≤ 10 :=
    (Nat.add_le_add hLow.2 hHigh.2).trans (hPairCount.trans hTen)
  constructor
  · intro fuel
    have hh := hDecomp.1 fuel
    simpa using hh.trans hGroups
  · have hh := hDecomp.2
    simpa using hh.trans hGroups

end ErdosSzekeres
