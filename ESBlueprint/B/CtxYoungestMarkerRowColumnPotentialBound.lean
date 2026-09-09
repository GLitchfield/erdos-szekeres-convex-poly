import ESBlueprint.B.RankRowColumnUnionCardEqGroupCharges

set_option maxHeartbeats 20000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Every-fuel and full context bound by endpoint row and column reservations around an actual youngest chosen-side marker when the chosen global is at most four. Left active children contribute lower-endpoint rows of opposite ranks, and right active children contribute upper-endpoint columns. Arbitrary older histories, maxima, inactive children, unused indexed levels and unindexed markers are allowed; only actual younger chosen markers are excluded. The proof combines physical-run pruning, linear active boundary-marker bounds, the doubled-rank bound for the merged pivot group and the exact row/column group count. Supplies the chosen-part charge for a no-marker recursive rank-pair induction using the existing tracked end reservations.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_youngest_marker_row_column_potential_bound (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (N x : ℕ)
  (hN : N ∈ σ.levels) (hNs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 4)
  (hyoung : ∀ j ∈ σ.levelsOn s N, σ.extPositions j = []) :
  let global := match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a
  let active := σ.childPositions.toFinset.filter
    (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
  let interval := fun p => Finset.Icc (σ.leftExt t 0 p + 1) (global - 1 - σ.rightExt t 0 p)
  let rows := (active.filter (fun p => p < x)).biUnion
    (fun p => ({σ.leftExt t 0 p + 1} : Finset ℕ).product (interval p))
  let columns := (active.filter (fun p => x < p)).biUnion
    (fun p => (interval p).product ({global - 1 - σ.rightExt t 0 p} : Finset ℕ))
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ (rows ∪ columns).card) ∧
    σ.bound ≤ (rows ∪ columns).card := by
  classical
  have hOneLeft (ρ : Context) (v : Side) (j p q : ℕ)
      (hj : j ∈ ρ.levelsOn v 0) (hq : q ∈ ρ.extPositions j) (hqp : q < p) :
      1 ≤ ρ.leftExt v 0 p := by
    have hm : q ∈ (ρ.extPositions j).filter (· < p) := by simp [hq, hqp]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v 0).sublists.map
      (fun ls => (ls.foldl (leftStep ρ) (p, 0)).2))
      (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ ρ.leftExt v 0 p at hv
    simpa only [List.foldl_cons, List.foldl_nil, leftStep,
      List.getLast?_eq_some_getLast hnonempty] using hv
  have hOneRight (ρ : Context) (v : Side) (j p q : ℕ)
      (hj : j ∈ ρ.levelsOn v 0) (hq : q ∈ ρ.extPositions j) (hpq : p < q) :
      1 ≤ ρ.rightExt v 0 p := by
    have hm : q ∈ (ρ.extPositions j).filter (p < ·) := by simp [hq, hpq]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v 0).sublists.map
      (fun ls => (ls.foldl (rightStep ρ) (p, 0)).2))
      (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ ρ.rightExt v 0 p at hv
    simpa only [List.foldl_cons, List.foldl_nil, rightStep,
      List.head?_eq_some_head hnonempty] using hv
  let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
  let active (ρ : Context) := ρ.childPositions.toFinset.filter
    (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
  let I (ρ : Context) (r : ℕ) :=
    Finset.Icc (ρ.leftExt t 0 r + 1) (G ρ t - 1 - ρ.rightExt t 0 r)
  let lo (p : ℕ) := σ.leftExt t 0 p + 1
  let hi (p : ℕ) := G σ t - 1 - σ.rightExt t 0 p
  let L := (active σ).filter (fun p => p < x)
  let R := (active σ).filter (fun p => x < p)
  let rows := L.biUnion (fun p => ({lo p} : Finset ℕ).product (I σ p))
  let columns := R.biUnion (fun p => (I σ p).product ({hi p} : Finset ℕ))
  let merge := ¬ Disjoint rows columns
  let lc (p : ℕ) := if merge ∧ lo p = lo x then 0 else 2 * lo p + 1
  let rc (p : ℕ) := if merge ∧ hi p = hi x then 0 else 2 * hi p + 2
  let color (p : ℕ) := if p < x then lc p else rc p
  let colors := σ.childPositions.toFinset.image color
  let ranks (c : ℕ) := ((active σ).filter (fun p => color p = c)).biUnion (I σ)
  let support (c : ℕ) := σ.childPositions.filter (fun p => color p = c)
  let group (c : ℕ) : Context := { σ with
    word := (List.range σ.word.length).map (fun p => match σ.letterAt p with
      | Letter.child => if p ∈ support c then Letter.child
          else Letter.ext (σ.maxima.length + 1) Side.lower
      | Letter.ext j v => Letter.ext j v) }
  change (∀ fuel, boundFuel fuel σ ≤ (rows ∪ columns).card) ∧ σ.bound ≤ (rows ∪ columns).card
  have hNe (p : ℕ) (hp : p ∈ σ.childPositions) : p ≠ x := by
    intro he
    subst x
    have hc := of_decide_eq_true (List.mem_filter.mp hp).2
    have he := (List.mem_filter.mp hx).2
    simp [hc] at he
  have hActiveChild (p : ℕ) (hp : p ∈ active σ) : p ∈ σ.childPositions :=
    List.mem_toFinset.mp (Finset.mem_filter.mp hp).1
  have hNOn : N ∈ σ.levelsOn s 0 := List.mem_filter.mpr ⟨hN, by simp [hNs]⟩
  have hSmall (r : ℕ) (hr : r ∈ σ.childPositions) : min (σ.cupLimit r r) (σ.capLimit r r) ≤ 2 := by
    have hrx : r ≠ x := by
      intro he
      subst x
      have hc := of_decide_eq_true (List.mem_filter.mp hr).2
      have he := (List.mem_filter.mp hx).2
      simp [hc] at he
    by_cases h : r < x
    · have he := hOneRight σ s N r x hNOn hx h
      cases s <;> simp only [cupLimit, capLimit, chainExt] at hglobal ⊢ <;> omega
    · have he := hOneLeft σ s N r x hNOn hx (by omega)
      cases s <;> simp only [cupLimit, capLimit, chainExt] at hglobal ⊢ <;> omega
  have hSort (ρ : Context) (j : ℕ) : (ρ.extPositions j).Pairwise (· ≤ ·) :=
    (List.pairwise_lt_range.filter _).imp le_of_lt
  have hStepLeft (ρ : Context) (j p q c d : ℕ) (hpq : p ≤ q) (hcd : c ≤ d) :
      (leftStep ρ (p, c) j).1 ≤ (leftStep ρ (q, d) j).1 ∧
      (leftStep ρ (p, c) j).2 ≤ (leftStep ρ (q, d) j).2 := by
    cases ha : ((ρ.extPositions j).filter (· < p)).getLast? with
    | none =>
      have hnil := List.getLast?_eq_none_iff.mp ha
      cases hb : ((ρ.extPositions j).filter (· < q)).getLast? with
      | none => simpa only [leftStep, ha, hb] using And.intro hpq hcd
      | some y =>
        have hy := List.mem_of_mem_getLast? (Option.mem_def.mpr hb)
        have hpy : p ≤ y := by
          by_contra h
          have hx : y ∈ (ρ.extPositions j).filter (· < p) :=
            List.mem_filter.mpr ⟨(List.mem_filter.mp hy).1, by simp only [decide_eq_true_eq]; omega⟩
          rw [hnil] at hx
          exact List.not_mem_nil hx
        simpa only [leftStep, ha, hb] using And.intro hpy (show c ≤ d + 1 by omega)
    | some x =>
      have hx := List.mem_of_mem_getLast? (Option.mem_def.mpr ha)
      have hxq : x ∈ (ρ.extPositions j).filter (· < q) := by
        have hxp : x < p := of_decide_eq_true (List.mem_filter.mp hx).2
        exact List.mem_filter.mpr ⟨(List.mem_filter.mp hx).1, by simp only [decide_eq_true_eq]; omega⟩
      cases hb : ((ρ.extPositions j).filter (· < q)).getLast? with
      | none =>
        have hnil := List.getLast?_eq_none_iff.mp hb
        rw [hnil] at hxq
        exact False.elim (List.not_mem_nil hxq)
      | some y =>
        have hlast : ((ρ.extPositions j).filter (· < q)).getLast (List.ne_nil_of_mem hxq) = y := by
          rw [List.getLast?_eq_some_getLast (List.ne_nil_of_mem hxq)] at hb
          exact Option.some.inj hb
        have hxy : x ≤ y := by
          simpa only [hlast] using ((hSort ρ j).filter _).rel_getLast hxq
        simpa only [leftStep, ha, hb] using And.intro hxy (show c + 1 ≤ d + 1 by omega)
  have hStepRight (ρ : Context) (j p q c d : ℕ) (hpq : p ≤ q) (hcd : d ≤ c) :
      (rightStep ρ (p, c) j).1 ≤ (rightStep ρ (q, d) j).1 ∧
      (rightStep ρ (q, d) j).2 ≤ (rightStep ρ (p, c) j).2 := by
    cases ha : ((ρ.extPositions j).filter (p < ·)).head? with
    | none =>
      have hnil := List.head?_eq_none_iff.mp ha
      cases hb : ((ρ.extPositions j).filter (q < ·)).head? with
      | none => simpa only [rightStep, ha, hb] using And.intro hpq hcd
      | some y =>
        have hy := List.mem_of_mem_head? (Option.mem_def.mpr hb)
        have hqy : q < y := of_decide_eq_true (List.mem_filter.mp hy).2
        have hyp : y ∈ (ρ.extPositions j).filter (p < ·) :=
          List.mem_filter.mpr ⟨(List.mem_filter.mp hy).1, by simp only [decide_eq_true_eq]; omega⟩
        rw [hnil] at hyp
        exact False.elim (List.not_mem_nil hyp)
    | some x =>
      have hx := List.mem_of_mem_head? (Option.mem_def.mpr ha)
      cases hb : ((ρ.extPositions j).filter (q < ·)).head? with
      | none =>
        have hnil := List.head?_eq_none_iff.mp hb
        have hxq : x ≤ q := by
          by_contra h
          have hmem : x ∈ (ρ.extPositions j).filter (q < ·) :=
            List.mem_filter.mpr ⟨(List.mem_filter.mp hx).1, by simp only [decide_eq_true_eq]; omega⟩
          rw [hnil] at hmem
          exact List.not_mem_nil hmem
        simpa only [rightStep, ha, hb] using And.intro hxq (show d ≤ c + 1 by omega)
      | some y =>
        have hy := List.mem_of_mem_head? (Option.mem_def.mpr hb)
        have hqy : q < y := of_decide_eq_true (List.mem_filter.mp hy).2
        have hyp : y ∈ (ρ.extPositions j).filter (p < ·) :=
          List.mem_filter.mpr ⟨(List.mem_filter.mp hy).1, by simp only [decide_eq_true_eq]; omega⟩
        have hhead : ((ρ.extPositions j).filter (p < ·)).head (List.ne_nil_of_mem hyp) = x := by
          rw [List.head?_eq_some_head (List.ne_nil_of_mem hyp)] at ha
          exact Option.some.inj ha
        have hxy : x ≤ y := by
          simpa only [hhead] using ((hSort ρ j).filter _).rel_head hyp
        simpa only [rightStep, ha, hb] using And.intro hxy (show d + 1 ≤ c + 1 by omega)
  have hFoldLeft (ρ : Context) : ∀ (ls : List ℕ) (p q c d : ℕ), p ≤ q → c ≤ d →
      (ls.foldl (leftStep ρ) (p, c)).1 ≤ (ls.foldl (leftStep ρ) (q, d)).1 ∧
      (ls.foldl (leftStep ρ) (p, c)).2 ≤ (ls.foldl (leftStep ρ) (q, d)).2 := by
    intro ls
    induction ls with
    | nil => intro p q c d hpq hcd; exact ⟨hpq, hcd⟩
    | cons j ls ih =>
      intro p q c d hpq hcd
      have h := hStepLeft ρ j p q c d hpq hcd
      simpa only [List.foldl_cons] using ih _ _ _ _ h.1 h.2
  have hFoldRight (ρ : Context) : ∀ (ls : List ℕ) (p q c d : ℕ), p ≤ q → d ≤ c →
      (ls.foldl (rightStep ρ) (p, c)).1 ≤ (ls.foldl (rightStep ρ) (q, d)).1 ∧
      (ls.foldl (rightStep ρ) (q, d)).2 ≤ (ls.foldl (rightStep ρ) (p, c)).2 := by
    intro ls
    induction ls with
    | nil => intro p q c d hpq hcd; exact ⟨hpq, hcd⟩
    | cons j ls ih =>
      intro p q c d hpq hcd
      have h := hStepRight ρ j p q c d hpq hcd
      simpa only [List.foldl_cons] using ih _ _ _ _ h.1 h.2
  have hLeftMono (ρ : Context) (v : Side) (top p q : ℕ) (hpq : p ≤ q) :
      ρ.leftExt v top p ≤ ρ.leftExt v top q := by
    simp only [leftExt_eq]
    apply getD_max?_le_of_forall
    intro value hv
    obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hv
    exact ⟨_, List.mem_map.mpr ⟨ls, hls, rfl⟩, (hFoldLeft ρ ls p q 0 0 hpq le_rfl).2⟩
  have hRightMono (ρ : Context) (v : Side) (top p q : ℕ) (hpq : p ≤ q) :
      ρ.rightExt v top q ≤ ρ.rightExt v top p := by
    simp only [rightExt_eq]
    apply getD_max?_le_of_forall
    intro value hv
    obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hv
    exact ⟨_, List.mem_map.mpr ⟨ls, hls, rfl⟩, (hFoldRight ρ ls p q 0 0 hpq le_rfl).2⟩
  have hLPivot (p : ℕ) (hp : p ∈ L) : lo p ≤ lo x ∧ hi p ≤ hi x := by
    have hpx := (Finset.mem_filter.mp hp).2
    have hl := hLeftMono σ t 0 p x (by omega)
    have hr := hRightMono σ t 0 p x (by omega)
    dsimp only [lo, hi]
    omega
  have hRPivot (p : ℕ) (hp : p ∈ R) : lo x ≤ lo p ∧ hi x ≤ hi p := by
    have hxp := (Finset.mem_filter.mp hp).2
    have hl := hLeftMono σ t 0 x p (by omega)
    have hr := hRightMono σ t 0 x p (by omega)
    dsimp only [lo, hi]
    omega
  have hCover : ∀ p ∈ σ.childPositions, color p ∈ colors := by
    intro p hp
    exact Finset.mem_image.mpr ⟨p, List.mem_toFinset.mpr hp, rfl⟩
  have hColor : ∀ a ∈ σ.childPositions, ∀ b ∈ σ.childPositions, a ≤ b →
      (∀ r, a ≤ r → r ≤ b → r ∈ σ.childPositions) → color a = color b := by
    intro a ha b hb hab hbetween
    have hside : (a < x) ↔ (b < x) := by
      have hax := hNe a ha
      have hbx := hNe b hb
      by_contra hn
      have hxc := hbetween x (by omega) (by omega)
      exact hNe x hxc rfl
    have hRegion : ∀ j ∈ σ.levelsOn t 0, ∀ z ∈ σ.extPositions j,
        (z < a ↔ z < b) ∧ (a < z ↔ b < z) := by
      intro j hj z hz
      have hOutside : z < a ∨ b < z := by
        by_contra h
        have hzc := hbetween z (by omega) (by omega)
        have hc := of_decide_eq_true (List.mem_filter.mp hzc).2
        have he := (List.mem_filter.mp hz).2
        simp [hc] at he
      omega
    have he := (ctx_axis_region_limits_exact σ t a b hRegion).1 0
    have hlo : lo a = lo b := by simp only [lo, he.1]
    have hhi : hi a = hi b := by simp only [hi, he.2]
    simp only [color, lc, rc, hside, hlo, hhi]
  have hRankSplit (c : ℕ) : ranks c =
      ((L.filter (fun p => lc p = c)).biUnion (I σ)) ∪
      ((R.filter (fun p => rc p = c)).biUnion (I σ)) := by
    ext z
    simp only [ranks, L, R, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨p, ⟨hp, hc⟩, hz⟩
      by_cases hl : p < x
      · left
        exact ⟨p, ⟨⟨hp, hl⟩, by simpa only [color, if_pos hl] using hc⟩, hz⟩
      · right
        have hn := hNe p (hActiveChild p hp)
        exact ⟨p, ⟨⟨hp, by omega⟩, by simpa only [color, if_neg hl] using hc⟩, hz⟩
    · rintro (⟨p, ⟨⟨hp, hl⟩, hc⟩, hz⟩ | ⟨p, ⟨⟨hp, hr⟩, hc⟩, hz⟩)
      · exact ⟨p, ⟨hp, by simpa only [color, if_pos hl] using hc⟩, hz⟩
      · exact ⟨p, ⟨hp, by simpa only [color, if_neg (show ¬p < x by omega)] using hc⟩, hz⟩
  have hCoverL (p : ℕ) (hp : p ∈ L) : lc p ∈ colors := by
    have hp' := Finset.mem_filter.mp hp
    have hh := hCover p (hActiveChild p hp'.1)
    simpa only [color, if_pos hp'.2] using hh
  have hCoverR (p : ℕ) (hp : p ∈ R) : rc p ∈ colors := by
    have hp' := Finset.mem_filter.mp hp
    have hh := hCover p (hActiveChild p hp'.1)
    simpa only [color, if_neg (show ¬p < x by omega)] using hh
  have hCharges := rank_row_column_union_card_eq_group_charges L R lo hi (lo x) (hi x)
    hLPivot hRPivot colors hCoverL hCoverR
  change (rows ∪ columns).card = colors.sum (fun c =>
    if c = 0 then 2 * (((L.filter (fun p => lc p = c)).biUnion (I σ)) ∪
      ((R.filter (fun p => rc p = c)).biUnion (I σ))).card - 1
    else (((L.filter (fun p => lc p = c)).biUnion (I σ)) ∪
      ((R.filter (fun p => rc p = c)).biUnion (I σ))).card) at hCharges
  simp_rw [← hRankSplit] at hCharges
  have hDifferent (p q c : ℕ) (hp : lc p = c) (hq : rc q = c) (hc : c ≠ 0) : False := by
    dsimp only [lc, rc] at hp hq
    split_ifs at hp hq <;> omega
  have hPos (c : ℕ) : ∀ p j v, (group c).letterAt p = Letter.ext j v → 1 ≤ j :=
    (ctx_part_pruning_history_transport σ hpositive (support c) Side.lower 0).1
  have hChild (c r : ℕ) : r ∈ (group c).childPositions ↔ r ∈ σ.childPositions ∧ color r = c := by
    have hh : (group c).childPositions = σ.childPositions.filter (· ∈ support c) :=
      (ctx_part_pruning_history_transport σ hpositive (support c) Side.lower 0).2.1
    rw [hh]
    simp [support, and_assoc]
  have hLimits (c p q : ℕ) : (group c).cupLimit p q = σ.cupLimit p q ∧
      (group c).capLimit p q = σ.capLimit p q :=
    (ctx_part_pruning_history_transport σ hpositive (support c) Side.lower 0).2.2.2.2.2.1 p q
  have hHist (c j : ℕ) (hj : j ∈ σ.levels) :
      (group c).extPositions j = σ.extPositions j ∧ (group c).sideAt j = σ.sideAt j :=
    (ctx_part_pruning_history_transport σ hpositive (support c) Side.lower 0).2.2.1 j hj
  have hLevels (c : ℕ) (v : Side) (top : ℕ) : (group c).levelsOn v top = σ.levelsOn v top :=
    (ctx_part_pruning_history_transport σ hpositive (support c) Side.lower 0).2.2.2.1 v top
  have hPure (c : ℕ) (v : Side) (top p : ℕ) :
      (group c).leftExt v top p = σ.leftExt v top p ∧
      (group c).rightExt v top p = σ.rightExt v top p :=
    (ctx_part_pruning_history_transport σ hpositive (support c) Side.lower 0).2.2.2.2.1 v top p
  have hActive (c r : ℕ) : r ∈ active (group c) ↔ r ∈ active σ ∧ color r = c := by
    simp only [active, Finset.mem_filter, List.mem_toFinset, hChild, (hLimits c r r).1,
      (hLimits c r r).2]
    tauto
  have hI (c r : ℕ) : I (group c) r = I σ r := by
    simp only [I, (hPure c t 0 r).1, (hPure c t 0 r).2]
    rfl
  have hRanks (c : ℕ) : (active (group c)).biUnion (I (group c)) = ranks c := by
    ext z
    simp only [ranks, Finset.mem_biUnion, Finset.mem_filter, hActive, hI]
  have hNSide (c : ℕ) : (group c).sideAt N = s := (hHist c N hN).2.trans hNs
  have hX (c : ℕ) : x ∈ (group c).extPositions N := by rw [(hHist c N hN).1]; exact hx
  have hDoubled (c : ℕ) : (group c).bound ≤ 2 * (ranks c).card - 1 := by
    have hh := ctx_one_level_refined_potential_bound (group c) (hPos c) s t hne N x
      hN (hNSide c) (hX c) hglobal
    have hb := hh.2.1.trans (Nat.min_le_right _ _)
    change (group c).bound ≤ 2 * ((active (group c)).biUnion (I (group c))).card - 1 at hb
    rw [hRanks c] at hb
    exact hb
  have hLinear (c : ℕ) (hc : c ≠ 0) : (group c).bound ≤ (ranks c).card := by
    have hBoundary (rightward : Bool)
        (hside : ∀ p ∈ active (group c), if rightward then p < x else x < p) :
        (group c).bound ≤ (ranks c).card := by
      have hy : ∀ j ∈ (group c).levelsOn ((group c).sideAt N) N,
          ∀ p ∈ (group c).extPositions j, if rightward then p < x else x < p := by
        intro j hj p hp
        rw [hNSide c, hLevels c s N] at hj
        rw [(hHist c j (List.mem_filter.mp hj).1).1, hyoung j hj] at hp
        exact False.elim (List.not_mem_nil hp)
      have hs : min ((match (group c).sideAt N with
          | Side.lower => (group c).u | Side.upper => (group c).a) - 1)
          ((group c).k - (group c).maximumAt N) ≤ 3 := by
        rw [hNSide c]
        change min (G σ s - 1) _ ≤ 3
        have hg : G σ s ≤ 4 := hglobal
        omega
      have hh := ctx_active_boundary_marker_rank_union_bound (group c) (hPos c) N x hN (hX c)
        rightward (by
          intro p hp hact
          exact hside p (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hp, hact⟩))
        hy t (by rw [hNSide c]; exact hne) hs
      have hb := hh.2
      change (group c).bound ≤ ((active (group c)).biUnion (I (group c))).card at hb
      rwa [hRanks c] at hb
    by_cases hl : ∃ p ∈ active σ, color p = c ∧ p < x
    · obtain ⟨p, hp, hpc, hpx⟩ := hl
      apply hBoundary true
      intro q hq
      simp only [Bool.true_eq, if_true]
      have hq' := (hActive c q).mp hq
      by_contra hn
      have hpcol : lc p = c := by simpa only [color, if_pos hpx] using hpc
      have hqcol : rc q = c := by simpa only [color, if_neg hn] using hq'.2
      exact hDifferent p q c hpcol hqcol hc
    · apply hBoundary false
      intro q hq
      simp only [Bool.false_eq_true, if_false]
      have hq' := (hActive c q).mp hq
      have hqx := hNe q (hActiveChild q hq'.1)
      have hnot : ¬ q < x := by
        intro h
        exact hl ⟨q, hq'.1, hq'.2, h⟩
      omega
  have hGroupBound (c : ℕ) : (group c).bound ≤
      if c = 0 then 2 * (ranks c).card - 1 else (ranks c).card := by
    by_cases hc : c = 0
    · simpa only [if_pos hc] using hDoubled c
    · simpa only [if_neg hc] using hLinear c hc
  have hDecomp := ctx_bound_le_sum_run_group_prunings σ hpositive color colors hCover hSmall hColor
  change (∀ fuel, boundFuel fuel σ ≤ colors.sum (fun c => (group c).bound)) ∧
    σ.bound ≤ colors.sum (fun c => (group c).bound) at hDecomp
  have hBudget : colors.sum (fun c => (group c).bound) ≤ (rows ∪ columns).card :=
    (Finset.sum_le_sum (fun c _ => hGroupBound c)).trans hCharges.symm.le
  exact ⟨fun fuel => (hDecomp.1 fuel).trans hBudget, hDecomp.2.trans hBudget⟩

end ErdosSzekeres
