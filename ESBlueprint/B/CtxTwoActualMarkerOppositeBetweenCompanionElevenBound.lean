import ESBlueprint.B.CtxBoundLeSumRunGroupPruningsOfActualMarkerGlobalFive
import ESBlueprint.B.CtxActiveBoundaryMarkerRankPairUnionBound
import ESBlueprint.B.CtxPartPruningHistoryTransport
import ESBlueprint.B.CtxPartPositiveLetters

namespace ErdosSzekeres

/-- For the exact actual opposite-between cut companion, prove the sharp bound eleven directly, retaining the transported physical level-one marker, maximum one, the oriented capacity-three witness, arbitrary histories, both marker orientations, every fuel approximation, and the full recursive bound. Split physical child runs at the level-one marker. Since no indexed level lies below level one, each pruning is boundary-ready; the two ordered chosen-marker positions confine the resulting chosen-rank pair supports to complementary regions of cardinalities five and six. The maximum-one equality is retained explicitly in the boundary normalization. This stronger spatial decomposition needs neither the low/high pair-cardinality-sum premise nor the residual straddling and overlap assumptions.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_bound_le_sum_run_group_prunings_of_actual_marker_global_five, ErdosSzekeres.ctx_active_boundary_marker_rank_pair_union_bound, ErdosSzekeres.ctx_part_pruning_history_transport, ErdosSzekeres.ctx_part_positive_letters
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_actual_marker_opposite_between_companion_eleven_bound (σ : Ctx.Context) (hpositive : ∀ r j v, σ.letterAt r = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hchosenGlobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j, z = x ∨ z = y) (keep : List ℕ) (m n p high : ℕ) (hp : p ∈ (σ.part keep s m).childPositions) (hn : n = 1) (hhighmem : high ∈ (σ.part (σ.childPositions.filter (· ∉ keep)) t n).childPositions) (hhigh : 3 ≤ (match s with | Ctx.Side.lower => (σ.part (σ.childPositions.filter (· ∉ keep)) t n).cupLimit high high | Ctx.Side.upper => (σ.part (σ.childPositions.filter (· ∉ keep)) t n).capLimit high high)) (hbetween : (x < p ∧ p < y) ∨ (y < p ∧ p < x)) : let B := σ.part (σ.childPositions.filter (· ∉ keep)) t n; p ∈ B.extPositions 1 ∧ B.maximumAt 1 = 1 ∧ (∀ fuel, Ctx.Context.boundFuel fuel B ≤ 11) ∧ B.bound ≤ 11 := by
  classical
  let rest := σ.childPositions.filter (· ∉ keep)
  let B := σ.part rest t n
  let color (q : ℕ) := if q < p then (0 : ℕ) else 1
  let support (c : ℕ) := B.childPositions.filter (fun q => color q = c)
  let group (c : ℕ) : Ctx.Context := { B with
    word := (List.range B.word.length).map (fun q => match B.letterAt q with
      | Ctx.Letter.child => if q ∈ support c then Ctx.Letter.child
          else Ctx.Letter.ext (B.maxima.length + 1) Ctx.Side.lower
      | Ctx.Letter.ext j v => Ctx.Letter.ext j v) }
  let G := match s with
    | Ctx.Side.lower => B.u
    | Ctx.Side.upper => B.a
  let active (c : ℕ) := (group c).childPositions.toFinset.filter
    (fun q => 0 < (group c).cupLimit q q ∧ 0 < (group c).capLimit q q)
  let I (c q : ℕ) := Finset.Icc ((group c).leftExt s 0 q + 1)
    (G - 1 - (group c).rightExt s 0 q)
  let Q (S : Finset ℕ) :=
    (S.product S).filter (fun z => z.1 ≤ z.2)
  let pairs (c : ℕ) := (active c).biUnion (fun q => Q (I c q))
  change p ∈ B.extPositions 1 ∧ B.maximumAt 1 = 1 ∧
    (∀ fuel, Ctx.Context.boundFuel fuel B ≤ 11) ∧ B.bound ≤ 11
  have hpa : p ∈ σ.childPositions ∧ p ∈ keep := by
    simpa only [Ctx.Context.part_childPositions, List.mem_filter,
      decide_eq_true_eq] using hp
  have hpB : p ∈ B.extPositions 1 := by
    change p ∈ (σ.part rest t n).extPositions 1
    rw [Ctx.Context.part_extPositions_one hpositive]
    exact List.mem_filter.mpr ⟨hpa.1, by simp [rest, hpa.2]⟩
  have hBMaximumOne : B.maximumAt 1 = 1 := by
    change (σ.part rest t n).maximumAt 1 = 1
    rw [Ctx.Context.part_maximumAt_one, hn]
  have hOne : 1 ∈ B.levels := by
    change 1 ∈ (σ.part rest t n).levels
    rw [Ctx.Context.part_levels]
    simp
  have hBsideOne : B.sideAt 1 = t :=
    Ctx.Context.part_sideAt_one_of_mem hpositive rest t n hpB
  have hNpos := Ctx.Context.one_le_of_mem_levels hN
  have hMpos := Ctx.Context.one_le_of_mem_levels hM
  have hNB : N + 1 ∈ B.levels := by
    change N + 1 ∈ (σ.part rest t n).levels
    rw [Ctx.Context.part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨N, hN, rfl⟩)
  have hMB : M + 1 ∈ B.levels := by
    change M + 1 ∈ (σ.part rest t n).levels
    rw [Ctx.Context.part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨M, hM, rfl⟩)
  have hNsB : B.sideAt (N + 1) = s :=
    (Ctx.Context.part_sideAt_succ σ rest t n hNpos).trans hNs
  have hMsB : B.sideAt (M + 1) = s :=
    (Ctx.Context.part_sideAt_succ σ rest t n hMpos).trans hMs
  have hxB : x ∈ B.extPositions (N + 1) := by
    change x ∈ (σ.part rest t n).extPositions (N + 1)
    rw [Ctx.Context.part_extPositions_succ σ rest t n hNpos]
    exact hx
  have hyB : y ∈ B.extPositions (M + 1) := by
    change y ∈ (σ.part rest t n).extPositions (M + 1)
    rw [Ctx.Context.part_extPositions_succ σ rest t n hMpos]
    exact hy
  have hPosB := ctx_part_positive_letters σ rest t n
  have hChosenGlobalB : G ≤ 5 := by
    cases s <;> exact hchosenGlobal
  have hOppositeB : (match t with
      | Ctx.Side.lower => B.u
      | Ctx.Side.upper => B.a) ≤ 5 := by
    cases t <;> exact hopposite
  have hChildNe (q j z : ℕ) (hq : q ∈ B.childPositions)
      (hz : z ∈ B.extPositions j) : q ≠ z := by
    have hc := of_decide_eq_true (List.mem_filter.mp hq).2
    have he := (List.mem_filter.mp hz).2
    intro h
    subst z
    simp [hc] at he
  have hpNotChild : p ∉ B.childPositions := by
    intro hpChild
    exact hChildNe p 1 p hpChild hpB rfl
  have hNOn : N + 1 ∈ B.levelsOn s 0 :=
    List.mem_filter.mpr ⟨hNB, by simp [hNsB]⟩
  have hMOn : M + 1 ∈ B.levelsOn s 0 :=
    List.mem_filter.mpr ⟨hMB, by simp [hMsB]⟩
  have hSorted : (B.levelsOn s 0).Pairwise (· < ·) := by
    apply List.Pairwise.filter
    exact List.pairwise_lt_range.map (fun i ↦ i + 1)
      (fun i j h ↦ by dsimp; omega)
  have hTwo : [N + 1, M + 1].Sublist (B.levelsOn s 0) := by
    have hs : [N + 1, M + 1].Pairwise (· < ·) := by simp [hNM]
    have hsub : [N + 1, M + 1] ⊆ B.levelsOn s 0 := by
      intro j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact hNOn
      · exact hMOn
    have he : (B.levelsOn s 0).filter (· ∈ [N + 1, M + 1]) =
        [N + 1, M + 1] := by
      apply (hSorted.filter _).eq_of_mem_iff hs
      intro j
      simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨And.right, fun hj => ⟨hsub hj, hj⟩⟩
    rw [← he]
    exact List.filter_sublist
  have hOneLeft (j q z : ℕ) (hj : j ∈ B.levelsOn s 0)
      (hz : z ∈ B.extPositions j) (hzq : z < q) :
      1 ≤ B.leftExt s 0 q := by
    have hm : z ∈ (B.extPositions j).filter (· < q) := by simp [hz, hzq]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := Ctx.le_getD_max?_of_mem
      (L := (B.levelsOn s 0).sublists.map
        (fun ls => (ls.foldl (Ctx.Context.leftStep B) (q, 0)).2))
      (List.mem_map.mpr ⟨[j],
        List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ B.leftExt s 0 q at hv
    simpa only [List.foldl_cons, List.foldl_nil, Ctx.Context.leftStep,
      List.getLast?_eq_some_getLast hnonempty] using hv
  have hOneRight (j q z : ℕ) (hj : j ∈ B.levelsOn s 0)
      (hz : z ∈ B.extPositions j) (hqz : q < z) :
      1 ≤ B.rightExt s 0 q := by
    have hm : z ∈ (B.extPositions j).filter (q < ·) := by simp [hz, hqz]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := Ctx.le_getD_max?_of_mem
      (L := (B.levelsOn s 0).sublists.map
        (fun ls => (ls.foldl (Ctx.Context.rightStep B) (q, 0)).2))
      (List.mem_map.mpr ⟨[j],
        List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ B.rightExt s 0 q at hv
    simpa only [List.foldl_cons, List.foldl_nil, Ctx.Context.rightStep,
      List.head?_eq_some_head hnonempty] using hv
  have hSortN : (B.extPositions (N + 1)).Pairwise (· ≤ ·) :=
    (List.pairwise_lt_range.filter _).imp le_of_lt
  have hTwoRight (q : ℕ) (hqx : q < x) (hxy : x < y) :
      2 ≤ B.rightExt s 0 q := by
    have hm : x ∈ (B.extPositions (N + 1)).filter (q < ·) := by
      simp [hxB, hqx]
    have hnonempty := List.ne_nil_of_mem hm
    let w := ((B.extPositions (N + 1)).filter (q < ·)).head hnonempty
    have hw : ((B.extPositions (N + 1)).filter (q < ·)).head? = some w :=
      List.head?_eq_some_head hnonempty
    have hwx : w ≤ x := (hSortN.filter _).rel_head hm
    have hmOld : y ∈ (B.extPositions (M + 1)).filter (w < ·) := by
      simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨hyB, by omega⟩
    have hneOld := List.ne_nil_of_mem hmOld
    have hv := Ctx.le_getD_max?_of_mem
      (L := (B.levelsOn s 0).sublists.map
        (fun ls => (ls.foldl (Ctx.Context.rightStep B) (q, 0)).2))
      (List.mem_map.mpr ⟨[N + 1, M + 1],
        List.mem_sublists.mpr hTwo, rfl⟩)
    change _ ≤ B.rightExt s 0 q at hv
    simpa only [List.foldl_cons, List.foldl_nil, Ctx.Context.rightStep, hw,
      List.head?_eq_some_head hneOld] using hv
  have hTwoLeft (q : ℕ) (hxq : x < q) (hyx : y < x) :
      2 ≤ B.leftExt s 0 q := by
    have hm : x ∈ (B.extPositions (N + 1)).filter (· < q) := by
      simp [hxB, hxq]
    have hnonempty := List.ne_nil_of_mem hm
    let w := ((B.extPositions (N + 1)).filter (· < q)).getLast hnonempty
    have hw : ((B.extPositions (N + 1)).filter (· < q)).getLast? = some w :=
      List.getLast?_eq_some_getLast hnonempty
    have hxw : x ≤ w := (hSortN.filter _).rel_getLast hm
    have hmOld : y ∈ (B.extPositions (M + 1)).filter (· < w) := by
      simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨hyB, by omega⟩
    have hneOld := List.ne_nil_of_mem hmOld
    have hv := Ctx.le_getD_max?_of_mem
      (L := (B.levelsOn s 0).sublists.map
        (fun ls => (ls.foldl (Ctx.Context.leftStep B) (q, 0)).2))
      (List.mem_map.mpr ⟨[N + 1, M + 1],
        List.mem_sublists.mpr hTwo, rfl⟩)
    change _ ≤ B.leftExt s 0 q at hv
    simpa only [List.foldl_cons, List.foldl_nil, Ctx.Context.leftStep, hw,
      List.getLast?_eq_some_getLast hneOld] using hv
  have hTransport (c : ℕ) :=
    ctx_part_pruning_history_transport B hPosB (support c) Ctx.Side.lower 0
  have hPosGroup (c : ℕ) : ∀ q j v,
      (group c).letterAt q = Ctx.Letter.ext j v → 1 ≤ j :=
    (hTransport c).1
  have hChild (c q : ℕ) : q ∈ (group c).childPositions ↔
      q ∈ B.childPositions ∧ color q = c := by
    have hh := (hTransport c).2.1
    change (group c).childPositions =
      B.childPositions.filter (· ∈ support c) at hh
    rw [hh]
    simp [support]
  have hHist (c j : ℕ) (hj : j ∈ B.levels) :
      (group c).extPositions j = B.extPositions j ∧
        (group c).sideAt j = B.sideAt j :=
    (hTransport c).2.2.1 j hj
  have hLevels (c : ℕ) (v : Ctx.Side) (top : ℕ) :
      (group c).levelsOn v top = B.levelsOn v top :=
    (hTransport c).2.2.2.1 v top
  have hExtensions (c : ℕ) (v : Ctx.Side) (top q : ℕ) :
      (group c).leftExt v top q = B.leftExt v top q ∧
        (group c).rightExt v top q = B.rightExt v top q :=
    (hTransport c).2.2.2.2.1 v top q
  have hOneGroup (c : ℕ) : 1 ∈ (group c).levels := hOne
  have hpGroup (c : ℕ) : p ∈ (group c).extPositions 1 := by
    rw [(hHist c 1 hOne).1]
    exact hpB
  have hSideGroup (c : ℕ) : (group c).sideAt 1 = t :=
    (hHist c 1 hOne).2.trans hBsideOne
  have hMaximumGroup (c : ℕ) : (group c).maximumAt 1 = 1 := by
    simpa only [group] using hBMaximumOne
  have hSmall (c : ℕ) :
      min ((match (group c).sideAt 1 with
        | Ctx.Side.lower => (group c).u
        | Ctx.Side.upper => (group c).a) - 1)
        ((group c).k - (group c).maximumAt 1) ≤ 4 := by
    rw [hSideGroup c, hMaximumGroup c]
    apply (Nat.min_le_left _ _).trans
    cases t <;> simp only [group, B] at hOppositeB ⊢ <;> omega
  have hYounger (c : ℕ) (rightward : Bool) :
      ∀ j ∈ (group c).levelsOn ((group c).sideAt 1) 1,
        ∀ z ∈ (group c).extPositions j,
          if rightward then z < p else p < z := by
    intro j hj z hz
    have hjmem := (List.mem_filter.mp hj).1
    have hjpos := Ctx.Context.one_le_of_mem_levels hjmem
    have hjpred := of_decide_eq_true (List.mem_filter.mp hj).2
    exfalso
    omega
  have hChildrenZero : ∀ q ∈ (group 0).childPositions,
      0 < (group 0).cupLimit q q ∧ 0 < (group 0).capLimit q q →
      if true then q < p else p < q := by
    intro q hq hactive
    have hc := (hChild 0 q).mp hq
    dsimp only [color] at hc
    by_cases hqp : q < p
    · simpa only [if_true] using hqp
    · simp [hqp] at hc
  have hChildrenOne : ∀ q ∈ (group 1).childPositions,
      0 < (group 1).cupLimit q q ∧ 0 < (group 1).capLimit q q →
      if false then q < p else p < q := by
    intro q hq hactive
    have hc := (hChild 1 q).mp hq
    have hnep := hChildNe q 1 p hc.1 hpB
    have hnlt : ¬ q < p := by
      intro hqp
      simpa [color, hqp] using hc.2
    simpa only [if_false] using (show p < q by omega)
  have hBoundZero :
      (∀ fuel, Ctx.Context.boundFuel fuel (group 0) ≤ (pairs 0).card) ∧
      (group 0).bound ≤ (pairs 0).card := by
    have hb := ctx_active_boundary_marker_rank_pair_union_bound
      (group 0) (hPosGroup 0) 1 p (hOneGroup 0) (hpGroup 0) true
      hChildrenZero (hYounger 0 true) s
      (by rw [hSideGroup 0]; exact Ne.symm hne) (hSmall 0)
    simpa only [pairs, active, I, Q, G, group] using hb
  have hBoundOne :
      (∀ fuel, Ctx.Context.boundFuel fuel (group 1) ≤ (pairs 1).card) ∧
      (group 1).bound ≤ (pairs 1).card := by
    have hb := ctx_active_boundary_marker_rank_pair_union_bound
      (group 1) (hPosGroup 1) 1 p (hOneGroup 1) (hpGroup 1) false
      hChildrenOne (hYounger 1 false) s
      (by rw [hSideGroup 1]; exact Ne.symm hne) (hSmall 1)
    simpa only [pairs, active, I, Q, G, group] using hb
  have hActiveChild (c q : ℕ) (hq : q ∈ active c) :
      q ∈ (group c).childPositions :=
    List.mem_toFinset.mp (Finset.mem_filter.mp hq).1
  have hQMono (A D : Finset ℕ) (hAD : A ⊆ D) : Q A ⊆ Q D := by
    intro z hz
    obtain ⟨hzProd, hzOrder⟩ := Finset.mem_filter.mp hz
    obtain ⟨hzLeft, hzRight⟩ := Finset.mem_product.mp hzProd
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hAD hzLeft, hAD hzRight⟩, hzOrder⟩
  have hPairSubOne (c : ℕ) (D : Finset ℕ)
      (hInside : ∀ q ∈ active c, I c q ⊆ D) : pairs c ⊆ Q D := by
    intro z hz
    obtain ⟨q, hq, hz⟩ := Finset.mem_biUnion.mp hz
    exact hQMono (I c q) D (hInside q hq) hz
  have hPairSubTwo (c : ℕ) (D E : Finset ℕ)
      (hInside : ∀ q ∈ active c, I c q ⊆ D ∨ I c q ⊆ E) :
      pairs c ⊆ Q D ∪ Q E := by
    intro z hz
    obtain ⟨q, hq, hz⟩ := Finset.mem_biUnion.mp hz
    rcases hInside q hq with hD | hE
    · exact Finset.mem_union_left _ (hQMono (I c q) D hD hz)
    · exact Finset.mem_union_right _ (hQMono (I c q) E hE hz)
  have hPairCard : (pairs 0).card + (pairs 1).card ≤ 11 := by
    rcases hbetween with hxy | hyx
    · have hSubZero : pairs 0 ⊆
          Q (Finset.Icc 1 2) ∪ Q (Finset.Icc 2 3) := by
        apply hPairSubTwo 0
        intro q hq
        have hqChild := hActiveChild 0 q hq
        have hqData := (hChild 0 q).mp hqChild
        have hqp : q < p := by
          have hc := hqData.2
          dsimp only [color] at hc
          by_cases h : q < p
          · exact h
          · simp [h] at hc
        have hqxne := hChildNe q (N + 1) x hqData.1 hxB
        rcases lt_or_gt_of_ne hqxne with hqx | hxq
        · apply Or.inl
          intro r hr
          have hrange := Finset.mem_Icc.mp hr
          have hright := hTwoRight q hqx (by omega)
          have hrightGroup : 2 ≤ (group 0).rightExt s 0 q := by
            rw [(hExtensions 0 s 0 q).2]
            exact hright
          exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        · apply Or.inr
          intro r hr
          have hrange := Finset.mem_Icc.mp hr
          have hleft := hOneLeft (N + 1) q x hNOn hxB hxq
          have hright := hOneRight (M + 1) q y hMOn hyB (by omega)
          have hleftGroup : 1 ≤ (group 0).leftExt s 0 q := by
            rw [(hExtensions 0 s 0 q).1]
            exact hleft
          have hrightGroup : 1 ≤ (group 0).rightExt s 0 q := by
            rw [(hExtensions 0 s 0 q).2]
            exact hright
          exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hSubOne : pairs 1 ⊆ Q (Finset.Icc 2 4) := by
        apply hPairSubOne 1
        intro q hq r hr
        have hqChild := hActiveChild 1 q hq
        have hqData := (hChild 1 q).mp hqChild
        have hqne := hChildNe q 1 p hqData.1 hpB
        have hnlt : ¬ q < p := by
          intro h
          simpa [color, h] using hqData.2
        have hpq : p < q := by omega
        have hleft := hOneLeft (N + 1) q x hNOn hxB (by omega)
        have hleftGroup : 1 ≤ (group 1).leftExt s 0 q := by
          rw [(hExtensions 1 s 0 q).1]
          exact hleft
        have hrange := Finset.mem_Icc.mp hr
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hCardZero : (pairs 0).card ≤ 5 := by
        have hCard : (Q (Finset.Icc 1 2) ∪ Q (Finset.Icc 2 3)).card = 5 := by
          decide
        rw [← hCard]
        exact Finset.card_le_card hSubZero
      have hCardOne : (pairs 1).card ≤ 6 := by
        have hCard : (Q (Finset.Icc 2 4)).card = 6 := by decide
        rw [← hCard]
        exact Finset.card_le_card hSubOne
      omega
    · have hSubZero : pairs 0 ⊆ Q (Finset.Icc 1 3) := by
        apply hPairSubOne 0
        intro q hq r hr
        have hqChild := hActiveChild 0 q hq
        have hqData := (hChild 0 q).mp hqChild
        have hqp : q < p := by
          have hc := hqData.2
          dsimp only [color] at hc
          by_cases h : q < p
          · exact h
          · simp [h] at hc
        have hright := hOneRight (N + 1) q x hNOn hxB (by omega)
        have hrightGroup : 1 ≤ (group 0).rightExt s 0 q := by
          rw [(hExtensions 0 s 0 q).2]
          exact hright
        have hrange := Finset.mem_Icc.mp hr
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hSubOne : pairs 1 ⊆
          Q (Finset.Icc 2 3) ∪ Q (Finset.Icc 3 4) := by
        apply hPairSubTwo 1
        intro q hq
        have hqChild := hActiveChild 1 q hq
        have hqData := (hChild 1 q).mp hqChild
        have hqne := hChildNe q (N + 1) x hqData.1 hxB
        have hpne := hChildNe q 1 p hqData.1 hpB
        have hnlt : ¬ q < p := by
          intro h
          simpa [color, h] using hqData.2
        have hpq : p < q := by omega
        rcases lt_or_gt_of_ne hqne with hqx | hxq
        · apply Or.inl
          intro r hr
          have hleft := hOneLeft (M + 1) q y hMOn hyB (by omega)
          have hright := hOneRight (N + 1) q x hNOn hxB hqx
          have hleftGroup : 1 ≤ (group 1).leftExt s 0 q := by
            rw [(hExtensions 1 s 0 q).1]
            exact hleft
          have hrightGroup : 1 ≤ (group 1).rightExt s 0 q := by
            rw [(hExtensions 1 s 0 q).2]
            exact hright
          have hrange := Finset.mem_Icc.mp hr
          exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        · apply Or.inr
          intro r hr
          have hleft := hTwoLeft q hxq (by omega)
          have hleftGroup : 2 ≤ (group 1).leftExt s 0 q := by
            rw [(hExtensions 1 s 0 q).1]
            exact hleft
          have hrange := Finset.mem_Icc.mp hr
          exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hCardZero : (pairs 0).card ≤ 6 := by
        have hCard : (Q (Finset.Icc 1 3)).card = 6 := by decide
        rw [← hCard]
        exact Finset.card_le_card hSubZero
      have hCardOne : (pairs 1).card ≤ 5 := by
        have hCard : (Q (Finset.Icc 2 3) ∪ Q (Finset.Icc 3 4)).card = 5 := by
          decide
        rw [← hCard]
        exact Finset.card_le_card hSubOne
      omega
  have hCover : ∀ q ∈ B.childPositions,
      color q ∈ ({0, 1} : Finset ℕ) := by
    intro q hq
    dsimp only [color]
    split_ifs <;> simp
  have hColor : ∀ q ∈ B.childPositions, ∀ r ∈ B.childPositions,
      q ≤ r → (∀ z, q ≤ z → z ≤ r → z ∈ B.childPositions) →
      color q = color r := by
    intro q hq r hr hqr hinterval
    by_cases hqp : q < p
    · have hrp : r < p := by
        by_contra h
        exact hpNotChild (hinterval p (by omega) (by omega))
      simp [color, hqp, hrp]
    · have hrp : ¬ r < p := by omega
      simp [color, hqp, hrp]
  have hDecomp :=
    ctx_bound_le_sum_run_group_prunings_of_actual_marker_global_five
      B hPosB t 1 p hOne hBsideOne hpB hOppositeB color
      ({0, 1} : Finset ℕ) hCover hColor
  change (∀ fuel, Ctx.Context.boundFuel fuel B ≤
      ({0, 1} : Finset ℕ).sum (fun c => (group c).bound)) ∧
      B.bound ≤ ({0, 1} : Finset ℕ).sum (fun c => (group c).bound) at hDecomp
  have hSum : ({0, 1} : Finset ℕ).sum (fun c => (group c).bound) =
      (group 0).bound + (group 1).bound := by simp
  rw [hSum] at hDecomp
  refine ⟨hpB, hBMaximumOne, ?_, ?_⟩
  · intro fuel
    exact (hDecomp.1 fuel).trans
      ((Nat.add_le_add hBoundZero.2 hBoundOne.2).trans hPairCard)
  · exact hDecomp.2.trans
      ((Nat.add_le_add hBoundZero.2 hBoundOne.2).trans hPairCard)

end ErdosSzekeres
