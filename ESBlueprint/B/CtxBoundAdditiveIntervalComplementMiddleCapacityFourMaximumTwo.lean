import ESBlueprint.B.CtxBoundAdditiveIntervalComplementMiddleCapacityFourBelowSaturation
import ESBlueprint.B.CtxSmallGlobalAxisRankTriplePotential
import ESBlueprint.B.CtxOldestAxisMaximumEraseNormalize
import ESBlueprint.B.CtxActiveTwoBoundaryMarkerRankUnionBound
import ErdosSzekeres.DecomposableContext

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Close both saturation bands in the reverse capacity-four orientation when outerMax>=2. Opposite-maximum erasure and the cubic rank potential charge the outer part by choose(k-1,3); the bracketed middle part costs at most the opposite ancestor capacity. Exact binomial-window identities pay the sum. Below saturation use the previous middle-capacity-four theorem.
Positive labels and one contiguous ancestor child run split into three nonempty blocks; distinct axes.
Middle ancestor capacity at most four and outer maximum at least two.
Arbitrary outer ancestor capacity, middle maximum, old history and block lengths; no sibling coupling or singleton-end premise. The outer-maximum-one saturation case remains separate.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_bound_additive_interval_complement_middle_capacity_four_maximum_two (σ : Ctx.Context)
  (hpositive : ∀ x j v, σ.letterAt x=Ctx.Letter.ext j v → 1≤j)
  (b l m r : ℕ) (hpos : σ.childPositions=List.range' b (l+m+r))
  (hl : 0<l) (hm : 0<m) (hr : 0<r)
  (outerSide middleSide : Ctx.Side) (hne : outerSide≠middleSide)
  (outerMax middleMax : ℕ) (houterMax : 2≤outerMax)
  (hchosen : (match middleSide with | Ctx.Side.lower => σ.cupLimit b b | Ctx.Side.upper => σ.capLimit b b)≤4) :
  (σ.part (List.range' b l ++ List.range' (b+l+m) r) outerSide outerMax).bound+
    (σ.part (List.range' (b+l) m) middleSide middleMax).bound≤σ.bound := by
  classical
  let C := σ.cupLimit b b
  let P := σ.capLimit b b
  let τ : Context := { σ with a := P + 1, u := C + 1, maxima := [] }
  let O := List.range' b l ++ List.range' (b + l + m) r
  let M := List.range' (b + l) m
  have hdis : ∀ p ∈ σ.childPositions, p ∈ O → p ∉ M := by
    intro p _ hp
    simp only [O, M, List.mem_append, List.mem_range'_1] at hp ⊢
    omega
  by_cases hbelow : (match outerSide with | Side.lower => C | Side.upper => P) ≤ σ.k-3
  · exact ctx_bound_additive_interval_complement_middle_capacity_four_below_saturation σ hpositive
      b l m r hpos hl hm hr outerSide middleSide hne outerMax middleMax hchosen
      (by cases outerSide <;> exact hbelow)
  by_cases hThree : (match middleSide with | Side.lower => C | Side.upper => P) ≤ 3
  · exact ctx_bound_additive_interval_complement_middle_capacity_three σ hpositive b l m r hpos
      hl hm hr outerSide middleSide hne outerMax middleMax (by omega)
      (by cases middleSide <;> exact hThree)
  by_cases hsmall : min C P ≤ 2
  · exact ctx_bound_additive_disjoint_single_run_small_axis σ hpositive b (l+m+r)
      hpos (by omega) hsmall O M outerSide middleSide hne outerMax middleMax hdis
  have hC : 3 ≤ C := by omega
  have hP : 3 ≤ P := by omega
  have hCk : C ≤ σ.k - 1 := by dsimp only [C, cupLimit]; omega
  have hPk : P ≤ σ.k - 1 := by dsimp only [P, capLimit]; omega
  have hτpos : ∀ x j v, τ.letterAt x = Letter.ext j v → 1 ≤ j := hpositive
  have hτchildren : τ.childPositions = σ.childPositions := rfl
  have hτlimits (p : ℕ) : τ.cupLimit p p = C ∧ τ.capLimit p p = P := by
    constructor
    · simp [τ, cupLimit, chainExt, joinExt, leftExt, rightExt, levelsOn, levels,
        Nat.min_eq_left hCk]
    · simp [τ, capLimit, chainExt, joinExt, leftExt, rightExt, levelsOn, levels,
        Nat.min_eq_left hPk]
  have hPartPositive (ρ : Context) (keep : List ℕ) (v : Side) (m : ℕ) :
      ∀ x j w, (ρ.part keep v m).letterAt x = Letter.ext j w → 1 ≤ j := by
    intro x j w hx
    have hxl : x < ρ.word.length := by
      by_contra h
      have hn := letterAt_of_length_le (ρ.part keep v m)
        (show (ρ.part keep v m).word.length ≤ x by rw [part_word_length]; omega)
      rw [hn] at hx
      cases hx
    cases he : ρ.letterAt x with
    | child =>
      rw [part_letterAt_of_child ρ keep v m hxl he] at hx
      split at hx
      · cases hx
      · cases hx
        omega
    | ext oldLevel oldSide =>
      rw [part_letterAt_of_ext ρ keep v m hxl he] at hx
      cases hx
      omega
  have hNormalize (keep : List ℕ) (v : Side) (newMax : ℕ) :
      (σ.part keep v newMax).bound = (τ.part keep v newMax).bound := by
    let π := σ.part keep v newMax
    have hHist : π.a = σ.a ∧ π.u = σ.u ∧ π.k = σ.k ∧
        π.maxima.length = 1 + σ.maxima.length ∧
        (∀ j, 1 ≤ j → π.extPositions (j + 1) = σ.extPositions j) ∧
        (∀ j, 1 ≤ j → π.sideAt (j + 1) = σ.sideAt j) ∧
        (∀ j, 1 ≤ j → π.maximumAt (j + 1) = σ.maximumAt j) := by
      refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · change (newMax :: σ.maxima).length = 1 + σ.maxima.length
        simp only [List.length_cons]
        omega
      · intro j hj
        exact part_extPositions_succ σ keep v newMax hj
      · intro j hj
        exact part_sideAt_succ σ keep v newMax hj
      · intro j hj
        exact part_maximumAt_succ σ keep v newMax hj
    have hNew : ∀ j x, 1 ≤ j → j ≤ 1 → x ∈ π.extPositions j → x ∈ σ.childPositions := by
      intro j x hj hj1 hx
      have he : j = 1 := by omega
      subst j
      change x ∈ (σ.part keep v newMax).extPositions 1 at hx
      rw [part_extPositions_one hpositive keep v newMax] at hx
      exact (List.mem_filter.mp hx).1
    have hChild : ∀ x ∈ π.childPositions, x ∈ σ.childPositions := by
      intro x hx
      change x ∈ (σ.part keep v newMax).childPositions at hx
      rw [part_childPositions] at hx
      exact (List.mem_filter.mp hx).1
    have h := (ctx_single_run_descendant_bound_normalize σ b (l+m+r) hpos π 1 hHist hNew hChild
      (hPartPositive σ keep v newMax)).2
    exact h
  have hrunBound : ∀ (ρ : Context) (a n : ℕ), 0 < n →
      ρ.childPositions = List.range' a n →
      ρ.bound = baseOf (ρ.cupLimit a a) (ρ.capLimit a a) ρ.k := by
    intro ρ a n hn hps
    have hmem : ∀ p, p ∈ ρ.childPositions ↔ a ≤ p ∧ p < a + n := by
      intro p
      rw [hps, List.mem_range'_1]
    let starts := (List.range ρ.word.length).filter fun p =>
      ρ.letterAt p = Letter.child ∧ (p = 0 ∨ ρ.letterAt (p - 1) ≠ Letter.child)
    have hsubset : starts.toFinset ⊆ ({a} : Finset ℕ) := by
      intro p hp
      have hstart : p < ρ.word.length ∧ ρ.letterAt p = Letter.child ∧
          (p = 0 ∨ ρ.letterAt (p - 1) ≠ Letter.child) := by
        simpa [starts] using hp
      have hp' := (hmem p).mp
        (by simpa [childPositions] using And.intro hstart.1 hstart.2.1)
      simp only [Finset.mem_singleton]
      by_contra hpa
      have hprev : p - 1 ∈ ρ.childPositions := (hmem (p - 1)).mpr ⟨by omega, by omega⟩
      have hprev' : ρ.letterAt (p - 1) = Letter.child :=
        of_decide_eq_true (List.mem_filter.mp hprev).2
      rcases hstart.2.2 with hz | hnot
      · omega
      · exact hnot hprev'
    have hruns : ρ.numRuns ≤ 1 := by
      calc
        ρ.numRuns = starts.toFinset.card :=
          (List.toFinset_card_of_nodup (List.nodup_range.filter _)).symm
        _ ≤ ({a} : Finset ℕ).card := Finset.card_le_card hsubset
        _ = 1 := by simp
    simp [bound, boundFuel, hruns, base_eq_baseOf, hps, List.head?_range', Nat.ne_of_gt hn]
  have hroot : σ.bound = baseOf C P σ.k :=
    hrunBound σ b (l+m+r) (by omega) hpos
  let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
  have hk4 : 4≤σ.k := by omega
  have hCubic (σ : Context)
      (hpositive : ∀ p j v, σ.letterAt p=Letter.ext j v → 1≤j)
      (s t : Side) (hne : s≠t) (hglobal : G σ s≤5)
      (N : ℕ) (hN : N ∈ σ.levels) (hside : σ.sideAt N=t)
      (hterminal : ∀ j ∈ σ.levelsOn t 0, j≤N) :
      σ.bound≤(min (G σ t) (σ.k-σ.maximumAt N)-1+2).choose 3 := by
    classical
    let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
    let B := min (G σ t) (σ.k - σ.maximumAt N)
    let f : Letter → Letter := fun z => match z with
      | Letter.child => Letter.child
      | Letter.ext j v => Letter.ext
          (if j = N then σ.maxima.length else if N < j then j - 1 else j) v
    let E : Context := { σ with word := σ.word.map f, maxima := σ.maxima.eraseIdx (N - 1) }
    let ν : Context := match σ.sideAt N with
      | Side.lower => { E with u := min σ.u (σ.k - σ.maximumAt N) }
      | Side.upper => { E with a := min σ.a (σ.k - σ.maximumAt N) }
    change σ.bound ≤ (B-1+2).choose 3
    have hn := ctx_oldest_axis_maximum_erase_normalize σ N hN
      (by simpa only [hside] using hterminal)
    have hνFuel : ∀ fuel, boundFuel fuel σ ≤ boundFuel fuel ν := hn.2.2.2.2.1
    have hνBound : σ.bound ≤ ν.bound := hn.2.2.2.2.2
    have hNpos : 1 ≤ N := one_le_of_mem_levels hN
    have hD : 1 ≤ σ.maxima.length := by
      have hp := List.length_pos_iff.mpr (List.ne_nil_of_mem hN)
      simp only [levels, List.length_map, List.length_range] at hp
      omega
    have hνWord : ν.word = σ.word.map f := by cases hs : σ.sideAt N <;> simp [ν, hs, E]
    have hνLetter (r : ℕ) : ν.letterAt r = f (σ.letterAt r) := by
      simp only [letterAt, hνWord, List.getElem?_map]
      cases σ.word[r]? <;> rfl
    have hνPos : ∀ r j v, ν.letterAt r = Letter.ext j v → 1 ≤ j := by
      intro r j v hj
      rw [hνLetter] at hj
      cases he : σ.letterAt r with
      | child =>
        simp only [he, f] at hj
        cases hj
      | ext i z =>
        rw [he] at hj
        have hi := hpositive r i z he
        have hnew : 1 ≤ (if i = N then σ.maxima.length else if N < i then i - 1 else i) := by
          split_ifs <;> omega
        change Letter.ext (if i = N then σ.maxima.length else if N < i then i - 1 else i) z =
          Letter.ext j v at hj
        cases hj
        exact hnew
    have hνChosen : G ν s = G σ s := by
      cases s <;> cases t
      · exact False.elim (hne rfl)
      · simp only [G, ν, hside]
        rfl
      · simp only [G, ν, hside]
        rfl
      · exact False.elim (hne rfl)
    have hνGlobal : G ν s ≤ 5 := by rw [hνChosen]; exact hglobal
    have hνOpposite : G ν t = B := by cases t <;> simp only [G, ν, hside, B]
    have hh := ctx_small_global_axis_rank_triple_potential ν hνPos s t hne hνGlobal
    have hb : ν.bound≤(G ν t-1+2).choose 3 := by cases t <;> exact hh.2.1.trans hh.2.2.1
    rw [hνOpposite] at hb
    exact hνBound.trans hb
  have hChild (p : ℕ) : p ∈ τ.childPositions ↔ b≤p ∧ p<b+(l+m+r) := by
    rw [hτchildren,hpos,List.mem_range'_1]
  have hGlobalPart (ks : List ℕ) (v u : Side) (q : ℕ) : G (τ.part ks v q) u=G τ u := by
    cases u <;> rfl
  have hGlobal (v : Side) (hcap : (match v with | Side.lower => C | Side.upper => P)≤4) :
      G τ v≤5 := by
    cases v with
    | lower =>
      change C≤4 at hcap
      change C+1≤5
      omega
    | upper =>
      change P≤4 at hcap
      change P+1≤5
      omega
  have hOuter (v u : Side) (hne' : v≠u)
      (hcap : (match v with | Side.lower => C | Side.upper => P)≤4) :
      (τ.part O u outerMax).bound≤(σ.k-1).choose 3 := by
    let A := τ.part O u outerMax
    have hOne : 1 ∈ A.levels := by simp only [A,part_levels,List.mem_cons,true_or]
    have hx : b+l ∈ A.extPositions 1 := by
      rw [part_extPositions_one hτpos]
      refine List.mem_filter.mpr ⟨(hChild _).mpr ⟨by omega,by omega⟩,?_⟩
      have hh : b+l ∉ O := by simp only [O,List.mem_append,List.mem_range'_1]; omega
      simp [hh]
    have hs : A.sideAt 1=u := part_sideAt_one_of_mem hτpos O u outerMax hx
    have ht : ∀ j ∈ A.levelsOn u 0, j≤1 := by
      intro j hj
      have hmem := (List.mem_filter.mp hj).1
      have he : j=1 := by simpa [A,part,τ,levels] using hmem
      omega
    have hg : G A v≤5 := by rw [hGlobalPart]; exact hGlobal v (by cases v <;> exact hcap)
    have hh := hCubic A (hPartPositive τ O u outerMax) v u hne' hg 1 hOne hs ht
    rw [part_maximumAt_one] at hh
    have hbound : min (G A u) (σ.k-outerMax)-1+2≤σ.k-1 := by
      have hmin := Nat.min_le_right (G A u) (σ.k-outerMax)
      omega
    exact hh.trans (Nat.choose_le_choose 3 hbound)
  have hMiddle (v u : Side) (hne' : v≠u)
      (hcap : (match v with | Side.lower => C | Side.upper => P)≤4) :
      (τ.part M v middleMax).bound≤G τ u-1 := by
    let A := τ.part M v middleMax
    have hOne : 1 ∈ A.levels := by simp only [A,part_levels,List.mem_cons,true_or]
    have hMark (q : ℕ) (hq : q ∈ τ.childPositions) (hn : q ∉ M) : q ∈ A.extPositions 1 := by
      rw [part_extPositions_one hτpos]
      exact List.mem_filter.mpr ⟨hq,by simp [hn]⟩
    have hL : b ∈ A.extPositions 1 := hMark b ((hChild _).mpr ⟨le_rfl,by omega⟩)
      (by simp only [M,List.mem_range'_1]; omega)
    have hR : b+l+m ∈ A.extPositions 1 := hMark (b+l+m) ((hChild _).mpr ⟨by omega,by omega⟩)
      (by simp only [M,List.mem_range'_1]; omega)
    have hs : A.sideAt 1=v := part_sideAt_one_of_mem hτpos M v middleMax hL
    have hInside : ∀ p ∈ A.childPositions, b<p ∧ p<b+l+m := by
      intro p hp
      rw [part_childPositions] at hp
      have hpm : p ∈ M := of_decide_eq_true (List.mem_filter.mp hp).2
      have hh : b+l≤p ∧ p<b+l+m := List.mem_range'_1.mp hpm
      omega
    have hg : G A v≤5 := by rw [hGlobalPart]; exact hGlobal v (by cases v <;> exact hcap)
    have hsmall : min ((match (generalizing := false) A.sideAt 1 with
        | Side.lower => A.u | Side.upper => A.a)-2) (A.k-A.maximumAt 1)≤3 := by
      rw [hs]
      apply (Nat.min_le_left _ _).trans
      change G A v-2≤3
      omega
    have hh := ctx_active_two_boundary_marker_rank_union_bound A (hPartPositive τ M v middleMax)
      1 b (b+l+m) hOne hL hR (fun p hp _ => hInside p hp)
      (by simp [levelsOn_one]) u (by rw [hs]; exact hne') hsmall
    let active := A.childPositions.toFinset.filter (fun p => 0<A.cupLimit p p ∧ 0<A.capLimit p p)
    let R := active.biUnion (fun p => Finset.Icc (A.leftExt u 0 p+1) (G A u-1-A.rightExt u 0 p))
    have hb : A.bound≤R.card := by cases u <;> exact hh.2
    have hsub : R ⊆ Finset.Icc 1 (G τ u-1) := by
      intro z hz
      obtain ⟨p,_,hz⟩ := Finset.mem_biUnion.mp hz
      have he := Finset.mem_Icc.mp hz
      rw [hGlobalPart] at he
      exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
    exact hb.trans (by simpa using Finset.card_le_card hsub)
  have hBaseSwap (x y k : ℕ) (hx : x ≤ k - 1) (hy : y ≤ k - 1) :
      baseOf x y k = baseOf y x k := by
    have hz (r : ℕ) : baseOf 0 r k = 0 := by simp [baseOf]
    have hz' (r : ℕ) : baseOf r 0 k = 0 := by simp [baseOf]
    apply Nat.le_antisymm
    · have hh := ctx_base_cross_axis_transfer 0 y x x k le_rfl hx (by omega)
      simpa only [Nat.zero_add, hz, hz', Nat.add_zero] using hh
    · have hh := ctx_base_cross_axis_transfer 0 x y y k le_rfl hy (by omega)
      simpa only [Nat.zero_add, hz, hz', Nat.add_zero] using hh
  have hFourEdges (k : ℕ) (hk : 5≤k) (p : ℕ) (hp : p=k-1 ∨ p=k-2) :
      baseOf 4 p k=(k-1).choose 3+p := by
    have hPascal := Nat.choose_succ_succ (k-2) 2
    simp only [Nat.succ_eq_add_one,Nat.reduceAdd,show k-2+1=k-1 by omega] at hPascal
    rcases hp with rfl | rfl
    · unfold baseOf
      rw [if_neg (by omega),if_neg (by omega),
        decomposableThreshold_eq_window (by omega) (by omega) (by omega)]
      have he : decomposableBinomialWindow (k-1+1) (4+1) k=
          1+(k-2)+(k-2).choose 2+(k-2).choose 3 := by
        have hh : k-1+1=k := by omega
        rw [hh]
        norm_num [decomposableBinomialWindow,Finset.sum_Icc_succ_top]
      rw [he]
      omega
    · unfold baseOf
      rw [if_neg (by omega),if_neg (by omega),
        decomposableThreshold_eq_window (by omega) (by omega) (by omega)]
      have he : decomposableBinomialWindow (k-2+1) (4+1) k=
          (k-2)+(k-2).choose 2+(k-2).choose 3 := by
        have hh : k-(k-2+1)=1 := by omega
        norm_num [decomposableBinomialWindow,hh,Finset.sum_Icc_succ_top]
      rw [he]
      omega
  change (σ.part O outerSide outerMax).bound+(σ.part M middleSide middleMax).bound≤σ.bound
  rw [hNormalize,hNormalize,hroot]
  cases outerSide <;> cases middleSide
  · exact False.elim (hne rfl)
  · change P≤4 at hchosen
    change ¬P≤3 at hThree
    change ¬C≤σ.k-3 at hbelow
    have hP4 : P=4 := by omega
    have hk5 : 5≤σ.k := by omega
    have hb := Nat.add_le_add (hOuter Side.upper Side.lower (by decide) hchosen)
      (hMiddle Side.upper Side.lower (by decide) hchosen)
    change (τ.part O Side.lower outerMax).bound+(τ.part M Side.upper middleMax).bound≤
      (σ.k-1).choose 3+C at hb
    rw [hP4,hBaseSwap C 4 σ.k hCk (by omega),hFourEdges σ.k hk5 C (by omega)]
    exact hb
  · change C≤4 at hchosen
    change ¬C≤3 at hThree
    change ¬P≤σ.k-3 at hbelow
    have hC4 : C=4 := by omega
    have hk5 : 5≤σ.k := by omega
    have hb := Nat.add_le_add (hOuter Side.lower Side.upper (by decide) hchosen)
      (hMiddle Side.lower Side.upper (by decide) hchosen)
    change (τ.part O Side.upper outerMax).bound+(τ.part M Side.lower middleMax).bound≤
      (σ.k-1).choose 3+P at hb
    rw [hC4,hFourEdges σ.k hk5 P (by omega)]
    exact hb
  · exact False.elim (hne rfl)

end ErdosSzekeres
