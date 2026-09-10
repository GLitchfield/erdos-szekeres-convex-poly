import ESBlueprint.B.CtxBoundAdditiveIntervalComplementCapacityFourBelowSaturation
import ESBlueprint.B.CtxBoundAdditiveIntervalComplementCapacityThreeFull
import ErdosSzekeres.DecomposableContext

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Prove interval/complement additivity for ancestor chosen capacity at most four, opposite capacity P with P>=12 or (P>=6 and P<=k-2), and outer maximum at most k-6. Below saturation use the checked capacity-four consequence; in the top two capacity bands, three Pascal combinations pay the actual-marker square estimate. Positive external labels and a contiguous ancestor child run split into three nonempty blocks. Distinct axes; chosen ancestor capacity at most four; opposite ancestor capacity P with P>=12 or (P>=6 and P<=k-2). Outer maximum plus six is at most k, and sibling maxima sum to k-1. No singleton-end, history-depth, outer-length or recursive-potential hypothesis. The outer maximum k-5 band and smaller opposite capacities remain outside this theorem.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_bound_additive_interval_complement_capacity_four_wide_low_maximum (σ : Ctx.Context)
  (hpositive : ∀ x j v, σ.letterAt x = Ctx.Letter.ext j v → 1 ≤ j)
  (b l m r : ℕ) (hpos : σ.childPositions = List.range' b (l + m + r))
  (hl : 0 < l) (hm : 0 < m) (hr : 0 < r)
  (outerSide middleSide : Ctx.Side) (hne : outerSide ≠ middleSide)
  (outerMax middleMax : ℕ)
  (hchosen : (match outerSide with
    | Ctx.Side.lower => σ.cupLimit b b | Ctx.Side.upper => σ.capLimit b b) ≤ 4)
  (hwide : let P := (match middleSide with
    | Ctx.Side.lower => σ.cupLimit b b | Ctx.Side.upper => σ.capLimit b b)
    12 ≤ P ∨ (6 ≤ P ∧ P ≤ σ.k - 2))
  (hlow : outerMax + 6 ≤ σ.k)
  (hcoupling : outerMax + middleMax = σ.k - 1) :
  (σ.part (List.range' b l ++ List.range' (b + l + m) r) outerSide outerMax).bound +
    (σ.part (List.range' (b + l) m) middleSide middleMax).bound ≤ σ.bound := by
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
  by_cases hbelow : (match middleSide with | Side.lower => C | Side.upper => P) ≤ σ.k-3
  · exact ctx_bound_additive_interval_complement_capacity_four_below_saturation σ hpositive
      b l m r hpos hl hm hr outerSide middleSide hne outerMax middleMax hchosen
      (by cases middleSide <;> exact hbelow)
  by_cases hThree : (match outerSide with | Side.lower => C | Side.upper => P) ≤ 3
  · exact ctx_bound_additive_interval_complement_capacity_three_full σ hpositive b l m r hpos
      hl hm hr outerSide middleSide hne outerMax middleMax hThree hcoupling
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
  have hchild (p : ℕ) : p ∈ τ.childPositions ↔ b ≤ p ∧ p < b + (l+m+r) := by
    rw [hτchildren, hpos, List.mem_range'_1]
  have hPartSide (keep : List ℕ) (v : Side) (n q : ℕ)
      (hq : q ∈ τ.childPositions) (hnot : q ∉ keep) :
      (τ.part keep v n).sideAt 1 = v := by
    apply part_sideAt_one_of_mem hτpos keep v n (q := q)
    rw [part_extPositions_one hτpos keep v n]
    exact List.mem_filter.mpr ⟨hq, by simp [hnot]⟩
  have houterSide (v : Side) : (τ.part O v outerMax).sideAt 1 = v := by
    apply hPartSide O v outerMax (b+l)
    · exact (hchild _).mpr ⟨by omega, by omega⟩
    · simp only [O, List.mem_append, List.mem_range'_1]
      omega
  have hOuter (v w : Side) (hvw : v ≠ w)
      (hcap : (match v with | Side.lower => C | Side.upper => P) ≤ 4) :
      (τ.part O v outerMax).bound ≤
        (match w with | Side.lower => C | Side.upper => P) ^ 2 := by
    have hj : 1 ∈ (τ.part O v outerMax).levels := by rw [part_levels]; simp
    have hx : b+l ∈ (τ.part O v outerMax).extPositions 1 := by
      rw [part_extPositions_one hτpos O v outerMax]
      refine List.mem_filter.mpr ⟨(hchild _).mpr ⟨by omega, by omega⟩, ?_⟩
      have hn : b+l ∉ O := by
        simp only [O, List.mem_append, List.mem_range'_1]
        omega
      simp [hn]
    have hg : (match v with
        | Side.lower => (τ.part O v outerMax).u
        | Side.upper => (τ.part O v outerMax).a) ≤ 5 := by
      cases v with
      | lower =>
        change C + 1 ≤ 5
        change C ≤ 4 at hcap
        omega
      | upper =>
        change P + 1 ≤ 5
        change P ≤ 4 at hcap
        omega
    let α := τ.part O v outerMax
    let budget := match w with | Side.lower => C | Side.upper => P
    let active := α.childPositions.toFinset.filter (fun p => 0 < α.cupLimit p p ∧ 0 < α.capLimit p p)
    let ranks := active.biUnion (fun p => Finset.Icc (α.leftExt w 0 p + 1) (budget - α.rightExt w 0 p))
    have hb := (ctx_actual_marker_rank_square_potential α (hPartPositive τ O v outerMax)
      v w hvw 1 (b+l) hj (houterSide v) hx hg).2
    have hb' : α.bound ≤ ranks.card ^ 2 := by
      cases w <;> exact hb
    have hSub : ranks ⊆ Finset.Icc 1 budget := by
      intro z hz
      obtain ⟨p, _, hz⟩ := Finset.mem_biUnion.mp hz
      have hh := Finset.mem_Icc.mp hz
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hCard : ranks.card ≤ budget := by simpa using Finset.card_le_card hSub
    exact hb'.trans (Nat.pow_le_pow_left hCard 2)
  have hsplit : τ.childPositions = List.range' b l ++ M ++ List.range' (b+l+m) r := by
    rw [hτchildren, hpos]
    simp only [M, List.range'_append_1, Nat.add_assoc]
  have hleftEmpty : (List.range' b l).filter (· ∈ M) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro p hp
    have hp' := List.mem_range'_1.mp hp
    have hn : p ∉ M := by simp only [M, List.mem_range'_1]; omega
    simpa only [decide_eq_true_eq] using hn
  have hrightEmpty : (List.range' (b+l+m) r).filter (· ∈ M) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro p hp
    have hp' := List.mem_range'_1.mp hp
    have hn : p ∉ M := by simp only [M, List.mem_range'_1]; omega
    simpa only [decide_eq_true_eq] using hn
  have hself : M.filter (· ∈ M) = M := List.filter_eq_self.mpr (fun p hp => by simp [hp])
  have hmiddlePos (v : Side) : (τ.part M v middleMax).childPositions = List.range' (b+l) m := by
    change (τ.part M v middleMax).childPositions = M
    rw [part_childPositions, hsplit]
    simp only [List.filter_append, hleftEmpty, hrightEmpty, hself, List.nil_append, List.append_nil]
  have hMiddleMaximum (v : Side) :
      middleMax ≤ (τ.part M v middleMax).joinExt v (b+l) (b+l) := by
    have hbl : b ∈ τ.childPositions := (hchild _).mpr ⟨le_rfl, by omega⟩
    have hnl : b ∉ M := by simp only [M, List.mem_range'_1]; omega
    have hs := hPartSide M v middleMax b hbl hnl
    have hj : 1 ∈ (τ.part M v middleMax).levelsOn v 0 := by
      rw [part_levelsOn_self_zero hs]
      simp
    have hh := le_joinExt_of_mem_levelsOn hj (b+l) (b+l)
    rw [part_maximumAt_one] at hh
    omega
  have hMiddleLower : (τ.part M Side.lower middleMax).bound ≤ baseOf outerMax P σ.k := by
    rw [hrunBound _ (b+l) m hm (hmiddlePos Side.lower)]
    have hcap := (ctx_part_limits_le τ M Side.lower middleMax (b+l) (b+l)).2
    rw [(hτlimits _).2] at hcap
    have hmax := hMiddleMaximum Side.lower
    have hcup : (τ.part M Side.lower middleMax).cupLimit (b+l) (b+l) ≤ outerMax := by
      dsimp only [cupLimit]
      have hk : (τ.part M Side.lower middleMax).k = σ.k := rfl
      rw [hk]
      omega
    exact baseOf_mono hcup hcap
  have hMiddleUpper : (τ.part M Side.upper middleMax).bound ≤ baseOf C outerMax σ.k := by
    rw [hrunBound _ (b+l) m hm (hmiddlePos Side.upper)]
    have hcup := (ctx_part_limits_le τ M Side.upper middleMax (b+l) (b+l)).1
    rw [(hτlimits _).1] at hcup
    have hmax := hMiddleMaximum Side.upper
    have hcap : (τ.part M Side.upper middleMax).capLimit (b+l) (b+l) ≤ outerMax := by
      dsimp only [capLimit]
      have hk : (τ.part M Side.upper middleMax).k = σ.k := rfl
      rw [hk]
      omega
    exact baseOf_mono hcup hcap
  have hThreeLeft (p k : ℕ) (hp : 2 ≤ p) (hpk : p ≤ k - 2) :
      baseOf 3 p k = (p + 1).choose 2 := by
    unfold baseOf
    rw [if_neg (by omega), if_neg (by omega),
      decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
    have hrow : p + 1 + (3 + 1) - 4 = p + 1 := by omega
    rw [hrow, Nat.choose_symm (by omega : 2 ≤ p + 1)]
  have hThreeRight (p k : ℕ) (hp : 2 ≤ p) (hpk : p ≤ k - 2) :
      baseOf p 3 k = (p + 1).choose 2 := by
    unfold baseOf
    rw [if_neg (by omega), if_neg (by omega),
      decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
    have hrow : 3 + 1 + (p + 1) - 4 = p + 1 := by omega
    rw [hrow]
  have hBaseSwap (x y k : ℕ) (hx : x ≤ k - 1) (hy : y ≤ k - 1) :
      baseOf x y k = baseOf y x k := by
    have hz (r : ℕ) : baseOf 0 r k = 0 := by simp [baseOf]
    have hz' (r : ℕ) : baseOf r 0 k = 0 := by simp [baseOf]
    apply Nat.le_antisymm
    · have hh := ctx_base_cross_axis_transfer 0 y x x k le_rfl hx (by omega)
      simpa only [Nat.zero_add, hz, hz', Nat.add_zero] using hh
    · have hh := ctx_base_cross_axis_transfer 0 x y y k le_rfl hy (by omega)
      simpa only [Nat.zero_add, hz, hz', Nat.add_zero] using hh
  have hSaturatedBaseEdge (k : ℕ) (hk : 4 ≤ k) :
      baseOf 3 (k - 1) k = (k - 2).choose 2 + (k - 1) := by
    unfold baseOf
    rw [if_neg (by omega), if_neg (by omega)]
    rw [show k - 1 + 1 = k by omega]
    rw [decomposableThreshold_eq_window (by omega) (by omega) (by omega)]
    have hw : decomposableBinomialWindow k (3 + 1) k =
        1 + (k - 2) + (k - 2).choose 2 := by
      norm_num [decomposableBinomialWindow, Finset.sum_Icc_succ_top]
    rw [hw]
    omega
  have hThreeLower (w k : ℕ) (hw : 12 ≤ w) (hwk : w ≤ k-1) :
      (w-1).choose 2 + w ≤ baseOf 3 w k := by
    by_cases hbelow : w ≤ k-2
    · rw [hThreeLeft w k (by omega) hbelow]
      have hA := Nat.choose_succ_succ (w-1) 1
      have hB := Nat.choose_succ_succ w 1
      have hpred : w-1+1 = w := by omega
      simp only [Nat.succ_eq_add_one, Nat.choose_one_right, Nat.reduceAdd, hpred] at hA hB
      omega
    · have he : w = k-1 := by omega
      rw [he, hSaturatedBaseEdge k (by omega)]
      have hp : k-1-1 = k-2 := by omega
      rw [hp]
  have hDouble (n : ℕ) (hn : 1 ≤ n) : n * (n-1) = n.choose 2 * 2 := by
    have hh := Nat.add_one_mul_choose_eq (n-1) 1
    simpa only [Nat.sub_add_cancel hn, Nat.choose_one_right, Nat.reduceAdd] using hh
  have hSquareBudget (w k : ℕ) (hw : 12 ≤ w) (hwk : w ≤ k-1) :
      w ^ 2 ≤ baseOf 3 w k + baseOf 3 (w-3) k + baseOf 3 (w-4) k := by
    have hA := hThreeLower w k hw hwk
    rw [hThreeLeft (w-3) k (by omega) (by omega),
      hThreeLeft (w-4) k (by omega) (by omega)]
    have hsub2 : w-3+1 = w-2 := by omega
    have hsub3 : w-4+1 = w-3 := by omega
    rw [hsub2, hsub3]
    have hd1 := hDouble (w-1) (by omega)
    have hd2 := hDouble (w-2) (by omega)
    have hd3 := hDouble (w-3) (by omega)
    have hs1 : w-1+1 = w := by omega
    have hs2 : w-2+2 = w := by omega
    have hs3 : w-3+3 = w := by omega
    have hs4 : w-4+4 = w := by omega
    have hp1 : w-1-1 = w-2 := by omega
    have hp2 : w-2-1 = w-3 := by omega
    have hp3 : w-3-1 = w-4 := by omega
    rw [hp1] at hd1
    rw [hp2] at hd2
    rw [hp3] at hd3
    have hs12 : w-12+12 = w := by omega
    have hnonneg : 0 ≤ (w-12)*(w-1) := Nat.zero_le _
    nlinarith
  have hPay (w q k : ℕ) (hw : 12 ≤ w) (hwk : w ≤ k-1) (hq : q+5 ≤ w) :
      w ^ 2 + baseOf 4 q k ≤ baseOf 4 w k := by
    have h1 := ctx_base_pascal_combine 3 w 4 (w-3) 4 w k
      (by omega) hwk (by omega) le_rfl le_rfl (by omega) (by omega)
    have h2 := ctx_base_pascal_combine 3 (w-3) 4 (w-4) 4 (w-3) k
      (by omega) (by omega) (by omega) le_rfl le_rfl (by omega) (by omega)
    have h3 := ctx_base_pascal_combine 3 (w-4) 4 (w-5) 4 (w-4) k
      (by omega) (by omega) (by omega) le_rfl le_rfl (by omega) (by omega)
    have hqB : baseOf 4 q k ≤ baseOf 4 (w-5) k := baseOf_mono le_rfl (by omega)
    have hs := hSquareBudget w k hw hwk
    omega
  have hSquareBudgetNext (w k : ℕ) (hw : 6 ≤ w) (hwk : w ≤ k-2) :
      w ^ 2 ≤ baseOf 3 w k + baseOf 3 (w-2) k + baseOf 3 (w-3) k := by
    rw [hThreeLeft w k (by omega) hwk,
      hThreeLeft (w-2) k (by omega) (by omega),
      hThreeLeft (w-3) k (by omega) (by omega)]
    have hsub1 : w-2+1 = w-1 := by omega
    have hsub2 : w-3+1 = w-2 := by omega
    rw [hsub1, hsub2]
    have hd0 := hDouble (w+1) (by omega)
    have hd1 := hDouble (w-1) (by omega)
    have hd2 := hDouble (w-2) (by omega)
    have hs1 : w-1+1 = w := by omega
    have hs2 : w-2+2 = w := by omega
    have hs3 : w-3+3 = w := by omega
    have hp1 : w-1-1 = w-2 := by omega
    have hp2 : w-2-1 = w-3 := by omega
    simp only [Nat.add_sub_cancel] at hd0
    rw [hp1] at hd1
    rw [hp2] at hd2
    have hs6 : w-6+6 = w := by omega
    have hnonneg : 0 ≤ (w-6)*(w-1) := Nat.zero_le _
    nlinarith
  have hPayNext (w q k : ℕ) (hw : 6 ≤ w) (hwk : w ≤ k-2) (hq : q+4 ≤ w) :
      w ^ 2 + baseOf 4 q k ≤ baseOf 4 w k := by
    have h1 := ctx_base_pascal_combine 3 w 4 (w-2) 4 w k
      (by omega) (by omega) (by omega) le_rfl le_rfl (by omega) (by omega)
    have h2 := ctx_base_pascal_combine 3 (w-2) 4 (w-3) 4 (w-2) k
      (by omega) (by omega) (by omega) le_rfl le_rfl (by omega) (by omega)
    have h3 := ctx_base_pascal_combine 3 (w-3) 4 (w-4) 4 (w-3) k
      (by omega) (by omega) (by omega) le_rfl le_rfl (by omega) (by omega)
    have hqB : baseOf 4 q k ≤ baseOf 4 (w-4) k := baseOf_mono le_rfl (by omega)
    have hs := hSquareBudgetNext w k hw hwk
    omega
  have hPayWide (w q k : ℕ) (hw : 12 ≤ w ∨ (6 ≤ w ∧ w ≤ k-2)) (hwk : w ≤ k-1)
      (hband : ¬ w ≤ k-3) (hq : q+6 ≤ k) : w^2 + baseOf 4 q k ≤ baseOf 4 w k := by
    by_cases hnext : w ≤ k-2
    · exact hPayNext w q k (by omega) hnext (by omega)
    · exact hPay w q k (by omega) hwk (by omega)
  change (σ.part O outerSide outerMax).bound + (σ.part M middleSide middleMax).bound ≤ σ.bound
  rw [hNormalize, hNormalize, hroot]
  cases outerSide <;> cases middleSide
  · exact False.elim (hne rfl)
  · change C ≤ 4 at hchosen
    change ¬ C ≤ 3 at hThree
    change 12 ≤ P ∨ (6 ≤ P ∧ P ≤ σ.k-2) at hwide
    change ¬ P ≤ σ.k-3 at hbelow
    have hC4 : C = 4 := by omega
    have hb := Nat.add_le_add (hOuter Side.lower Side.upper (by decide) hchosen) hMiddleUpper
    change (τ.part O Side.lower outerMax).bound + (τ.part M Side.upper middleMax).bound ≤
      P^2 + baseOf C outerMax σ.k at hb
    rw [hC4] at hb ⊢
    exact hb.trans (hPayWide P outerMax σ.k hwide hPk hbelow hlow)
  · change P ≤ 4 at hchosen
    change ¬ P ≤ 3 at hThree
    change 12 ≤ C ∨ (6 ≤ C ∧ C ≤ σ.k-2) at hwide
    change ¬ C ≤ σ.k-3 at hbelow
    have hP4 : P = 4 := by omega
    have hb := Nat.add_le_add (hOuter Side.upper Side.lower (by decide) hchosen) hMiddleLower
    change (τ.part O Side.upper outerMax).bound + (τ.part M Side.lower middleMax).bound ≤
      C^2 + baseOf outerMax P σ.k at hb
    rw [hP4] at hb ⊢
    rw [hBaseSwap outerMax 4 σ.k (by omega) (by omega)] at hb
    rw [hBaseSwap C 4 σ.k hCk (by omega)]
    exact hb.trans (hPayWide C outerMax σ.k hwide hCk hbelow hlow)
  · exact False.elim (hne rfl)

end ErdosSzekeres
