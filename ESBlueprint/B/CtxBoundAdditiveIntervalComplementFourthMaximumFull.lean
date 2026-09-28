import ESBlueprint.B.CtxBoundAdditiveIntervalComplementFourthMaximumBand
import ESBlueprint.B.CtxSmallGlobalAxisSaturatedTriangleBound
import ESBlueprint.B.CtxBoundAdditiveIntervalComplementCapacityThreeFull
import ErdosSzekeres.DecomposableContext

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Extend interval/complement additivity to every ancestor capacity when the outer maximum is at least k-4 and the sibling maxima sum to k-1. The unsaturated band uses the previous triangle consequence. At saturation the global-four triangle and the middle maximum loss of three fit one checked Pascal combination.
Positive external labels and a contiguous ancestor child run split into three nonempty blocks. Distinct outer and middle axes, outer maximum at least k-4, and outerMax + middleMax = k-1. No chosen-capacity, opposite-capacity, singleton-end, history or length restriction; lower outer maxima remain open.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_bound_additive_interval_complement_fourth_maximum_full (σ : Ctx.Context)
  (hpositive : ∀ x j v, σ.letterAt x = Ctx.Letter.ext j v → 1 ≤ j)
  (b l m r : ℕ) (hpos : σ.childPositions = List.range' b (l + m + r))
  (hl : 0 < l) (hm : 0 < m) (hr : 0 < r)
  (outerSide middleSide : Ctx.Side) (hne : outerSide ≠ middleSide)
  (outerMax middleMax : ℕ)
  (hnear : σ.k - 4 ≤ outerMax)
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
  by_cases hnearThree : σ.k - 3 ≤ outerMax
  · exact ctx_bound_additive_near_saturated_interval_complement σ hpositive b l m r hpos
      hl hm hr outerSide middleSide hne outerMax middleMax hnearThree
  by_cases hbelow : (match middleSide with | Side.lower => C | Side.upper => P) ≤ σ.k - 2
  · exact ctx_bound_additive_interval_complement_fourth_maximum_band σ hpositive b l m r hpos
      hl hm hr outerSide middleSide hne outerMax middleMax hnear
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
  have hk4 : 4 ≤ σ.k := by omega
  have hcritical : outerMax + 4 = σ.k := by omega
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
  have hOuter (v : Side) : (τ.part O v outerMax).bound ≤
      (σ.k - 2).choose 2 + (σ.k - 1) := by
    let ρ := τ.part O v outerMax
    have hj : 1 ∈ ρ.levels := by rw [part_levels]; simp
    have hs : ρ.sideAt 1 = v := houterSide v
    have hn := (ctx_sibling_maximum_upper_normalize ρ 1 hj).2.2
    have hmax : ρ.k - 4 ≤ ρ.maximumAt 1 := by
      rw [part_maximumAt_one]
      exact hnear
    cases v with
    | lower =>
      let ν : Context := {ρ with u := min ρ.u (ρ.k - ρ.maximumAt 1), maxima := ρ.maxima.take 0}
      have hb : ρ.bound ≤ ν.bound := by simpa only [hs, Nat.sub_self] using hn
      have hg : ν.u ≤ 4 := by dsimp only [ν]; omega
      have ho : ν.a ≤ ν.k := by change P + 1 ≤ σ.k; omega
      have hv := (ctx_small_global_axis_saturated_triangle_bound ν
        (hPartPositive τ O Side.lower outerMax) Side.lower Side.upper (by decide) hg ho hk4).2.1
      exact hb.trans hv
    | upper =>
      let ν : Context := {ρ with a := min ρ.a (ρ.k - ρ.maximumAt 1), maxima := ρ.maxima.take 0}
      have hb : ρ.bound ≤ ν.bound := by simpa only [hs, Nat.sub_self] using hn
      have hg : ν.a ≤ 4 := by dsimp only [ν]; omega
      have ho : ν.u ≤ ν.k := by change C + 1 ≤ σ.k; omega
      have hv := (ctx_small_global_axis_saturated_triangle_bound ν
        (hPartPositive τ O Side.upper outerMax) Side.upper Side.lower (by decide) hg ho hk4).2.1
      exact hb.trans hv
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
  change (σ.part O outerSide outerMax).bound + (σ.part M middleSide middleMax).bound ≤ σ.bound
  rw [hNormalize, hNormalize, hroot]
  cases outerSide <;> cases middleSide
  · exact False.elim (hne rfl)
  · change ¬ C ≤ 3 at hThree
    change ¬ P ≤ σ.k - 2 at hbelow
    have hPkEq : P = σ.k - 1 := by omega
    have hM : outerMax ≤ P - 3 := by omega
    have hb := Nat.add_le_add (hOuter Side.lower) hMiddleUpper
    have hmBase : baseOf C outerMax σ.k ≤ baseOf C (P-3) σ.k := baseOf_mono le_rfl hM
    have hp := ctx_base_pascal_combine 3 P C (P-3) C P σ.k
      hCk hPk (by omega) le_rfl le_rfl (by omega) (by omega)
    have hBase : baseOf 3 P σ.k = (σ.k-2).choose 2 + (σ.k-1) := by
      rw [hPkEq]
      exact hSaturatedBaseEdge σ.k hk4
    rw [hBase] at hp
    exact hb.trans ((Nat.add_le_add_left hmBase _).trans hp)
  · change ¬ P ≤ 3 at hThree
    change ¬ C ≤ σ.k - 2 at hbelow
    have hCkEq : C = σ.k - 1 := by omega
    have hM : outerMax ≤ C - 3 := by omega
    have hb := Nat.add_le_add (hOuter Side.upper) hMiddleLower
    have hmBase : baseOf outerMax P σ.k ≤ baseOf (C-3) P σ.k := baseOf_mono hM le_rfl
    have hp := ctx_base_pascal_combine (C-3) P C 3 C P σ.k
      hCk hPk (by omega) le_rfl le_rfl (by omega) (by omega)
    have hBase : baseOf C 3 σ.k = (σ.k-2).choose 2 + (σ.k-1) := by
      rw [hBaseSwap C 3 σ.k hCk (by omega), hCkEq]
      exact hSaturatedBaseEdge σ.k hk4
    rw [hBase] at hp
    exact hb.trans ((Nat.add_le_add_left hmBase _).trans (by simpa only [Nat.add_comm] using hp))
  · exact False.elim (hne rfl)

end ErdosSzekeres
