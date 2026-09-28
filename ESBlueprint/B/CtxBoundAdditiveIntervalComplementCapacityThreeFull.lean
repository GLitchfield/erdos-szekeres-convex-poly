import ESBlueprint.B.CtxSingleLevelSaturatedLinearBound
import ESBlueprint.B.CtxBoundAdditiveCapacityThreeLowOuterMaximum

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- Full interval/complement additivity inside one ancestor child run when the outer-side ancestor capacity is at most three and the two sibling maxima sum to k-1. Covers either opposite-side orientation, arbitrary positive left/middle/right block lengths, and arbitrary positive old histories. Combines the below-saturation, near-maximum and low-maximum regimes with the critical saturated case. In the latter, the single-level saturated bound charges the normalized outer part by 2*k-4 and two Pascal combinations pay that charge using the middle sibling maximum. Removes all outer-length and maximum restrictions from the selected capacity-three regime of the singleton-end sandwich obstruction; larger selected capacities remain separate.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_bound_additive_interval_complement_capacity_three_full (σ : Ctx.Context)
  (hpositive : ∀ x j v, σ.letterAt x = Ctx.Letter.ext j v → 1 ≤ j)
  (b l m r : ℕ) (hpos : σ.childPositions = List.range' b (l + m + r))
  (hl : 0 < l) (hm : 0 < m) (hr : 0 < r)
  (outerSide middleSide : Ctx.Side) (hne : outerSide ≠ middleSide)
  (outerMax middleMax : ℕ)
  (hchosen : (match outerSide with
    | Ctx.Side.lower => σ.cupLimit b b | Ctx.Side.upper => σ.capLimit b b) ≤ 3)
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
  by_cases hnear : σ.k - 3 ≤ outerMax
  · exact ctx_bound_additive_near_saturated_interval_complement σ hpositive b l m r hpos
      hl hm hr outerSide middleSide hne outerMax middleMax hnear
  by_cases hfar : outerMax + 5 ≤ σ.k
  · exact ctx_bound_additive_capacity_three_low_outer_maximum σ hpositive b l m r hpos
      hl hm hr outerSide middleSide hne outerMax middleMax hchosen hcoupling hfar
  by_cases hbelow : (match middleSide with | Side.lower => C | Side.upper => P) ≤ σ.k - 2
  · exact ctx_bound_additive_interval_complement_capacity_three σ hpositive b l m r hpos
      hl hm hr outerSide middleSide hne outerMax middleMax hchosen
      (by cases middleSide <;> exact hbelow)
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
  have hTwoLeft (p k : ℕ) (hp : p ≤ k - 1) : baseOf 2 p k = p := by
    by_cases hz : p = 0
    · simp [baseOf, hz]
    by_cases ho : p = 1
    · simp [baseOf, ho]
    unfold baseOf
    rw [if_neg (by omega), if_neg (by omega),
      decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
    have hrow : p + 1 + (2 + 1) - 4 = p := by omega
    have hcol : p + 1 - 2 = p - 1 := by omega
    rw [hrow, hcol, Nat.choose_symm (show 1 ≤ p by omega)]
    simp
  have hTwoRight (c k : ℕ) (hc : c ≤ k - 1) : baseOf c 2 k = c := by
    by_cases hz : c = 0
    · simp [baseOf, hz]
    by_cases ho : c = 1
    · simp [baseOf, ho]
    unfold baseOf
    rw [if_neg (by omega), if_neg (by omega),
      decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
    have hrow : 2 + 1 + (c + 1) - 4 = c := by omega
    rw [hrow]
    simp
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
      (hcap : (match v with | Side.lower => C | Side.upper => P) ≤ 3) :
      (τ.part O v outerMax).bound ≤ 2 * σ.k - 4 := by
    have hx : b+l ∈ (τ.part O v outerMax).extPositions 1 := by
      rw [part_extPositions_one hτpos O v outerMax]
      refine List.mem_filter.mpr ⟨(hchild _).mpr ⟨by omega, by omega⟩, ?_⟩
      have hn : b+l ∉ O := by
        simp only [O, List.mem_append, List.mem_range'_1]
        omega
      simp [hn]
    have hg : (match v with
        | Side.lower => (τ.part O v outerMax).u
        | Side.upper => (τ.part O v outerMax).a) ≤ 4 := by
      cases v with
      | lower =>
        change C + 1 ≤ 4
        change C ≤ 3 at hcap
        omega
      | upper =>
        change P + 1 ≤ 4
        change P ≤ 3 at hcap
        omega
    have ho : (match w with
        | Side.lower => (τ.part O v outerMax).u
        | Side.upper => (τ.part O v outerMax).a) ≤ (τ.part O v outerMax).k := by
      cases w
      · change C + 1 ≤ σ.k
        omega
      · change P + 1 ≤ σ.k
        omega
    exact (ctx_single_level_saturated_linear_bound (τ.part O v outerMax)
      (hPartPositive τ O v outerMax) rfl v w hvw (b+l) (houterSide v) hx hg
      (by cases w <;> exact ho) hk4).2
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
  change (σ.part O outerSide outerMax).bound + (σ.part M middleSide middleMax).bound ≤ σ.bound
  rw [hNormalize, hNormalize, hroot]
  cases outerSide <;> cases middleSide
  · exact False.elim (hne rfl)
  · change C ≤ 3 at hchosen
    change ¬ P ≤ σ.k - 2 at hbelow
    have hC3 : C = 3 := by omega
    have hPkEq : P = σ.k - 1 := by omega
    have hP3 : 3 ≤ P := by omega
    have hM : outerMax ≤ P - 3 := by omega
    have hb := Nat.add_le_add (hOuter Side.lower Side.upper (by decide) hchosen) hMiddleUpper
    change (τ.part O Side.lower outerMax).bound + (τ.part M Side.upper middleMax).bound ≤
      2 * σ.k - 4 + baseOf C outerMax σ.k at hb
    rw [hC3] at hb ⊢
    have hmBase : baseOf 3 outerMax σ.k ≤ baseOf 3 (P-3) σ.k := baseOf_mono le_rfl hM
    have hp₁ := ctx_base_pascal_combine 2 P 3 (P-2) 3 P σ.k
      (by omega) hPk (by omega) le_rfl le_rfl (by omega) (by omega)
    have hp₂ := ctx_base_pascal_combine 2 (P-2) 3 (P-3) 3 (P-2) σ.k
      (by omega) (by omega) (by omega) le_rfl le_rfl (by omega) (by omega)
    rw [hTwoLeft P σ.k hPk] at hp₁
    rw [hTwoLeft (P-2) σ.k (by omega)] at hp₂
    omega
  · change P ≤ 3 at hchosen
    change ¬ C ≤ σ.k - 2 at hbelow
    have hP3 : P = 3 := by omega
    have hCkEq : C = σ.k - 1 := by omega
    have hC3 : 3 ≤ C := by omega
    have hM : outerMax ≤ C - 3 := by omega
    have hb := Nat.add_le_add (hOuter Side.upper Side.lower (by decide) hchosen) hMiddleLower
    change (τ.part O Side.upper outerMax).bound + (τ.part M Side.lower middleMax).bound ≤
      2 * σ.k - 4 + baseOf outerMax P σ.k at hb
    rw [hP3] at hb ⊢
    have hmBase : baseOf outerMax 3 σ.k ≤ baseOf (C-3) 3 σ.k := baseOf_mono hM le_rfl
    have hp₁ := ctx_base_pascal_combine (C-2) 3 C 2 C 3 σ.k
      hCk (by omega) (by omega) le_rfl le_rfl (by omega) (by omega)
    have hp₂ := ctx_base_pascal_combine (C-3) 3 (C-2) 2 (C-2) 3 σ.k
      (by omega) (by omega) (by omega) le_rfl le_rfl (by omega) (by omega)
    rw [hTwoRight C σ.k hCk] at hp₁
    rw [hTwoRight (C-2) σ.k (by omega)] at hp₂
    omega
  · exact False.elim (hne rfl)

end ErdosSzekeres
