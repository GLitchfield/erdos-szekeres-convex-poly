import ESBlueprint.B.CtxBoundAdditiveIntervalComplementCapacityFourBelowSaturation
import ESBlueprint.B.CtxSmallGlobalAxisRankTriplePotential
import ESBlueprint.B.CtxSiblingMaximumUpperNormalize
import ESBlueprint.B.CtxSingleRunDescendantBoundNormalize
import ESBlueprint.B.CtxBasePascalCombine
import ESBlueprint.B.CtxBoundAdditiveDisjointSingleRunSmallAxis
import ErdosSzekeres.DecomposableContext

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Prove interval/complement additivity when the outer sibling maximum is at least k-5 and the opposite ancestor capacity is at most k-3. The ancestor has one positive child run split into nonempty left, middle and right pieces; distinct axes and positive physical labels are required. The chosen ancestor capacity, history and both new maxima are otherwise unrestricted, and no coupling premise is needed. For chosen capacity at most four use the checked below-saturation estimate. Otherwise normalize the outer maximum to chosen global five, apply the ordered-triple potential, and pay the middle two-rank loss by a single Pascal combination. Extends the earlier fourth-maximum band by one maximum level; top/next opposite capacities and lower outer maxima remain separate.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_bound_additive_interval_complement_fifth_maximum_band (σ : Ctx.Context)
  (hpositive : ∀ x j v, σ.letterAt x = Ctx.Letter.ext j v → 1 ≤ j)
  (b l m r : ℕ) (hpos : σ.childPositions = List.range' b (l + m + r))
  (hl : 0 < l) (hm : 0 < m) (hr : 0 < r)
  (outerSide middleSide : Ctx.Side) (hne : outerSide ≠ middleSide)
  (outerMax middleMax : ℕ)
  (hnear : σ.k - 5 ≤ outerMax)
  (hopposite : (match middleSide with
    | Ctx.Side.lower => σ.cupLimit b b | Ctx.Side.upper => σ.capLimit b b) ≤ σ.k - 3) :
  (σ.part (List.range' b l ++ List.range' (b + l + m) r) outerSide outerMax).bound +
    (σ.part (List.range' (b + l) m) middleSide middleMax).bound ≤ σ.bound := by
  classical
  let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
  let C := σ.cupLimit b b
  let P := σ.capLimit b b
  let τ : Context := { σ with a := P + 1, u := C + 1, maxima := [] }
  let O := List.range' b l ++ List.range' (b + l + m) r
  let M := List.range' (b + l) m
  have hdis : ∀ p ∈ σ.childPositions, p ∈ O → p ∉ M := by
    intro p _ hp
    simp only [O, M, List.mem_append, List.mem_range'_1] at hp ⊢
    omega
  by_cases hFour : (match outerSide with | Side.lower => C | Side.upper => P) ≤ 4
  · exact ctx_bound_additive_interval_complement_capacity_four_below_saturation σ hpositive b l m r hpos
      hl hm hr outerSide middleSide hne outerMax middleMax hFour
      (by cases middleSide <;> simp only [C, P] at hopposite ⊢ <;> omega)
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
  have hCubic (ρ : Context)
      (hPos : ∀ x j v, ρ.letterAt x = Letter.ext j v → 1 ≤ j)
      (s t : Side) (hne : s ≠ t)
      (hg : G ρ s ≤ 5) :
      ρ.bound ≤ ((G ρ t)-1+2).choose 3 := by
    have hh := ctx_small_global_axis_rank_triple_potential ρ hPos s t hne hg
    exact hh.2.1.trans hh.2.2.1
  have hLarge (ρ : Context)
      (hPos : ∀ x j v, ρ.letterAt x = Letter.ext j v → 1 ≤ j)
      (j : ℕ) (hj : j ∈ ρ.levels) (hmax : ρ.k - 5 ≤ ρ.maximumAt j) :
      ρ.bound ≤ ((match ρ.sideAt j with | Side.lower => ρ.a | Side.upper => ρ.u)-1+2).choose 3 := by
    have hn := (ctx_sibling_maximum_upper_normalize ρ j hj).2.2
    cases hs : ρ.sideAt j with
    | lower =>
      let ν : Context := {ρ with u := min ρ.u (ρ.k - ρ.maximumAt j), maxima := ρ.maxima.take (j-1)}
      have hb : ρ.bound ≤ ν.bound := by simpa only [hs] using hn
      have hg : ν.u ≤ 5 := by dsimp [ν]; omega
      have hv := hCubic ν hPos Side.lower Side.upper (by decide) hg
      simpa only [hs] using hb.trans hv
    | upper =>
      let ν : Context := {ρ with a := min ρ.a (ρ.k - ρ.maximumAt j), maxima := ρ.maxima.take (j-1)}
      have hb : ρ.bound ≤ ν.bound := by simpa only [hs] using hn
      have hg : ν.a ≤ 5 := by dsimp [ν]; omega
      have hv := hCubic ν hPos Side.upper Side.lower (by decide) hg
      simpa only [hs] using hb.trans hv
  have hOuter (v : Side) : (τ.part O v outerMax).bound ≤
      (match v with | Side.lower => P + 2 | Side.upper => C + 2).choose 3 := by
    have hj : 1 ∈ (τ.part O v outerMax).levels := by rw [part_levels]; simp
    have hh : (τ.part O v outerMax).k - 5 ≤ (τ.part O v outerMax).maximumAt 1 := by
      rw [part_maximumAt_one]
      exact hnear
    have hb := hLarge (τ.part O v outerMax) (hPartPositive τ O v outerMax) 1 hj hh
    rw [houterSide] at hb
    cases v <;> simpa [τ, part] using hb
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
  have hOneLeft (ρ : Context) (v : Side) (j p x : ℕ)
      (hj : j ∈ ρ.levelsOn v 0) (hx : x ∈ ρ.extPositions j) (hxp : x < p) :
      1 ≤ ρ.leftExt v 0 p := by
    have hm : x ∈ (ρ.extPositions j).filter (· < p) := by simp [hx, hxp]
    have hne := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v 0).sublists.map
      (fun ls => (ls.foldl (leftStep ρ) (p, 0)).2))
      (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ ρ.leftExt v 0 p at hv
    simpa only [List.foldl_cons, List.foldl_nil, leftStep, List.getLast?_eq_some_getLast hne] using hv
  have hOneRight (ρ : Context) (v : Side) (j p x : ℕ)
      (hj : j ∈ ρ.levelsOn v 0) (hx : x ∈ ρ.extPositions j) (hpx : p < x) :
      1 ≤ ρ.rightExt v 0 p := by
    have hm : x ∈ (ρ.extPositions j).filter (p < ·) := by simp [hx, hpx]
    have hne := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v 0).sublists.map
      (fun ls => (ls.foldl (rightStep ρ) (p, 0)).2))
      (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ ρ.rightExt v 0 p at hv
    simpa only [List.foldl_cons, List.foldl_nil, rightStep, List.head?_eq_some_head hne] using hv
  have hMiddlePure (v : Side) :
      2 ≤ (τ.part M v middleMax).chainExt v (b+l) (b+l) := by
    have hbl : b ∈ τ.childPositions := (hchild _).mpr ⟨le_rfl, by omega⟩
    have hbr : b+l+m ∈ τ.childPositions := (hchild _).mpr ⟨by omega, by omega⟩
    have hnl : b ∉ M := by simp only [M, List.mem_range'_1]; omega
    have hnr : b+l+m ∉ M := by simp only [M, List.mem_range'_1]; omega
    have hs := hPartSide M v middleMax b hbl hnl
    have hj : 1 ∈ (τ.part M v middleMax).levelsOn v 0 := by
      rw [part_levelsOn_self_zero hs]
      simp
    have hxl : b ∈ (τ.part M v middleMax).extPositions 1 := by
      rw [part_extPositions_one hτpos M v middleMax]
      exact List.mem_filter.mpr ⟨hbl, by simp [hnl]⟩
    have hxr : b+l+m ∈ (τ.part M v middleMax).extPositions 1 := by
      rw [part_extPositions_one hτpos M v middleMax]
      exact List.mem_filter.mpr ⟨hbr, by simp [hnr]⟩
    have ha := hOneLeft _ v 1 (b+l) b hj hxl (by omega)
    have hb := hOneRight _ v 1 (b+l) (b+l+m) hj hxr (by omega)
    dsimp only [chainExt]
    omega
  have hMiddleLower : (τ.part M Side.lower middleMax).bound ≤ baseOf (C-2) P σ.k := by
    rw [hrunBound _ (b+l) m hm (hmiddlePos Side.lower)]
    have hcap := (ctx_part_limits_le τ M Side.lower middleMax (b+l) (b+l)).2
    rw [(hτlimits _).2] at hcap
    have hpure := hMiddlePure Side.lower
    have hcup : (τ.part M Side.lower middleMax).cupLimit (b+l) (b+l) ≤ C-2 := by
      dsimp only [cupLimit]
      have hu : (τ.part M Side.lower middleMax).u - 1 = C := by simp [τ, part]
      rw [hu]
      omega
    exact baseOf_mono hcup hcap
  have hMiddleUpper : (τ.part M Side.upper middleMax).bound ≤ baseOf C (P-2) σ.k := by
    rw [hrunBound _ (b+l) m hm (hmiddlePos Side.upper)]
    have hcup := (ctx_part_limits_le τ M Side.upper middleMax (b+l) (b+l)).1
    rw [(hτlimits _).1] at hcup
    have hpure := hMiddlePure Side.upper
    have hcap : (τ.part M Side.upper middleMax).capLimit (b+l) (b+l) ≤ P-2 := by
      dsimp only [capLimit]
      have ha : (τ.part M Side.upper middleMax).a - 1 = P := by simp [τ, part]
      rw [ha]
      omega
    exact baseOf_mono hcup hcap
  have hFourLeft (p k : ℕ) (hp : 2 ≤ p) (hpk : p ≤ k-3) :
      baseOf 4 p k = (p+2).choose 3 := by
    unfold baseOf
    rw [if_neg (by omega),if_neg (by omega),
      decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
    have hr : p+1+(4+1)-4=p+2 := by omega
    rw [hr]
    simpa only [show p+2-3=p+1-2 by omega] using Nat.choose_symm (show 3 ≤ p+2 by omega)
  have hFourRight (p k : ℕ) (hp : 2 ≤ p) (hpk : p ≤ k-3) :
      baseOf p 4 k = (p+2).choose 3 := by
    unfold baseOf
    rw [if_neg (by omega),if_neg (by omega),
      decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
    have hr : 4+1+(p+1)-4=p+2 := by omega
    rw [hr]
  change (σ.part O outerSide outerMax).bound + (σ.part M middleSide middleMax).bound ≤ σ.bound
  rw [hNormalize, hNormalize, hroot]
  cases outerSide <;> cases middleSide
  · exact False.elim (hne rfl)
  · change ¬ C ≤ 4 at hFour
    change P ≤ σ.k - 3 at hopposite
    have hb := Nat.add_le_add (hOuter Side.lower) hMiddleUpper
    change (τ.part O Side.lower outerMax).bound + (τ.part M Side.upper middleMax).bound ≤
      (P + 2).choose 3 + baseOf C (P-2) σ.k at hb
    have hp := ctx_base_pascal_combine 4 P C (P-2) C P σ.k
      hCk hPk (by omega) le_rfl le_rfl (by omega) (by omega)
    rw [hFourLeft P σ.k (by omega) hopposite] at hp
    exact hb.trans hp
  · change ¬ P ≤ 4 at hFour
    change C ≤ σ.k - 3 at hopposite
    have hb := Nat.add_le_add (hOuter Side.upper) hMiddleLower
    change (τ.part O Side.upper outerMax).bound + (τ.part M Side.lower middleMax).bound ≤
      (C + 2).choose 3 + baseOf (C-2) P σ.k at hb
    have hp := ctx_base_pascal_combine (C-2) P C 4 C P σ.k
      hCk hPk (by omega) le_rfl le_rfl (by omega) (by omega)
    rw [hFourRight C σ.k (by omega) hopposite] at hp
    exact hb.trans (by simpa only [Nat.add_comm] using hp)
  · exact False.elim (hne rfl)

end ErdosSzekeres
