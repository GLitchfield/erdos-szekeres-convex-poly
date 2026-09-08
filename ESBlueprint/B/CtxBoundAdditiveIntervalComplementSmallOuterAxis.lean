import ESBlueprint.B.CtxBoundLeOneOfClearUnitAxis
import ESBlueprint.B.CtxBoundLeNumRunsOfUnitAxisLimit
import ESBlueprint.B.CtxSingleRunPartLimitsExact
import ESBlueprint.B.CtxBoundAdditiveSaturatedIntervalComplement

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- Conditional additivity for a contiguous middle interval and its two outer blocks in a single ancestor child run. If the ancestor cup capacity is at most two, lower outer plus upper middle is bounded by the parent; if its cap capacity is at most two, the dual orientation is bounded. The three blocks may have arbitrary positive lengths and both new maxima are arbitrary natural numbers. The two capacity assumptions govern separate orientations. Uses unit-axis region bounds, exact two-sided middle capacity loss, and two Pascal allocations to remove the unbounded outer-length obstruction in this capacity range.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_bound_additive_interval_complement_small_outer_axis (σ : Ctx.Context) (hwf : σ.WellFormed)
  (b l m r : ℕ) (hpos : σ.childPositions = List.range' b (l + m + r))
  (hl : 0 < l) (hm : 0 < m) (hr : 0 < r) (outerMax middleMax : ℕ) :
  (σ.cupLimit b b ≤ 2 →
    (σ.part (List.range' b l ++ List.range' (b + l + m) r)
      Ctx.Side.lower outerMax).bound +
      (σ.part (List.range' (b + l) m) Ctx.Side.upper middleMax).bound ≤ σ.bound) ∧
  (σ.capLimit b b ≤ 2 →
    (σ.part (List.range' b l ++ List.range' (b + l + m) r)
      Ctx.Side.upper outerMax).bound +
      (σ.part (List.range' (b + l) m) Ctx.Side.lower middleMax).bound ≤ σ.bound) := by
  classical
  have hpositive : ∀ x j t, σ.letterAt x = Letter.ext j t → 1 ≤ j :=
    fun x j t hx => (hwf.2.2.2.2.2 x j t hx).1
  let C := σ.cupLimit b b
  let P := σ.capLimit b b
  let O := List.range' b l ++ List.range' (b + l + m) r
  let M := List.range' (b + l) m
  have hCk : C ≤ σ.k - 1 := by dsimp [C, cupLimit]; omega
  have hPk : P ≤ σ.k - 1 := by dsimp [P, capLimit]; omega
  have hchild (p : ℕ) : p ∈ σ.childPositions ↔ b ≤ p ∧ p < b + (l + m + r) := by
    rw [hpos, List.mem_range'_1]
  have hconst (p : ℕ) (hp : p ∈ σ.childPositions) :
      σ.cupLimit p p = C ∧ σ.capLimit p p = P := by
    let τ : Context := { σ with a := P + 1, u := C + 1, maxima := [] }
    have h := ctx_single_run_descendant_limits_normalize σ b (l + m + r) hpos σ 0
      ⟨rfl, rfl, rfl, by simp, by intro j _; simp, by intro j _; simp, by intro j _; simp⟩
      (by intro j x hj hj0 _; omega) p p hp hp
    change σ.cupLimit p p = τ.cupLimit p p ∧ σ.capLimit p p = τ.capLimit p p at h
    have hc : τ.cupLimit p p = C := by
      simp [τ, cupLimit, chainExt, joinExt, leftExt, rightExt, levelsOn, levels,
        Nat.min_eq_left hCk]
    have hp' : τ.capLimit p p = P := by
      simp [τ, capLimit, chainExt, joinExt, leftExt, rightExt, levelsOn, levels,
        Nat.min_eq_left hPk]
    exact ⟨h.1.trans hc, h.2.trans hp'⟩
  have hrunBound : ∀ (τ : Context) (a n : ℕ), 0 < n →
      τ.childPositions = List.range' a n →
      τ.bound = baseOf (τ.cupLimit a a) (τ.capLimit a a) τ.k := by
    intro τ a n hn hps
    have hmem : ∀ p, p ∈ τ.childPositions ↔ a ≤ p ∧ p < a + n := by
      intro p
      rw [hps, List.mem_range'_1]
    let starts := (List.range τ.word.length).filter fun p =>
      τ.letterAt p = Letter.child ∧ (p = 0 ∨ τ.letterAt (p - 1) ≠ Letter.child)
    have hsubset : starts.toFinset ⊆ ({a} : Finset ℕ) := by
      intro p hp
      have hstart : p < τ.word.length ∧ τ.letterAt p = Letter.child ∧
          (p = 0 ∨ τ.letterAt (p - 1) ≠ Letter.child) := by
        simpa [starts] using hp
      have hp' := (hmem p).mp
        (by simpa [childPositions] using And.intro hstart.1 hstart.2.1)
      simp only [Finset.mem_singleton]
      by_contra hpa
      have hprev : p - 1 ∈ τ.childPositions := (hmem (p - 1)).mpr ⟨by omega, by omega⟩
      have hprev' : τ.letterAt (p - 1) = Letter.child :=
        of_decide_eq_true (List.mem_filter.mp hprev).2
      rcases hstart.2.2 with hz | hnot
      · omega
      · exact hnot hprev'
    have hruns : τ.numRuns ≤ 1 := by
      calc
        τ.numRuns = starts.toFinset.card :=
          (List.toFinset_card_of_nodup (List.nodup_range.filter _)).symm
        _ ≤ ({a} : Finset ℕ).card := Finset.card_le_card hsubset
        _ = 1 := by simp
    simp [bound, boundFuel, hruns, base_eq_baseOf, hps, List.head?_range', Nat.ne_of_gt hn]
  have hroot : σ.bound = baseOf C P σ.k :=
    hrunBound σ b (l + m + r) (by omega) hpos
  have hsplit : σ.childPositions = List.range' b l ++ M ++ List.range' (b + l + m) r := by
    rw [hpos]
    simp only [M, List.range'_append_1, Nat.add_assoc]
  have hleftEmpty : (List.range' b l).filter (· ∈ M) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro p hp
    have hp' := List.mem_range'_1.mp hp
    have hn : p ∉ M := by
      simp only [M, List.mem_range'_1]
      omega
    simpa only [decide_eq_true_eq] using hn
  have hrightEmpty : (List.range' (b + l + m) r).filter (· ∈ M) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro p hp
    have hp' := List.mem_range'_1.mp hp
    have hn : p ∉ M := by
      simp only [M, List.mem_range'_1]
      omega
    simpa only [decide_eq_true_eq] using hn
  have hself : M.filter (· ∈ M) = M := List.filter_eq_self.mpr (fun p hp => by simp [hp])
  have hmiddlePos (t : Side) (n : ℕ) :
      (σ.part M t n).childPositions = List.range' (b + l) m := by
    change (σ.part M t n).childPositions = M
    rw [part_childPositions, hsplit]
    simp only [List.filter_append, hleftEmpty, hrightEmpty, hself, List.nil_append, List.append_nil]
  have hmiddlePoint : b + l ∈ σ.childPositions := (hchild _).mpr ⟨by omega, by omega⟩
  have hmiddleNotOuter : b + l ∉ O := by
    simp only [O, List.mem_append, List.mem_range'_1]
    omega
  have hremovedOuter : ∃ p ∈ σ.childPositions, p ∉ O := ⟨b + l, hmiddlePoint, hmiddleNotOuter⟩
  have hremovedMiddle : ∃ p ∈ σ.childPositions, p ∉ M := by
    by_cases hl : 0 < l
    · refine ⟨b, (hchild _).mpr ⟨le_rfl, by omega⟩, ?_⟩
      simp only [M, List.mem_range'_1]
      omega
    · refine ⟨b + l + m, (hchild _).mpr ⟨by omega, by omega⟩, ?_⟩
      simp only [M, List.mem_range'_1]
      omega
  have hextOutside (j x : ℕ) (hx : x ∈ σ.extPositions j) :
      x < b ∨ b + (l + m + r) ≤ x := by
    by_contra h
    have hc := (hchild x).mpr ⟨by omega, by omega⟩
    have hl : σ.letterAt x = Letter.child := of_decide_eq_true (List.mem_filter.mp hc).2
    simp [extPositions, hl] at hx
  have hpartOld (keep : List ℕ) (t : Side) (n p : ℕ)
      (hp : p ∈ (σ.part keep t n).childPositions) :
      (σ.part keep t n).cupLimit p p ≤ C ∧ (σ.part keep t n).capLimit p p ≤ P := by
    rw [part_childPositions] at hp
    have hc := hconst p (List.mem_filter.mp hp).1
    simpa only [hc.1, hc.2] using ctx_part_limits_le σ keep t n p p
  have hdrop (keep : List ℕ) (t : Side) (n p : ℕ)
      (hp : p ∈ (σ.part keep t n).childPositions)
      (hremoved : ∃ q ∈ σ.childPositions, q ∉ keep) :
      match t with
      | Side.lower => (σ.part keep t n).cupLimit p p ≤ C - 1
      | Side.upper => (σ.part keep t n).capLimit p p ≤ P - 1 := by
    rw [part_childPositions] at hp
    have hpold := (List.mem_filter.mp hp).1
    have hpkeep : p ∈ keep := by simpa using (List.mem_filter.mp hp).2
    obtain ⟨q, hq, hqnot⟩ := hremoved
    have hclear : ∀ j ∈ σ.levelsOn t 0, ∀ x ∈ σ.extPositions j,
        x < min p q ∨ max p q < x := by
      intro j _ x hx
      have he := hextOutside j x hx
      have hpb := (hchild p).mp hpold
      have hqb := (hchild q).mp hq
      omega
    have hd := (ctx_part_capacity_drop_in_clear_interval σ hpositive keep t n p q
      hpold hpkeep hq hqnot hclear).2.2
    have hc := hconst p hpold
    cases t <;> simpa only [hc.1, hc.2] using hd
  have hZero (τ : Context)
      (hzero : ∀ p ∈ τ.childPositions, τ.cupLimit p p = 0 ∨ τ.capLimit p p = 0) : τ.bound = 0 := by
    have hsum : (τ.childPositions.map (fun p => baseOf (τ.cupLimit p p) (τ.capLimit p p) τ.k)).sum = 0 := by
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      simp [baseOf, hzero p hp]
    have h := ctx_bound_le_sum_point_bases τ
    rw [hsum] at h
    exact Nat.eq_zero_of_le_zero h
  have hPositivePart (keep : List ℕ) (t : Side) (n : ℕ) :
      ∀ x j u, (σ.part keep t n).letterAt x = Letter.ext j u → 1 ≤ j := by
    intro x j u hx
    have hxl : x < σ.word.length := by
      by_contra h
      have hn := letterAt_of_length_le (σ.part keep t n)
        (show (σ.part keep t n).word.length ≤ x by rw [part_word_length]; omega)
      rw [hn] at hx
      cases hx
    cases he : σ.letterAt x with
    | child =>
      rw [part_letterAt_of_child σ keep t n hxl he] at hx
      split at hx
      · cases hx
      · cases hx
        omega
    | ext oldLevel oldSide =>
      rw [part_letterAt_of_ext σ keep t n hxl he] at hx
      cases hx
      omega
  have houterMem (t : Side) (n p : ℕ) :
      p ∈ (σ.part O t n).childPositions ↔
        (b ≤ p ∧ p < b + l) ∨ (b + l + m ≤ p ∧ p < b + l + m + r) := by
    rw [part_childPositions, List.mem_filter]
    simp only [decide_eq_true_eq, hpos, List.mem_range'_1, O, List.mem_append]
    omega
  have houterRuns (t : Side) (n : ℕ) : (σ.part O t n).numRuns ≤ 2 := by
    let τ := σ.part O t n
    let starts := (List.range τ.word.length).filter fun p =>
      τ.letterAt p = Letter.child ∧ (p = 0 ∨ τ.letterAt (p - 1) ≠ Letter.child)
    have hsubset : starts.toFinset ⊆ ({b, b + l + m} : Finset ℕ) := by
      intro p hp
      have hstart : p < τ.word.length ∧ τ.letterAt p = Letter.child ∧
          (p = 0 ∨ τ.letterAt (p - 1) ≠ Letter.child) := by
        simpa [starts] using hp
      have hp' := (houterMem t n p).mp
        (by simpa [childPositions] using And.intro hstart.1 hstart.2.1)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_contra hnot
      have hprev : p - 1 ∈ τ.childPositions :=
        (houterMem t n (p - 1)).mpr (by omega)
      have hprev' : τ.letterAt (p - 1) = Letter.child :=
        of_decide_eq_true (List.mem_filter.mp hprev).2
      rcases hstart.2.2 with hz | hnot
      · omega
      · exact hnot hprev'
    calc
      (σ.part O t n).numRuns = starts.toFinset.card :=
        (List.toFinset_card_of_nodup (List.nodup_range.filter _)).symm
      _ ≤ ({b, b + l + m} : Finset ℕ).card := Finset.card_le_card hsubset
      _ = 2 := by simp [show b ≠ b + l + m by omega]
  have hOuterTwo (t : Side) (n : ℕ)
      (hsmall : (match t with | Side.lower => C | Side.upper => P) ≤ 2) :
      (σ.part O t n).bound ≤ 2 := by
    have hu : ∀ p ∈ (σ.part O t n).childPositions,
        (match t with
          | Side.lower => (σ.part O t n).cupLimit p p
          | Side.upper => (σ.part O t n).capLimit p p) ≤ 1 := by
      intro p hp
      have hd := hdrop O t n p hp hremovedOuter
      cases t <;> dsimp only at hd hsmall ⊢ <;> omega
    exact (ctx_bound_le_numRuns_of_unit_axis_limit (σ.part O t n)
      (hPositivePart O t n) t hu).2.trans (houterRuns t n)
  have hdouble (n : ℕ) :
      (σ.part M Side.lower n).cupLimit (b + l) (b + l) ≤ C - 2 ∧
      (σ.part M Side.upper n).capLimit (b + l) (b + l) ≤ P - 2 := by
    let removed := σ.childPositions.filter (· ∉ M)
    have hleft : (removed.filter (· < b + l)).isEmpty = false := by
      apply List.isEmpty_eq_false_iff_exists_mem.mpr
      refine ⟨b, ?_⟩
      simp only [removed, List.mem_filter, decide_eq_true_eq, hpos, List.mem_range'_1, M]
      omega
    have hright : (removed.filter (b + l < ·)).isEmpty = false := by
      apply List.isEmpty_eq_false_iff_exists_mem.mpr
      refine ⟨b + l + m, ?_⟩
      simp only [removed, List.mem_filter, decide_eq_true_eq, hpos, List.mem_range'_1, M]
      omega
    have he := ctx_single_run_part_limits_exact σ hwf b (l + m + r) hpos M
      hremovedMiddle (b + l) (b + l) hmiddlePoint hmiddlePoint n
    change (σ.part M Side.lower n).cupLimit (b + l) (b + l) =
        min (σ.cupLimit (b + l) (b + l) -
          ((if (removed.filter (· < b + l)).isEmpty then 0 else 1) +
           (if (removed.filter (b + l < ·)).isEmpty then 0 else 1))) (σ.k - 1 - n) ∧
      (σ.part M Side.upper n).capLimit (b + l) (b + l) =
        min (σ.capLimit (b + l) (b + l) -
          ((if (removed.filter (· < b + l)).isEmpty then 0 else 1) +
           (if (removed.filter (b + l < ·)).isEmpty then 0 else 1))) (σ.k - 1 - n) at he
    have hc := hconst (b + l) hmiddlePoint
    simp only [hleft, hright, Bool.false_eq_true, if_false, Nat.reduceAdd, hc.1, hc.2] at he
    exact ⟨he.1.le.trans (Nat.min_le_left _ _), he.2.le.trans (Nat.min_le_left _ _)⟩
  have hmiddleMem (t : Side) (n : ℕ) : b + l ∈ (σ.part M t n).childPositions := by
    rw [hmiddlePos]
    simp only [List.mem_range'_1]
    omega
  have hMiddleUpper (n : ℕ) : (σ.part M Side.upper n).bound ≤ baseOf C (P - 2) σ.k := by
    rw [hrunBound _ (b + l) m hm (hmiddlePos Side.upper n)]
    exact baseOf_mono (hpartOld M Side.upper n (b + l) (hmiddleMem _ _)).1 (hdouble n).2
  have hMiddleLower (n : ℕ) : (σ.part M Side.lower n).bound ≤ baseOf (C - 2) P σ.k := by
    rw [hrunBound _ (b + l) m hm (hmiddlePos Side.lower n)]
    exact baseOf_mono (hdouble n).1 (hpartOld M Side.lower n (b + l) (hmiddleMem _ _)).2
  have hOuterClear (t s : Side) (n : ℕ) (hne : t ≠ s) :
      ∀ p ∈ (σ.part O t n).childPositions, ∀ q ∈ (σ.part O t n).childPositions,
        ∀ j ∈ (σ.part O t n).levelsOn s 0, ∀ x ∈ (σ.part O t n).extPositions j,
          x < min p q ∨ max p q < x := by
    have hs : (σ.part O t n).sideAt 1 = t := by
      apply part_sideAt_one_of_mem hpositive O t n (q := b + l)
      rw [part_extPositions_one hpositive O t n]
      exact List.mem_filter.mpr ⟨hmiddlePoint, by simp [hmiddleNotOuter]⟩
    intro p hp q hq j hj x hx
    rw [part_childPositions] at hp hq
    have hpb := (hchild p).mp (List.mem_filter.mp hp).1
    have hqb := (hchild q).mp (List.mem_filter.mp hq).1
    rw [part_levelsOn_other_zero (by simpa only [hs] using hne)] at hj
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hj
    rw [part_extPositions_succ σ O t n (one_le_of_mem_levelsOn hv).1] at hx
    have hout := hextOutside v x hx
    omega
  have hpayLower (hC : C = 2) (hp : 2 ≤ P) :
      2 + baseOf C (P - 2) σ.k ≤ baseOf C P σ.k := by
    have h1 := ctx_base_pascal_combine 1 P 2 (P - 1) 2 P σ.k
      (by omega) hPk (by omega) le_rfl le_rfl (by omega) (by omega)
    have h2 := ctx_base_pascal_combine 1 (P - 1) 2 (P - 2) 2 (P - 1) σ.k
      (by omega) (by omega) (by omega) le_rfl le_rfl (by omega) (by omega)
    have hb1 : baseOf 1 P σ.k = 1 := by simp [baseOf, show P ≠ 0 by omega]
    have hb2 : baseOf 1 (P - 1) σ.k = 1 := by simp [baseOf, show P - 1 ≠ 0 by omega]
    rw [hb1] at h1
    rw [hb2] at h2
    rw [hC]
    omega
  have hpayUpper (hP : P = 2) (hc : 2 ≤ C) :
      2 + baseOf (C - 2) P σ.k ≤ baseOf C P σ.k := by
    have h1 := ctx_base_pascal_combine (C - 1) 2 C 1 C 2 σ.k
      hCk (by omega) (by omega) le_rfl le_rfl (by omega) (by omega)
    have h2 := ctx_base_pascal_combine (C - 2) 2 (C - 1) 1 (C - 1) 2 σ.k
      (by omega) (by omega) (by omega) le_rfl le_rfl (by omega) (by omega)
    have hb1 : baseOf C 1 σ.k = 1 := by simp [baseOf, show C ≠ 0 by omega]
    have hb2 : baseOf (C - 1) 1 σ.k = 1 := by simp [baseOf, show C - 1 ≠ 0 by omega]
    rw [hb1] at h1
    rw [hb2] at h2
    rw [hP]
    omega
  change (C ≤ 2 → (σ.part O Side.lower outerMax).bound +
      (σ.part M Side.upper middleMax).bound ≤ σ.bound) ∧
    (P ≤ 2 → (σ.part O Side.upper outerMax).bound +
      (σ.part M Side.lower middleMax).bound ≤ σ.bound)
  rw [hroot]
  constructor
  · intro hc
    have hmid := hMiddleUpper middleMax
    by_cases hc1 : C ≤ 1
    · have hz : (σ.part O Side.lower outerMax).bound = 0 := by
        apply hZero
        intro p hp
        left
        have hd := hdrop O Side.lower outerMax p hp hremovedOuter
        dsimp only at hd
        omega
      rw [hz, Nat.zero_add]
      exact hmid.trans (baseOf_mono le_rfl (Nat.sub_le P 2))
    have hc2 : C = 2 := by omega
    by_cases hp0 : P = 0
    · have hz : (σ.part O Side.lower outerMax).bound = 0 := by
        apply hZero
        intro p hp
        right
        have hd := (hpartOld O Side.lower outerMax p hp).2
        omega
      rw [hz, Nat.zero_add]
      simpa [hp0, baseOf] using hmid
    by_cases hp1 : P = 1
    · have houter : (σ.part O Side.lower outerMax).bound ≤ 1 := by
        apply (ctx_bound_le_one_of_clear_unit_axis (σ.part O Side.lower outerMax)
          (hPositivePart O Side.lower outerMax) Side.upper ?_
          (hOuterClear Side.lower Side.upper outerMax (by decide))).2
        intro p hp
        dsimp only
        have hd := (hpartOld O Side.lower outerMax p hp).2
        omega
      have hm0 : (σ.part M Side.upper middleMax).bound ≤ 0 := by
        simpa [hp1, baseOf] using hmid
      have hbase : baseOf C P σ.k = 1 := by simp [hp1, baseOf, show C ≠ 0 by omega]
      rw [hbase]
      omega
    exact (Nat.add_le_add (hOuterTwo Side.lower outerMax hc) hmid).trans
      (hpayLower hc2 (by omega))
  · intro hp
    have hmid := hMiddleLower middleMax
    by_cases hp1 : P ≤ 1
    · have hz : (σ.part O Side.upper outerMax).bound = 0 := by
        apply hZero
        intro p hmem
        right
        have hd := hdrop O Side.upper outerMax p hmem hremovedOuter
        dsimp only at hd
        omega
      rw [hz, Nat.zero_add]
      exact hmid.trans (baseOf_mono (Nat.sub_le C 2) le_rfl)
    have hp2 : P = 2 := by omega
    by_cases hc0 : C = 0
    · have hz : (σ.part O Side.upper outerMax).bound = 0 := by
        apply hZero
        intro p hmem
        left
        have hd := (hpartOld O Side.upper outerMax p hmem).1
        omega
      rw [hz, Nat.zero_add]
      simpa [hc0, baseOf] using hmid
    by_cases hc1 : C = 1
    · have houter : (σ.part O Side.upper outerMax).bound ≤ 1 := by
        apply (ctx_bound_le_one_of_clear_unit_axis (σ.part O Side.upper outerMax)
          (hPositivePart O Side.upper outerMax) Side.lower ?_
          (hOuterClear Side.upper Side.lower outerMax (by decide))).2
        intro p hmem
        dsimp only
        have hd := (hpartOld O Side.upper outerMax p hmem).1
        omega
      have hm0 : (σ.part M Side.lower middleMax).bound ≤ 0 := by
        simpa [hc1, baseOf] using hmid
      have hbase : baseOf C P σ.k = 1 := by simp [hc1, baseOf, show P ≠ 0 by omega]
      rw [hbase]
      omega
    exact (Nat.add_le_add (hOuterTwo Side.upper outerMax hp) hmid).trans
      (hpayUpper hp2 (by omega))

end ErdosSzekeres
