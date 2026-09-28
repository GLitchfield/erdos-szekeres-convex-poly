import ESBlueprint.B.CtxBoundLeOneOfLargeSiblingMaximum
import ESBlueprint.B.CtxPartCapacityDropInClearInterval
import ESBlueprint.B.CtxSingleRunDescendantLimitsNormalize
import ESBlueprint.B.CtxBasePascalCombine
import ESBlueprint.B.CtxBoundLeSumPointBases

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- Additivity for a contiguous middle block and its complement in a single child run when the outer sibling maximum is k-2 and the middle sibling maximum is one. Covers both choices of the outer side, arbitrary block lengths, and either empty outer end, provided the middle and its complement are nonempty. Positive external labels suffice; no WellFormed or lower bound on k is required. Combines large-sibling saturation, clear-interval capacity loss, ancestor-limit normalization, and the Pascal base allocation. Gives the saturated outer orientation at each extreme coupling of the sandwich problem.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_bound_additive_saturated_interval_complement (σ : Ctx.Context)
  (hpositive : ∀ x l t, σ.letterAt x = Ctx.Letter.ext l t → 1 ≤ l)
  (b l m r : ℕ) (hpos : σ.childPositions = List.range' b (l + m + r))
  (hm : 0 < m) (houter : 0 < l + r) :
  (σ.part (List.range' b l ++ List.range' (b + l + m) r)
      Ctx.Side.lower (σ.k - 2)).bound +
    (σ.part (List.range' (b + l) m) Ctx.Side.upper 1).bound ≤ σ.bound ∧
  (σ.part (List.range' b l ++ List.range' (b + l + m) r)
      Ctx.Side.upper (σ.k - 2)).bound +
    (σ.part (List.range' (b + l) m) Ctx.Side.lower 1).bound ≤ σ.bound := by
  classical
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
  have hSaturated (t : Side) : (σ.part O t (σ.k - 2)).bound ≤ 1 := by
    apply (ctx_bound_le_one_of_large_sibling_maximum (σ.part O t (σ.k - 2))
      (hPositivePart O t (σ.k - 2)) 1 ?_ ?_).2
    · rw [part_levels]
      simp
    · rw [part_maximumAt_one]
      exact le_rfl
  have hOuterLower : (σ.part O Side.lower (σ.k - 2)).bound ≤
      baseOf (min (C - 1) 1) P σ.k := by
    by_cases hc : C ≤ 1
    · have hz : (σ.part O Side.lower (σ.k - 2)).bound = 0 := by
        apply hZero
        intro p hp
        left
        have hd := hdrop O Side.lower (σ.k - 2) p hp hremovedOuter
        dsimp only at hd
        omega
      rw [hz]
      exact Nat.zero_le _
    by_cases hp : P = 0
    · have hz : (σ.part O Side.lower (σ.k - 2)).bound = 0 := by
        apply hZero
        intro p hmem
        right
        have hv := (hpartOld O Side.lower (σ.k - 2) p hmem).2
        omega
      rw [hz]
      exact Nat.zero_le _
    have hone : min (C - 1) 1 = 1 := by omega
    simpa [hone, baseOf, hp] using hSaturated Side.lower
  have hOuterUpper : (σ.part O Side.upper (σ.k - 2)).bound ≤
      baseOf C (min (P - 1) 1) σ.k := by
    by_cases hp : P ≤ 1
    · have hz : (σ.part O Side.upper (σ.k - 2)).bound = 0 := by
        apply hZero
        intro p hmem
        right
        have hd := hdrop O Side.upper (σ.k - 2) p hmem hremovedOuter
        dsimp only at hd
        omega
      rw [hz]
      exact Nat.zero_le _
    by_cases hc : C = 0
    · have hz : (σ.part O Side.upper (σ.k - 2)).bound = 0 := by
        apply hZero
        intro p hmem
        left
        have hv := (hpartOld O Side.upper (σ.k - 2) p hmem).1
        omega
      rw [hz]
      exact Nat.zero_le _
    have hone : min (P - 1) 1 = 1 := by omega
    simpa [hone, baseOf, hc] using hSaturated Side.upper
  have hmiddleMem (t : Side) : b + l ∈ (σ.part M t 1).childPositions := by
    rw [hmiddlePos]
    simp only [List.mem_range'_1]
    omega
  have hMiddleUpper : (σ.part M Side.upper 1).bound ≤ baseOf C (P - 1) σ.k := by
    rw [hrunBound _ (b + l) m hm (hmiddlePos Side.upper 1)]
    exact baseOf_mono (hpartOld M Side.upper 1 (b + l) (hmiddleMem _)).1
      (hdrop M Side.upper 1 (b + l) (hmiddleMem _) hremovedMiddle)
  have hMiddleLower : (σ.part M Side.lower 1).bound ≤ baseOf (C - 1) P σ.k := by
    rw [hrunBound _ (b + l) m hm (hmiddlePos Side.lower 1)]
    exact baseOf_mono (hdrop M Side.lower 1 (b + l) (hmiddleMem _) hremovedMiddle)
      (hpartOld M Side.lower 1 (b + l) (hmiddleMem _)).2
  have hlo := Nat.add_le_add hOuterLower hMiddleUpper
  have hup := Nat.add_le_add hOuterUpper hMiddleLower
  change (σ.part O Side.lower (σ.k - 2)).bound + (σ.part M Side.upper 1).bound ≤ σ.bound ∧
    (σ.part O Side.upper (σ.k - 2)).bound + (σ.part M Side.lower 1).bound ≤ σ.bound
  rw [hroot]
  by_cases hc : C = 0
  · constructor
    · simpa [hc, baseOf] using hlo
    · simpa [hc, baseOf] using hup
  by_cases hp : P = 0
  · constructor
    · simpa [hp, baseOf] using hlo
    · simpa [hp, baseOf] using hup
  have hlow := ctx_base_pascal_combine (min (C - 1) 1) P C (P - 1) C P σ.k
    hCk hPk (by omega) le_rfl le_rfl (by omega) (by omega)
  have hhigh := ctx_base_pascal_combine (C - 1) P C (min (P - 1) 1) C P σ.k
    hCk hPk (by omega) le_rfl le_rfl (by omega) (by omega)
  exact ⟨hlo.trans hlow, hup.trans (by simpa only [Nat.add_comm] using hhigh)⟩

end ErdosSzekeres
