import ESBlueprint.B.CtxTwoMarkerMixedCapacityPairIntersectionOneElevenBound
import ESBlueprint.B.CtxPartPositiveLetters

set_option maxHeartbeats 4000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

/-- For the actual cut companion with its physical opposite level-one marker of maximum one, the exact mixed-capacity overlap formula closes every fuel and the full bound at eleven whenever the low/high active rank-pair intersection has cardinality at most one.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_two_marker_mixed_capacity_pair_intersection_one_eleven_bound, ErdosSzekeres.ctx_part_positive_letters
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_actual_marker_opposite_between_small_pair_overlap_companion_eleven_bound (σ : Ctx.Context) (hpositive : ∀ r j v, σ.letterAt r = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hchosenGlobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j, z = x ∨ z = y) (keep : List ℕ) (m n p high : ℕ) (hp : p ∈ (σ.part keep s m).childPositions) (hn : n = 1) (hhighmem : high ∈ (σ.part (σ.childPositions.filter (· ∉ keep)) t n).childPositions) (hhigh : 3 ≤ (match s with | Ctx.Side.lower => (σ.part (σ.childPositions.filter (· ∉ keep)) t n).cupLimit high high | Ctx.Side.upper => (σ.part (σ.childPositions.filter (· ∉ keep)) t n).capLimit high high)) (hbetween : (x < p ∧ p < y) ∨ (y < p ∧ p < x)) (hOverlap : let B := σ.part (σ.childPositions.filter (· ∉ keep)) t n; let capacity : ℕ → ℕ := fun q => match s with | Ctx.Side.lower => B.cupLimit q q | Ctx.Side.upper => B.capLimit q q; let color : ℕ → ℕ := fun q => if capacity q ≤ 2 then 0 else 1; let support : ℕ → List ℕ := fun c => B.childPositions.filter (fun q => color q = c); let group : ℕ → Ctx.Context := fun c => ({ B with word := (List.range B.word.length).map (fun q => match B.letterAt q with | Ctx.Letter.child => if q ∈ support c then Ctx.Letter.child else Ctx.Letter.ext (B.maxima.length + 1) Ctx.Side.lower | Ctx.Letter.ext j v => Ctx.Letter.ext j v) } : Ctx.Context); let global := match t with | Ctx.Side.lower => B.u | Ctx.Side.upper => B.a; let active : ℕ → Finset ℕ := fun c => (group c).childPositions.toFinset.filter (fun q => 0 < (group c).cupLimit q q ∧ 0 < (group c).capLimit q q); let interval : ℕ → ℕ → Finset ℕ := fun c q => Finset.Icc ((group c).leftExt t 0 q + 1) (global - 1 - (group c).rightExt t 0 q); let pairs : ℕ → Finset (ℕ × ℕ) := fun c => (active c).biUnion (fun q => ((interval c q).product (interval c q)).filter (fun z => z.1 ≤ z.2)); ((pairs 0) ∩ (pairs 1)).card ≤ 1) : let B := σ.part (σ.childPositions.filter (· ∉ keep)) t n; p ∈ B.extPositions 1 ∧ B.maximumAt 1 = 1 ∧ (∀ fuel, Ctx.Context.boundFuel fuel B ≤ 11) ∧ B.bound ≤ 11 := by
  classical
  let rest := σ.childPositions.filter (· ∉ keep)
  let B := σ.part rest t n
  let C (q : ℕ) := match s with
    | Ctx.Side.lower => B.cupLimit q q
    | Ctx.Side.upper => B.capLimit q q
  let color (q : ℕ) := if C q ≤ 2 then (0 : ℕ) else 1
  let support (c : ℕ) := B.childPositions.filter (fun q => color q = c)
  let group (c : ℕ) : Ctx.Context := { B with
    word := (List.range B.word.length).map (fun q => match B.letterAt q with
      | Ctx.Letter.child => if q ∈ support c then Ctx.Letter.child
          else Ctx.Letter.ext (B.maxima.length + 1) Ctx.Side.lower
      | Ctx.Letter.ext j v => Ctx.Letter.ext j v) }
  let G := match t with
    | Ctx.Side.lower => B.u
    | Ctx.Side.upper => B.a
  let active (c : ℕ) := (group c).childPositions.toFinset.filter
    (fun q => 0 < (group c).cupLimit q q ∧ 0 < (group c).capLimit q q)
  let I (c q : ℕ) := Finset.Icc ((group c).leftExt t 0 q + 1)
    (G - 1 - (group c).rightExt t 0 q)
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
  have hChosenB : ∀ j ∈ B.levelsOn s 0, ∀ z ∈ B.extPositions j,
      z = x ∨ z = y := by
    have hBsideOne : B.sideAt 1 = t :=
      Ctx.Context.part_sideAt_one_of_mem hpositive rest t n hpB
    have hs : B.sideAt 1 ≠ s := by
      rw [hBsideOne]
      exact Ne.symm hne
    intro j hj z hz
    change j ∈ (σ.part rest t n).levelsOn s 0 at hj
    rw [Ctx.Context.part_levelsOn_other_zero hs] at hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
    change z ∈ (σ.part rest t n).extPositions (i + 1) at hz
    rw [Ctx.Context.part_extPositions_succ σ rest t n
      (Ctx.Context.one_le_of_mem_levels (List.mem_filter.mp hi).1)] at hz
    exact hchosen i hi z hz
  have hPosB := ctx_part_positive_letters σ rest t n
  have hChosenGlobalB : (match s with
      | Ctx.Side.lower => B.u
      | Ctx.Side.upper => B.a) ≤ 5 := by
    cases s <;> exact hchosenGlobal
  have hOppositeB : (match t with
      | Ctx.Side.lower => B.u
      | Ctx.Side.upper => B.a) ≤ 5 := by
    cases t <;> exact hopposite
  have hHighB : 3 ≤ (match s with
      | Ctx.Side.lower => B.cupLimit high high
      | Ctx.Side.upper => B.capLimit high high) := by
    cases s <;> exact hhigh
  have hOverlapB : ((pairs 0) ∩ (pairs 1)).card ≤ 1 := by
    cases s <;> cases t <;>
      simpa only [B, rest, C, color, support, group, G, active, I, Q, pairs]
        using hOverlap
  have hBound :=
    ctx_two_marker_mixed_capacity_pair_intersection_one_eleven_bound
      B hPosB s t hne (N + 1) (M + 1) x y high hNB hMB (by omega)
      hNsB hMsB hxB hyB hChosenGlobalB hOppositeB hChosenB hhighmem hHighB
  have hBound' : (∀ fuel, Ctx.Context.boundFuel fuel B ≤ 11) ∧
      B.bound ≤ 11 := by
    apply hBound
    cases s <;> cases t <;>
      simpa only [C, color, support, group, G, active, I, Q, pairs]
        using hOverlapB
  exact ⟨hpB, hBMaximumOne, hBound'.1, hBound'.2⟩

end ErdosSzekeres
