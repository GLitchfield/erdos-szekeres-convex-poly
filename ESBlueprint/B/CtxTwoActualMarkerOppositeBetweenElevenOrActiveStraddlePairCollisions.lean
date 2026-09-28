import ESBlueprint.B.CtxTwoActualMarkerOppositeBetweenSmallPairOverlapCompanionElevenBound
import ESBlueprint.B.CtxTwoActualMarkerOppositeBetweenElevenOrActiveLowStraddlesBothGlobalFive

set_option maxHeartbeats 4000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

/-- The actual opposite-between companion is bounded by eleven unless both globals equal five, active low chosen-capacity children straddle the physical level-one marker, and the canonical low/high active rank-pair supports have at least two shared pairs. The marker occurrence, maximum one, every fuel, arbitrary histories and both orientations remain explicit.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_two_actual_marker_opposite_between_eleven_or_active_low_straddles_both_global_five, ErdosSzekeres.ctx_two_actual_marker_opposite_between_small_pair_overlap_companion_eleven_bound
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_actual_marker_opposite_between_eleven_or_active_straddle_pair_collisions (σ : Ctx.Context) (hpositive : ∀ r j v, σ.letterAt r = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hchosenGlobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j, z = x ∨ z = y) (keep : List ℕ) (m n p high : ℕ) (hp : p ∈ (σ.part keep s m).childPositions) (hn : n = 1) (hhighmem : high ∈ (σ.part (σ.childPositions.filter (· ∉ keep)) t n).childPositions) (hhigh : 3 ≤ (match s with | Ctx.Side.lower => (σ.part (σ.childPositions.filter (· ∉ keep)) t n).cupLimit high high | Ctx.Side.upper => (σ.part (σ.childPositions.filter (· ∉ keep)) t n).capLimit high high)) (hbetween : (x < p ∧ p < y) ∨ (y < p ∧ p < x)) : let B := σ.part (σ.childPositions.filter (· ∉ keep)) t n; let capacity : ℕ → ℕ := fun q => match s with | Ctx.Side.lower => B.cupLimit q q | Ctx.Side.upper => B.capLimit q q; let color : ℕ → ℕ := fun q => if capacity q ≤ 2 then 0 else 1; let support : ℕ → List ℕ := fun c => B.childPositions.filter (fun q => color q = c); let group : ℕ → Ctx.Context := fun c => ({ B with word := (List.range B.word.length).map (fun q => match B.letterAt q with | Ctx.Letter.child => if q ∈ support c then Ctx.Letter.child else Ctx.Letter.ext (B.maxima.length + 1) Ctx.Side.lower | Ctx.Letter.ext j v => Ctx.Letter.ext j v) } : Ctx.Context); let global := match t with | Ctx.Side.lower => B.u | Ctx.Side.upper => B.a; let active : ℕ → Finset ℕ := fun c => (group c).childPositions.toFinset.filter (fun q => 0 < (group c).cupLimit q q ∧ 0 < (group c).capLimit q q); let interval : ℕ → ℕ → Finset ℕ := fun c q => Finset.Icc ((group c).leftExt t 0 q + 1) (global - 1 - (group c).rightExt t 0 q); let pairs : ℕ → Finset (ℕ × ℕ) := fun c => (active c).biUnion (fun q => ((interval c q).product (interval c q)).filter (fun z => z.1 ≤ z.2)); p ∈ B.extPositions 1 ∧ B.maximumAt 1 = 1 ∧ (((∀ fuel, Ctx.Context.boundFuel fuel B ≤ 11) ∧ B.bound ≤ 11) ∨ ((match s with | Ctx.Side.lower => B.u | Ctx.Side.upper => B.a) = 5 ∧ (match t with | Ctx.Side.lower => B.u | Ctx.Side.upper => B.a) = 5 ∧ (∃ q ∈ active 0, ∃ r ∈ active 0, q < p ∧ p < r) ∧ 2 ≤ ((pairs 0) ∩ (pairs 1)).card)) := by
  classical
  dsimp only
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
  let lowSupport := B.childPositions.filter (fun q => C q ≤ 2)
  let low : Ctx.Context := { B with
    word := (List.range B.word.length).map (fun q => match B.letterAt q with
      | Ctx.Letter.child => if q ∈ lowSupport then Ctx.Letter.child
          else Ctx.Letter.ext (B.maxima.length + 1) Ctx.Side.lower
      | Ctx.Letter.ext j v => Ctx.Letter.ext j v) }
  have hd :=
    ctx_two_actual_marker_opposite_between_eleven_or_active_low_straddles_both_global_five
      σ hpositive s t hne N M x y hN hM hNM hNs hMs hx hy hchosenGlobal
      hopposite hchosen keep m n p high hp hn hhighmem hhigh hbetween
  change p ∈ B.extPositions 1 ∧ B.maximumAt 1 = 1 ∧
    (((∀ fuel, Ctx.Context.boundFuel fuel B ≤ 11) ∧ B.bound ≤ 11) ∨
      ((match s with | Ctx.Side.lower => B.u | Ctx.Side.upper => B.a) = 5 ∧
       (match t with | Ctx.Side.lower => B.u | Ctx.Side.upper => B.a) = 5 ∧
       ∃ q ∈ low.childPositions,
         0 < low.cupLimit q q ∧ 0 < low.capLimit q q ∧
         ∃ r ∈ low.childPositions,
           0 < low.cupLimit r r ∧ 0 < low.capLimit r r ∧
           q < p ∧ p < r)) at hd
  obtain ⟨hpB, hmax, hcase⟩ := hd
  refine ⟨hpB, hmax, ?_⟩
  rcases hcase with hbound | hresidual
  · exact Or.inl hbound
  have hStraddle : ∃ q ∈ active 0, ∃ r ∈ active 0, q < p ∧ p < r := by
    obtain ⟨q, hq, hqCup, hqCap, r, hr, hrCup, hrCap, hqpr⟩ := hresidual.2.2
    refine ⟨q, ?_, r, ?_, hqpr⟩
    · simpa [active, group, support, color, low, lowSupport] using
        (show q ∈ low.childPositions.toFinset.filter
          (fun w => 0 < low.cupLimit w w ∧ 0 < low.capLimit w w) from
            Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hq, hqCup, hqCap⟩)
    · simpa [active, group, support, color, low, lowSupport] using
        (show r ∈ low.childPositions.toFinset.filter
          (fun w => 0 < low.cupLimit w w ∧ 0 < low.capLimit w w) from
            Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr, hrCup, hrCap⟩)
  by_cases hoverlap : ((pairs 0) ∩ (pairs 1)).card ≤ 1
  · left
    have hs :=
      ctx_two_actual_marker_opposite_between_small_pair_overlap_companion_eleven_bound
        σ hpositive s t hne N M x y hN hM hNM hNs hMs hx hy hchosenGlobal
        hopposite hchosen keep m n p high hp hn hhighmem hhigh hbetween
        (by
          cases s <;> cases t <;>
            simpa only [B, rest, C, color, support, group, G, active, I, Q, pairs]
              using hoverlap)
    change p ∈ B.extPositions 1 ∧ B.maximumAt 1 = 1 ∧
      (∀ fuel, Ctx.Context.boundFuel fuel B ≤ 11) ∧ B.bound ≤ 11 at hs
    exact ⟨hs.2.2.1, hs.2.2.2⟩
  · right
    refine ⟨hresidual.1, hresidual.2.1, hStraddle, ?_⟩
    have hTwo : 2 ≤ ((pairs 0) ∩ (pairs 1)).card := by omega
    cases s <;> cases t <;>
      simpa only [B, rest, C, color, support, group, G, active, I, Q, pairs]
        using hTwo

end ErdosSzekeres
