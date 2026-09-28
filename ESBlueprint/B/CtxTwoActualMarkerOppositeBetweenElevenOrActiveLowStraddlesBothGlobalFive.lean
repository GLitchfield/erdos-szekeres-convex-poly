import ESBlueprint.B.CtxTwoActualMarkerOppositeBetweenElevenOrActiveLowStraddles
import ESBlueprint.B.CtxSmallOppositeGlobalMarkerSquareBound

namespace ErdosSzekeres

/-- The actual companion is bounded by eleven unless both axis globals equal five and active low children straddle the physical opposite level-one marker; if either global is at most four, an actual-marker square potential gives the stronger bound nine.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_two_actual_marker_opposite_between_eleven_or_active_low_straddles, ErdosSzekeres.ctx_small_opposite_global_marker_square_bound, ErdosSzekeres.ctx_part_positive_letters
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_actual_marker_opposite_between_eleven_or_active_low_straddles_both_global_five (σ : Ctx.Context) (hpositive : ∀ r j v, σ.letterAt r = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hchosenGlobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j, z = x ∨ z = y) (keep : List ℕ) (m n p high : ℕ) (hp : p ∈ (σ.part keep s m).childPositions) (hn : n = 1) (hhighmem : high ∈ (σ.part (σ.childPositions.filter (· ∉ keep)) t n).childPositions) (hhigh : 3 ≤ (match s with | Ctx.Side.lower => (σ.part (σ.childPositions.filter (· ∉ keep)) t n).cupLimit high high | Ctx.Side.upper => (σ.part (σ.childPositions.filter (· ∉ keep)) t n).capLimit high high)) (hbetween : (x < p ∧ p < y) ∨ (y < p ∧ p < x)) : let B := σ.part (σ.childPositions.filter (· ∉ keep)) t n; let capacity : ℕ → ℕ := fun q => match s with | Ctx.Side.lower => B.cupLimit q q | Ctx.Side.upper => B.capLimit q q; let support : List ℕ := B.childPositions.filter (fun q => capacity q ≤ 2); let low : Ctx.Context := ({ B with word := (List.range B.word.length).map (fun q => match B.letterAt q with | Ctx.Letter.child => if q ∈ support then Ctx.Letter.child else Ctx.Letter.ext (B.maxima.length + 1) Ctx.Side.lower | Ctx.Letter.ext j v => Ctx.Letter.ext j v) } : Ctx.Context); p ∈ B.extPositions 1 ∧ B.maximumAt 1 = 1 ∧ (((∀ fuel, Ctx.Context.boundFuel fuel B ≤ 11) ∧ B.bound ≤ 11) ∨ ((match s with | Ctx.Side.lower => B.u | Ctx.Side.upper => B.a) = 5 ∧ (match t with | Ctx.Side.lower => B.u | Ctx.Side.upper => B.a) = 5 ∧ ∃ q ∈ low.childPositions, 0 < low.cupLimit q q ∧ 0 < low.capLimit q q ∧ ∃ r ∈ low.childPositions, 0 < low.cupLimit r r ∧ 0 < low.capLimit r r ∧ q < p ∧ p < r)) := by
  classical
  dsimp only
  let rest := σ.childPositions.filter (· ∉ keep)
  let B := σ.part rest t n
  let G (v : Ctx.Side) := match v with
    | Ctx.Side.lower => B.u
    | Ctx.Side.upper => B.a
  let capacity : ℕ → ℕ := fun q => match (generalizing := false) s with
    | Ctx.Side.lower => B.cupLimit q q
    | Ctx.Side.upper => B.capLimit q q
  let support : List ℕ := B.childPositions.filter (fun q => capacity q ≤ 2)
  let low : Ctx.Context := { B with
    word := (List.range B.word.length).map (fun q => match B.letterAt q with
      | Ctx.Letter.child => if q ∈ support then Ctx.Letter.child
          else Ctx.Letter.ext (B.maxima.length + 1) Ctx.Side.lower
      | Ctx.Letter.ext j v => Ctx.Letter.ext j v) }
  have hd := ctx_two_actual_marker_opposite_between_eleven_or_active_low_straddles
    σ hpositive s t hne N M x y hN hM hNM hNs hMs hx hy hchosenGlobal
    hopposite hchosen keep m n p high hp hn hhighmem hhigh hbetween
  change p ∈ B.extPositions 1 ∧ B.maximumAt 1 = 1 ∧
    (((∀ fuel, Ctx.Context.boundFuel fuel B ≤ 11) ∧ B.bound ≤ 11) ∨
      ∃ q ∈ low.childPositions,
        0 < low.cupLimit q q ∧ 0 < low.capLimit q q ∧
        ∃ r ∈ low.childPositions,
          0 < low.cupLimit r r ∧ 0 < low.capLimit r r ∧ q < p ∧ p < r) at hd
  obtain ⟨hpB, hMaximum, hcase⟩ := hd
  refine ⟨hpB, hMaximum, ?_⟩
  rcases hcase with hBound | hstraddle
  · exact Or.inl hBound
  have hPosB := ctx_part_positive_letters σ rest t n
  have hBlevelOne : 1 ∈ B.levels := by
    simp [B, Ctx.Context.part_levels]
  have hBsideOne : B.sideAt 1 = t :=
    Ctx.Context.part_sideAt_one_of_mem hpositive rest t n hpB
  have hNpos := Ctx.Context.one_le_of_mem_levels hN
  have hNB : N + 1 ∈ B.levels := by
    rw [Ctx.Context.part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨N, hN, rfl⟩)
  have hNsB : B.sideAt (N + 1) = s :=
    (Ctx.Context.part_sideAt_succ σ rest t n hNpos).trans hNs
  have hxB : x ∈ B.extPositions (N + 1) := by
    rw [Ctx.Context.part_extPositions_succ σ rest t n hNpos]
    exact hx
  have hChosenB : G s ≤ 5 := by
    cases s <;> exact hchosenGlobal
  have hOppositeB : G t ≤ 5 := by
    cases t <;> exact hopposite
  have closeSquare (u v : Ctx.Side) (huv : u ≠ v) (J z : ℕ)
      (hJ : J ∈ B.levels) (hJu : B.sideAt J = u)
      (hz : z ∈ B.extPositions J) (hu : G u ≤ 5) (hv : G v ≤ 4) :
      (∀ fuel, Ctx.Context.boundFuel fuel B ≤ 11) ∧ B.bound ≤ 11 := by
    have hb := ctx_small_opposite_global_marker_square_bound B hPosB u v huv
      J z hJ hJu hz (by cases u <;> exact hu) (by cases v <;> exact hv)
    change (∀ fuel, Ctx.Context.boundFuel fuel B ≤ (G v - 1) ^ 2) ∧
      B.bound ≤ (G v - 1) ^ 2 at hb
    have hw : G v - 1 ≤ 3 := by omega
    have hbudget : (G v - 1) ^ 2 ≤ 11 :=
      (Nat.pow_le_pow_left hw 2).trans (by decide)
    exact ⟨fun fuel => (hb.1 fuel).trans hbudget, hb.2.trans hbudget⟩
  by_cases hChosenSmall : G s ≤ 4
  · exact Or.inl (closeSquare t s (Ne.symm hne) 1 p hBlevelOne hBsideOne
      hpB hOppositeB hChosenSmall)
  by_cases hOppositeSmall : G t ≤ 4
  · exact Or.inl (closeSquare s t hne (N + 1) x hNB hNsB hxB
      hChosenB hOppositeSmall)
  · right
    change G s = 5 ∧ G t = 5 ∧ _
    exact ⟨by omega, by omega, hstraddle⟩

end ErdosSzekeres
