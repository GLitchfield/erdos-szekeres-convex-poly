import ESBlueprint.B.CtxTwoActualMarkerOppositeBetweenActiveSeparatedCompanionElevenBound

namespace ErdosSzekeres

/-- For the actual opposite level-one marker between the chosen markers, either the companion has every-fuel/full bound eleven or two active children of its low chosen-capacity pruning lie strictly on opposite sides of that physical marker; the theorem also records marker membership and maximum one.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_two_actual_marker_opposite_between_active_separated_companion_eleven_bound, ErdosSzekeres.ctx_part_positive_letters, ErdosSzekeres.ctx_part_pruning_history_transport
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_actual_marker_opposite_between_eleven_or_active_low_straddles (σ : Ctx.Context) (hpositive : ∀ r j v, σ.letterAt r = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hchosenGlobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j, z = x ∨ z = y) (keep : List ℕ) (m n p high : ℕ) (hp : p ∈ (σ.part keep s m).childPositions) (hn : n = 1) (hhighmem : high ∈ (σ.part (σ.childPositions.filter (· ∉ keep)) t n).childPositions) (hhigh : 3 ≤ (match s with | Ctx.Side.lower => (σ.part (σ.childPositions.filter (· ∉ keep)) t n).cupLimit high high | Ctx.Side.upper => (σ.part (σ.childPositions.filter (· ∉ keep)) t n).capLimit high high)) (hbetween : (x < p ∧ p < y) ∨ (y < p ∧ p < x)) : let B := σ.part (σ.childPositions.filter (· ∉ keep)) t n; let capacity : ℕ → ℕ := fun q => match s with | Ctx.Side.lower => B.cupLimit q q | Ctx.Side.upper => B.capLimit q q; let support : List ℕ := B.childPositions.filter (fun q => capacity q ≤ 2); let low : Ctx.Context := ({ B with word := (List.range B.word.length).map (fun q => match B.letterAt q with | Ctx.Letter.child => if q ∈ support then Ctx.Letter.child else Ctx.Letter.ext (B.maxima.length + 1) Ctx.Side.lower | Ctx.Letter.ext j v => Ctx.Letter.ext j v) } : Ctx.Context); p ∈ B.extPositions 1 ∧ B.maximumAt 1 = 1 ∧ (((∀ fuel, Ctx.Context.boundFuel fuel B ≤ 11) ∧ B.bound ≤ 11) ∨ ∃ q ∈ low.childPositions, 0 < low.cupLimit q q ∧ 0 < low.capLimit q q ∧ ∃ r ∈ low.childPositions, 0 < low.cupLimit r r ∧ 0 < low.capLimit r r ∧ q < p ∧ p < r) := by
  classical
  dsimp only
  let rest := σ.childPositions.filter (· ∉ keep)
  let B := σ.part rest t n
  let capacity : ℕ → ℕ := fun q => match (generalizing := false) s with
    | Ctx.Side.lower => B.cupLimit q q
    | Ctx.Side.upper => B.capLimit q q
  let support : List ℕ := B.childPositions.filter (fun q => capacity q ≤ 2)
  let low : Ctx.Context := { B with
    word := (List.range B.word.length).map (fun q => match B.letterAt q with
      | Ctx.Letter.child => if q ∈ support then Ctx.Letter.child
          else Ctx.Letter.ext (B.maxima.length + 1) Ctx.Side.lower
      | Ctx.Letter.ext j v => Ctx.Letter.ext j v) }
  have hpa : p ∈ σ.childPositions ∧ p ∈ keep := by
    simpa only [Ctx.Context.part_childPositions, List.mem_filter,
      decide_eq_true_eq] using hp
  have hpB : p ∈ B.extPositions 1 := by
    change p ∈ (σ.part rest t n).extPositions 1
    rw [Ctx.Context.part_extPositions_one hpositive]
    exact List.mem_filter.mpr ⟨hpa.1, by simp [rest, hpa.2]⟩
  have hMaximum : B.maximumAt 1 = 1 := by
    rw [Ctx.Context.part_maximumAt_one, hn]
  refine ⟨hpB, hMaximum, ?_⟩
  by_cases hboundary :
      (∀ q ∈ low.childPositions,
        0 < low.cupLimit q q ∧ 0 < low.capLimit q q → q < p) ∨
      (∀ q ∈ low.childPositions,
        0 < low.cupLimit q q ∧ 0 < low.capLimit q q → p < q)
  · left
    have hh :=
      ctx_two_actual_marker_opposite_between_active_separated_companion_eleven_bound
        σ hpositive s t hne N M x y hN hM hNM hNs hMs hx hy
        hchosenGlobal hopposite hchosen keep m n p high hp hn hhighmem hhigh
        hbetween
    apply hh
    simpa [B, rest, capacity, support, low] using hboundary
  · right
    have hPosB := ctx_part_positive_letters σ rest t n
    have hTransport := ctx_part_pruning_history_transport B hPosB support
      Ctx.Side.lower 0
    have hChildEq : low.childPositions =
        B.childPositions.filter (· ∈ support) := by
      exact hTransport.2.1
    have hChildB (q : ℕ) (hq : q ∈ low.childPositions) :
        q ∈ B.childPositions := by
      rw [hChildEq] at hq
      exact (List.mem_filter.mp hq).1
    have hChildNe (q : ℕ) (hq : q ∈ low.childPositions) : q ≠ p := by
      have hc := of_decide_eq_true (List.mem_filter.mp (hChildB q hq)).2
      have he := (List.mem_filter.mp hpB).2
      intro h
      subst q
      simp [hc] at he
    push Not at hboundary
    obtain ⟨⟨r, hr, hrActive, hnotRight⟩,
        q, hq, hqActive, hnotLeft⟩ := hboundary
    have hqne := hChildNe q hq
    have hrne := hChildNe r hr
    exact ⟨q, hq, hqActive.1, hqActive.2,
      r, hr, hrActive.1, hrActive.2, by omega, by omega⟩

end ErdosSzekeres
