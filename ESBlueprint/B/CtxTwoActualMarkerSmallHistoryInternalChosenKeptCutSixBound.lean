import ESBlueprint.B.CtxTwoActualMarkerOppositeYoungerExteriorCompanionElevenBound
import ESBlueprint.B.CtxExtremeCutSixSmallHistoryMixedCapacityResidualClassification
import ESBlueprint.B.CtxSmallGlobalAxisRankTriplePotential
import ESBlueprint.B.CtxTwoMarkerLowCapacityPruningFiveBoundOfOppositeBoundary
import ESBlueprint.B.CtxTwoMarkerHighCapacityPruningRankPairBoundOfHighWitness
import ESBlueprint.B.CtxBoundLeSumRunGroupPruningsOfActualMarkerGlobalFive
import ESBlueprint.B.CtxPointLimitsEqOfChildInterval
import ESBlueprint.B.CtxTwoMarkerOlderExteriorInternalIntervalCutPotentialBound

namespace ErdosSzekeres

/-- Partial assembly of the exact small-history internally bracketed chosen-kept cut at k six. The retained part contributes at most one. The chosen-global-at-most-four, classifier-done, between-marker, and younger-exterior branches close; the older-exterior branch at chosen global five still requires a coupled one-unit saving.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_bound_le_one_of_large_sibling_maximum, ErdosSzekeres.ctx_small_global_axis_rank_triple_potential, ErdosSzekeres.ctx_extreme_cut_six_small_history_mixed_capacity_residual_classification, ErdosSzekeres.ctx_two_actual_marker_opposite_between_companion_eleven_bound, ErdosSzekeres.ctx_two_actual_marker_opposite_younger_exterior_companion_eleven_bound
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_actual_marker_small_history_internal_chosen_kept_cut_six_bound (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hchosenGlobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hoppositeLower : 2 ≤ (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a)) (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j, z = x ∨ z = y) (hmax : ∀ j ∈ σ.levelsOn s 0, σ.maximumAt j ≤ 1) (keep : List ℕ) (q₀ l r m n : ℕ) (hq₀ : q₀ ∈ keep) (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions) (hl : l ∈ σ.childPositions) (hr : r ∈ σ.childPositions) (hlnot : l ∉ keep) (hrnot : r ∉ keep) (hinside : ∀ p ∈ keep, l < p ∧ p < r) (hconvex : ∀ p ∈ keep, ∀ q ∈ keep, ∀ z ∈ σ.childPositions, p ≤ z → z ≤ q → z ∈ keep) (hm : m + 2 = σ.k) (hk : σ.k = 6) (hn : 1 ≤ n) (hcoupling : m + n = σ.k - 1) : let rest := σ.childPositions.filter (· ∉ keep); (∀ f g, Ctx.Context.boundFuel f (σ.part keep s m) + Ctx.Context.boundFuel g (σ.part rest t n) ≤ 12) ∧ (σ.part keep s m).bound + (σ.part rest t n).bound ≤ 12 := by
  classical
  let rest := σ.childPositions.filter (· ∉ keep)
  let A := σ.part keep s m
  let B := σ.part rest t n
  change (∀ f g, Ctx.Context.boundFuel f A + Ctx.Context.boundFuel g B ≤ 12) ∧
    A.bound + B.bound ≤ 12
  have hmFour : m = 4 := by omega
  have hnOne : n = 1 := by omega
  have hqA : q₀ ∈ A.childPositions := by
    simp only [A, Ctx.Context.part_childPositions, List.mem_filter,
      decide_eq_true_eq]
    exact ⟨hkeep q₀ hq₀, hq₀⟩
  have hPosA := ctx_part_positive_letters σ keep s m
  have hPosB := ctx_part_positive_letters σ rest t n
  have hOneA : 1 ∈ A.levels := by
    simp [A, Ctx.Context.part_levels]
  have hLargeA : A.k - 2 ≤ A.maximumAt 1 := by
    rw [Ctx.Context.part_maximumAt_one]
    change σ.k - 2 ≤ m
    omega
  have hA := ctx_bound_le_one_of_large_sibling_maximum A hPosA 1 hOneA hLargeA
  have hOppositeB : (match t with
      | Ctx.Side.lower => B.u
      | Ctx.Side.upper => B.a) ≤ 5 := by
    cases t <;> exact hopposite
  have hChosenBLe : (match s with
      | Ctx.Side.lower => B.u
      | Ctx.Side.upper => B.a) ≤ 5 := by
    cases s <;> exact hchosenGlobal
  by_cases hChosenSmall : (match s with
      | Ctx.Side.lower => B.u
      | Ctx.Side.upper => B.a) ≤ 4
  · let w := (match s with
        | Ctx.Side.lower => B.u
        | Ctx.Side.upper => B.a) - 1
    let active := B.childPositions.toFinset.filter
      (fun p => 0 < B.cupLimit p p ∧ 0 < B.capLimit p p)
    let interval := fun p => Finset.Icc (B.leftExt s 0 p + 1)
      (w - B.rightExt s 0 p)
    let triples := active.biUnion (fun p =>
      ((interval p).product ((interval p).product (interval p))).filter
        (fun z => z.1 ≤ z.2.1 ∧ z.2.1 ≤ z.2.2))
    have hTriple := ctx_small_global_axis_rank_triple_potential B hPosB
      t s (Ne.symm hne) hOppositeB
    change (∀ fuel, Ctx.Context.boundFuel fuel B ≤ triples.card) ∧
      B.bound ≤ triples.card ∧ triples.card ≤ (w + 2).choose 3 ∧ _ at hTriple
    have hw : w ≤ 3 := by
      dsimp only [w]
      omega
    have hChoose : (w + 2).choose 3 ≤ 10 := by
      have hh := Nat.choose_le_choose 3 (show w + 2 ≤ 5 by omega)
      norm_num at hh ⊢
      exact hh
    exact ⟨fun f g => (Nat.add_le_add (hA.1 f)
        ((hTriple.1 g).trans (hTriple.2.2.1.trans hChoose))).trans (by omega),
      (Nat.add_le_add hA.2
        (hTriple.2.1.trans (hTriple.2.2.1.trans hChoose))).trans (by omega)⟩
  · have hChosenFive : (match s with
        | Ctx.Side.lower => B.u
        | Ctx.Side.upper => B.a) = 5 := by omega
    have hClass :=
      ctx_extreme_cut_six_small_history_mixed_capacity_residual_classification
        σ hpositive s t hne N M x y hN hM hNM hNs hMs hx hy
        hchosenGlobal hoppositeLower hopposite hchosen hmax keep m n q₀ hqA hm hk
    change ((∀ f g, Ctx.Context.boundFuel f A + Ctx.Context.boundFuel g B ≤ 11) ∧
        A.bound + B.bound ≤ 11) ∨
      ∃ high ∈ B.childPositions, 0 < B.cupLimit high high ∧
        0 < B.capLimit high high ∧
        3 ≤ (match s with
          | Ctx.Side.lower => B.cupLimit high high
          | Ctx.Side.upper => B.capLimit high high) ∧
        ∃ low ∈ B.childPositions, 0 < B.cupLimit low low ∧
          0 < B.capLimit low low ∧
          (match s with
            | Ctx.Side.lower => B.cupLimit low low
            | Ctx.Side.upper => B.capLimit low low) ≤ 2 ∧
          ((x < y ∧ low < y ∧ y < high) ∨
            (y < x ∧ high < y ∧ y < low)) at hClass
    rcases hClass with hDone | ⟨high, hHighMem, hHighCup, hHighCap,
      hHigh, low, hLowMem, hLowCup, hLowCap, hLow, hSeparated⟩
    · exact ⟨fun f g => (hDone.1 f g).trans (by omega),
        hDone.2.trans (by omega)⟩
    have hChildNe (p j z : ℕ) (hp : p ∈ σ.childPositions)
        (hz : z ∈ σ.extPositions j) : p ≠ z := by
      have hc := of_decide_eq_true (List.mem_filter.mp hp).2
      have he := (List.mem_filter.mp hz).2
      intro h
      subst z
      simp [hc] at he
    by_cases hbetween : ∃ p ∈ keep,
        (x < p ∧ p < y) ∨ (y < p ∧ p < x)
    · obtain ⟨p, hp, hpBetween⟩ := hbetween
      have hpA : p ∈ A.childPositions := by
        simp only [A, Ctx.Context.part_childPositions, List.mem_filter,
          decide_eq_true_eq]
        exact ⟨hkeep p hp, hp⟩
      have hB := ctx_two_actual_marker_opposite_between_companion_eleven_bound
        σ hpositive s t hne N M x y hN hM hNM hNs hMs hx hy
        hchosenGlobal hopposite hchosen keep m n p high hpA hnOne hHighMem
        hHigh hpBetween
      exact ⟨fun f g => (Nat.add_le_add (hA.1 f) (hB.2.2.1 g)).trans (by omega),
        (Nat.add_le_add hA.2 hB.2.2.2).trans (by omega)⟩
    by_cases hyounger : ∃ p ∈ keep,
        (p < x ∧ x < y) ∨ (y < x ∧ x < p)
    · obtain ⟨p, hp, hpYounger⟩ := hyounger
      have hpA : p ∈ A.childPositions := by
        simp only [A, Ctx.Context.part_childPositions, List.mem_filter,
          decide_eq_true_eq]
        exact ⟨hkeep p hp, hp⟩
      have hB := ctx_two_actual_marker_opposite_younger_exterior_companion_eleven_bound
        σ hpositive s t hne N M x y hN hM hNM hNs hMs hx hy
        hchosenGlobal hopposite hchosen keep m n p hpA hnOne hpYounger
      exact ⟨fun f g => (Nat.add_le_add (hA.1 f) (hB.2.2.1 g)).trans (by omega),
        (Nat.add_le_add hA.2 hB.2.2.2).trans (by omega)⟩
    have hexterior : (x < y ∧ ∀ p ∈ keep, y < p) ∨
        (y < x ∧ ∀ p ∈ keep, p < y) := by
      rcases hSeparated with ⟨hxy, _, _⟩ | ⟨hyx, _, _⟩
      · left
        refine ⟨hxy, ?_⟩
        intro p hp
        have hpx := hChildNe p N x (hkeep p hp) hx
        have hpy := hChildNe p M y (hkeep p hp) hy
        by_cases hlt : p < x
        · exact False.elim (hyounger ⟨p, hp, Or.inl ⟨hlt, hxy⟩⟩)
        by_cases hlt' : p < y
        · exact False.elim (hbetween ⟨p, hp, Or.inl ⟨by omega, hlt'⟩⟩)
        omega
      · right
        refine ⟨hyx, ?_⟩
        intro p hp
        have hpx := hChildNe p N x (hkeep p hp) hx
        have hpy := hChildNe p M y (hkeep p hp) hy
        by_cases hgt : x < p
        · exact False.elim (hyounger ⟨p, hp, Or.inr ⟨hyx, hgt⟩⟩)
        by_cases hgt' : y < p
        · exact False.elim (hbetween ⟨p, hp, Or.inr ⟨hgt', by omega⟩⟩)
        omega
    sorry

end ErdosSzekeres
