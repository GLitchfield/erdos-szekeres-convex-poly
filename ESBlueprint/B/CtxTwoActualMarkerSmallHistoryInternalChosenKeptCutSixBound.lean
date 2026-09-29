import ESBlueprint.B.CtxTwoActualMarkerOppositeYoungerExteriorCompanionElevenBound
import ESBlueprint.B.CtxExtremeCutSixSmallHistoryMixedCapacityResidualClassification
import ESBlueprint.B.CtxSmallGlobalAxisRankTriplePotential
import ESBlueprint.B.CtxTwoMarkerLowCapacityPruningFiveBoundOfOppositeBoundary
import ESBlueprint.B.CtxTwoMarkerHighCapacityPruningRankPairBoundOfHighWitness
import ESBlueprint.B.CtxBoundLeSumRunGroupPruningsOfActualMarkerGlobalFive
import ESBlueprint.B.CtxPointLimitsEqOfChildInterval
import ESBlueprint.B.CtxTwoMarkerOlderExteriorInternalIntervalCutPotentialBound
import ESBlueprint.B.CtxBoundaryMarkerRankBudgetAllHistory
import ESBlueprint.B.CtxSingleLevelOccurrencePruneBoundMono
import ESBlueprint.B.CtxPartPruningHistoryTransport
import ESBlueprint.B.CtxActiveTwoBoundaryMarkerRankUnionBound
import ESBlueprint.B.CtxTwoActualMarkerCompanionMaximumBound
import ESBlueprint.B.CtxBoundLeOppositeWidthOfSiblingMaximumGeKMinusThree
import ESBlueprint.B.CtxActiveBoundaryMarkerRankPairUnionBound
import ESBlueprint.B.CtxActualMarkerRankPairUnionNineBound
import ESBlueprint.B.CtxBoundLeOneOfCommonSingletonRank
import ESBlueprint.B.CtxBoundLeSumRunGroupPruningsCapacityThree
import ESBlueprint.B.CtxNonmonotoneTripleLinearPotential
import ESBlueprint.B.CtxNonmonotoneTripleSaturatedPotentialArbitraryOppositeHistory
import ESBlueprint.B.CtxThinRankWindowsLinearPotential
import ESBlueprint.B.CtxExtensionsLeZeroCutoff
import ESBlueprint.B.CtxTwoMarkerYoungerSurroundingInternalComplementCutTenBound
import ESBlueprint.B.CtxAllActiveCapacityThreeTwoMarkerTriangleBound

namespace ErdosSzekeres

open Ctx Ctx.Context

set_option maxHeartbeats 8000000
set_option maxRecDepth 15000

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
    simpa only [B, Ctx.Context.part] using hopposite
  have hChosenBLe : (match s with
      | Ctx.Side.lower => B.u
      | Ctx.Side.upper => B.a) ≤ 5 := by
    simpa only [B, Ctx.Context.part] using hchosenGlobal
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
    by_cases hOppSmall : (match t with
        | Ctx.Side.lower => σ.u
        | Ctx.Side.upper => σ.a) ≤ 4
    · let w := (match t with
          | Ctx.Side.lower => B.u
          | Ctx.Side.upper => B.a) - 1
      let active := B.childPositions.toFinset.filter
        (fun p => 0 < B.cupLimit p p ∧ 0 < B.capLimit p p)
      let interval := fun p => Finset.Icc (B.leftExt t 0 p + 1)
        (w - B.rightExt t 0 p)
      let triples := active.biUnion (fun p =>
        ((interval p).product ((interval p).product (interval p))).filter
          (fun z => z.1 ≤ z.2.1 ∧ z.2.1 ≤ z.2.2))
      have hTriple := ctx_small_global_axis_rank_triple_potential B hPosB
        s t hne hChosenBLe
      change (∀ fuel, Ctx.Context.boundFuel fuel B ≤ triples.card) ∧
        B.bound ≤ triples.card ∧ triples.card ≤ (w + 2).choose 3 ∧ _ at hTriple
      have hw : w ≤ 3 := by
        dsimp only [w]
        cases t <;> exact Nat.sub_le_sub_right hOppSmall 1
      have hChoose : (w + 2).choose 3 ≤ 10 := by
        have hh := Nat.choose_le_choose 3 (show w + 2 ≤ 5 by omega)
        norm_num at hh ⊢
        exact hh
      exact ⟨fun f g => (Nat.add_le_add (hA.1 f)
          ((hTriple.1 g).trans (hTriple.2.2.1.trans hChoose))).trans (by omega),
        (Nat.add_le_add hA.2
          (hTriple.2.1.trans (hTriple.2.2.1.trans hChoose))).trans (by omega)⟩
    · have hOppFive : (match t with
          | Ctx.Side.lower => σ.u
          | Ctx.Side.upper => σ.a) = 5 := by omega
      have hOneB : 1 ∈ B.levels := by
        simp only [B, Ctx.Context.part_levels, List.mem_cons, true_or]
      have hqB : q₀ ∈ B.extPositions 1 := by
        change q₀ ∈ (σ.part rest t n).extPositions 1
        rw [Ctx.Context.part_extPositions_one hpositive]
        simp only [rest, List.mem_filter, decide_eq_true_eq]
        exact ⟨hkeep q₀ hq₀, by simp [hq₀]⟩
      have hSideB : B.sideAt 1 = t :=
        Ctx.Context.part_sideAt_one_of_mem hpositive rest t n hqB
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
      have hThreeOrderedActualOppositeTen
          (ρ : Context)
          (hPos : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j)
          (J' N' M' a b d L' q' : ℕ)
          (hJ' : J' ∈ ρ.levels) (hN' : N' ∈ ρ.levels)
          (hM' : M' ∈ ρ.levels) (hJN' : J' < N') (hNM' : N' < M')
          (hJSide : ρ.sideAt J' = s) (hNSide : ρ.sideAt N' = s)
          (hMSide : ρ.sideAt M' = s)
          (ha : a ∈ ρ.extPositions J') (hb : b ∈ ρ.extPositions N')
          (hd : d ∈ ρ.extPositions M')
          (hglobalS : (match s with
            | Side.lower => ρ.u | Side.upper => ρ.a) ≤ 5)
          (hyoung : ∀ j ∈ ρ.levelsOn s J', ρ.extPositions j = [])
          (horder : (a < b ∧ b < d) ∨ (d < b ∧ b < a))
          (hL' : L' ∈ ρ.levels) (hLSide : ρ.sideAt L' = t)
          (hq' : q' ∈ ρ.extPositions L')
          (hglobalT : (match t with
            | Side.lower => ρ.u | Side.upper => ρ.a) ≤ 5) :
          (∀ fuel, boundFuel fuel ρ ≤ 10) ∧ ρ.bound ≤ 10 := by
        classical
        have hOneLeft (η : Context) (v : Side) (j p q : ℕ)
            (hj : j ∈ η.levelsOn v 0) (hq : q ∈ η.extPositions j) (hqp : q < p) :
            1 ≤ η.leftExt v 0 p := by
          have hm : q ∈ (η.extPositions j).filter (· < p) := by simp [hq, hqp]
          have hnonempty := List.ne_nil_of_mem hm
          have hv := le_getD_max?_of_mem (L := (η.levelsOn v 0).sublists.map
            (fun ls => (ls.foldl (leftStep η) (p, 0)).2))
            (List.mem_map.mpr ⟨[j],
              List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
          change _ ≤ η.leftExt v 0 p at hv
          simpa only [List.foldl_cons, List.foldl_nil, leftStep,
            List.getLast?_eq_some_getLast hnonempty] using hv
        have hOneRight (η : Context) (v : Side) (j p q : ℕ)
            (hj : j ∈ η.levelsOn v 0) (hq : q ∈ η.extPositions j) (hpq : p < q) :
            1 ≤ η.rightExt v 0 p := by
          have hm : q ∈ (η.extPositions j).filter (p < ·) := by simp [hq, hpq]
          have hnonempty := List.ne_nil_of_mem hm
          have hv := le_getD_max?_of_mem (L := (η.levelsOn v 0).sublists.map
            (fun ls => (ls.foldl (rightStep η) (p, 0)).2))
            (List.mem_map.mpr ⟨[j],
              List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
          change _ ≤ η.rightExt v 0 p at hv
          simpa only [List.foldl_cons, List.foldl_nil, rightStep,
            List.head?_eq_some_head hnonempty] using hv
        have hTrip (η : Context) (A E D u v e : ℕ)
            (hA : A ∈ η.levels) (hE : E ∈ η.levels) (hD : D ∈ η.levels)
            (hAE : A < E) (hED : E < D)
            (hAs : η.sideAt A = s) (hEs : η.sideAt E = s)
            (hDs : η.sideAt D = s)
            (hu : u ∈ η.extPositions A) (hv : v ∈ η.extPositions E)
            (he : e ∈ η.extPositions D) :
            (∀ p, p < u → u < v → v < e → 3 ≤ η.rightExt s 0 p) ∧
            (∀ p, u < p → v < u → e < v → 3 ≤ η.leftExt s 0 p) := by
          have hAOn : A ∈ η.levelsOn s 0 :=
            List.mem_filter.mpr ⟨hA, by simp [hAs]⟩
          have hEOn : E ∈ η.levelsOn s 0 :=
            List.mem_filter.mpr ⟨hE, by simp [hEs]⟩
          have hDOn : D ∈ η.levelsOn s 0 :=
            List.mem_filter.mpr ⟨hD, by simp [hDs]⟩
          have hSorted : (η.levelsOn s 0).Pairwise (· < ·) := by
            apply List.Pairwise.filter
            exact List.pairwise_lt_range.map (fun i => i + 1)
              (fun i j h => by dsimp; omega)
          have hThree : [A, E, D].Sublist (η.levelsOn s 0) := by
            have hs : [A, E, D].Pairwise (· < ·) := by simp; omega
            have hsub : [A, E, D] ⊆ η.levelsOn s 0 := by
              intro j hj
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
              rcases hj with rfl | rfl | rfl
              · exact hAOn
              · exact hEOn
              · exact hDOn
            have heq : (η.levelsOn s 0).filter (· ∈ [A, E, D]) = [A, E, D] := by
              apply (hSorted.filter _).eq_of_mem_iff hs
              intro j
              simp only [List.mem_filter, decide_eq_true_eq]
              exact ⟨And.right, fun hj => ⟨hsub hj, hj⟩⟩
            rw [← heq]
            exact List.filter_sublist
          have hSort (j : ℕ) : (η.extPositions j).Pairwise (· ≤ ·) :=
            (List.pairwise_lt_range.filter _).imp le_of_lt
          constructor
          · intro p hpu huv hve
            have hmA : u ∈ (η.extPositions A).filter (p < ·) := by simp [hu, hpu]
            have hneA := List.ne_nil_of_mem hmA
            let u' := ((η.extPositions A).filter (p < ·)).head hneA
            have hu' : ((η.extPositions A).filter (p < ·)).head? = some u' :=
              List.head?_eq_some_head hneA
            have hu'u : u' ≤ u := ((hSort A).filter _).rel_head hmA
            have hmE : v ∈ (η.extPositions E).filter (u' < ·) := by
              simp [hv]; omega
            have hneE := List.ne_nil_of_mem hmE
            let v' := ((η.extPositions E).filter (u' < ·)).head hneE
            have hv' : ((η.extPositions E).filter (u' < ·)).head? = some v' :=
              List.head?_eq_some_head hneE
            have hv'v : v' ≤ v := ((hSort E).filter _).rel_head hmE
            have hmD : e ∈ (η.extPositions D).filter (v' < ·) := by
              simp [he]; omega
            have hneD := List.ne_nil_of_mem hmD
            have hh := le_getD_max?_of_mem (L := (η.levelsOn s 0).sublists.map
              (fun ls => (ls.foldl (rightStep η) (p, 0)).2))
              (List.mem_map.mpr ⟨[A, E, D], List.mem_sublists.mpr hThree, rfl⟩)
            change _ ≤ η.rightExt s 0 p at hh
            simpa only [List.foldl_cons, List.foldl_nil, rightStep, hu', hv',
              List.head?_eq_some_head hneD] using hh
          · intro p hup hvu hev
            have hmA : u ∈ (η.extPositions A).filter (· < p) := by simp [hu, hup]
            have hneA := List.ne_nil_of_mem hmA
            let u' := ((η.extPositions A).filter (· < p)).getLast hneA
            have hu' : ((η.extPositions A).filter (· < p)).getLast? = some u' :=
              List.getLast?_eq_some_getLast hneA
            have huu' : u ≤ u' := ((hSort A).filter _).rel_getLast hmA
            have hmE : v ∈ (η.extPositions E).filter (· < u') := by
              simp [hv]; omega
            have hneE := List.ne_nil_of_mem hmE
            let v' := ((η.extPositions E).filter (· < u')).getLast hneE
            have hv' : ((η.extPositions E).filter (· < u')).getLast? = some v' :=
              List.getLast?_eq_some_getLast hneE
            have hvv' : v ≤ v' := ((hSort E).filter _).rel_getLast hmE
            have hmD : e ∈ (η.extPositions D).filter (· < v') := by
              simp [he]; omega
            have hneD := List.ne_nil_of_mem hmD
            have hh := le_getD_max?_of_mem (L := (η.levelsOn s 0).sublists.map
              (fun ls => (ls.foldl (leftStep η) (p, 0)).2))
              (List.mem_map.mpr ⟨[A, E, D], List.mem_sublists.mpr hThree, rfl⟩)
            change _ ≤ η.leftExt s 0 p at hh
            simpa only [List.foldl_cons, List.foldl_nil, leftStep, hu', hv',
              List.getLast?_eq_some_getLast hneD] using hh
        let w := (match t with | Side.lower => ρ.u | Side.upper => ρ.a) - 1
        let color (p : ℕ) := if p < a then (0 : ℕ) else 1
        let support (c : ℕ) := ρ.childPositions.filter (fun p => color p = c)
        let group (c : ℕ) : Context := { ρ with
          word := (List.range ρ.word.length).map (fun p => match ρ.letterAt p with
            | Letter.child => if p ∈ support c then Letter.child
                else Letter.ext (ρ.maxima.length + 1) Side.lower
            | Letter.ext j v => Letter.ext j v) }
        let active (η : Context) := η.childPositions.toFinset.filter
          (fun p => 0 < η.cupLimit p p ∧ 0 < η.capLimit p p)
        let I (η : Context) (p : ℕ) :=
          Finset.Icc (η.leftExt t 0 p + 1) (w - η.rightExt t 0 p)
        let Q (S : Finset ℕ) := (S.product S).filter (fun z => z.1 ≤ z.2)
        let pairs (η : Context) := (active η).biUnion (fun p => Q (I η p))
        have hNe (p : ℕ) (hp : p ∈ ρ.childPositions) : p ≠ a := by
          intro heq
          subst p
          have hc := of_decide_eq_true (List.mem_filter.mp hp).2
          have he := (List.mem_filter.mp ha).2
          simp [hc] at he
        have hJOn : J' ∈ ρ.levelsOn s 0 :=
          List.mem_filter.mpr ⟨hJ', by simp [hJSide]⟩
        have hSmall : ∀ p ∈ ρ.childPositions,
            min (ρ.cupLimit p p) (ρ.capLimit p p) ≤ 3 := by
          intro p hp
          have hn := hNe p hp
          by_cases hpa : p < a
          · have he := hOneRight ρ s J' p a hJOn ha hpa
            cases s <;>
              simp only [cupLimit, capLimit, chainExt] at hglobalS ⊢ <;> omega
          · have he := hOneLeft ρ s J' p a hJOn ha (by omega)
            cases s <;>
              simp only [cupLimit, capLimit, chainExt] at hglobalS ⊢ <;> omega
        have hCover : ∀ p ∈ ρ.childPositions,
            color p ∈ ({0, 1} : Finset ℕ) := by
          intro p hp
          dsimp only [color]
          split_ifs <;> simp
        have hColor : ∀ p ∈ ρ.childPositions, ∀ q ∈ ρ.childPositions, p ≤ q →
            (∀ z, p ≤ z → z ≤ q → z ∈ ρ.childPositions) → color p = color q := by
          intro p hp q hq hpq hbetween
          have hside : (p < a) = (q < a) := by
            apply propext
            constructor
            · intro hpa
              by_contra hqa
              have hac := hbetween a (by omega) (by omega)
              exact hNe a hac rfl
            · omega
          simp only [color, hside]
        have hPosGroup (c : ℕ) : ∀ p j v,
            (group c).letterAt p = Letter.ext j v → 1 ≤ j :=
          (ctx_part_pruning_history_transport ρ hPos (support c) Side.lower 0).1
        have hChild (c p : ℕ) : p ∈ (group c).childPositions ↔
            p ∈ ρ.childPositions ∧ color p = c := by
          have hh : (group c).childPositions =
              ρ.childPositions.filter (· ∈ support c) :=
            (ctx_part_pruning_history_transport ρ hPos
              (support c) Side.lower 0).2.1
          rw [hh]
          simp [support]
        have hHist (c j : ℕ) (hj : j ∈ ρ.levels) :
            (group c).extPositions j = ρ.extPositions j ∧
              (group c).sideAt j = ρ.sideAt j :=
          (ctx_part_pruning_history_transport ρ hPos
            (support c) Side.lower 0).2.2.1 j hj
        have hLevels (c : ℕ) (v : Side) (top : ℕ) :
            (group c).levelsOn v top = ρ.levelsOn v top :=
          (ctx_part_pruning_history_transport ρ hPos
            (support c) Side.lower 0).2.2.2.1 v top
        have hA (c : ℕ) : a ∈ (group c).extPositions J' := by
          rw [(hHist c J' hJ').1]
          exact ha
        have hB (c : ℕ) : b ∈ (group c).extPositions N' := by
          rw [(hHist c N' hN').1]
          exact hb
        have hD (c : ℕ) : d ∈ (group c).extPositions M' := by
          rw [(hHist c M' hM').1]
          exact hd
        have hSide (c : ℕ) : (group c).sideAt J' = s :=
          (hHist c J' hJ').2.trans hJSide
        have hQ (c : ℕ) : q' ∈ (group c).extPositions L' := by
          rw [(hHist c L' hL').1]
          exact hq'
        have hQSide (c : ℕ) : (group c).sideAt L' = t :=
          (hHist c L' hL').2.trans hLSide
        have h0 (p : ℕ) (hp : p ∈ (group 0).childPositions) : p < a := by
          have hh := ((hChild 0 p).mp hp).2
          dsimp only [color] at hh
          split_ifs at hh <;> omega
        have h1 (p : ℕ) (hp : p ∈ (group 1).childPositions) : a < p := by
          have hh := ((hChild 1 p).mp hp).2
          have hn := hNe p ((hChild 1 p).mp hp).1
          dsimp only [color] at hh
          split_ifs at hh <;> omega
        have hPair (c : ℕ) (direction : Bool)
            (hboundary : ∀ p ∈ (group c).childPositions,
              if direction then p < a else a < p) :
            (group c).bound ≤ 9 := by
          have hSmallG : min ((match (group c).sideAt J' with
              | Side.lower => (group c).u | Side.upper => (group c).a) - 1)
              ((group c).k - (group c).maximumAt J') ≤ 4 := by
            rw [hSide c]
            change min ((match s with
              | Side.lower => ρ.u | Side.upper => ρ.a) - 1) _ ≤ 4
            omega
          have hh := ctx_active_boundary_marker_rank_pair_union_bound
            (group c) (hPosGroup c) J' a hJ' (hA c) direction
            (by intro p hp hact; exact hboundary p hp)
            (by
              intro j hj p hp
              rw [hSide c, hLevels c s J'] at hj
              rw [(hHist c j (List.mem_filter.mp hj).1).1, hyoung j hj] at hp
              exact False.elim (List.not_mem_nil hp))
            t (by rw [hSide c]; exact hne) hSmallG
          have hbound : (group c).bound ≤ (pairs (group c)).card := hh.2
          have hNine := ctx_actual_marker_rank_pair_union_nine_bound
            (group c) t L' q' hL' (hQSide c) (hQ c) hglobalT
          change (pairs (group c)).card ≤ 9 at hNine
          exact hbound.trans hNine
        have hUnit0 (hab : a < b) (hbd : b < d) : (group 0).bound ≤ 1 := by
          have hRank : ∀ p ∈ (group 0).childPositions,
              0 < (group 0).cupLimit p p → 0 < (group 0).capLimit p p →
              (group 0).leftExt s 0 p + 1 = 1 ∧
              1 + (group 0).rightExt s 0 p =
                (match (generalizing := false) s with
                  | Side.lower => (group 0).u - 1
                  | Side.upper => (group 0).a - 1) := by
            intro p hp hcup hcap
            have ht := (hTrip (group 0) J' N' M' a b d hJ' hN' hM'
              hJN' hNM' (hSide 0) ((hHist 0 N' hN').2.trans hNSide)
              ((hHist 0 M' hM').2.trans hMSide)
              (hA 0) (hB 0) (hD 0)).1 p (h0 p hp) hab hbd
            have hg : (match s with
              | Side.lower => (group 0).u | Side.upper => (group 0).a) ≤ 5 :=
              hglobalS
            cases s <;>
              simp only [cupLimit, capLimit, chainExt] at hg hcup hcap ⊢ <;> omega
          exact (ctx_bound_le_one_of_common_singleton_rank
            (group 0) (hPosGroup 0) s 1 hRank).2.1
        have hUnit1 (hdb : d < b) (hba : b < a) : (group 1).bound ≤ 1 := by
          have hRank : ∀ p ∈ (group 1).childPositions,
              0 < (group 1).cupLimit p p → 0 < (group 1).capLimit p p →
              (group 1).leftExt s 0 p + 1 = 4 ∧
              4 + (group 1).rightExt s 0 p =
                (match (generalizing := false) s with
                  | Side.lower => (group 1).u - 1
                  | Side.upper => (group 1).a - 1) := by
            intro p hp hcup hcap
            have ht := (hTrip (group 1) J' N' M' a b d hJ' hN' hM'
              hJN' hNM' (hSide 1) ((hHist 1 N' hN').2.trans hNSide)
              ((hHist 1 M' hM').2.trans hMSide)
              (hA 1) (hB 1) (hD 1)).2 p (h1 p hp) hba hdb
            have hg : (match s with
              | Side.lower => (group 1).u | Side.upper => (group 1).a) ≤ 5 :=
              hglobalS
            cases s <;>
              simp only [cupLimit, capLimit, chainExt] at hg hcup hcap ⊢ <;> omega
          exact (ctx_bound_le_one_of_common_singleton_rank
            (group 1) (hPosGroup 1) s 4 hRank).2.1
        have hSum : (group 0).bound + (group 1).bound ≤ 10 := by
          rcases horder with ⟨hab, hbd⟩ | ⟨hdb, hba⟩
          · have hleft := hUnit0 hab hbd
            have hright := hPair 1 false h1
            omega
          · have hleft := hPair 0 true h0
            have hright := hUnit1 hdb hba
            omega
        have hDecomp := ctx_bound_le_sum_run_group_prunings_capacity_three
          ρ hPos color ({0, 1} : Finset ℕ) hCover hSmall hColor
        change (∀ fuel, boundFuel fuel ρ ≤
            ({0, 1} : Finset ℕ).sum (fun c => (group c).bound)) ∧
          ρ.bound ≤ ({0, 1} : Finset ℕ).sum (fun c => (group c).bound) at hDecomp
        have hBudget : ({0, 1} : Finset ℕ).sum
            (fun c => (group c).bound) ≤ 10 := by
          simpa using hSum
        exact ⟨fun fuel => (hDecomp.1 fuel).trans hBudget,
          hDecomp.2.trans hBudget⟩
      have hBoundaryMaximumThree
          (K : List ℕ) (z : ℕ) (hzB : z ∈ B.childPositions) (hzNot : z ∉ K)
          (direction : Bool)
          (hBoundary : ∀ p ∈ K, if direction then p < z else z < p)
          (hqBoundary : (∀ p ∈ K, q₀ < p) ∨ (∀ p ∈ K, p < q₀)) :
          let C := B.part K s 3
          (∀ fuel, Ctx.Context.boundFuel fuel C ≤ 3) ∧ C.bound ≤ 3 := by
        let C := B.part K s 3
        change (∀ fuel, Ctx.Context.boundFuel fuel C ≤ 3) ∧ C.bound ≤ 3
        have hPosC := ctx_part_positive_letters B K s 3
        have hOneC : 1 ∈ C.levels := by
          simp only [C, Ctx.Context.part_levels, List.mem_cons, true_or]
        have hzC : z ∈ C.extPositions 1 := by
          change z ∈ (B.part K s 3).extPositions 1
          rw [Ctx.Context.part_extPositions_one hPosB]
          exact List.mem_filter.mpr ⟨hzB, by simpa⟩
        have hSideC : C.sideAt 1 = s :=
          Ctx.Context.part_sideAt_one_of_mem hPosB K s 3 hzC
        have hTwoC : 2 ∈ C.levels := by
          change 2 ∈ (B.part K s 3).levels
          rw [Ctx.Context.part_levels]
          exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨1, hOneB, by omega⟩)
        have hqC : q₀ ∈ C.extPositions 2 := by
          change q₀ ∈ (B.part K s 3).extPositions 2
          simpa only [show 2 = 1 + 1 by omega] using
            (show q₀ ∈ (B.part K s 3).extPositions (1 + 1) by
              rw [Ctx.Context.part_extPositions_succ B K s 3 (by omega)]
              exact hqB)
        have hSideTwoC : C.sideAt 2 = t := by
          change (B.part K s 3).sideAt 2 = t
          rw [show 2 = 1 + 1 by omega,
            Ctx.Context.part_sideAt_succ B K s 3 (by omega)]
          exact hSideB
        have hTwoOn : 2 ∈ C.levelsOn t 0 :=
          List.mem_filter.mpr ⟨hTwoC, by simp [hSideTwoC]⟩
        have hChildC (p : ℕ) (hp : p ∈ C.childPositions) : p ∈ K := by
          have hh : p ∈ B.childPositions ∧ p ∈ K := by
            simpa only [C, Ctx.Context.part_childPositions, List.mem_filter,
              decide_eq_true_eq] using hp
          exact hh.2
        have hChildren : ∀ p ∈ C.childPositions,
            if direction then p < z else z < p := by
          intro p hp
          exact hBoundary p (hChildC p hp)
        have hYounger : ∀ j ∈ C.levelsOn (C.sideAt 1) 1,
            ∀ p ∈ C.extPositions j, if direction then p < z else z < p := by
          simp only [Ctx.Context.levelsOn_one, List.not_mem_nil, false_implies,
            implies_true]
        have hSmall : min ((match C.sideAt 1 with
              | Ctx.Side.lower => C.u
              | Ctx.Side.upper => C.a) - 1)
              (C.k - C.maximumAt 1) ≤ 3 := by
          apply (Nat.min_le_right _ _).trans
          change (B.part K s 3).k - (B.part K s 3).maximumAt 1 ≤ 3
          rw [Ctx.Context.part_maximumAt_one]
          change σ.k - 3 ≤ 3
          omega
        have hOneLeft (p : ℕ) (hp : q₀ < p) : 1 ≤ C.leftExt t 0 p := by
          have hm : q₀ ∈ (C.extPositions 2).filter (· < p) := by simp [hqC, hp]
          have hnonempty := List.ne_nil_of_mem hm
          have hv := Ctx.le_getD_max?_of_mem
            (L := (C.levelsOn t 0).sublists.map
              (fun ls => (ls.foldl (Ctx.Context.leftStep C) (p, 0)).2))
            (List.mem_map.mpr ⟨[2],
              List.mem_sublists.mpr (List.singleton_sublist.mpr hTwoOn), rfl⟩)
          change _ ≤ C.leftExt t 0 p at hv
          simpa only [List.foldl_cons, List.foldl_nil, Ctx.Context.leftStep,
            List.getLast?_eq_some_getLast hnonempty] using hv
        have hOneRight (p : ℕ) (hp : p < q₀) : 1 ≤ C.rightExt t 0 p := by
          have hm : q₀ ∈ (C.extPositions 2).filter (p < ·) := by simp [hqC, hp]
          have hnonempty := List.ne_nil_of_mem hm
          have hv := Ctx.le_getD_max?_of_mem
            (L := (C.levelsOn t 0).sublists.map
              (fun ls => (ls.foldl (Ctx.Context.rightStep C) (p, 0)).2))
            (List.mem_map.mpr ⟨[2],
              List.mem_sublists.mpr (List.singleton_sublist.mpr hTwoOn), rfl⟩)
          change _ ≤ C.rightExt t 0 p at hv
          simpa only [List.foldl_cons, List.foldl_nil, Ctx.Context.rightStep,
            List.head?_eq_some_head hnonempty] using hv
        rcases hqBoundary with hqLeft | hqRight
        · have hh := ctx_boundary_marker_rank_budget_all_history C hPosC 1 z hOneC hzC
            direction hChildren hYounger t (by rw [hSideC]; exact hne)
            hSmall 1 0
            (fun p hp => hOneLeft p (hqLeft p (hChildC p hp)))
            (by intros; omega)
          have hcap : (match t with
                | Ctx.Side.lower => C.u
                | Ctx.Side.upper => C.a) - 1 - 1 - 0 ≤ 3 := by
            cases t <;> simp only [C, B, Ctx.Context.part] at hOppFive ⊢ <;> omega
          exact ⟨fun fuel => (hh.1 fuel).trans hcap, hh.2.trans hcap⟩
        · have hh := ctx_boundary_marker_rank_budget_all_history C hPosC 1 z hOneC hzC
            direction hChildren hYounger t (by rw [hSideC]; exact hne)
            hSmall 0 1 (by intros; omega)
            (fun p hp => hOneRight p (hqRight p (hChildC p hp)))
          have hcap : (match t with
                | Ctx.Side.lower => C.u
                | Ctx.Side.upper => C.a) - 1 - 0 - 1 ≤ 3 := by
            cases t <;> simp only [C, B, Ctx.Context.part] at hOppFive ⊢ <;> omega
          exact ⟨fun fuel => (hh.1 fuel).trans hcap, hh.2.trans hcap⟩
      have hBoundaryAnyMaximumNine
          (K : List ℕ) (z newMaximum : ℕ)
          (hzB : z ∈ B.childPositions) (hzNot : z ∉ K)
          (direction : Bool)
          (hBoundary : ∀ p ∈ K, if direction then p < z else z < p) :
          let C := B.part K s newMaximum
          (∀ fuel, Ctx.Context.boundFuel fuel C ≤ 9) ∧ C.bound ≤ 9 := by
        classical
        let C := B.part K s newMaximum
        let budget := (match t with
          | Ctx.Side.lower => C.u | Ctx.Side.upper => C.a) - 1
        let active := C.childPositions.toFinset.filter
          (fun p => 0 < C.cupLimit p p ∧ 0 < C.capLimit p p)
        let ranks := active.biUnion (fun p =>
          (let I := Finset.Icc (C.leftExt t 0 p + 1)
            (budget - C.rightExt t 0 p)
          (I.product I).filter (fun r => r.1 ≤ r.2)))
        change (∀ fuel, Ctx.Context.boundFuel fuel C ≤ 9) ∧ C.bound ≤ 9
        have hPosC := ctx_part_positive_letters B K s newMaximum
        have hOneC : 1 ∈ C.levels := by
          simp only [C, Ctx.Context.part_levels, List.mem_cons, true_or]
        have hzC : z ∈ C.extPositions 1 := by
          change z ∈ (B.part K s newMaximum).extPositions 1
          rw [Ctx.Context.part_extPositions_one hPosB]
          exact List.mem_filter.mpr ⟨hzB, by simpa⟩
        have hSideC : C.sideAt 1 = s :=
          Ctx.Context.part_sideAt_one_of_mem hPosB K s newMaximum hzC
        have hChildC (p : ℕ) (hp : p ∈ C.childPositions) : p ∈ K := by
          exact of_decide_eq_true
            (List.mem_filter.mp (show p ∈ B.childPositions.filter (· ∈ K) by
              simpa only [C, Ctx.Context.part_childPositions] using hp)).2
        have hSmall : min ((match C.sideAt 1 with
              | Ctx.Side.lower => C.u | Ctx.Side.upper => C.a) - 1)
              (C.k - C.maximumAt 1) ≤ 4 := by
          apply (Nat.min_le_left _ _).trans
          rw [hSideC]
          cases s <;> simp only [C, B, Ctx.Context.part] at hChosenFive ⊢ <;> omega
        have hPair := ctx_active_boundary_marker_rank_pair_union_bound
          C hPosC 1 z hOneC hzC direction
          (by
            intro p hp _
            exact hBoundary p (hChildC p hp))
          (by
            simp only [Ctx.Context.levelsOn_one, List.not_mem_nil,
              false_implies, implies_true])
          t (by rw [hSideC]; exact hne) hSmall
        change (∀ fuel, Ctx.Context.boundFuel fuel C ≤ ranks.card) ∧
          C.bound ≤ ranks.card at hPair
        have hTwoC : 2 ∈ C.levels := by
          change 2 ∈ (B.part K s newMaximum).levels
          rw [Ctx.Context.part_levels]
          exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨1, hOneB, by omega⟩)
        have hqC : q₀ ∈ C.extPositions 2 := by
          change q₀ ∈ (B.part K s newMaximum).extPositions 2
          simpa only [show 2 = 1 + 1 by omega] using
            (show q₀ ∈ (B.part K s newMaximum).extPositions (1 + 1) by
              rw [Ctx.Context.part_extPositions_succ B K s newMaximum (by omega)]
              exact hqB)
        have hSideTwoC : C.sideAt 2 = t := by
          change (B.part K s newMaximum).sideAt 2 = t
          rw [show 2 = 1 + 1 by omega,
            Ctx.Context.part_sideAt_succ B K s newMaximum (by omega)]
          exact hSideB
        have hGlobalC : (match t with
            | Ctx.Side.lower => C.u | Ctx.Side.upper => C.a) ≤ 5 := by
          simpa only [C, B, Ctx.Context.part] using le_of_eq hOppFive
        have hNine := ctx_actual_marker_rank_pair_union_nine_bound
          C t 2 q₀ hTwoC hSideTwoC hqC hGlobalC
        change ranks.card ≤ 9 at hNine
        exact ⟨fun fuel => (hPair.1 fuel).trans hNine,
          hPair.2.trans hNine⟩
      have hOppositeBoundaryMaximumTwoSix
          (K : List ℕ) (z : ℕ)
          (hzB : z ∈ B.childPositions) (hzNot : z ∉ K)
          (direction : Bool)
          (hBoundary : ∀ p ∈ K, if direction then p < z else z < p)
          (hqBoundary : (∀ p ∈ K, p < q₀) ∨ (∀ p ∈ K, q₀ < p)) :
          let C := B.part K s 2
          (∀ fuel, boundFuel fuel C ≤ 6) ∧ C.bound ≤ 6 := by
        classical
        let C := B.part K s 2
        let budget := (match t with
          | Side.lower => C.u | Side.upper => C.a) - 1
        let active := C.childPositions.toFinset.filter
          (fun p => 0 < C.cupLimit p p ∧ 0 < C.capLimit p p)
        let I (p : ℕ) := Finset.Icc (C.leftExt t 0 p + 1)
          (budget - C.rightExt t 0 p)
        let Q (T : Finset ℕ) := (T.product T).filter (fun r => r.1 ≤ r.2)
        let ranks := active.biUnion (fun p => Q (I p))
        change (∀ fuel, boundFuel fuel C ≤ 6) ∧ C.bound ≤ 6
        have hPosC := ctx_part_positive_letters B K s 2
        have hOneC : 1 ∈ C.levels := by
          simp only [C, Ctx.Context.part_levels, List.mem_cons, true_or]
        have hzC : z ∈ C.extPositions 1 := by
          change z ∈ (B.part K s 2).extPositions 1
          rw [Ctx.Context.part_extPositions_one hPosB]
          exact List.mem_filter.mpr ⟨hzB, by simpa⟩
        have hSideC : C.sideAt 1 = s :=
          Ctx.Context.part_sideAt_one_of_mem hPosB K s 2 hzC
        have hChildC (p : ℕ) (hp : p ∈ C.childPositions) : p ∈ K := by
          exact of_decide_eq_true
            (List.mem_filter.mp (show p ∈ B.childPositions.filter (· ∈ K) by
              simpa only [C, Ctx.Context.part_childPositions] using hp)).2
        have hSmall : min ((match C.sideAt 1 with
              | Side.lower => C.u | Side.upper => C.a) - 1)
              (C.k - C.maximumAt 1) ≤ 4 := by
          apply (Nat.min_le_left _ _).trans
          rw [hSideC]
          cases s <;> simp only [C, B, Ctx.Context.part] at hChosenFive ⊢ <;> omega
        have hh := ctx_active_boundary_marker_rank_pair_union_bound
          C hPosC 1 z hOneC hzC direction
          (by
            intro p hp _
            exact hBoundary p (hChildC p hp))
          (by
            simp only [Ctx.Context.levelsOn_one, List.not_mem_nil,
              false_implies, implies_true])
          t (by rw [hSideC]; exact hne) hSmall
        change (∀ fuel, boundFuel fuel C ≤ ranks.card) ∧
          C.bound ≤ ranks.card at hh
        have hTwoC : 2 ∈ C.levels := by
          change 2 ∈ (B.part K s 2).levels
          rw [Ctx.Context.part_levels]
          exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨1, hOneB, by omega⟩)
        have hqC : q₀ ∈ C.extPositions 2 := by
          change q₀ ∈ (B.part K s 2).extPositions 2
          simpa only [show 2 = 1 + 1 by omega] using
            (show q₀ ∈ (B.part K s 2).extPositions (1 + 1) by
              rw [Ctx.Context.part_extPositions_succ B K s 2 (by omega)]
              exact hqB)
        have hSideTwoC : C.sideAt 2 = t := by
          change (B.part K s 2).sideAt 2 = t
          rw [show 2 = 1 + 1 by omega,
            Ctx.Context.part_sideAt_succ B K s 2 (by omega)]
          exact hSideB
        have hTwoOn : 2 ∈ C.levelsOn t 0 :=
          List.mem_filter.mpr ⟨hTwoC, by simp [hSideTwoC]⟩
        have hOneLeft (p : ℕ) (hqp : q₀ < p) :
            1 ≤ C.leftExt t 0 p := by
          have hm : q₀ ∈ (C.extPositions 2).filter (· < p) := by
            simp [hqC, hqp]
          have hnonempty := List.ne_nil_of_mem hm
          have hv := le_getD_max?_of_mem
            (L := (C.levelsOn t 0).sublists.map
              (fun ls => (ls.foldl (leftStep C) (p, 0)).2))
            (List.mem_map.mpr ⟨[2],
              List.mem_sublists.mpr (List.singleton_sublist.mpr hTwoOn), rfl⟩)
          change _ ≤ C.leftExt t 0 p at hv
          simpa only [List.foldl_cons, List.foldl_nil, leftStep,
            List.getLast?_eq_some_getLast hnonempty] using hv
        have hOneRight (p : ℕ) (hpq : p < q₀) :
            1 ≤ C.rightExt t 0 p := by
          have hm : q₀ ∈ (C.extPositions 2).filter (p < ·) := by
            simp [hqC, hpq]
          have hnonempty := List.ne_nil_of_mem hm
          have hv := le_getD_max?_of_mem
            (L := (C.levelsOn t 0).sublists.map
              (fun ls => (ls.foldl (rightStep C) (p, 0)).2))
            (List.mem_map.mpr ⟨[2],
              List.mem_sublists.mpr (List.singleton_sublist.mpr hTwoOn), rfl⟩)
          change _ ≤ C.rightExt t 0 p at hv
          simpa only [List.foldl_cons, List.foldl_nil, rightStep,
            List.head?_eq_some_head hnonempty] using hv
        have hBudget : budget = 4 := by
          cases t <;>
            simp only [budget, C, B, Ctx.Context.part] at hOppFive ⊢ <;> omega
        rcases hqBoundary with hleft | hright
        · let T := Finset.Icc 1 3
          have hSub : ranks ⊆ Q T := by
            intro r hr
            obtain ⟨p, hp, hr⟩ := Finset.mem_biUnion.mp hr
            have hpChild : p ∈ C.childPositions :=
              List.mem_toFinset.mp (Finset.mem_filter.mp hp).1
            have hpq := hleft p (hChildC p hpChild)
            have hrightExt := hOneRight p hpq
            have hrData := Finset.mem_filter.mp hr
            have hcoords := Finset.mem_product.mp hrData.1
            apply Finset.mem_filter.mpr
            refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hrData.2⟩
            · exact Finset.mem_Icc.mpr ⟨by
                have := (Finset.mem_Icc.mp hcoords.1).1
                omega, by
                have := (Finset.mem_Icc.mp hcoords.1).2
                omega⟩
            · exact Finset.mem_Icc.mpr ⟨by
                have := (Finset.mem_Icc.mp hcoords.2).1
                omega, by
                have := (Finset.mem_Icc.mp hcoords.2).2
                omega⟩
          have hCard : (Q T).card ≤ 6 := by
            change ({r ∈ (Finset.Icc 1 3).product (Finset.Icc 1 3) |
              r.1 ≤ r.2} : Finset (ℕ × ℕ)).card ≤ 6
            decide
          have hrank : ranks.card ≤ 6 :=
            (Finset.card_le_card hSub).trans hCard
          exact ⟨fun fuel => (hh.1 fuel).trans hrank, hh.2.trans hrank⟩
        · let T := Finset.Icc 2 4
          have hSub : ranks ⊆ Q T := by
            intro r hr
            obtain ⟨p, hp, hr⟩ := Finset.mem_biUnion.mp hr
            have hpChild : p ∈ C.childPositions :=
              List.mem_toFinset.mp (Finset.mem_filter.mp hp).1
            have hqp := hright p (hChildC p hpChild)
            have hleftExt := hOneLeft p hqp
            have hrData := Finset.mem_filter.mp hr
            have hcoords := Finset.mem_product.mp hrData.1
            apply Finset.mem_filter.mpr
            refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hrData.2⟩
            · exact Finset.mem_Icc.mpr ⟨by
                have := (Finset.mem_Icc.mp hcoords.1).1
                omega, by
                have := (Finset.mem_Icc.mp hcoords.1).2
                omega⟩
            · exact Finset.mem_Icc.mpr ⟨by
                have := (Finset.mem_Icc.mp hcoords.2).1
                omega, by
                have := (Finset.mem_Icc.mp hcoords.2).2
                omega⟩
          have hCard : (Q T).card ≤ 6 := by
            change ({r ∈ (Finset.Icc 2 4).product (Finset.Icc 2 4) |
              r.1 ≤ r.2} : Finset (ℕ × ℕ)).card ≤ 6
            decide
          have hrank : ranks.card ≤ 6 :=
            (Finset.card_le_card hSub).trans hCard
          exact ⟨fun fuel => (hh.1 fuel).trans hrank, hh.2.trans hrank⟩
      have hPartLowBoundaryMaximumTwoSeven
          (K : List ℕ) (z : ℕ)
          (hzB : z ∈ B.childPositions) (hzNot : z ∉ K)
          (direction : Bool)
          (hBoundary : ∀ p ∈ K, if direction then p < z else z < p)
          (hLowPart : ∀ p ∈ (B.part K s 2).childPositions,
            0 < (B.part K s 2).cupLimit p p →
            0 < (B.part K s 2).capLimit p p →
            (match s with
              | Side.lower => (B.part K s 2).cupLimit p p
              | Side.upper => (B.part K s 2).capLimit p p) ≤ 2) :
          let C := B.part K s 2
          (∀ fuel, boundFuel fuel C ≤ 7) ∧ C.bound ≤ 7 := by
        classical
        let C := B.part K s 2
        change (∀ fuel, boundFuel fuel C ≤ 7) ∧ C.bound ≤ 7
        have hPosC := ctx_part_positive_letters B K s 2
        have hOneC : 1 ∈ C.levels := by
          simp only [C, Ctx.Context.part_levels, List.mem_cons, true_or]
        have hzC : z ∈ C.extPositions 1 := by
          change z ∈ (B.part K s 2).extPositions 1
          rw [Ctx.Context.part_extPositions_one hPosB]
          exact List.mem_filter.mpr ⟨hzB, by simpa⟩
        have hSideC : C.sideAt 1 = s :=
          Ctx.Context.part_sideAt_one_of_mem hPosB K s 2 hzC
        have hOneOn : 1 ∈ C.levelsOn s 0 :=
          List.mem_filter.mpr ⟨hOneC, by simp [hSideC]⟩
        have hChildC (p : ℕ) (hp : p ∈ C.childPositions) : p ∈ K := by
          exact of_decide_eq_true
            (List.mem_filter.mp (show p ∈ B.childPositions.filter (· ∈ K) by
              simpa only [C, Ctx.Context.part_childPositions] using hp)).2
        have hMaxB : ∀ j ∈ B.levelsOn s 0, B.maximumAt j ≤ 1 := by
          have hs : B.sideAt 1 ≠ s := by
            rw [hSideB]
            exact Ne.symm hne
          intro j hj
          rw [Ctx.Context.part_levelsOn_other_zero hs] at hj
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
          rw [Ctx.Context.part_maximumAt_succ σ rest t n
            (Ctx.Context.one_le_of_mem_levels (List.mem_filter.mp hi).1)]
          exact hmax i hi
        have hMaxC (j : ℕ) (hj : j ∈ C.levelsOn s 0) (hjNe : j ≠ 1) :
            C.maximumAt j ≤ 1 := by
          rw [Ctx.Context.part_levelsOn_self_zero hSideC] at hj
          rcases List.mem_cons.mp hj with hj | hj
          · exact False.elim (hjNe hj)
          · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
            rw [Ctx.Context.part_maximumAt_succ B K s 2
              (Ctx.Context.one_le_of_mem_levelsOn hi).1]
            exact hMaxB i hi
        have hJoinSmall (p : ℕ) (hchain : C.chainExt s p p ≤ 1) :
            C.joinExt s p p ≤ 2 := by
          unfold Ctx.Context.joinExt
          apply max_le
          · omega
          · apply getD_max?_le
            intro value hvalue
            obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hvalue
            by_cases hjOne : j = 1
            · subst j
              rw [Ctx.Context.leftExt_one, Ctx.Context.rightExt_one,
                Ctx.Context.part_maximumAt_one]
            · have hext := ctx_extensions_le_zero_cutoff C s j p
              have hm := hMaxC j hj hjOne
              simp only [Ctx.Context.chainExt] at hchain
              omega
        have hGlobalC : (match s with
            | Side.lower => C.u | Side.upper => C.a) = 5 := by
          simpa only [C, B, Ctx.Context.part] using hChosenFive
        have hOppGlobalC : (match t with
            | Side.lower => C.u | Side.upper => C.a) = 5 := by
          simpa only [C, B, Ctx.Context.part] using hOppFive
        have hKC : C.k = 6 := by
          simpa only [C, B, Ctx.Context.part] using hk
        have hThin : ∀ p ∈ C.childPositions,
            0 < C.cupLimit p p → 0 < C.capLimit p p →
            (match s with | Side.lower => C.u | Side.upper => C.a) - 1 -
                C.rightExt s 0 p ≤ C.leftExt s 0 p + 2 := by
          intro p hp hcup hcap
          have hlow := hLowPart p (by simpa only [C] using hp)
            (by simpa only [C] using hcup) (by simpa only [C] using hcap)
          change (match s with
            | Side.lower => C.cupLimit p p
            | Side.upper => C.capLimit p p) ≤ 2 at hlow
          have hchain : 2 ≤ C.chainExt s p p := by
            by_contra hbad
            have hj := hJoinSmall p (by omega)
            cases s with
            | lower =>
                simp only [cupLimit] at hlow
                simp only at hGlobalC
                omega
            | upper =>
                simp only [capLimit] at hlow
                simp only at hGlobalC
                omega
          simp only [Ctx.Context.chainExt] at hchain
          cases s <;> simp only at hGlobalC ⊢ <;> omega
        have hThinDep : ∀ p ∈ C.childPositions,
            0 < C.cupLimit p p → 0 < C.capLimit p p →
            (match s, hne with
              | Side.lower, _ => C.u
              | Side.upper, _ => C.a) - 1 -
                C.rightExt s 0 p ≤ C.leftExt s 0 p + 2 := by
          cases s <;> simpa only using hThin
        have hOneLeft (p : ℕ) (hzp : z < p) : 1 ≤ C.leftExt s 0 p := by
          have hm : z ∈ (C.extPositions 1).filter (· < p) := by simp [hzC, hzp]
          have hnonempty := List.ne_nil_of_mem hm
          have hv := le_getD_max?_of_mem
            (L := (C.levelsOn s 0).sublists.map
              (fun ls => (ls.foldl (leftStep C) (p, 0)).2))
            (List.mem_map.mpr ⟨[1],
              List.mem_sublists.mpr (List.singleton_sublist.mpr hOneOn), rfl⟩)
          change _ ≤ C.leftExt s 0 p at hv
          simpa only [List.foldl_cons, List.foldl_nil, leftStep,
            List.getLast?_eq_some_getLast hnonempty] using hv
        have hOneRight (p : ℕ) (hpz : p < z) : 1 ≤ C.rightExt s 0 p := by
          have hm : z ∈ (C.extPositions 1).filter (p < ·) := by simp [hzC, hpz]
          have hnonempty := List.ne_nil_of_mem hm
          have hv := le_getD_max?_of_mem
            (L := (C.levelsOn s 0).sublists.map
              (fun ls => (ls.foldl (rightStep C) (p, 0)).2))
            (List.mem_map.mpr ⟨[1],
              List.mem_sublists.mpr (List.singleton_sublist.mpr hOneOn), rfl⟩)
          change _ ≤ C.rightExt s 0 p at hv
          simpa only [List.foldl_cons, List.foldl_nil, rightStep,
            List.head?_eq_some_head hnonempty] using hv
        cases hd : direction
        · have hh := ctx_thin_rank_windows_linear_potential
              C hPosC s t hne 2 1 3 4 hThinDep
              (by
                intro p hp hcup hcap
                have hzp := hBoundary p (hChildC p hp)
                simp only [hd, if_false] at hzp
                have hl := hOneLeft p hzp
                constructor
                · omega
                · cases s <;> simp only at hGlobalC ⊢ <;> omega)
              (by
                intro p hp hcup hcap
                constructor
                · omega
                · cases t <;> simp only at hOppGlobalC ⊢ <;> omega)
          simpa using hh
        · have hh := ctx_thin_rank_windows_linear_potential
              C hPosC s t hne 1 1 3 4 hThinDep
              (by
                intro p hp hcup hcap
                have hpz := hBoundary p (hChildC p hp)
                simp only [hd, if_true] at hpz
                have hr := hOneRight p hpz
                constructor
                · omega
                · cases s <;> simp only at hGlobalC ⊢ <;> omega)
              (by
                intro p hp hcup hcap
                constructor
                · omega
                · cases t <;> simp only at hOppGlobalC ⊢ <;> omega)
          simpa using hh
      have hFarComplementMaximumThreeTwo
          (K : List ℕ) (z : ℕ)
          (hzB : z ∈ B.childPositions) (hzNot : z ∉ K)
          (direction : Bool)
          (hBoundary : ∀ p ∈ K, if direction then p < z else z < p)
          (hFar : (x < y ∧ ∀ p ∈ K, p < x) ∨
            (y < x ∧ ∀ p ∈ K, x < p)) :
          let D := B.part K t 3
          (∀ fuel, boundFuel fuel D ≤ 2) ∧ D.bound ≤ 2 := by
        let D := B.part K t 3
        change (∀ fuel, boundFuel fuel D ≤ 2) ∧ D.bound ≤ 2
        have hPosD := ctx_part_positive_letters B K t 3
        have hOneD : 1 ∈ D.levels := by
          simp only [D, Ctx.Context.part_levels, List.mem_cons, true_or]
        have hzD : z ∈ D.extPositions 1 := by
          change z ∈ (B.part K t 3).extPositions 1
          rw [Ctx.Context.part_extPositions_one hPosB]
          exact List.mem_filter.mpr ⟨hzB, by simpa⟩
        have hSideD : D.sideAt 1 = t :=
          Ctx.Context.part_sideAt_one_of_mem hPosB K t 3 hzD
        have hChildD (p : ℕ) (hp : p ∈ D.childPositions) : p ∈ K := by
          exact of_decide_eq_true
            (List.mem_filter.mp (show p ∈ B.childPositions.filter (· ∈ K) by
              simpa only [D, Ctx.Context.part_childPositions] using hp)).2
        have hChildren : ∀ p ∈ D.childPositions,
            if direction then p < z else z < p := by
          intro p hp
          exact hBoundary p (hChildD p hp)
        have hYounger : ∀ j ∈ D.levelsOn (D.sideAt 1) 1,
            ∀ p ∈ D.extPositions j, if direction then p < z else z < p := by
          simp only [Ctx.Context.levelsOn_one, List.not_mem_nil,
            false_implies, implies_true]
        have hSmall : min ((match D.sideAt 1 with
              | Side.lower => D.u | Side.upper => D.a) - 1)
              (D.k - D.maximumAt 1) ≤ 3 := by
          apply (Nat.min_le_right _ _).trans
          change (B.part K t 3).k - (B.part K t 3).maximumAt 1 ≤ 3
          rw [Ctx.Context.part_maximumAt_one]
          change σ.k - 3 ≤ 3
          omega
        have hND : N + 2 ∈ D.levels := by
          change N + 2 ∈ (B.part K t 3).levels
          rw [Ctx.Context.part_levels]
          exact List.mem_cons_of_mem _
            (List.mem_map.mpr ⟨N + 1, hNB, by omega⟩)
        have hMD : M + 2 ∈ D.levels := by
          change M + 2 ∈ (B.part K t 3).levels
          rw [Ctx.Context.part_levels]
          exact List.mem_cons_of_mem _
            (List.mem_map.mpr ⟨M + 1, hMB, by omega⟩)
        have hSideND : D.sideAt (N + 2) = s := by
          change (B.part K t 3).sideAt (N + 2) = s
          rw [show N + 2 = (N + 1) + 1 by omega,
            Ctx.Context.part_sideAt_succ B K t 3
              (Ctx.Context.one_le_of_mem_levels hNB)]
          exact hNsB
        have hSideMD : D.sideAt (M + 2) = s := by
          change (B.part K t 3).sideAt (M + 2) = s
          rw [show M + 2 = (M + 1) + 1 by omega,
            Ctx.Context.part_sideAt_succ B K t 3
              (Ctx.Context.one_le_of_mem_levels hMB)]
          exact hMsB
        have hxD : x ∈ D.extPositions (N + 2) := by
          change x ∈ (B.part K t 3).extPositions (N + 2)
          rw [show N + 2 = (N + 1) + 1 by omega,
            Ctx.Context.part_extPositions_succ B K t 3
              (Ctx.Context.one_le_of_mem_levels hNB)]
          exact hxB
        have hyD : y ∈ D.extPositions (M + 2) := by
          change y ∈ (B.part K t 3).extPositions (M + 2)
          rw [show M + 2 = (M + 1) + 1 by omega,
            Ctx.Context.part_extPositions_succ B K t 3
              (Ctx.Context.one_le_of_mem_levels hMB)]
          exact hyB
        have hNOn : N + 2 ∈ D.levelsOn s 0 :=
          List.mem_filter.mpr ⟨hND, by simp [hSideND]⟩
        have hMOn : M + 2 ∈ D.levelsOn s 0 :=
          List.mem_filter.mpr ⟨hMD, by simp [hSideMD]⟩
        have hSorted : (D.levelsOn s 0).Pairwise (· < ·) := by
          apply List.Pairwise.filter
          exact List.pairwise_lt_range.map (fun i => i + 1)
            (fun i j hij => Nat.add_lt_add_right hij 1)
        have hTwo : [N + 2, M + 2].Sublist (D.levelsOn s 0) := by
          have hs : [N + 2, M + 2].Pairwise (· < ·) := by simp; omega
          have hsub : [N + 2, M + 2] ⊆ D.levelsOn s 0 := by
            intro j hj
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
            rcases hj with rfl | rfl
            · exact hNOn
            · exact hMOn
          have heq : (D.levelsOn s 0).filter
              (· ∈ [N + 2, M + 2]) = [N + 2, M + 2] := by
            apply (hSorted.filter _).eq_of_mem_iff hs
            intro j
            simp only [List.mem_filter, decide_eq_true_eq]
            exact ⟨And.right, fun hj => ⟨hsub hj, hj⟩⟩
          rw [← heq]
          exact List.filter_sublist
        have hSort (j : ℕ) : (D.extPositions j).Pairwise (· ≤ ·) :=
          (List.pairwise_lt_range.filter _).imp le_of_lt
        rcases hFar with ⟨hxy, hKLeft⟩ | ⟨hyx, hKRight⟩
        · have hRightTwo : ∀ p ∈ D.childPositions, 2 ≤ D.rightExt s 0 p := by
            intro p hp
            have hpx := hKLeft p (hChildD p hp)
            have hmx : x ∈ (D.extPositions (N + 2)).filter (p < ·) := by
              simp [hxD, hpx]
            have hnex := List.ne_nil_of_mem hmx
            let x' := ((D.extPositions (N + 2)).filter (p < ·)).head hnex
            have hx' : ((D.extPositions (N + 2)).filter (p < ·)).head? = some x' :=
              List.head?_eq_some_head hnex
            have hx'le : x' ≤ x := ((hSort (N + 2)).filter _).rel_head hmx
            have hmy : y ∈ (D.extPositions (M + 2)).filter (x' < ·) := by
              simp [hyD]
              omega
            have hney := List.ne_nil_of_mem hmy
            have hh := le_getD_max?_of_mem
              (L := (D.levelsOn s 0).sublists.map
                (fun ls => (ls.foldl (rightStep D) (p, 0)).2))
              (List.mem_map.mpr ⟨[N + 2, M + 2],
                List.mem_sublists.mpr hTwo, rfl⟩)
            change _ ≤ D.rightExt s 0 p at hh
            simpa only [List.foldl_cons, List.foldl_nil, rightStep, hx',
              List.head?_eq_some_head hney] using hh
          have hh := ctx_boundary_marker_rank_budget_all_history
            D hPosD 1 z hOneD hzD direction hChildren hYounger s
            (by rw [hSideD]; exact Ne.symm hne) hSmall 0 2
            (by intros; omega) hRightTwo
          have hcap : (match s with
                | Side.lower => D.u | Side.upper => D.a) - 1 - 0 - 2 ≤ 2 := by
            cases s <;>
              simp only [D, B, Ctx.Context.part] at hChosenFive ⊢ <;> omega
          exact ⟨fun fuel => (hh.1 fuel).trans hcap, hh.2.trans hcap⟩
        · have hLeftTwo : ∀ p ∈ D.childPositions, 2 ≤ D.leftExt s 0 p := by
            intro p hp
            have hxp := hKRight p (hChildD p hp)
            have hmx : x ∈ (D.extPositions (N + 2)).filter (· < p) := by
              simp [hxD, hxp]
            have hnex := List.ne_nil_of_mem hmx
            let x' := ((D.extPositions (N + 2)).filter (· < p)).getLast hnex
            have hx' : ((D.extPositions (N + 2)).filter (· < p)).getLast? = some x' :=
              List.getLast?_eq_some_getLast hnex
            have hxle : x ≤ x' := ((hSort (N + 2)).filter _).rel_getLast hmx
            have hmy : y ∈ (D.extPositions (M + 2)).filter (· < x') := by
              simp [hyD]
              omega
            have hney := List.ne_nil_of_mem hmy
            have hh := le_getD_max?_of_mem
              (L := (D.levelsOn s 0).sublists.map
                (fun ls => (ls.foldl (leftStep D) (p, 0)).2))
              (List.mem_map.mpr ⟨[N + 2, M + 2],
                List.mem_sublists.mpr hTwo, rfl⟩)
            change _ ≤ D.leftExt s 0 p at hh
            simpa only [List.foldl_cons, List.foldl_nil, leftStep, hx',
              List.getLast?_eq_some_getLast hney] using hh
          have hh := ctx_boundary_marker_rank_budget_all_history
            D hPosD 1 z hOneD hzD direction hChildren hYounger s
            (by rw [hSideD]; exact Ne.symm hne) hSmall 2 0 hLeftTwo
            (by intros; omega)
          have hcap : (match s with
                | Side.lower => D.u | Side.upper => D.a) - 1 - 2 - 0 ≤ 2 := by
            cases s <;>
              simp only [D, B, Ctx.Context.part] at hChosenFive ⊢ <;> omega
          exact ⟨fun fuel => (hh.1 fuel).trans hcap, hh.2.trans hcap⟩
      have hOlderExteriorMaximumThreeThree
          (K : List ℕ) (z : ℕ)
          (hzB : z ∈ B.childPositions) (hzNot : z ∉ K)
          (direction : Bool)
          (hBoundary : ∀ p ∈ K, if direction then p < z else z < p)
          (hOlder : (x < y ∧ ∀ p ∈ K, y < p) ∨
            (y < x ∧ ∀ p ∈ K, p < y)) :
          let D := B.part K t 3
          (∀ fuel, boundFuel fuel D ≤ 3) ∧ D.bound ≤ 3 := by
        let D := B.part K t 3
        change (∀ fuel, boundFuel fuel D ≤ 3) ∧ D.bound ≤ 3
        have hPosD := ctx_part_positive_letters B K t 3
        have hOneD : 1 ∈ D.levels := by
          simp only [D, Ctx.Context.part_levels, List.mem_cons, true_or]
        have hzD : z ∈ D.extPositions 1 := by
          change z ∈ (B.part K t 3).extPositions 1
          rw [Ctx.Context.part_extPositions_one hPosB]
          exact List.mem_filter.mpr ⟨hzB, by simpa⟩
        have hSideD : D.sideAt 1 = t :=
          Ctx.Context.part_sideAt_one_of_mem hPosB K t 3 hzD
        have hChildD (p : ℕ) (hp : p ∈ D.childPositions) : p ∈ K := by
          exact of_decide_eq_true
            (List.mem_filter.mp (show p ∈ B.childPositions.filter (· ∈ K) by
              simpa only [D, Ctx.Context.part_childPositions] using hp)).2
        have hChildren : ∀ p ∈ D.childPositions,
            if direction then p < z else z < p := by
          intro p hp
          exact hBoundary p (hChildD p hp)
        have hYounger : ∀ j ∈ D.levelsOn (D.sideAt 1) 1,
            ∀ p ∈ D.extPositions j, if direction then p < z else z < p := by
          simp only [Ctx.Context.levelsOn_one, List.not_mem_nil,
            false_implies, implies_true]
        have hSmall : min ((match D.sideAt 1 with
              | Side.lower => D.u | Side.upper => D.a) - 1)
              (D.k - D.maximumAt 1) ≤ 3 := by
          apply (Nat.min_le_right _ _).trans
          change (B.part K t 3).k - (B.part K t 3).maximumAt 1 ≤ 3
          rw [Ctx.Context.part_maximumAt_one]
          change σ.k - 3 ≤ 3
          omega
        have hMD : M + 2 ∈ D.levels := by
          change M + 2 ∈ (B.part K t 3).levels
          rw [Ctx.Context.part_levels]
          exact List.mem_cons_of_mem _
            (List.mem_map.mpr ⟨M + 1, hMB, by omega⟩)
        have hSideMD : D.sideAt (M + 2) = s := by
          change (B.part K t 3).sideAt (M + 2) = s
          rw [show M + 2 = (M + 1) + 1 by omega,
            Ctx.Context.part_sideAt_succ B K t 3
              (Ctx.Context.one_le_of_mem_levels hMB)]
          exact hMsB
        have hyD : y ∈ D.extPositions (M + 2) := by
          change y ∈ (B.part K t 3).extPositions (M + 2)
          rw [show M + 2 = (M + 1) + 1 by omega,
            Ctx.Context.part_extPositions_succ B K t 3
              (Ctx.Context.one_le_of_mem_levels hMB)]
          exact hyB
        have hMOn : M + 2 ∈ D.levelsOn s 0 :=
          List.mem_filter.mpr ⟨hMD, by simp [hSideMD]⟩
        have hOneLeft (p : ℕ) (hyp : y < p) : 1 ≤ D.leftExt s 0 p := by
          have hm : y ∈ (D.extPositions (M + 2)).filter (· < p) := by
            simp [hyD, hyp]
          have hnonempty := List.ne_nil_of_mem hm
          have hv := le_getD_max?_of_mem
            (L := (D.levelsOn s 0).sublists.map
              (fun ls => (ls.foldl (leftStep D) (p, 0)).2))
            (List.mem_map.mpr ⟨[M + 2],
              List.mem_sublists.mpr (List.singleton_sublist.mpr hMOn), rfl⟩)
          change _ ≤ D.leftExt s 0 p at hv
          simpa only [List.foldl_cons, List.foldl_nil, leftStep,
            List.getLast?_eq_some_getLast hnonempty] using hv
        have hOneRight (p : ℕ) (hpy : p < y) : 1 ≤ D.rightExt s 0 p := by
          have hm : y ∈ (D.extPositions (M + 2)).filter (p < ·) := by
            simp [hyD, hpy]
          have hnonempty := List.ne_nil_of_mem hm
          have hv := le_getD_max?_of_mem
            (L := (D.levelsOn s 0).sublists.map
              (fun ls => (ls.foldl (rightStep D) (p, 0)).2))
            (List.mem_map.mpr ⟨[M + 2],
              List.mem_sublists.mpr (List.singleton_sublist.mpr hMOn), rfl⟩)
          change _ ≤ D.rightExt s 0 p at hv
          simpa only [List.foldl_cons, List.foldl_nil, rightStep,
            List.head?_eq_some_head hnonempty] using hv
        rcases hOlder with ⟨_, hRight⟩ | ⟨_, hLeft⟩
        · have hh := ctx_boundary_marker_rank_budget_all_history
              D hPosD 1 z hOneD hzD direction hChildren hYounger s
              (by rw [hSideD]; exact Ne.symm hne) hSmall 1 0
              (by intro p hp; exact hOneLeft p (hRight p (hChildD p hp)))
              (by intros; omega)
          have hcap : (match s with
                | Side.lower => D.u | Side.upper => D.a) - 1 - 1 - 0 ≤ 3 := by
            cases s <;>
              simp only [D, B, Ctx.Context.part] at hChosenFive ⊢ <;> omega
          exact ⟨fun fuel => (hh.1 fuel).trans hcap, hh.2.trans hcap⟩
        · have hh := ctx_boundary_marker_rank_budget_all_history
              D hPosD 1 z hOneD hzD direction hChildren hYounger s
              (by rw [hSideD]; exact Ne.symm hne) hSmall 0 1
              (by intros; omega)
              (by intro p hp; exact hOneRight p (hLeft p (hChildD p hp)))
          have hcap : (match s with
                | Side.lower => D.u | Side.upper => D.a) - 1 - 0 - 1 ≤ 3 := by
            cases s <;>
              simp only [D, B, Ctx.Context.part] at hChosenFive ⊢ <;> omega
          exact ⟨fun fuel => (hh.1 fuel).trans hcap, hh.2.trans hcap⟩
      have hTwoBoundaryMaximumTwoFour
          (K : List ℕ) (a b : ℕ)
          (haB : a ∈ B.childPositions) (hbB : b ∈ B.childPositions)
          (haNot : a ∉ K) (hbNot : b ∉ K)
          (hbetween : ∀ p ∈ K, a < p ∧ p < b) :
          let D := B.part K t 2
          (∀ fuel, boundFuel fuel D ≤ 4) ∧ D.bound ≤ 4 := by
        classical
        let D := B.part K t 2
        let budget := (match s with | Side.lower => D.u | Side.upper => D.a) - 1
        let active := D.childPositions.toFinset.filter
          (fun p => 0 < D.cupLimit p p ∧ 0 < D.capLimit p p)
        let ranks := active.biUnion (fun p =>
          Finset.Icc (D.leftExt s 0 p + 1) (budget - D.rightExt s 0 p))
        change (∀ fuel, boundFuel fuel D ≤ 4) ∧ D.bound ≤ 4
        have hPosD := ctx_part_positive_letters B K t 2
        have hOneD : 1 ∈ D.levels := by
          simp only [D, Ctx.Context.part_levels, List.mem_cons, true_or]
        have haD : a ∈ D.extPositions 1 := by
          change a ∈ (B.part K t 2).extPositions 1
          rw [Ctx.Context.part_extPositions_one hPosB]
          exact List.mem_filter.mpr ⟨haB, by simpa⟩
        have hbD : b ∈ D.extPositions 1 := by
          change b ∈ (B.part K t 2).extPositions 1
          rw [Ctx.Context.part_extPositions_one hPosB]
          exact List.mem_filter.mpr ⟨hbB, by simpa⟩
        have hSideD : D.sideAt 1 = t :=
          Ctx.Context.part_sideAt_one_of_mem hPosB K t 2 haD
        have hChildD (p : ℕ) (hp : p ∈ D.childPositions) : p ∈ K := by
          exact of_decide_eq_true
            (List.mem_filter.mp (show p ∈ B.childPositions.filter (· ∈ K) by
              simpa only [D, Ctx.Context.part_childPositions] using hp)).2
        have hChildren : ∀ p ∈ D.childPositions,
            0 < D.cupLimit p p ∧ 0 < D.capLimit p p → a < p ∧ p < b := by
          intro p hp _
          exact hbetween p (hChildD p hp)
        have hYounger : ∀ j ∈ D.levelsOn (D.sideAt 1) 1,
            ∀ p ∈ D.extPositions j, a < p ∧ p < b := by
          simp only [Ctx.Context.levelsOn_one, List.not_mem_nil, false_implies,
            implies_true]
        have hSmall : min ((match D.sideAt 1 with
              | Side.lower => D.u | Side.upper => D.a) - 2)
              (D.k - D.maximumAt 1) ≤ 3 := by
          rw [hSideD]
          apply (Nat.min_le_left _ _).trans
          cases t <;> simp only [D, B, Ctx.Context.part] at hOppFive ⊢ <;> omega
        have hh := ctx_active_two_boundary_marker_rank_union_bound
          D hPosD 1 a b hOneD haD hbD hChildren hYounger s
          (by rw [hSideD]; exact Ne.symm hne) hSmall
        change (∀ fuel, boundFuel fuel D ≤ ranks.card) ∧
          D.bound ≤ ranks.card at hh
        have hSub : ranks ⊆ Finset.Icc 1 4 := by
          intro z hz
          obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
          have hzRange := Finset.mem_Icc.mp hz
          have hBudget : budget = 4 := by
            cases s <;>
              simp only [budget, D, B, Ctx.Context.part] at hChosenFive ⊢ <;> omega
          exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        have hCard : ranks.card ≤ 4 := by
          have hh := Finset.card_le_card hSub
          simpa using hh
        exact ⟨fun fuel => (hh.1 fuel).trans hCard, hh.2.trans hCard⟩
      have hTwoBoundaryChosenMaximumTwoFour
          (K : List ℕ) (a b : ℕ)
          (haB : a ∈ B.childPositions) (hbB : b ∈ B.childPositions)
          (haNot : a ∉ K) (hbNot : b ∉ K)
          (hbetween : ∀ p ∈ K, a < p ∧ p < b) :
          let C := B.part K s 2
          (∀ fuel, boundFuel fuel C ≤ 4) ∧ C.bound ≤ 4 := by
        classical
        let C := B.part K s 2
        let budget := (match t with | Side.lower => C.u | Side.upper => C.a) - 1
        let active := C.childPositions.toFinset.filter
          (fun p => 0 < C.cupLimit p p ∧ 0 < C.capLimit p p)
        let ranks := active.biUnion (fun p =>
          Finset.Icc (C.leftExt t 0 p + 1) (budget - C.rightExt t 0 p))
        change (∀ fuel, boundFuel fuel C ≤ 4) ∧ C.bound ≤ 4
        have hPosC := ctx_part_positive_letters B K s 2
        have hOneC : 1 ∈ C.levels := by
          simp only [C, Ctx.Context.part_levels, List.mem_cons, true_or]
        have haC : a ∈ C.extPositions 1 := by
          change a ∈ (B.part K s 2).extPositions 1
          rw [Ctx.Context.part_extPositions_one hPosB]
          exact List.mem_filter.mpr ⟨haB, by simpa⟩
        have hbC : b ∈ C.extPositions 1 := by
          change b ∈ (B.part K s 2).extPositions 1
          rw [Ctx.Context.part_extPositions_one hPosB]
          exact List.mem_filter.mpr ⟨hbB, by simpa⟩
        have hSideC : C.sideAt 1 = s :=
          Ctx.Context.part_sideAt_one_of_mem hPosB K s 2 haC
        have hChildC (p : ℕ) (hp : p ∈ C.childPositions) : p ∈ K := by
          exact of_decide_eq_true
            (List.mem_filter.mp (show p ∈ B.childPositions.filter (· ∈ K) by
              simpa only [C, Ctx.Context.part_childPositions] using hp)).2
        have hChildren : ∀ p ∈ C.childPositions,
            0 < C.cupLimit p p ∧ 0 < C.capLimit p p → a < p ∧ p < b := by
          intro p hp _
          exact hbetween p (hChildC p hp)
        have hYounger : ∀ j ∈ C.levelsOn (C.sideAt 1) 1,
            ∀ p ∈ C.extPositions j, a < p ∧ p < b := by
          simp only [Ctx.Context.levelsOn_one, List.not_mem_nil,
            false_implies, implies_true]
        have hSmall : min ((match C.sideAt 1 with
              | Side.lower => C.u | Side.upper => C.a) - 2)
              (C.k - C.maximumAt 1) ≤ 3 := by
          rw [hSideC]
          apply (Nat.min_le_left _ _).trans
          cases s <;> simp only [C, B, Ctx.Context.part] at hChosenFive ⊢ <;> omega
        have hh := ctx_active_two_boundary_marker_rank_union_bound
          C hPosC 1 a b hOneC haC hbC hChildren hYounger t
          (by rw [hSideC]; exact hne) hSmall
        change (∀ fuel, boundFuel fuel C ≤ ranks.card) ∧
          C.bound ≤ ranks.card at hh
        have hSub : ranks ⊆ Finset.Icc 1 4 := by
          intro r hr
          obtain ⟨p, hp, hr⟩ := Finset.mem_biUnion.mp hr
          have hrRange := Finset.mem_Icc.mp hr
          have hBudget : budget = 4 := by
            cases t <;>
              simp only [budget, C, B, Ctx.Context.part] at hOppFive ⊢ <;> omega
          exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        have hCard : ranks.card ≤ 4 := by
          have hh := Finset.card_le_card hSub
          simpa using hh
        exact ⟨fun fuel => (hh.1 fuel).trans hCard, hh.2.trans hCard⟩
      have hNestedBoundaryRankBudgetAllHistory
          (ρ : Context)
          (hPos : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j)
          (N' J' outerPos innerPos : ℕ)
          (hN' : N' ∈ ρ.levels) (hJ' : J' ∈ ρ.levels) (hJN' : J' < N')
          (hOuterPos : outerPos ∈ ρ.extPositions N')
          (hInnerPos : innerPos ∈ ρ.extPositions J')
          (hSameSide : ρ.sideAt J' = ρ.sideAt N')
          (outer inner : Bool)
          (hOuterChildren : ∀ p ∈ ρ.childPositions,
            if outer then p < outerPos else outerPos < p)
          (hOuterYoung : ∀ j ∈ ρ.levelsOn (ρ.sideAt N') N',
            ∀ p ∈ ρ.extPositions j,
              if outer then p < outerPos else outerPos < p)
          (hInnerChildren : ∀ p ∈ ρ.childPositions,
            if inner then p < innerPos else innerPos < p)
          (hInnerYoung : ∀ j ∈ ρ.levelsOn (ρ.sideAt J') J',
            ∀ p ∈ ρ.extPositions j,
              if inner then p < innerPos else innerPos < p)
          (v : Side) (hne' : ρ.sideAt N' ≠ v)
          (hMarkerGlobal : (match ρ.sideAt N' with
            | Side.lower => ρ.u | Side.upper => ρ.a) ≤ 5)
          (leftLoss rightLoss : ℕ)
          (hLeftLoss : ∀ p ∈ ρ.childPositions,
            leftLoss ≤ ρ.leftExt v 0 p)
          (hRightLoss : ∀ p ∈ ρ.childPositions,
            rightLoss ≤ ρ.rightExt v 0 p) :
          let budget := (match (generalizing := false) v with
            | Side.lower => ρ.u | Side.upper => ρ.a) - 1 - leftLoss - rightLoss
          (∀ fuel, boundFuel fuel ρ ≤ budget) ∧ ρ.bound ≤ budget := by
        classical
        let idx (D L j : ℕ) := if j = L then D else if L < j then j - 1 else j
        let letter (D L : ℕ) : Letter → Letter := fun z => match z with
          | Letter.child => Letter.child
          | Letter.ext j w => Letter.ext (idx D L j) w
        let erase (η : Context) (L : ℕ) : Context :=
          { η with word := η.word.map (letter η.maxima.length L), maxima := η.maxima.eraseIdx (L - 1) }
        let up (L j : ℕ) := if j < L then j else j + 1
        have hLevelMem (η : Context) (j : ℕ) :
            j ∈ η.levels ↔ 1 ≤ j ∧ j ≤ η.maxima.length := by
          simp only [levels, List.mem_map, List.mem_range]
          constructor
          · rintro ⟨i, hi, rfl⟩
            omega
          · intro hj
            exact ⟨j - 1, by omega, by omega⟩
        have hSorted (η : Context) : η.levels.Pairwise (· < ·) := by
          unfold levels
          exact List.pairwise_lt_range.map (fun z => z + 1)
            (fun a b hab => Nat.add_lt_add_right hab 1)
        have hLen (η : Context) (L : ℕ) :
            (erase η L).word.length = η.word.length := by
          simp only [erase, List.length_map]
        have hLetter (η : Context) (L p : ℕ) :
            (erase η L).letterAt p = letter η.maxima.length L (η.letterAt p) := by
          simp only [erase, letterAt, List.getElem?_map]
          cases η.word[p]? <;> rfl
        have hIsChild (η : Context) (L p : ℕ) :
            (erase η L).letterAt p = Letter.child ↔
              η.letterAt p = Letter.child := by
          rw [hLetter]
          cases η.letterAt p <;> simp [letter]
        have hChild (η : Context) (L : ℕ) :
            (erase η L).childPositions = η.childPositions := by
          simp only [childPositions, hLen, hIsChild]
        have hDepth (η : Context) (L : ℕ) (hL : L ∈ η.levels) :
            (erase η L).maxima.length = η.maxima.length - 1 := by
          have hh := (hLevelMem η L).mp hL
          exact List.length_eraseIdx_of_lt (by omega)
        have hLive (η : Context) (L j : ℕ) (hL : L ∈ η.levels)
            (hj : j ∈ (erase η L).levels) :
            1 ≤ j ∧ j < η.maxima.length ∧ up L j ∈ η.levels := by
          have hh := (hLevelMem η L).mp hL
          have hj' := (hLevelMem (erase η L) j).mp hj
          rw [hDepth η L hL] at hj'
          refine ⟨hj'.1, by omega, ?_⟩
          apply (hLevelMem η _).mpr
          dsimp [up]
          split_ifs <;> omega
        have hIndex (D L i j : ℕ) (hL : 1 ≤ L) (hLD : L ≤ D)
            (hj : 1 ≤ j) (hjD : j < D) :
            idx D L i = j ↔ i = up L j := by
          dsimp [idx, up]
          split_ifs <;> omega
        have hExt (η : Context) (L j : ℕ) (hL : L ∈ η.levels)
            (hj : j ∈ (erase η L).levels) :
            (erase η L).extPositions j = η.extPositions (up L j) := by
          have hLj := (hLevelMem η L).mp hL
          have hj' := hLive η L j hL hj
          simp only [extPositions, hLen, hLetter]
          apply List.filter_congr
          intro p _
          cases η.letterAt p with
          | child => rfl
          | ext i w =>
              simp only [letter, hIndex _ _ i j hLj.1 hLj.2 hj'.1 hj'.2.1]
        have hSide (η : Context) (L j : ℕ) (hL : L ∈ η.levels)
            (hj : j ∈ (erase η L).levels) :
            (erase η L).sideAt j = η.sideAt (up L j) := by
          simp only [sideAt, hExt η L j hL hj]
          cases hh : (η.extPositions (up L j)).head? with
          | none => rfl
          | some p =>
              dsimp only
              rw [hLetter]
              cases η.letterAt p <;> rfl
        have hMaximum (η : Context) (L j : ℕ) (hL : L ∈ η.levels)
            (hj : j ∈ (erase η L).levels) :
            (erase η L).maximumAt j = η.maximumAt (up L j) := by
          have hh := (hLevelMem η L).mp hL
          have hj' := (hLive η L j hL hj).1
          simp only [maximumAt, erase, List.getElem?_eraseIdx]
          by_cases h : j < L
          · simp [up, h, show j - 1 < L - 1 by omega]
          · simp [up, h, show ¬j - 1 < L - 1 by omega,
                show j - 1 + 1 = j by omega]
        have hUpMono (L i j : ℕ) (hij : i < j) : up L i < up L j := by
          dsimp [up]
          split_ifs <;> omega
        have hUpZero (L : ℕ) (hL : 1 ≤ L) : up L 0 = 0 := by
          simp [up, show 0 < L by omega]
        have hSub (η : Context) (L : ℕ) (hL : L ∈ η.levels)
            (w : Side) (top : ℕ) :
            (((erase η L).levelsOn w top).map (up L)).Sublist
              (η.levelsOn w (up L top)) := by
          have hs : (((erase η L).levelsOn w top).map (up L)).Pairwise (· < ·) :=
            ((hSorted (erase η L)).filter _).map (up L)
              (fun i j hij => hUpMono L i j hij)
          have ho : (η.levelsOn w (up L top)).Pairwise (· < ·) :=
            (hSorted η).filter _
          have hsubset : (((erase η L).levelsOn w top).map (up L)) ⊆
              η.levelsOn w (up L top) := by
            intro z hz
            obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hz
            have hjl := (List.mem_filter.mp hj).1
            have hjc : (erase η L).sideAt j = w ∧ (top = 0 ∨ j < top) :=
              of_decide_eq_true (List.mem_filter.mp hj).2
            apply List.mem_filter.mpr
            refine ⟨(hLive η L j hL hjl).2.2, ?_⟩
            apply decide_eq_true
            refine ⟨?_, ?_⟩
            · rw [← hSide η L j hL hjl]
              exact hjc.1
            · rcases hjc.2 with rfl | hlt
              · exact Or.inl (hUpZero L (one_le_of_mem_levels hL))
              · exact Or.inr (hUpMono L j top hlt)
          have he : (η.levelsOn w (up L top)).filter
              (· ∈ (((erase η L).levelsOn w top).map (up L))) =
              (((erase η L).levelsOn w top).map (up L)) := by
            apply (ho.filter _).eq_of_mem_iff hs
            intro z
            simp only [List.mem_filter, decide_eq_true_eq]
            exact ⟨And.right, fun hz => ⟨hsubset hz, hz⟩⟩
          rw [← he]
          exact List.filter_sublist
        have hFoldLeft (η : Context) (L : ℕ) (hL : L ∈ η.levels) :
            ∀ (ls : List ℕ), (∀ j ∈ ls, j ∈ (erase η L).levels) → ∀ z,
            ls.foldl (leftStep (erase η L)) z =
              (ls.map (up L)).foldl (leftStep η) z := by
          intro ls
          induction ls with
          | nil => intro _ z; rfl
          | cons j ls ih =>
              intro hj z
              simp only [List.foldl_cons, List.map_cons, leftStep,
                hExt η L j hL (hj j (by simp))]
              exact ih (fun i hi => hj i (by simp [hi])) _
        have hFoldRight (η : Context) (L : ℕ) (hL : L ∈ η.levels) :
            ∀ (ls : List ℕ), (∀ j ∈ ls, j ∈ (erase η L).levels) → ∀ z,
            ls.foldl (rightStep (erase η L)) z =
              (ls.map (up L)).foldl (rightStep η) z := by
          intro ls
          induction ls with
          | nil => intro _ z; rfl
          | cons j ls ih =>
              intro hj z
              simp only [List.foldl_cons, List.map_cons, rightStep,
                hExt η L j hL (hj j (by simp))]
              exact ih (fun i hi => hj i (by simp [hi])) _
        have hOppLevels (η : Context) (L : ℕ) (hL : L ∈ η.levels)
            (w : Side) (hneq : η.sideAt L ≠ w) :
            ((erase η L).levelsOn w 0).map (up L) = η.levelsOn w 0 := by
          have hs : (((erase η L).levelsOn w 0).map (up L)).Pairwise (· < ·) :=
            ((hSorted (erase η L)).filter _).map (up L)
              (fun i j hij => hUpMono L i j hij)
          apply hs.eq_of_mem_iff ((hSorted η).filter _)
          intro i
          constructor
          · intro hi
            obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
            have hjl := (List.mem_filter.mp hj).1
            have hjc : (erase η L).sideAt j = w ∧ (0 = 0 ∨ j < 0) :=
              of_decide_eq_true (List.mem_filter.mp hj).2
            apply List.mem_filter.mpr
            refine ⟨(hLive η L j hL hjl).2.2, ?_⟩
            rw [hSide η L j hL hjl] at hjc
            apply decide_eq_true
            exact ⟨hjc.1, Or.inl rfl⟩
          · intro hi
            have hil := (hLevelMem η i).mp (List.mem_filter.mp hi).1
            have hic : η.sideAt i = w ∧ (0 = 0 ∨ i < 0) :=
              of_decide_eq_true (List.mem_filter.mp hi).2
            have hiL : i ≠ L := by
              intro h
              subst i
              exact hneq hic.1
            have hLL := (hLevelMem η L).mp hL
            let j := if i < L then i else i - 1
            have hup : up L j = i := by
              dsimp [up, j]
              split_ifs <;> omega
            have hjl : j ∈ (erase η L).levels := by
              apply (hLevelMem (erase η L) j).mpr
              rw [hDepth η L hL]
              dsimp [j]
              split_ifs <;> omega
            apply List.mem_map.mpr
            refine ⟨j, ?_, hup⟩
            apply List.mem_filter.mpr
            refine ⟨hjl, ?_⟩
            apply decide_eq_true
            rw [hSide η L j hL hjl, hup]
            exact ⟨hic.1, Or.inl rfl⟩
        have hEraseLeft (η : Context) (L : ℕ) (hL : L ∈ η.levels)
            (w : Side) (hneq : η.sideAt L ≠ w) (p : ℕ) :
            (erase η L).leftExt w 0 p = η.leftExt w 0 p := by
          rw [leftExt_eq, leftExt_eq, ← hOppLevels η L hL w hneq,
            List.sublists_map, List.map_map]
          apply congrArg (fun vals : List ℕ => vals.max?.getD 0)
          apply List.map_congr_left
          intro ls hls
          have hl : ∀ j ∈ ls, j ∈ (erase η L).levels :=
            fun j hj => (List.mem_filter.mp
              ((List.mem_sublists.mp hls).subset hj)).1
          exact congrArg Prod.snd (hFoldLeft η L hL ls hl (p, 0))
        have hEraseRight (η : Context) (L : ℕ) (hL : L ∈ η.levels)
            (w : Side) (hneq : η.sideAt L ≠ w) (p : ℕ) :
            (erase η L).rightExt w 0 p = η.rightExt w 0 p := by
          rw [rightExt_eq, rightExt_eq, ← hOppLevels η L hL w hneq,
            List.sublists_map, List.map_map]
          apply congrArg (fun vals : List ℕ => vals.max?.getD 0)
          apply List.map_congr_left
          intro ls hls
          have hl : ∀ j ∈ ls, j ∈ (erase η L).levels :=
            fun j hj => (List.mem_filter.mp
              ((List.mem_sublists.mp hls).subset hj)).1
          exact congrArg Prod.snd (hFoldRight η L hL ls hl (p, 0))
        have hErasePositive (η : Context) (L : ℕ) (hL : L ∈ η.levels)
            (hPositive : ∀ p j w, η.letterAt p = Letter.ext j w → 1 ≤ j) :
            ∀ p j w, (erase η L).letterAt p = Letter.ext j w → 1 ≤ j := by
          intro p j w hp
          rw [hLetter] at hp
          have hL1 := one_le_of_mem_levels hL
          have hDepthPos : 1 ≤ η.maxima.length := by
            have h := (hLevelMem η L).mp hL
            omega
          cases he : η.letterAt p with
          | child =>
              simp only [he, letter] at hp
              cases hp
          | ext i z =>
              have hi := hPositive p i z he
              simp only [he, letter] at hp
              have hij := (Letter.ext.inj hp).1
              dsimp only [idx] at hij
              split_ifs at hij <;> omega
        have hAll : ∀ D (η : Context), η.maxima.length = D →
            (∀ p j w, η.letterAt p = Letter.ext j w → 1 ≤ j) →
            ∀ (N J x y : ℕ), N ∈ η.levels → J ∈ η.levels → J < N →
            x ∈ η.extPositions N → y ∈ η.extPositions J →
            η.sideAt J = η.sideAt N →
            ∀ (outer inner : Bool),
            (∀ p ∈ η.childPositions, if outer then p < x else x < p) →
            (∀ j ∈ η.levelsOn (η.sideAt N) N, ∀ p ∈ η.extPositions j,
              if outer then p < x else x < p) →
            (∀ p ∈ η.childPositions, if inner then p < y else y < p) →
            (∀ j ∈ η.levelsOn (η.sideAt J) J, ∀ p ∈ η.extPositions j,
              if inner then p < y else y < p) →
            (match η.sideAt N with | Side.lower => η.u | Side.upper => η.a) ≤ 5 →
            ∀ w : Side, η.sideAt N ≠ w →
            ∀ A R : ℕ, (∀ p ∈ η.childPositions, A ≤ η.leftExt w 0 p) →
            (∀ p ∈ η.childPositions, R ≤ η.rightExt w 0 p) →
            ∀ fuel, boundFuel fuel η ≤
              (match w with | Side.lower => η.u | Side.upper => η.a) - 1 - A - R := by
          intro D
          induction D using Nat.strong_induction_on with
          | h D ih =>
              intro η hD hPositive N J x y hN hJ hJN hx hy hSides outer inner
                hc hoYoung hi hiYoung hglobal
              by_cases hterminal :
                  ∀ j ∈ η.levelsOn (η.sideAt N) 0, j ≤ N
              · let τ : Context := match η.sideAt N with
                  | Side.lower =>
                      { erase η N with
                        u := min (η.u - 1) (η.k - η.maximumAt N) }
                  | Side.upper =>
                      { erase η N with
                        a := min (η.a - 1) (η.k - η.maximumAt N) }
                have hτWord : τ.word = (erase η N).word := by
                  cases hs : η.sideAt N <;> simp only [τ, hs]
                have hτMaxima : τ.maxima = (erase η N).maxima := by
                  cases hs : η.sideAt N <;> simp only [τ, hs]
                have hτLetter (p : ℕ) : τ.letterAt p = (erase η N).letterAt p := by
                  simp only [letterAt, hτWord]
                have hτLevels : τ.levels = (erase η N).levels := by
                  simp only [levels, hτMaxima]
                have hτExt (j : ℕ) :
                    τ.extPositions j = (erase η N).extPositions j := by
                  simp only [extPositions, hτWord, hτLetter]
                have hτSide (j : ℕ) :
                    τ.sideAt j = (erase η N).sideAt j := by
                  simp only [sideAt, hτExt, hτLetter]
                have hτLevelsOn (z : Side) (top : ℕ) :
                    τ.levelsOn z top = (erase η N).levelsOn z top := by
                  simp only [levelsOn, hτLevels, hτSide]
                have hτMaximum (j : ℕ) :
                    τ.maximumAt j = (erase η N).maximumAt j := by
                  simp only [maximumAt, hτMaxima]
                have hτChild : τ.childPositions = (erase η N).childPositions := by
                  simp only [childPositions, hτWord, hτLetter]
                have hτLeft (z : Side) (top p : ℕ) :
                    τ.leftExt z top p = (erase η N).leftExt z top p := by
                  simp only [leftExt, hτLevelsOn, hτExt]
                have hτRight (z : Side) (top p : ℕ) :
                    τ.rightExt z top p = (erase η N).rightExt z top p := by
                  simp only [rightExt, hτLevelsOn, hτExt]
                have hOppGlobalAll : ∀ z : Side, η.sideAt N ≠ z →
                    (match z with | Side.lower => τ.u | Side.upper => τ.a) =
                    (match z with | Side.lower => η.u | Side.upper => η.a) := by
                  intro z hneZ
                  refine Side.rec (motive := fun w => η.sideAt N ≠ w →
                      (match w with | Side.lower => τ.u | Side.upper => τ.a) =
                      (match w with | Side.lower => η.u | Side.upper => η.a))
                    ?_ ?_ z hneZ
                  · intro hneLower
                    have hs : η.sideAt N = Side.upper :=
                      Side.rec (motive := fun w => w ≠ Side.lower → w = Side.upper)
                        (fun h => False.elim (h rfl)) (fun _ => rfl)
                        (η.sideAt N) hneLower
                    simp only [τ, hs, erase]
                  · intro hneUpper
                    have hs : η.sideAt N = Side.lower :=
                      Side.rec (motive := fun w => w ≠ Side.upper → w = Side.lower)
                        (fun _ => rfl) (fun h => False.elim (h rfl))
                        (η.sideAt N) hneUpper
                    simp only [τ, hs, erase]
                intro w hneq A R hLeft hRight
                have hNorm := ctx_boundary_marker_erase_normalize η hPositive N x hN hx
                  outer hc hoYoung hterminal
                have hFuel : ∀ fuel, boundFuel fuel η ≤ boundFuel fuel τ := by
                  simpa only [τ] using hNorm.2.1
                have hFull : η.bound ≤ τ.bound := by
                  simpa only [τ] using hNorm.2.2
                have hNMem := (hLevelMem η N).mp hN
                have hJτ : J ∈ τ.levels := by
                  rw [hτLevels]
                  apply (hLevelMem (erase η N) J).mpr
                  rw [hDepth η N hN]
                  have hNUpper := hNMem.2
                  have hJLower := (hLevelMem η J).mp hJ |>.1
                  omega
                have hupJ : up N J = J := by simp only [up, if_pos hJN]
                have hSideJτ : τ.sideAt J = η.sideAt J := by
                  rw [hτSide, hSide η N J hN (by simpa only [hτLevels] using hJτ), hupJ]
                have hMaxJτ : τ.maximumAt J = η.maximumAt J := by
                  rw [hτMaximum,
                    hMaximum η N J hN (by simpa only [hτLevels] using hJτ), hupJ]
                have hyτ : y ∈ τ.extPositions J := by
                  rw [hτExt,
                    hExt η N J hN (by simpa only [hτLevels] using hJτ), hupJ]
                  exact hy
                have hChildτ : τ.childPositions = η.childPositions := by
                  rw [hτChild]
                  exact hChild η N
                have hPosτ : ∀ p j z,
                    τ.letterAt p = Letter.ext j z → 1 ≤ j := by
                  intro p j z hp
                  rw [hτLetter] at hp
                  exact hErasePositive η N hN hPositive p j z hp
                have hiτ : ∀ p ∈ τ.childPositions,
                    if inner then p < y else y < p := by
                  simpa only [hChildτ] using hi
                have hiYoungτ : ∀ j ∈ τ.levelsOn (τ.sideAt J) J,
                    ∀ p ∈ τ.extPositions j,
                      if inner then p < y else y < p := by
                  intro j hj p hp
                  have hj' : j ∈ (erase η N).levelsOn (η.sideAt J) J := by
                    rw [← hτLevelsOn, ← hSideJτ]
                    exact hj
                  have hjl : j ∈ (erase η N).levels := (List.mem_filter.mp hj').1
                  have hm := (hSub η N hN (η.sideAt J) J).subset
                    (List.mem_map.mpr ⟨j, hj', rfl⟩)
                  rw [hupJ] at hm
                  have hpOld : p ∈ η.extPositions (up N j) := by
                    rw [hτExt, hExt η N j hN hjl] at hp
                    exact hp
                  exact hiYoung (up N j) hm p hpOld
                have hneqτ : τ.sideAt J ≠ w := by
                  rw [hSideJτ, hSides]
                  exact hneq
                have hChosenτ : (match τ.sideAt J with
                    | Side.lower => τ.u | Side.upper => τ.a) ≤ 4 := by
                  rw [hSideJτ, hSides]
                  cases hs : η.sideAt N <;>
                    simp only [τ, hs] at hglobal ⊢
                  all_goals
                    exact (Nat.min_le_left _ _).trans (by omega)
                have hSmallτ : min ((match τ.sideAt J with
                    | Side.lower => τ.u | Side.upper => τ.a) - 1)
                    (τ.k - τ.maximumAt J) ≤ 3 := by
                  apply (Nat.min_le_left _ _).trans
                  omega
                have hLeftτ : ∀ p ∈ τ.childPositions,
                    A ≤ τ.leftExt w 0 p := by
                  intro p hp
                  have hpOld : p ∈ η.childPositions := by simpa only [hChildτ] using hp
                  have hOpp : η.sideAt N ≠ w := hneq
                  rw [hτLeft, hEraseLeft η N hN w hOpp p]
                  exact hLeft p hpOld
                have hRightτ : ∀ p ∈ τ.childPositions,
                    R ≤ τ.rightExt w 0 p := by
                  intro p hp
                  have hpOld : p ∈ η.childPositions := by simpa only [hChildτ] using hp
                  have hOpp : η.sideAt N ≠ w := hneq
                  rw [hτRight, hEraseRight η N hN w hOpp p]
                  exact hRight p hpOld
                have hBudget := ctx_boundary_marker_rank_budget_all_history τ hPosτ
                  J y hJτ hyτ inner hiτ hiYoungτ w hneqτ hSmallτ A R
                  hLeftτ hRightτ
                have hOppGlobal := hOppGlobalAll w hneq
                intro fuel
                exact (hFuel fuel).trans (by
                  have hb := hBudget.1 fuel
                  exact Eq.mp (congrArg
                    (fun z => boundFuel fuel τ ≤ z - 1 - A - R) hOppGlobal) hb)
              · push Not at hterminal
                intro w hneq A R hLeft hRight
                obtain ⟨L, hLOn, hNL⟩ := hterminal
                have hL : L ∈ η.levels := (List.mem_filter.mp hLOn).1
                have hLSide : η.sideAt L = η.sideAt N :=
                  (of_decide_eq_true (List.mem_filter.mp hLOn).2).1
                have hLOpposite : η.sideAt L ≠ w := by
                  simpa only [hLSide] using hneq
                let τ := erase η L
                have hNMem := (hLevelMem η N).mp hN
                have hLMem := (hLevelMem η L).mp hL
                have hNτ : N ∈ τ.levels := by
                  apply (hLevelMem τ N).mpr
                  change 1 ≤ N ∧ N ≤ (erase η L).maxima.length
                  rw [hDepth η L hL]
                  omega
                have hJτ : J ∈ τ.levels := by
                  apply (hLevelMem τ J).mpr
                  change 1 ≤ J ∧ J ≤ (erase η L).maxima.length
                  rw [hDepth η L hL]
                  have hNUpper := hNMem.2
                  have hLUpper := hLMem.2
                  have hJLower := (hLevelMem η J).mp hJ |>.1
                  omega
                have hupN : up L N = N := by simp only [up, if_pos hNL]
                have hupJ : up L J = J := by
                  simp only [up, if_pos (lt_trans hJN hNL)]
                have hSideNτ : τ.sideAt N = η.sideAt N := by
                  rw [hSide η L N hL hNτ, hupN]
                have hSideJτ : τ.sideAt J = η.sideAt J := by
                  rw [hSide η L J hL hJτ, hupJ]
                have hxτ : x ∈ τ.extPositions N := by
                  rw [hExt η L N hL hNτ, hupN]
                  exact hx
                have hyτ : y ∈ τ.extPositions J := by
                  rw [hExt η L J hL hJτ, hupJ]
                  exact hy
                have hChildτ : τ.childPositions = η.childPositions := hChild η L
                have hcτ : ∀ p ∈ τ.childPositions,
                    if outer then p < x else x < p := by
                  simpa only [hChildτ] using hc
                have hiτ : ∀ p ∈ τ.childPositions,
                    if inner then p < y else y < p := by
                  simpa only [hChildτ] using hi
                have hoYoungτ : ∀ j ∈ τ.levelsOn (τ.sideAt N) N,
                    ∀ p ∈ τ.extPositions j,
                      if outer then p < x else x < p := by
                  intro j hj p hp
                  have hj' : j ∈ τ.levelsOn (η.sideAt N) N := by
                    simpa only [hSideNτ] using hj
                  have hjl : j ∈ τ.levels := (List.mem_filter.mp hj').1
                  have hm := (hSub η L hL (η.sideAt N) N).subset
                    (List.mem_map.mpr ⟨j, hj', rfl⟩)
                  rw [hupN] at hm
                  have hpOld : p ∈ η.extPositions (up L j) := by
                    simpa only [τ, hExt η L j hL hjl] using hp
                  exact hoYoung (up L j) hm p hpOld
                have hiYoungτ : ∀ j ∈ τ.levelsOn (τ.sideAt J) J,
                    ∀ p ∈ τ.extPositions j,
                      if inner then p < y else y < p := by
                  intro j hj p hp
                  have hj' : j ∈ τ.levelsOn (η.sideAt J) J := by
                    simpa only [hSideJτ] using hj
                  have hjl : j ∈ τ.levels := (List.mem_filter.mp hj').1
                  have hm := (hSub η L hL (η.sideAt J) J).subset
                    (List.mem_map.mpr ⟨j, hj', rfl⟩)
                  rw [hupJ] at hm
                  have hpOld : p ∈ η.extPositions (up L j) := by
                    simpa only [τ, hExt η L j hL hjl] using hp
                  exact hiYoung (up L j) hm p hpOld
                have hneqτ : τ.sideAt N ≠ w := by simpa only [hSideNτ] using hneq
                have hGlobalτ : (match τ.sideAt N with
                    | Side.lower => τ.u | Side.upper => τ.a) ≤ 5 := by
                  simpa only [hSideNτ] using hglobal
                have hLeftτ : ∀ p ∈ τ.childPositions,
                    A ≤ τ.leftExt w 0 p := by
                  intro p hp
                  have hpOld : p ∈ η.childPositions := by simpa only [hChildτ] using hp
                  simpa only [τ, hEraseLeft η L hL w hLOpposite p] using hLeft p hpOld
                have hRightτ : ∀ p ∈ τ.childPositions,
                    R ≤ τ.rightExt w 0 p := by
                  intro p hp
                  have hpOld : p ∈ η.childPositions := by simpa only [hChildτ] using hp
                  simpa only [τ, hEraseRight η L hL w hLOpposite p] using hRight p hpOld
                have hDepthLt : τ.maxima.length < D := by
                  change (erase η L).maxima.length < D
                  rw [hDepth η L hL, hD]
                  rw [hD] at hLMem
                  omega
                have hRec := ih τ.maxima.length hDepthLt τ rfl
                  (hErasePositive η L hL hPositive) N J x y hNτ hJτ hJN hxτ hyτ
                  (hSideJτ.trans (hSides.trans hSideNτ.symm)) outer inner hcτ
                  hoYoungτ hiτ hiYoungτ hGlobalτ w hneqτ A R hLeftτ hRightτ
                have hMono := (ctx_erase_level_bound_mono η L hL).2.1
                intro fuel
                exact (hMono fuel).trans (hRec fuel)
        have h := hAll ρ.maxima.length ρ rfl hPos N' J' outerPos innerPos
          hN' hJ' hJN' hOuterPos hInnerPos hSameSide outer inner
          hOuterChildren hOuterYoung hInnerChildren hInnerYoung hMarkerGlobal
          v hne' leftLoss rightLoss hLeftLoss hRightLoss
        exact ⟨h, by simpa only [bound] using h (ρ.childPositions.length + 1)⟩
      have hStraddlingCompanionSeven
          (newMaximum : ℕ) (K : List ℕ) (a b : ℕ)
          (haK : a ∈ K) (hbK : b ∈ K)
          (haB : a ∈ B.childPositions) (hbB : b ∈ B.childPositions)
          (haq : a < q₀) (hqb : q₀ < b)
          (hOutside : ∀ p ∈ B.childPositions, p ∉ K → p < a ∨ b < p) :
          let R := B.childPositions.filter (· ∉ K)
          let D := B.part R t newMaximum
          (∀ fuel, boundFuel fuel D ≤ 7) ∧ D.bound ≤ 7 := by
        classical
        let R := B.childPositions.filter (· ∉ K)
        let D := B.part R t newMaximum
        let color (p : ℕ) := if p < a then (0 : ℕ) else 1
        let support (c : ℕ) := D.childPositions.filter (fun p => color p = c)
        let group (c : ℕ) : Context := { D with
          word := (List.range D.word.length).map (fun p => match D.letterAt p with
            | Letter.child => if p ∈ support c then Letter.child
                else Letter.ext (D.maxima.length + 1) Side.lower
            | Letter.ext j v => Letter.ext j v) }
        change (∀ fuel, boundFuel fuel D ≤ 7) ∧ D.bound ≤ 7
        have hPosD := ctx_part_positive_letters B R t newMaximum
        have hOneD : 1 ∈ D.levels := by
          simp only [D, Ctx.Context.part_levels, List.mem_cons, true_or]
        have hTwoD : 2 ∈ D.levels := by
          change 2 ∈ (B.part R t newMaximum).levels
          rw [Ctx.Context.part_levels]
          exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨1, hOneB, by omega⟩)
        have haD : a ∈ D.extPositions 1 := by
          change a ∈ (B.part R t newMaximum).extPositions 1
          rw [Ctx.Context.part_extPositions_one hPosB]
          exact List.mem_filter.mpr ⟨haB, by simp [R, haK]⟩
        have hbD : b ∈ D.extPositions 1 := by
          change b ∈ (B.part R t newMaximum).extPositions 1
          rw [Ctx.Context.part_extPositions_one hPosB]
          exact List.mem_filter.mpr ⟨hbB, by simp [R, hbK]⟩
        have hSideOneD : D.sideAt 1 = t :=
          Ctx.Context.part_sideAt_one_of_mem hPosB R t newMaximum haD
        have hqD : q₀ ∈ D.extPositions 2 := by
          change q₀ ∈ (B.part R t newMaximum).extPositions 2
          simpa only [show 2 = 1 + 1 by omega] using
            (show q₀ ∈ (B.part R t newMaximum).extPositions (1 + 1) by
              rw [Ctx.Context.part_extPositions_succ B R t newMaximum (by omega)]
              exact hqB)
        have hSideTwoD : D.sideAt 2 = t := by
          change (B.part R t newMaximum).sideAt 2 = t
          rw [show 2 = 1 + 1 by omega,
            Ctx.Context.part_sideAt_succ B R t newMaximum (by omega)]
          exact hSideB
        have hM2D : M + 2 ∈ D.levels := by
          change M + 2 ∈ (B.part R t newMaximum).levels
          rw [Ctx.Context.part_levels]
          exact List.mem_cons_of_mem _
            (List.mem_map.mpr ⟨M + 1, hMB, by omega⟩)
        have hyD : y ∈ D.extPositions (M + 2) := by
          change y ∈ (B.part R t newMaximum).extPositions (M + 2)
          simpa only [show M + 2 = (M + 1) + 1 by omega] using
            (show y ∈ (B.part R t newMaximum).extPositions ((M + 1) + 1) by
              rw [Ctx.Context.part_extPositions_succ B R t newMaximum
                (Ctx.Context.one_le_of_mem_levels hMB)]
              exact hyB)
        have hSideM2D : D.sideAt (M + 2) = s := by
          change (B.part R t newMaximum).sideAt (M + 2) = s
          rw [show M + 2 = (M + 1) + 1 by omega,
            Ctx.Context.part_sideAt_succ B R t newMaximum
              (Ctx.Context.one_le_of_mem_levels hMB)]
          exact hMsB
        have hTGlobalD : (match t with
            | Side.lower => D.u | Side.upper => D.a) ≤ 5 := by
          simpa only [D, B, Ctx.Context.part] using le_of_eq hOppFive
        have hSGlobalD : (match s with
            | Side.lower => D.u | Side.upper => D.a) ≤ 5 := by
          simpa only [D, Ctx.Context.part] using le_of_eq hChosenFive
        have hChildD (p : ℕ) (hp : p ∈ D.childPositions) :
            p ∈ B.childPositions ∧ p ∉ K := by
          have hh : p ∈ B.childPositions ∧ p ∈ R := by
            simpa only [D, Ctx.Context.part_childPositions, List.mem_filter,
              decide_eq_true_eq] using hp
          exact ⟨hh.1, of_decide_eq_true (List.mem_filter.mp hh.2).2⟩
        have hOutsideD (p : ℕ) (hp : p ∈ D.childPositions) : p < a ∨ b < p :=
          hOutside p (hChildD p hp).1 (hChildD p hp).2
        have hChildNeD (p j z : ℕ) (hp : p ∈ D.childPositions)
            (hz : z ∈ D.extPositions j) : p ≠ z := by
          have hc := of_decide_eq_true (List.mem_filter.mp hp).2
          have he := (List.mem_filter.mp hz).2
          intro h
          subst z
          simp [hc] at he
        have haNotChild : a ∉ D.childPositions := by
          intro haChild
          exact hChildNeD a 1 a haChild haD rfl
        have hCover : ∀ p ∈ D.childPositions,
            color p ∈ ({0, 1} : Finset ℕ) := by
          intro p hp
          dsimp only [color]
          split_ifs <;> simp
        have hColor : ∀ p ∈ D.childPositions, ∀ q ∈ D.childPositions,
            p ≤ q → (∀ z, p ≤ z → z ≤ q → z ∈ D.childPositions) →
            color p = color q := by
          intro p hp q hq hpq hinterval
          by_cases hpa : p < a
          · have hqa : q < a := by
              by_contra h
              exact haNotChild (hinterval a (by omega) (by omega))
            simp [color, hpa, hqa]
          · have hqa : ¬ q < a := by omega
            simp [color, hpa, hqa]
        have hTransport (c : ℕ) :=
          ctx_part_pruning_history_transport D hPosD (support c) Side.lower 0
        have hPosGroup (c : ℕ) : ∀ p j v,
            (group c).letterAt p = Letter.ext j v → 1 ≤ j :=
          (hTransport c).1
        have hChildGroup (c p : ℕ) : p ∈ (group c).childPositions ↔
            p ∈ D.childPositions ∧ color p = c := by
          have hh := (hTransport c).2.1
          change (group c).childPositions =
            D.childPositions.filter (· ∈ support c) at hh
          rw [hh]
          simp [support]
        have hHistGroup (c j : ℕ) (hj : j ∈ D.levels) :
            (group c).extPositions j = D.extPositions j ∧
              (group c).sideAt j = D.sideAt j :=
          (hTransport c).2.2.1 j hj
        have hLevelsGroup (c : ℕ) (v : Side) (top : ℕ) :
            (group c).levelsOn v top = D.levelsOn v top :=
          (hTransport c).2.2.2.1 v top
        have hExtensionsGroup (c : ℕ) (v : Side) (top p : ℕ) :
            (group c).leftExt v top p = D.leftExt v top p ∧
              (group c).rightExt v top p = D.rightExt v top p :=
          (hTransport c).2.2.2.2.1 v top p
        have hLeftChild (p : ℕ) (hp : p ∈ (group 0).childPositions) : p < a := by
          have hc := (hChildGroup 0 p).mp hp
          dsimp only [color] at hc
          by_cases hpa : p < a
          · exact hpa
          · simp [hpa] at hc
        have hRightChild (p : ℕ) (hp : p ∈ (group 1).childPositions) : b < p := by
          have hc := (hChildGroup 1 p).mp hp
          have ho := hOutsideD p hc.1
          dsimp only [color] at hc
          by_cases hpa : p < a
          · simp [hpa] at hc
          · exact ho.resolve_left hpa
        have hM2OnGroup (c : ℕ) : M + 2 ∈ (group c).levelsOn s 0 := by
          rw [hLevelsGroup]
          exact List.mem_filter.mpr ⟨hM2D, by simp [hSideM2D]⟩
        have hyGroup (c : ℕ) : y ∈ (group c).extPositions (M + 2) := by
          rw [(hHistGroup c (M + 2) hM2D).1]
          exact hyD
        have hOneLeftGroup (c p : ℕ) (hyp : y < p) :
            1 ≤ (group c).leftExt s 0 p := by
          have hm : y ∈ ((group c).extPositions (M + 2)).filter (· < p) := by
            simp [hyGroup c, hyp]
          have hnonempty := List.ne_nil_of_mem hm
          have hv := Ctx.le_getD_max?_of_mem
            (L := ((group c).levelsOn s 0).sublists.map
              (fun ls => (ls.foldl (Ctx.Context.leftStep (group c)) (p, 0)).2))
            (List.mem_map.mpr ⟨[M + 2],
              List.mem_sublists.mpr (List.singleton_sublist.mpr (hM2OnGroup c)), rfl⟩)
          change _ ≤ (group c).leftExt s 0 p at hv
          simpa only [List.foldl_cons, List.foldl_nil, Ctx.Context.leftStep,
            List.getLast?_eq_some_getLast hnonempty] using hv
        have hOneRightGroup (c p : ℕ) (hpy : p < y) :
            1 ≤ (group c).rightExt s 0 p := by
          have hm : y ∈ ((group c).extPositions (M + 2)).filter (p < ·) := by
            simp [hyGroup c, hpy]
          have hnonempty := List.ne_nil_of_mem hm
          have hv := Ctx.le_getD_max?_of_mem
            (L := ((group c).levelsOn s 0).sublists.map
              (fun ls => (ls.foldl (Ctx.Context.rightStep (group c)) (p, 0)).2))
            (List.mem_map.mpr ⟨[M + 2],
              List.mem_sublists.mpr (List.singleton_sublist.mpr (hM2OnGroup c)), rfl⟩)
          change _ ≤ (group c).rightExt s 0 p at hv
          simpa only [List.foldl_cons, List.foldl_nil, Ctx.Context.rightStep,
            List.head?_eq_some_head hnonempty] using hv
        have hArm (c q : ℕ) (hq : q ∈ D.extPositions 1) (direction : Bool)
            (hBoundary : ∀ p ∈ (group c).childPositions,
              if direction then p < q else q < p)
            (hqOuter : if direction then q < q₀ else q₀ < q)
            (leftLoss rightLoss : ℕ)
            (hLeftLoss : ∀ p ∈ (group c).childPositions,
              leftLoss ≤ (group c).leftExt s 0 p)
            (hRightLoss : ∀ p ∈ (group c).childPositions,
              rightLoss ≤ (group c).rightExt s 0 p) :
            (group c).bound ≤ 4 - leftLoss - rightLoss := by
          let ρ : Context := { group c with
            word := (List.range (group c).word.length).map (fun p =>
              match (group c).letterAt p with
              | Letter.child => Letter.child
              | Letter.ext j v => if j = 1 then
                  if p ∈ [q] then Letter.ext 1 ((group c).sideAt 1)
                  else Letter.ext ((group c).maxima.length + 1) v
                  else Letter.ext j v) }
          have hqGroup : q ∈ (group c).extPositions 1 := by
            rw [(hHistGroup c 1 hOneD).1]
            exact hq
          have hp := ctx_single_level_occurrence_prune_bound_mono
            (group c) (hPosGroup c) 1 hOneD [q] q hqGroup (by simp)
          have hPosρ : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j := hp.1
          have hChildρ : ρ.childPositions = (group c).childPositions := hp.2.1
          have hHistρ : ∀ j ∈ D.levels,
              ρ.sideAt j = (group c).sideAt j ∧
                ρ.maximumAt j = (group c).maximumAt j ∧
                ρ.extPositions j = if j = 1 then
                  ((group c).extPositions j).filter (· ∈ [q])
                  else (group c).extPositions j := hp.2.2.1
          have hSideρ (j : ℕ) (hj : j ∈ D.levels) : ρ.sideAt j = D.sideAt j :=
            (hHistρ j hj).1.trans (hHistGroup c j hj).2
          have hqρ : q ∈ ρ.extPositions 1 := by
            rw [(hHistρ 1 hOneD).2.2, if_pos rfl]
            simp [hqGroup]
          have hqOuterρ : q₀ ∈ ρ.extPositions 2 := by
            rw [(hHistρ 2 hTwoD).2.2, if_neg (by omega),
              (hHistGroup c 2 hTwoD).1]
            exact hqD
          have hOuterChildren : ∀ p ∈ ρ.childPositions,
              if direction then p < q₀ else q₀ < p := by
            intro p hpρ
            rw [hChildρ] at hpρ
            have hbnd := hBoundary p hpρ
            cases direction
            · change q₀ < p
              change q₀ < q at hqOuter
              change q < p at hbnd
              omega
            · change p < q₀
              change q < q₀ at hqOuter
              change p < q at hbnd
              omega
          have hOuterYoung : ∀ j ∈ ρ.levelsOn (ρ.sideAt 2) 2,
              ∀ p ∈ ρ.extPositions j,
                if direction then p < q₀ else q₀ < p := by
            intro j hj p hpj
            have hjLevel : j ∈ D.levels := (List.mem_filter.mp hj).1
            have hjPos := Ctx.Context.one_le_of_mem_levels hjLevel
            have hjPred := of_decide_eq_true (List.mem_filter.mp hj).2
            have hjOne : j = 1 := by omega
            subst j
            rw [(hHistρ 1 hOneD).2.2, if_pos rfl] at hpj
            have hpq := List.mem_singleton.mp
              (of_decide_eq_true (List.mem_filter.mp hpj).2)
            subst p
            exact hqOuter
          have hInnerYoung : ∀ j ∈ ρ.levelsOn (ρ.sideAt 1) 1,
              ∀ p ∈ ρ.extPositions j,
                if direction then p < q else q < p := by
            intro j hj p hpj
            have hjLevel : j ∈ D.levels := (List.mem_filter.mp hj).1
            have hjPos := Ctx.Context.one_le_of_mem_levels hjLevel
            have hjPred := of_decide_eq_true (List.mem_filter.mp hj).2
            exfalso
            omega
          have hLeftρ : ∀ p ∈ ρ.childPositions,
              leftLoss ≤ ρ.leftExt s 0 p := by
            intro p hpρ
            have hpGroup : p ∈ (group c).childPositions := by
              simpa only [hChildρ] using hpρ
            have hOpp : (group c).sideAt 1 ≠ s := by
              rw [(hHistGroup c 1 hOneD).2, hSideOneD]
              exact Ne.symm hne
            exact Eq.mp
              (congrArg (fun z => leftLoss ≤ z)
                (hp.2.2.2.1 s hOpp 0 p).1.symm)
              (hLeftLoss p hpGroup)
          have hRightρ : ∀ p ∈ ρ.childPositions,
              rightLoss ≤ ρ.rightExt s 0 p := by
            intro p hpρ
            have hpGroup : p ∈ (group c).childPositions := by
              simpa only [hChildρ] using hpρ
            have hOpp : (group c).sideAt 1 ≠ s := by
              rw [(hHistGroup c 1 hOneD).2, hSideOneD]
              exact Ne.symm hne
            exact Eq.mp
              (congrArg (fun z => rightLoss ≤ z)
                (hp.2.2.2.1 s hOpp 0 p).2.symm)
              (hRightLoss p hpGroup)
          have hGlobalρ : (match ρ.sideAt 2 with
              | Side.lower => ρ.u | Side.upper => ρ.a) ≤ 5 := by
            rw [hSideρ 2 hTwoD, hSideTwoD]
            simpa only [ρ, group] using hTGlobalD
          have hh := hNestedBoundaryRankBudgetAllHistory ρ hPosρ 2 1 q₀ q
            hTwoD hOneD (by omega) hqOuterρ hqρ
            (by rw [hSideρ 1 hOneD, hSideρ 2 hTwoD, hSideOneD, hSideTwoD])
            direction direction hOuterChildren hOuterYoung
            (by intro p hpρ; rw [hChildρ] at hpρ; exact hBoundary p hpρ)
            hInnerYoung s
            (by rw [hSideρ 2 hTwoD, hSideTwoD]; exact Ne.symm hne)
            hGlobalρ leftLoss rightLoss hLeftρ hRightρ
          have hFull : (group c).bound ≤ ρ.bound := hp.2.2.2.2.2.2
          have hBudget : (match (generalizing := false) s with
                | Side.lower => ρ.u | Side.upper => ρ.a) - 1 - leftLoss - rightLoss ≤
              4 - leftLoss - rightLoss := by
            have hg : (match (generalizing := false) s with
                | Side.lower => ρ.u | Side.upper => ρ.a) ≤ 5 := by
              simpa only [ρ, group] using hSGlobalD
            have hOne : (match (generalizing := false) s with
                  | Side.lower => ρ.u | Side.upper => ρ.a) - 1 ≤ 4 := by
              simpa using Nat.sub_le_sub_right hg 1
            exact Nat.sub_le_sub_right
              (Nat.sub_le_sub_right hOne leftLoss) rightLoss
          exact hFull.trans (hh.2.trans hBudget)
        have hArms : (group 0).bound + (group 1).bound ≤ 7 := by
          rcases hexterior with ⟨hxy, hKeepRight⟩ | ⟨hyx, hKeepLeft⟩
          · have hyq : y < q₀ := hKeepRight q₀ hq₀
            have hLeftArm := hArm 0 a haD true hLeftChild haq 0 0
              (by intros; omega) (by intros; omega)
            have hRightLoss : ∀ p ∈ (group 1).childPositions,
                1 ≤ (group 1).leftExt s 0 p := by
              intro p hp
              exact hOneLeftGroup 1 p
                (lt_trans hyq (lt_trans hqb (hRightChild p hp)))
            have hRightArm := hArm 1 b hbD false hRightChild hqb 1 0
              hRightLoss (by intros; omega)
            omega
          · have hqy : q₀ < y := hKeepLeft q₀ hq₀
            have hLeftLoss : ∀ p ∈ (group 0).childPositions,
                1 ≤ (group 0).rightExt s 0 p := by
              intro p hp
              exact hOneRightGroup 0 p
                (lt_trans (hLeftChild p hp) (lt_trans haq hqy))
            have hLeftArm := hArm 0 a haD true hLeftChild haq 0 1
              (by intros; omega) hLeftLoss
            have hRightArm := hArm 1 b hbD false hRightChild hqb 0 0
              (by intros; omega) (by intros; omega)
            omega
        have hDecomp :=
          ctx_bound_le_sum_run_group_prunings_of_actual_marker_global_five
            D hPosD t 2 q₀ hTwoD hSideTwoD hqD hTGlobalD color
            ({0, 1} : Finset ℕ) hCover hColor
        change (∀ fuel, boundFuel fuel D ≤
            ({0, 1} : Finset ℕ).sum (fun c => (group c).bound)) ∧
          D.bound ≤ ({0, 1} : Finset ℕ).sum (fun c => (group c).bound) at hDecomp
        have hSum : ({0, 1} : Finset ℕ).sum (fun c => (group c).bound) ≤ 7 := by
          simpa using hArms
        exact ⟨fun fuel => (hDecomp.1 fuel).trans hSum, hDecomp.2.trans hSum⟩
      have hConvexMaximumThreeCutEleven
          (K : List ℕ) (p z : ℕ)
          (hpK : p ∈ K) (hpB : p ∈ B.childPositions)
          (hzB : z ∈ B.childPositions) (hzNot : z ∉ K)
          (hKsub : ∀ r ∈ K, r ∈ B.childPositions)
          (hconvexK : ∀ a ∈ K, ∀ b ∈ K, ∀ r ∈ B.childPositions,
            a ≤ r → r ≤ b → r ∈ K) :
          let R := B.childPositions.filter (· ∉ K)
          let C := B.part K s 3
          let D := B.part R t 2
          (∀ f g, boundFuel f C + boundFuel g D ≤ 11) ∧
            C.bound + D.bound ≤ 11 := by
        classical
        let R := B.childPositions.filter (· ∉ K)
        let C := B.part K s 3
        let D := B.part R t 2
        change (∀ f g, boundFuel f C + boundFuel g D ≤ 11) ∧
          C.bound + D.bound ≤ 11
        have hPosC := ctx_part_positive_letters B K s 3
        have hOneC : 1 ∈ C.levels := by
          simp only [C, Ctx.Context.part_levels, List.mem_cons, true_or]
        have hzC : z ∈ C.extPositions 1 := by
          change z ∈ (B.part K s 3).extPositions 1
          rw [Ctx.Context.part_extPositions_one hPosB]
          exact List.mem_filter.mpr ⟨hzB, by simpa⟩
        have hSideC : C.sideAt 1 = s :=
          Ctx.Context.part_sideAt_one_of_mem hPosB K s 3 hzC
        have hMaximumC : C.k - 3 ≤ C.maximumAt 1 := by
          change (B.part K s 3).k - 3 ≤ (B.part K s 3).maximumAt 1
          rw [Ctx.Context.part_maximumAt_one]
          change σ.k - 3 ≤ 3
          omega
        have hOwn := ctx_bound_le_opposite_width_of_sibling_maximum_ge_k_minus_three
          C hPosC s t hne 1 hOneC hSideC hMaximumC
        have hOwnFour : (∀ fuel, boundFuel fuel C ≤ 4) ∧ C.bound ≤ 4 := by
          constructor
          · intro fuel
            have h := hOwn.1 fuel
            cases t <;> simp only [C, B, Ctx.Context.part] at hOppFive h ⊢ <;> omega
          · have h := hOwn.2
            cases t <;> simp only [C, B, Ctx.Context.part] at hOppFive h ⊢ <;> omega
        have hCompRaw := ctx_two_actual_marker_companion_maximum_bound
          B hPosB s t hne (N + 1) (M + 1) x y hNB hMB (by omega)
          hNsB hMsB hxB hyB
          (by cases s <;> exact le_of_eq hChosenFive)
          K 3 2 p z
          (by
            simp only [C, Ctx.Context.part_childPositions, List.mem_filter,
              decide_eq_true_eq]
            exact ⟨hpB, hpK⟩)
          hzB hzNot
        have hBudget : B.k - 2 - 1 = 3 := by
          change σ.k - 2 - 1 = 3
          omega
        change (∀ fuel, boundFuel fuel D ≤
            ((B.k - 2 - 1 + 1).choose 2 + (B.k - 2 - 1) - 1)) ∧
          D.bound ≤ ((B.k - 2 - 1 + 1).choose 2 + (B.k - 2 - 1) - 1) at hCompRaw
        have hCompEight : (∀ fuel, boundFuel fuel D ≤ 8) ∧ D.bound ≤ 8 := by
          simpa only [hBudget] using hCompRaw
        have hChildNeQ (r : ℕ) (hrB : r ∈ B.childPositions) : r ≠ q₀ := by
          have hc := of_decide_eq_true (List.mem_filter.mp hrB).2
          have he := (List.mem_filter.mp hqB).2
          intro h
          subst r
          simp [hc] at he
        by_cases hstraddle : ∃ a ∈ K, ∃ b ∈ K, a < q₀ ∧ q₀ < b
        · obtain ⟨a, haK, b, hbK, haq, hqb⟩ := hstraddle
          have haB := hKsub a haK
          have hbB := hKsub b hbK
          have hOutside : ∀ r ∈ B.childPositions, r ∉ K → r < a ∨ b < r := by
            intro r hrB hrNot
            by_contra h
            have har : a ≤ r := by omega
            have hrb : r ≤ b := by omega
            exact hrNot (hconvexK a haK b hbK r hrB har hrb)
          have hCompSeven := hStraddlingCompanionSeven 2 K a b haK hbK haB hbB
            haq hqb hOutside
          exact ⟨fun f g =>
              (Nat.add_le_add (hOwnFour.1 f) (hCompSeven.1 g)).trans (by omega),
            (Nat.add_le_add hOwnFour.2 hCompSeven.2).trans (by omega)⟩
        · have hQSide : (∀ r ∈ K, q₀ < r) ∨ (∀ r ∈ K, r < q₀) := by
            have hpNe := hChildNeQ p hpB
            rcases lt_or_gt_of_ne hpNe with hpq | hqp
            · right
              intro r hrK
              have hrB := hKsub r hrK
              have hrNe := hChildNeQ r hrB
              by_contra hbad
              have hqr : q₀ < r := by omega
              exact hstraddle ⟨p, hpK, r, hrK, hpq, hqr⟩
            · left
              intro r hrK
              have hrB := hKsub r hrK
              have hrNe := hChildNeQ r hrB
              by_contra hbad
              have hrq : r < q₀ := by omega
              exact hstraddle ⟨r, hrK, p, hpK, hrq, hqp⟩
          have hZBoundary :
              (∀ r ∈ K, r < z) ∨ (∀ r ∈ K, z < r) := by
            by_cases hpz : p < z
            · left
              intro r hrK
              have hrB := hKsub r hrK
              by_contra hbad
              have hzr : z ≤ r := by omega
              exact hzNot (hconvexK p hpK r hrK z hzB (by omega) hzr)
            · right
              intro r hrK
              have hrB := hKsub r hrK
              by_contra hbad
              have hrz : r ≤ z := by omega
              exact hzNot (hconvexK r hrK p hpK z hzB hrz (by omega))
          rcases hZBoundary with hBefore | hAfter
          · have hOwnThree := hBoundaryMaximumThree K z hzB hzNot true
              (by intro r hrK; simpa using hBefore r hrK) hQSide
            exact ⟨fun f g =>
                (Nat.add_le_add (hOwnThree.1 f) (hCompEight.1 g)).trans (by omega),
              (Nat.add_le_add hOwnThree.2 hCompEight.2).trans (by omega)⟩
          · have hOwnThree := hBoundaryMaximumThree K z hzB hzNot false
              (by intro r hrK; simpa using hAfter r hrK) hQSide
            exact ⟨fun f g =>
                (Nat.add_le_add (hOwnThree.1 f) (hCompEight.1 g)).trans (by omega),
              (Nat.add_le_add hOwnThree.2 hCompEight.2).trans (by omega)⟩
      have hConvexMaximumOneCutTen
          (K : List ℕ) (p z : ℕ)
          (hpK : p ∈ K) (hpB : p ∈ B.childPositions)
          (hzB : z ∈ B.childPositions) (hzNot : z ∉ K)
          (hKsub : ∀ r ∈ K, r ∈ B.childPositions)
          (hconvexK : ∀ a ∈ K, ∀ b ∈ K, ∀ r ∈ B.childPositions,
            a ≤ r → r ≤ b → r ∈ K) :
          let R := B.childPositions.filter (· ∉ K)
          let C := B.part K s 1
          let D := B.part R t 4
          (∀ f g, boundFuel f C + boundFuel g D ≤ 10) ∧
            C.bound + D.bound ≤ 10 := by
        classical
        let R := B.childPositions.filter (· ∉ K)
        let C := B.part K s 1
        let D := B.part R t 4
        change (∀ f g, boundFuel f C + boundFuel g D ≤ 10) ∧
          C.bound + D.bound ≤ 10
        have hZBoundary :
            (∀ r ∈ K, r < z) ∨ (∀ r ∈ K, z < r) := by
          by_cases hpz : p < z
          · left
            intro r hrK
            by_contra hbad
            have hzr : z ≤ r := by omega
            exact hzNot (hconvexK p hpK r hrK z hzB (by omega) hzr)
          · right
            intro r hrK
            by_contra hbad
            have hrz : r ≤ z := by omega
            exact hzNot (hconvexK r hrK p hpK z hzB hrz (by omega))
        have hOwnNine : (∀ fuel, boundFuel fuel C ≤ 9) ∧ C.bound ≤ 9 := by
          rcases hZBoundary with hBefore | hAfter
          · simpa only [C] using hBoundaryAnyMaximumNine K z 1 hzB hzNot true
              (by intro r hrK; simpa using hBefore r hrK)
          · simpa only [C] using hBoundaryAnyMaximumNine K z 1 hzB hzNot false
              (by intro r hrK; simpa using hAfter r hrK)
        have hCompRaw := ctx_two_actual_marker_companion_maximum_bound
          B hPosB s t hne (N + 1) (M + 1) x y hNB hMB (by omega)
          hNsB hMsB hxB hyB
          (by cases s <;> exact le_of_eq hChosenFive)
          K 1 4 p z
          (by
            simp only [Ctx.Context.part_childPositions, List.mem_filter,
              decide_eq_true_eq]
            exact ⟨hpB, hpK⟩)
          hzB hzNot
        have hBudget : B.k - 4 - 1 = 1 := by
          change σ.k - 4 - 1 = 1
          omega
        change (∀ fuel, boundFuel fuel D ≤
            ((B.k - 4 - 1 + 1).choose 2 + (B.k - 4 - 1) - 1)) ∧
          D.bound ≤ ((B.k - 4 - 1 + 1).choose 2 + (B.k - 4 - 1) - 1)
          at hCompRaw
        have hCompOne : (∀ fuel, boundFuel fuel D ≤ 1) ∧ D.bound ≤ 1 := by
          simpa only [hBudget] using hCompRaw
        exact ⟨fun f g =>
            (Nat.add_le_add (hOwnNine.1 f) (hCompOne.1 g)).trans (by omega),
          (Nat.add_le_add hOwnNine.2 hCompOne.2).trans (by omega)⟩
      have hMaximumOneOwnTen
          (K : List ℕ) (z : ℕ)
          (hzB : z ∈ B.childPositions) (hzNot : z ∉ K) :
          let C := B.part K s 1
          (∀ fuel, boundFuel fuel C ≤ 10) ∧ C.bound ≤ 10 := by
        classical
        let C := B.part K s 1
        change (∀ fuel, boundFuel fuel C ≤ 10) ∧ C.bound ≤ 10
        have hPosC := ctx_part_positive_letters B K s 1
        have hOneC : 1 ∈ C.levels := by
          simp only [C, Ctx.Context.part_levels, List.mem_cons, true_or]
        have hzC : z ∈ C.extPositions 1 := by
          change z ∈ (B.part K s 1).extPositions 1
          rw [Ctx.Context.part_extPositions_one hPosB]
          exact List.mem_filter.mpr ⟨hzB, by simpa⟩
        have hSideOneC : C.sideAt 1 = s :=
          Ctx.Context.part_sideAt_one_of_mem hPosB K s 1 hzC
        have hNC : N + 2 ∈ C.levels := by
          change N + 2 ∈ (B.part K s 1).levels
          rw [Ctx.Context.part_levels]
          exact List.mem_cons_of_mem _
            (List.mem_map.mpr ⟨N + 1, hNB, by omega⟩)
        have hMC : M + 2 ∈ C.levels := by
          change M + 2 ∈ (B.part K s 1).levels
          rw [Ctx.Context.part_levels]
          exact List.mem_cons_of_mem _
            (List.mem_map.mpr ⟨M + 1, hMB, by omega⟩)
        have hSideNC : C.sideAt (N + 2) = s := by
          change (B.part K s 1).sideAt (N + 2) = s
          rw [show N + 2 = (N + 1) + 1 by omega,
            Ctx.Context.part_sideAt_succ B K s 1
              (Ctx.Context.one_le_of_mem_levels hNB)]
          exact hNsB
        have hSideMC : C.sideAt (M + 2) = s := by
          change (B.part K s 1).sideAt (M + 2) = s
          rw [show M + 2 = (M + 1) + 1 by omega,
            Ctx.Context.part_sideAt_succ B K s 1
              (Ctx.Context.one_le_of_mem_levels hMB)]
          exact hMsB
        have hxC : x ∈ C.extPositions (N + 2) := by
          change x ∈ (B.part K s 1).extPositions (N + 2)
          rw [show N + 2 = (N + 1) + 1 by omega,
            Ctx.Context.part_extPositions_succ B K s 1
              (Ctx.Context.one_le_of_mem_levels hNB)]
          exact hxB
        have hyC : y ∈ C.extPositions (M + 2) := by
          change y ∈ (B.part K s 1).extPositions (M + 2)
          rw [show M + 2 = (M + 1) + 1 by omega,
            Ctx.Context.part_extPositions_succ B K s 1
              (Ctx.Context.one_le_of_mem_levels hMB)]
          exact hyB
        have hTwoC : 2 ∈ C.levels := by
          change 2 ∈ (B.part K s 1).levels
          rw [Ctx.Context.part_levels]
          exact List.mem_cons_of_mem _
            (List.mem_map.mpr ⟨1, hOneB, by omega⟩)
        have hqC : q₀ ∈ C.extPositions 2 := by
          change q₀ ∈ (B.part K s 1).extPositions 2
          simpa only [show 2 = 1 + 1 by omega] using
            (show q₀ ∈ (B.part K s 1).extPositions (1 + 1) by
              rw [Ctx.Context.part_extPositions_succ B K s 1 (by omega)]
              exact hqB)
        have hSideTwoC : C.sideAt 2 = t := by
          change (B.part K s 1).sideAt 2 = t
          rw [show 2 = 1 + 1 by omega,
            Ctx.Context.part_sideAt_succ B K s 1 (by omega)]
          exact hSideB
        have hGlobalSC : (match s with
            | Side.lower => C.u | Side.upper => C.a) ≤ 5 := by
          simpa only [C, B, Ctx.Context.part] using le_of_eq hChosenFive
        have hGlobalTC : (match t with
            | Side.lower => C.u | Side.upper => C.a) ≤ 5 := by
          simpa only [C, B, Ctx.Context.part] using le_of_eq hOppFive
        have hWidthC : 1 ≤ (match t with
            | Side.lower => C.u | Side.upper => C.a) - 1 := by
          cases t <;>
            simp only [C, B, Ctx.Context.part] at hOppFive ⊢ <;> omega
        have hNoYoung : ∀ j ∈ C.levelsOn s 1, C.extPositions j = [] := by
          simp only [Ctx.Context.levelsOn_one, List.not_mem_nil,
            false_implies, implies_true]
        have hChildNe (r j u : ℕ) (hr : r ∈ B.childPositions)
            (hu : u ∈ B.extPositions j) : r ≠ u := by
          intro heq
          subst r
          have hc := of_decide_eq_true (List.mem_filter.mp hr).2
          have he := (List.mem_filter.mp hu).2
          simp [hc] at he
        have hzx : z ≠ x := hChildNe z (N + 1) x hzB hxB
        rcases hexterior with ⟨hxy, hout⟩ | ⟨hyx, hout⟩
        · by_cases hzxOrder : z < x
          · exact hThreeOrderedActualOppositeTen C hPosC
              1 (N + 2) (M + 2) z x y 2 q₀
              hOneC hNC hMC (by omega) (by omega)
              hSideOneC hSideNC hSideMC hzC hxC hyC hGlobalSC hNoYoung
              (Or.inl ⟨hzxOrder, hxy⟩)
              hTwoC hSideTwoC hqC hGlobalTC
          · have hgeometry : (z < x ∧ y < x) ∨ (x < z ∧ x < y) :=
              Or.inr ⟨by omega, hxy⟩
            have hLinear := ctx_nonmonotone_triple_linear_potential
              C hPosC s t hne 1 (N + 2) (M + 2) z x y
              hOneC hNC hMC (by omega) (by omega)
              hSideOneC hSideNC hSideMC hzC hxC hyC hgeometry
              hGlobalSC hWidthC
            have hWidthEq : (match t with
                | Side.lower => C.u | Side.upper => C.a) - 1 = 4 := by
              cases t <;>
                simp only [C, B, Ctx.Context.part] at hOppFive ⊢ <;> omega
            change (∀ fuel, boundFuel fuel C ≤
                3 * ((match t with
                  | Side.lower => C.u | Side.upper => C.a) - 1) - 2) ∧
              C.bound ≤ 3 * ((match t with
                | Side.lower => C.u | Side.upper => C.a) - 1) - 2 at hLinear
            simpa only [hWidthEq] using hLinear
        · by_cases hzxOrder : z < x
          · have hgeometry : (z < x ∧ y < x) ∨ (x < z ∧ x < y) :=
              Or.inl ⟨hzxOrder, hyx⟩
            have hLinear := ctx_nonmonotone_triple_linear_potential
              C hPosC s t hne 1 (N + 2) (M + 2) z x y
              hOneC hNC hMC (by omega) (by omega)
              hSideOneC hSideNC hSideMC hzC hxC hyC hgeometry
              hGlobalSC hWidthC
            have hWidthEq : (match t with
                | Side.lower => C.u | Side.upper => C.a) - 1 = 4 := by
              cases t <;>
                simp only [C, B, Ctx.Context.part] at hOppFive ⊢ <;> omega
            change (∀ fuel, boundFuel fuel C ≤
                3 * ((match t with
                  | Side.lower => C.u | Side.upper => C.a) - 1) - 2) ∧
              C.bound ≤ 3 * ((match t with
                | Side.lower => C.u | Side.upper => C.a) - 1) - 2 at hLinear
            simpa only [hWidthEq] using hLinear
          · exact hThreeOrderedActualOppositeTen C hPosC
              1 (N + 2) (M + 2) z x y 2 q₀
              hOneC hNC hMC (by omega) (by omega)
              hSideOneC hSideNC hSideMC hzC hxC hyC hGlobalSC hNoYoung
              (Or.inr ⟨hyx, by omega⟩)
              hTwoC hSideTwoC hqC hGlobalTC
      have hChosenB : ∀ j ∈ B.levelsOn s 0, ∀ z ∈ B.extPositions j,
          z = x ∨ z = y := by
        have hs : B.sideAt 1 ≠ s := by
          rw [hSideB]
          exact Ne.symm hne
        intro j hj z hz
        rw [Ctx.Context.part_levelsOn_other_zero hs] at hj
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
        rw [Ctx.Context.part_extPositions_succ σ rest t n
          (Ctx.Context.one_le_of_mem_levels (List.mem_filter.mp hi).1)] at hz
        exact hchosen i hi z hz
      have hMaxB : ∀ j ∈ B.levelsOn s 0, B.maximumAt j ≤ 1 := by
        have hs : B.sideAt 1 ≠ s := by
          rw [hSideB]
          exact Ne.symm hne
        intro j hj
        rw [Ctx.Context.part_levelsOn_other_zero hs] at hj
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
        rw [Ctx.Context.part_maximumAt_succ σ rest t n
          (Ctx.Context.one_le_of_mem_levels (List.mem_filter.mp hi).1)]
        exact hmax i hi
      have hFuelFull (C : Ctx.Context) (fuel : ℕ) :
          Ctx.Context.boundFuel fuel C ≤ C.bound := by
        by_cases hf : C.childPositions.length + 1 ≤ fuel
        · exact (Ctx.Context.boundFuel_eq_bound C hf).le
        · exact Ctx.Context.boundFuel_mono
            (by omega : fuel ≤ C.childPositions.length + 1) C
      have hBlockConvex (K : List ℕ) (hK : K ∈ B.blocks) :
          ∀ a ∈ K, ∀ b ∈ K, ∀ z ∈ B.childPositions,
            a ≤ z → z ≤ b → z ∈ K := by
        obtain ⟨i, len, _, _, hwindow⟩ := Ctx.Context.exists_take_drop_of_mem_blocks hK
        have hinfix : K <:+: B.childPositions := by
          refine ⟨B.childPositions.take i,
            (B.childPositions.drop i).drop (len + 1), ?_⟩
          rw [hwindow, List.append_assoc, List.take_append_drop,
            List.take_append_drop]
        obtain ⟨pre, post, he⟩ := hinfix
        have he' : pre ++ (K ++ post) = B.childPositions := by
          simpa only [List.append_assoc] using he
        have hs : (pre ++ (K ++ post)).Pairwise (· < ·) := by
          rw [he']
          exact Ctx.Context.childPositions_pairwise B
        have hbefore : ∀ a ∈ pre, ∀ b ∈ K, a < b := by
          intro a ha b hb
          exact (List.pairwise_append.mp hs).2.2 a ha b
            (List.mem_append_left post hb)
        have hafter : ∀ a ∈ K, ∀ b ∈ post, a < b :=
          (List.pairwise_append.mp (List.pairwise_append.mp hs).2.1).2.2
        intro a ha b hb z hz haz hzb
        rw [← he'] at hz
        rcases List.mem_append.mp hz with hz | hz
        · have hh := hbefore z hz a ha
          omega
        · rcases List.mem_append.mp hz with hz | hz
          · exact hz
          · have hh := hafter b hb z hz
            omega
      have hExtremeBlockCut
          (K : List ℕ) (hK : K ∈ B.blocks) (f g : ℕ) :
          let R := B.childPositions.filter (· ∉ K)
          Ctx.Context.boundFuel f (B.part K s 1) +
              Ctx.Context.boundFuel g (B.part R t 4) ≤ 11 ∧
            Ctx.Context.boundFuel f (B.part R s 1) +
              Ctx.Context.boundFuel g (B.part K t 4) ≤ 11 := by
        classical
        obtain ⟨hKlen, hKne, hKsub⟩ := Ctx.Context.mem_blocks hK
        obtain ⟨p, hpK⟩ := List.exists_mem_of_ne_nil K hKne
        have hpB := hKsub p hpK
        have hremoved : ∃ z ∈ B.childPositions, z ∉ K := by
          by_contra h
          push Not at h
          have hlen := ((Ctx.Context.childPositions_nodup B).subperm h).length_le
          omega
        obtain ⟨z, hzB, hzNot⟩ := hremoved
        let R := B.childPositions.filter (· ∉ K)
        change Ctx.Context.boundFuel f (B.part K s 1) +
              Ctx.Context.boundFuel g (B.part R t 4) ≤ 11 ∧
            Ctx.Context.boundFuel f (B.part R s 1) +
              Ctx.Context.boundFuel g (B.part K t 4) ≤ 11
        have hR (r : ℕ) : r ∈ R ↔ r ∈ B.childPositions ∧ r ∉ K := by
          simp only [R, List.mem_filter, decide_eq_true_eq]
        have hzR : z ∈ R := (hR z).mpr ⟨hzB, hzNot⟩
        have hpNotR : p ∉ R := by simp [R, hpK]
        have hForward := hConvexMaximumOneCutTen K p z hpK hpB hzB hzNot
          hKsub (hBlockConvex K hK)
        have hForwardFuel : Ctx.Context.boundFuel f (B.part K s 1) +
            Ctx.Context.boundFuel g (B.part R t 4) ≤ 11 := by
          have hh := hForward.1 f g
          simpa only [R] using hh.trans (by omega)
        refine ⟨hForwardFuel, ?_⟩
        have hOwn := hMaximumOneOwnTen R p hpB hpNotR
        have hzPart : z ∈ (B.part R s 1).childPositions := by
          simp only [Ctx.Context.part_childPositions, List.mem_filter,
            decide_eq_true_eq]
          exact ⟨hzB, hzR⟩
        have hCompRaw := ctx_two_actual_marker_companion_maximum_bound
          B hPosB s t hne (N + 1) (M + 1) x y hNB hMB (by omega)
          hNsB hMsB hxB hyB
          (by cases s <;> exact le_of_eq hChosenFive)
          R 1 4 z p hzPart hpB hpNotR
        have hBudget : B.k - 4 - 1 = 1 := by
          change σ.k - 4 - 1 = 1
          omega
        change (∀ fuel, boundFuel fuel
            (B.part (B.childPositions.filter (· ∉ R)) t 4) ≤
              ((B.k - 4 - 1 + 1).choose 2 + (B.k - 4 - 1) - 1)) ∧
          (B.part (B.childPositions.filter (· ∉ R)) t 4).bound ≤
            ((B.k - 4 - 1 + 1).choose 2 + (B.k - 4 - 1) - 1) at hCompRaw
        have hDouble (v : Side) (c : ℕ) :
            B.part (B.childPositions.filter (· ∉ R)) v c = B.part K v c := by
          apply Ctx.Context.part_congr
          intro r hrB
          simp only [R, List.mem_filter, decide_eq_true_eq, hrB, true_and,
            not_not]
        have hCompOne : (∀ fuel, boundFuel fuel (B.part K t 4) ≤ 1) ∧
            (B.part K t 4).bound ≤ 1 := by
          constructor
          · intro fuel
            have hh := hCompRaw.1 fuel
            rw [hDouble] at hh
            simpa only [hBudget] using hh
          · have hh := hCompRaw.2
            rw [hDouble] at hh
            simpa only [hBudget] using hh
        exact (Nat.add_le_add (hOwn.1 f) (hCompOne.1 g)).trans (by omega)
      have hCentralBlockCut
          (K : List ℕ) (hK : K ∈ B.blocks) (f g : ℕ) :
          let R := B.childPositions.filter (· ∉ K)
          Ctx.Context.boundFuel f (B.part K s 3) +
              Ctx.Context.boundFuel g (B.part R t 2) ≤ 11 ∧
            Ctx.Context.boundFuel f (B.part R s 3) +
              Ctx.Context.boundFuel g (B.part K t 2) ≤ 11 := by
        classical
        obtain ⟨hKlen, hKne, hKsub⟩ := Ctx.Context.mem_blocks hK
        obtain ⟨p, hpK⟩ := List.exists_mem_of_ne_nil K hKne
        have hpB := hKsub p hpK
        have hremoved : ∃ z ∈ B.childPositions, z ∉ K := by
          by_contra h
          push Not at h
          have hlen := ((Ctx.Context.childPositions_nodup B).subperm h).length_le
          omega
        obtain ⟨z, hzB, hzNot⟩ := hremoved
        let R := B.childPositions.filter (· ∉ K)
        change Ctx.Context.boundFuel f (B.part K s 3) +
              Ctx.Context.boundFuel g (B.part R t 2) ≤ 11 ∧
            Ctx.Context.boundFuel f (B.part R s 3) +
              Ctx.Context.boundFuel g (B.part K t 2) ≤ 11
        have hR (r : ℕ) : r ∈ R ↔ r ∈ B.childPositions ∧ r ∉ K := by
          simp only [R, List.mem_filter, decide_eq_true_eq]
        have hzR : z ∈ R := (hR z).mpr ⟨hzB, hzNot⟩
        have hpNotR : p ∉ R := by simp [R, hpK]
        have hconvK := hBlockConvex K hK
        have hForward := hConvexMaximumThreeCutEleven K p z hpK hpB hzB hzNot
          hKsub hconvK
        have hForwardFuel : Ctx.Context.boundFuel f (B.part K s 3) +
            Ctx.Context.boundFuel g (B.part R t 2) ≤ 11 := by
          simpa only [R] using hForward.1 f g
        refine ⟨hForwardFuel, ?_⟩
        have hOutside (r : ℕ) (hrR : r ∈ R) :
            (∀ q ∈ K, r < q) ∨ (∀ q ∈ K, q < r) := by
          have hrData := (hR r).mp hrR
          by_cases hrp : r < p
          · left
            intro q hqK
            by_contra hbad
            exact hrData.2 (hconvK q hqK p hpK r hrData.1 (by omega) (by omega))
          · right
            intro q hqK
            by_contra hbad
            exact hrData.2 (hconvK p hpK q hqK r hrData.1 (by omega) (by omega))
        by_cases hLeft : ∃ a ∈ R, ∀ q ∈ K, a < q
        · obtain ⟨a, haR, haLeft⟩ := hLeft
          by_cases hRight : ∃ b ∈ R, ∀ q ∈ K, q < b
          · obtain ⟨b, hbR, hbRight⟩ := hRight
            have haData := (hR a).mp haR
            have hbData := (hR b).mp hbR
            have hTwo := hTwoBoundaryMaximumTwoFour K a b haData.1 hbData.1
              haData.2 hbData.2
              (by intro q hqK; exact ⟨haLeft q hqK, hbRight q hqK⟩)
            let C := B.part R s 3
            have hPosC := ctx_part_positive_letters B R s 3
            have hOneC : 1 ∈ C.levels := by
              simp only [C, Ctx.Context.part_levels, List.mem_cons, true_or]
            have hpC : p ∈ C.extPositions 1 := by
              change p ∈ (B.part R s 3).extPositions 1
              rw [Ctx.Context.part_extPositions_one hPosB]
              exact List.mem_filter.mpr ⟨hpB, by simpa⟩
            have hSideC : C.sideAt 1 = s :=
              Ctx.Context.part_sideAt_one_of_mem hPosB R s 3 hpC
            have hMaximumC : C.k - 3 ≤ C.maximumAt 1 := by
              change (B.part R s 3).k - 3 ≤ (B.part R s 3).maximumAt 1
              rw [Ctx.Context.part_maximumAt_one]
              change σ.k - 3 ≤ 3
              omega
            have hOwn :=
              ctx_bound_le_opposite_width_of_sibling_maximum_ge_k_minus_three
                C hPosC s t hne 1 hOneC hSideC hMaximumC
            have hOwnFour : Ctx.Context.boundFuel f C ≤ 4 := by
              have hh := hOwn.1 f
              cases t <;>
                simp only [C, R, B, Ctx.Context.part] at hOppFive hh ⊢ <;> omega
            exact (Nat.add_le_add hOwnFour (hTwo.1 g)).trans (by omega)
          · have hconvR : ∀ a ∈ R, ∀ b ∈ R, ∀ r ∈ B.childPositions,
                a ≤ r → r ≤ b → r ∈ R := by
              intro a haR b hbR r hrB har hrb
              by_cases hrK : r ∈ K
              · rcases hOutside b hbR with hbLeft | hbRight
                · have hh := hbLeft r hrK
                  omega
                · exact False.elim (hRight ⟨b, hbR, hbRight⟩)
              · exact (hR r).mpr ⟨hrB, hrK⟩
            have hBack := hConvexMaximumThreeCutEleven R z p hzR hzB hpB hpNotR
              (by intro r hrR; exact (hR r).mp hrR |>.1) hconvR
            have hDouble (v : Ctx.Side) (c : ℕ) :
                B.part (B.childPositions.filter (· ∉ R)) v c = B.part K v c := by
              apply Ctx.Context.part_congr
              intro r hrB
              simp only [R, List.mem_filter, decide_eq_true_eq, hrB, true_and,
                not_not]
            have hh := hBack.1 f g
            rw [hDouble] at hh
            exact hh
        · have hconvR : ∀ a ∈ R, ∀ b ∈ R, ∀ r ∈ B.childPositions,
              a ≤ r → r ≤ b → r ∈ R := by
            intro a haR b hbR r hrB har hrb
            by_cases hrK : r ∈ K
            · rcases hOutside a haR with haLeft | haRight
              · exact False.elim (hLeft ⟨a, haR, haLeft⟩)
              · have hh := haRight r hrK
                omega
            · exact (hR r).mpr ⟨hrB, hrK⟩
          have hBack := hConvexMaximumThreeCutEleven R z p hzR hzB hpB hpNotR
            (by intro r hrR; exact (hR r).mp hrR |>.1) hconvR
          have hDouble (v : Ctx.Side) (c : ℕ) :
              B.part (B.childPositions.filter (· ∉ R)) v c = B.part K v c := by
            apply Ctx.Context.part_congr
            intro r hrB
            simp only [R, List.mem_filter, decide_eq_true_eq, hrB, true_and,
              not_not]
          have hh := hBack.1 f g
          rw [hDouble] at hh
          exact hh
      have hRetainedHighMiddleCut
          (K : List ℕ) (p z : ℕ)
          (hpK : p ∈ K) (hpB : p ∈ B.childPositions)
          (hzB : z ∈ B.childPositions) (hzNot : z ∉ K)
          (hKsub : ∀ r ∈ K, r ∈ B.childPositions)
          (hconvexK : ∀ a ∈ K, ∀ b ∈ K, ∀ r ∈ B.childPositions,
            a ≤ r → r ≤ b → r ∈ K)
          (hHighPart : 3 ≤ (match s with
            | Side.lower => (B.part K s 2).cupLimit p p
            | Side.upper => (B.part K s 2).capLimit p p)) :
          let R := B.childPositions.filter (· ∉ K)
          let C := B.part K s 2
          let D := B.part R t 3
          (∀ f g, boundFuel f C + boundFuel g D ≤ 11) ∧
            C.bound + D.bound ≤ 11 := by
        classical
        let R := B.childPositions.filter (· ∉ K)
        let C := B.part K s 2
        let D := B.part R t 3
        change (∀ f g, boundFuel f C + boundFuel g D ≤ 11) ∧
          C.bound + D.bound ≤ 11
        have hR (r : ℕ) : r ∈ R ↔ r ∈ B.childPositions ∧ r ∉ K := by
          simp only [R, List.mem_filter, decide_eq_true_eq]
        have hpNotR : p ∉ R := by simp [R, hpK]
        have hPosC := ctx_part_positive_letters B K s 2
        have hOneC : 1 ∈ C.levels := by
          simp only [C, Ctx.Context.part_levels, List.mem_cons, true_or]
        have hNC : N + 2 ∈ C.levels := by
          change N + 2 ∈ (B.part K s 2).levels
          rw [Ctx.Context.part_levels]
          exact List.mem_cons_of_mem _
            (List.mem_map.mpr ⟨N + 1, hNB, by omega⟩)
        have hMC : M + 2 ∈ C.levels := by
          change M + 2 ∈ (B.part K s 2).levels
          rw [Ctx.Context.part_levels]
          exact List.mem_cons_of_mem _
            (List.mem_map.mpr ⟨M + 1, hMB, by omega⟩)
        have hSideNC : C.sideAt (N + 2) = s := by
          change (B.part K s 2).sideAt (N + 2) = s
          rw [show N + 2 = (N + 1) + 1 by omega,
            Ctx.Context.part_sideAt_succ B K s 2
              (Ctx.Context.one_le_of_mem_levels hNB)]
          exact hNsB
        have hSideMC : C.sideAt (M + 2) = s := by
          change (B.part K s 2).sideAt (M + 2) = s
          rw [show M + 2 = (M + 1) + 1 by omega,
            Ctx.Context.part_sideAt_succ B K s 2
              (Ctx.Context.one_le_of_mem_levels hMB)]
          exact hMsB
        have hxC : x ∈ C.extPositions (N + 2) := by
          change x ∈ (B.part K s 2).extPositions (N + 2)
          rw [show N + 2 = (N + 1) + 1 by omega,
            Ctx.Context.part_extPositions_succ B K s 2
              (Ctx.Context.one_le_of_mem_levels hNB)]
          exact hxB
        have hyC : y ∈ C.extPositions (M + 2) := by
          change y ∈ (B.part K s 2).extPositions (M + 2)
          rw [show M + 2 = (M + 1) + 1 by omega,
            Ctx.Context.part_extPositions_succ B K s 2
              (Ctx.Context.one_le_of_mem_levels hMB)]
          exact hyB
        have hpC : p ∈ C.childPositions := by
          simp only [C, Ctx.Context.part_childPositions, List.mem_filter,
            decide_eq_true_eq]
          exact ⟨hpB, hpK⟩
        have hGlobalC : (match s with
            | Side.lower => C.u | Side.upper => C.a) ≤ 5 := by
          simpa only [C, B, Ctx.Context.part] using le_of_eq hChosenFive
        have hHighSource : 3 ≤ (match s with
            | Side.lower => B.cupLimit p p
            | Side.upper => B.capLimit p p) := by
          have hle := ctx_part_limits_le B K s 2 p p
          cases s <;> simp only at hHighPart ⊢ <;> omega
        have hNOnB : N + 1 ∈ B.levelsOn s 0 :=
          List.mem_filter.mpr ⟨hNB, by simp [hNsB]⟩
        have hSourceGeom :=
          ctx_capacity_three_children_exterior_of_two_levels_global_five
            B s (N + 1) (M + 1) x y hNB hMB (by omega)
            hNsB hMsB hxB hyB (le_of_eq hChosenFive)
        have hBoundaryK : ∃ direction : Bool,
            ∀ q ∈ K, if direction then q < z else z < q := by
          by_cases hzp : z < p
          · refine ⟨false, ?_⟩
            intro q hq
            by_contra hbad
            have hqz : q ≤ z := Nat.le_of_not_gt hbad
            have hzp' : z ≤ p := le_of_lt hzp
            exact hzNot (hconvexK q hq p hpK z hzB hqz hzp')
          · refine ⟨true, ?_⟩
            intro q hq
            simp only [if_true]
            by_contra hbad
            have hpz : p ≤ z := Nat.le_of_not_gt hzp
            have hzq : z ≤ q := Nat.le_of_not_gt hbad
            exact hzNot (hconvexK p hpK q hq z hzB hpz hzq)
        obtain ⟨direction, hBoundaryK⟩ := hBoundaryK
        have hOwn := hBoundaryAnyMaximumNine K z 2 hzB hzNot direction hBoundaryK
        have hFar : (x < y ∧ ∀ r ∈ R, r < x) ∨
            (y < x ∧ ∀ r ∈ R, x < r) := by
          rcases hSourceGeom with hForward | hBackward
          · refine Or.inl ⟨hForward.1, ?_⟩
            have hxp := hForward.2 p hpB hHighSource (N + 1) hNOnB x hxB
            intro r hrR
            have hrData := (hR r).mp hrR
            have hrC : r ∈ C.extPositions 1 := by
              change r ∈ (B.part K s 2).extPositions 1
              rw [Ctx.Context.part_extPositions_one hPosB]
              exact List.mem_filter.mpr ⟨hrData.1, by simpa using hrData.2⟩
            have hSideOneC : C.sideAt 1 = s :=
              Ctx.Context.part_sideAt_one_of_mem hPosB K s 2 hrC
            rcases ctx_capacity_three_children_exterior_of_two_levels_global_five
                C s 1 (N + 2) r x hOneC hNC (by omega) hSideOneC hSideNC
                hrC hxC hGlobalC with hNear | hWrong
            · exact hNear.1
            · have hNOnC : N + 2 ∈ C.levelsOn s 0 :=
                List.mem_filter.mpr ⟨hNC, by simp [hSideNC]⟩
              have hpx := hWrong.2 p hpC hHighPart (N + 2) hNOnC x hxC
              omega
          · refine Or.inr ⟨hBackward.1, ?_⟩
            have hpx := hBackward.2 p hpB hHighSource (N + 1) hNOnB x hxB
            intro r hrR
            have hrData := (hR r).mp hrR
            have hrC : r ∈ C.extPositions 1 := by
              change r ∈ (B.part K s 2).extPositions 1
              rw [Ctx.Context.part_extPositions_one hPosB]
              exact List.mem_filter.mpr ⟨hrData.1, by simpa using hrData.2⟩
            have hSideOneC : C.sideAt 1 = s :=
              Ctx.Context.part_sideAt_one_of_mem hPosB K s 2 hrC
            rcases ctx_capacity_three_children_exterior_of_two_levels_global_five
                C s 1 (N + 2) r x hOneC hNC (by omega) hSideOneC hSideNC
                hrC hxC hGlobalC with hWrong | hNear
            · have hNOnC : N + 2 ∈ C.levelsOn s 0 :=
                List.mem_filter.mpr ⟨hNC, by simp [hSideNC]⟩
              have hxp := hWrong.2 p hpC hHighPart (N + 2) hNOnC x hxC
              omega
            · exact hNear.1
        have hComp : (∀ fuel, boundFuel fuel D ≤ 2) ∧ D.bound ≤ 2 := by
          rcases hFar with hFar | hFar
          · have hxp := (show x < p by
                rcases hSourceGeom with hh | hh
                · exact hh.2 p hpB hHighSource (N + 1) hNOnB x hxB
                · omega)
            have hh := hFarComplementMaximumThreeTwo R p hpB hpNotR true
              (by intro r hrR; simp only [if_true]; exact lt_trans (hFar.2 r hrR) hxp)
              (Or.inl hFar)
            simpa only [D] using hh
          · have hpx := (show p < x by
                rcases hSourceGeom with hh | hh
                · omega
                · exact hh.2 p hpB hHighSource (N + 1) hNOnB x hxB)
            have hh := hFarComplementMaximumThreeTwo R p hpB hpNotR false
              (by intro r hrR; exact lt_trans hpx (hFar.2 r hrR))
              (Or.inr hFar)
            simpa only [D] using hh
        exact ⟨fun f g =>
            (Nat.add_le_add (hOwn.1 f) (hComp.1 g)).trans (by omega),
          (Nat.add_le_add hOwn.2 hComp.2).trans (by omega)⟩
      have hConvexMaximumTwoCutEleven
          (K : List ℕ) (p z : ℕ)
          (hpK : p ∈ K) (hpB : p ∈ B.childPositions)
          (hzB : z ∈ B.childPositions) (hzNot : z ∉ K)
          (hKsub : ∀ r ∈ K, r ∈ B.childPositions)
          (hconvexK : ∀ a ∈ K, ∀ b ∈ K, ∀ r ∈ B.childPositions,
            a ≤ r → r ≤ b → r ∈ K) :
          let R := B.childPositions.filter (· ∉ K)
          let C := B.part K s 2
          let D := B.part R t 3
          (∀ f g, boundFuel f C + boundFuel g D ≤ 11) ∧
            C.bound + D.bound ≤ 11 := by
        classical
        let R := B.childPositions.filter (· ∉ K)
        let C := B.part K s 2
        let D := B.part R t 3
        change (∀ f g, boundFuel f C + boundFuel g D ≤ 11) ∧
          C.bound + D.bound ≤ 11
        have hPosD := ctx_part_positive_letters B R t 3
        have hOneD : 1 ∈ D.levels := by
          simp only [D, Ctx.Context.part_levels, List.mem_cons, true_or]
        have hpD : p ∈ D.extPositions 1 := by
          change p ∈ (B.part R t 3).extPositions 1
          rw [Ctx.Context.part_extPositions_one hPosB]
          exact List.mem_filter.mpr ⟨hpB, by simp [R, hpK]⟩
        have hSideD : D.sideAt 1 = t :=
          Ctx.Context.part_sideAt_one_of_mem hPosB R t 3 hpD
        have hMaximumD : D.k - 3 ≤ D.maximumAt 1 := by
          change (B.part R t 3).k - 3 ≤ (B.part R t 3).maximumAt 1
          rw [Ctx.Context.part_maximumAt_one]
          change σ.k - 3 ≤ 3
          omega
        have hDRaw := ctx_bound_le_opposite_width_of_sibling_maximum_ge_k_minus_three
          D hPosD t s (Ne.symm hne) 1 hOneD hSideD hMaximumD
        have hDFour : (∀ fuel, boundFuel fuel D ≤ 4) ∧ D.bound ≤ 4 := by
          constructor
          · intro fuel
            have hh := hDRaw.1 fuel
            cases s <;>
              simp only [D, B, Ctx.Context.part] at hChosenFive hh ⊢ <;> omega
          · have hh := hDRaw.2
            cases s <;>
              simp only [D, B, Ctx.Context.part] at hChosenFive hh ⊢ <;> omega
        by_cases hHighPart : ∃ q ∈ C.childPositions,
            3 ≤ (match s with
              | Side.lower => C.cupLimit q q
              | Side.upper => C.capLimit q q)
        · obtain ⟨q, hqC, hqHigh⟩ := hHighPart
          have hqData : q ∈ B.childPositions ∧ q ∈ K := by
            change q ∈ (B.part K s 2).childPositions at hqC
            simpa only [Ctx.Context.part_childPositions, List.mem_filter,
              decide_eq_true_eq] using hqC
          have hh := hRetainedHighMiddleCut K q z hqData.2 hqData.1 hzB hzNot
            hKsub hconvexK (by simpa only [C] using hqHigh)
          simpa only [R, C, D] using hh
        · have hBoundaryK : ∃ direction : Bool,
              ∀ q ∈ K, if direction then q < z else z < q := by
            by_cases hzp : z < p
            · refine ⟨false, ?_⟩
              intro q hq
              by_contra hbad
              have hqz : q ≤ z := Nat.le_of_not_gt hbad
              exact hzNot (hconvexK q hq p hpK z hzB hqz (by omega))
            · refine ⟨true, ?_⟩
              intro q hq
              simp only [if_true]
              by_contra hbad
              have hzq : z ≤ q := Nat.le_of_not_gt hbad
              exact hzNot (hconvexK p hpK q hq z hzB (by omega) hzq)
          obtain ⟨direction, hBoundaryK⟩ := hBoundaryK
          have hCLow : ∀ q ∈ (B.part K s 2).childPositions,
              0 < (B.part K s 2).cupLimit q q →
              0 < (B.part K s 2).capLimit q q →
              (match s with
                | Side.lower => (B.part K s 2).cupLimit q q
                | Side.upper => (B.part K s 2).capLimit q q) ≤ 2 := by
            intro q hq _ _
            by_contra hbad
            have hge : 3 ≤ (match s with
                | Side.lower => (B.part K s 2).cupLimit q q
                | Side.upper => (B.part K s 2).capLimit q q) := by
              cases s <;> simp only at hbad ⊢ <;> omega
            exact hHighPart ⟨q, by simpa only [C] using hq,
              by simpa only [C] using hge⟩
          have hCSeven := hPartLowBoundaryMaximumTwoSeven K z hzB hzNot
            direction hBoundaryK hCLow
          exact ⟨fun f g =>
              (Nat.add_le_add (hCSeven.1 f) (hDFour.1 g)).trans (by omega),
            (Nat.add_le_add hCSeven.2 hDFour.2).trans (by omega)⟩
      have hMiddleBlockCut
          (K : List ℕ) (hK : K ∈ B.blocks) (f g : ℕ) :
          let R := B.childPositions.filter (· ∉ K)
          boundFuel f (B.part K s 2) + boundFuel g (B.part R t 3) ≤ 11 ∧
            boundFuel f (B.part R s 2) + boundFuel g (B.part K t 3) ≤ 11 := by
        classical
        obtain ⟨hKlen, hKne, hKsub⟩ := Ctx.Context.mem_blocks hK
        obtain ⟨p, hpK⟩ := List.exists_mem_of_ne_nil K hKne
        have hpB := hKsub p hpK
        have hremoved : ∃ z ∈ B.childPositions, z ∉ K := by
          by_contra h
          push Not at h
          have hlen := ((Ctx.Context.childPositions_nodup B).subperm h).length_le
          omega
        obtain ⟨z, hzB, hzNot⟩ := hremoved
        let R := B.childPositions.filter (· ∉ K)
        change boundFuel f (B.part K s 2) + boundFuel g (B.part R t 3) ≤ 11 ∧
          boundFuel f (B.part R s 2) + boundFuel g (B.part K t 3) ≤ 11
        have hR (r : ℕ) : r ∈ R ↔ r ∈ B.childPositions ∧ r ∉ K := by
          simp only [R, List.mem_filter, decide_eq_true_eq]
        have hzR : z ∈ R := (hR z).mpr ⟨hzB, hzNot⟩
        have hpNotR : p ∉ R := by simp [R, hpK]
        have hForward := hConvexMaximumTwoCutEleven K p z hpK hpB hzB hzNot
          hKsub (hBlockConvex K hK)
        refine ⟨by simpa only [R] using hForward.1 f g, ?_⟩
        have hconvK := hBlockConvex K hK
        have hOutside (r : ℕ) (hrR : r ∈ R) :
            (∀ q ∈ K, r < q) ∨ (∀ q ∈ K, q < r) := by
          have hrData := (hR r).mp hrR
          by_cases hrp : r < p
          · left
            intro q hqK
            by_contra hbad
            exact hrData.2 (hconvK q hqK p hpK r hrData.1 (by omega) (by omega))
          · right
            intro q hqK
            by_contra hbad
            exact hrData.2 (hconvK p hpK q hqK r hrData.1 (by omega) (by omega))
        by_cases hLeft : ∃ a ∈ R, ∀ q ∈ K, a < q
        · obtain ⟨a, haR, haLeft⟩ := hLeft
          by_cases hRight : ∃ b ∈ R, ∀ q ∈ K, q < b
          · obtain ⟨b, hbR, hbRight⟩ := hRight
            by_cases hSurroundX :
                ∃ u ∈ K, ∃ v ∈ K, u < x ∧ x < v
            · obtain ⟨u, huK, v, hvK, hux, hxv⟩ := hSurroundX
              have haData := (hR a).mp haR
              have hbData := (hR b).mp hbR
              have hh :=
                ctx_two_marker_younger_surrounding_internal_complement_cut_ten_bound
                  B hPosB s t hne (N + 1) (M + 1) x y hNB hMB (by omega)
                  hNsB hMsB hxB hyB
                  (by cases s <;> exact le_of_eq hChosenFive)
                  (by cases t <;> exact le_of_eq hOppFive)
                  hChosenB
                  (by
                    cases t <;>
                      simp only [B, Ctx.Context.part] at hOppFive ⊢ <;> omega)
                  K u v a b 2 3 huK hvK hux hxv hKsub
                  haData.1 hbData.1 haData.2 hbData.2
                  (by intro q hqK; exact ⟨haLeft q hqK, hbRight q hqK⟩)
                  hconvK
              have hfg := hh.1 f g
              simpa only [R] using hfg.trans (by omega)
            · -- Exact remaining middle obstruction: R has two nonempty arms
              -- around K and K does not surround the younger marker x.  In
              -- the checked sharp rows the maximum-two complement costs
              -- eight and B.part K t 3 costs three; the missing proof is the
              -- coupled two-cluster 5+3 rank cover in the residual geometry.
              have hKNeX (q : ℕ) (hqK : q ∈ K) : q ≠ x := by
                intro heq
                subst q
                have hc := of_decide_eq_true
                  (List.mem_filter.mp (hKsub x hqK)).2
                have he := (List.mem_filter.mp hxB).2
                simp [hc] at he
              have hpx : p ≠ x := hKNeX p hpK
              have hOneSideX :
                  (∀ q ∈ K, q < x) ∨ (∀ q ∈ K, x < q) := by
                rcases lt_or_gt_of_ne hpx with hpx | hxp
                · left
                  intro q hqK
                  by_contra hbad
                  exact hSurroundX
                    ⟨p, hpK, q, hqK, hpx, by have := hKNeX q hqK; omega⟩
                · right
                  intro q hqK
                  by_contra hbad
                  exact hSurroundX
                    ⟨q, hqK, p, hpK, by have := hKNeX q hqK; omega, hxp⟩
              let D := B.part K t 3
              let budget := (match s with
                | Side.lower => D.u | Side.upper => D.a) - 1
              let active := D.childPositions.toFinset.filter
                (fun q => 0 < D.cupLimit q q ∧ 0 < D.capLimit q q)
              let ranks := active.biUnion (fun q =>
                Finset.Icc (D.leftExt s 0 q + 1)
                  (budget - D.rightExt s 0 q))
              have hPosD := ctx_part_positive_letters B K t 3
              have hOneD : 1 ∈ D.levels := by
                simp only [D, Ctx.Context.part_levels, List.mem_cons, true_or]
              have haData := (hR a).mp haR
              have hbData := (hR b).mp hbR
              have haD : a ∈ D.extPositions 1 := by
                change a ∈ (B.part K t 3).extPositions 1
                rw [Ctx.Context.part_extPositions_one hPosB]
                exact List.mem_filter.mpr ⟨haData.1, by simpa using haData.2⟩
              have hbD : b ∈ D.extPositions 1 := by
                change b ∈ (B.part K t 3).extPositions 1
                rw [Ctx.Context.part_extPositions_one hPosB]
                exact List.mem_filter.mpr ⟨hbData.1, by simpa using hbData.2⟩
              have hSideD : D.sideAt 1 = t :=
                Ctx.Context.part_sideAt_one_of_mem hPosB K t 3 haD
              have hChildD (q : ℕ) (hq : q ∈ D.childPositions) : q ∈ K := by
                have hh : q ∈ B.childPositions ∧ q ∈ K := by
                  simpa only [D, Ctx.Context.part_childPositions, List.mem_filter,
                    decide_eq_true_eq] using hq
                exact hh.2
              have hSmallD : min ((match D.sideAt 1 with
                    | Side.lower => D.u | Side.upper => D.a) - 2)
                    (D.k - D.maximumAt 1) ≤ 3 := by
                apply (Nat.min_le_right _ _).trans
                change (B.part K t 3).k - (B.part K t 3).maximumAt 1 ≤ 3
                rw [Ctx.Context.part_maximumAt_one]
                change σ.k - 3 ≤ 3
                omega
              have hRankBound := ctx_active_two_boundary_marker_rank_union_bound
                D hPosD 1 a b hOneD haD hbD
                (by
                  intro q hq _
                  exact ⟨haLeft q (hChildD q hq), hbRight q (hChildD q hq)⟩)
                (by
                  simp only [Ctx.Context.levelsOn_one, List.not_mem_nil,
                    false_implies, implies_true])
                s (by rw [hSideD]; exact Ne.symm hne) hSmallD
              change (∀ fuel, boundFuel fuel D ≤ ranks.card) ∧
                D.bound ≤ ranks.card at hRankBound
              have hND : N + 2 ∈ D.levels := by
                change N + 2 ∈ (B.part K t 3).levels
                rw [Ctx.Context.part_levels]
                exact List.mem_cons_of_mem _
                  (List.mem_map.mpr ⟨N + 1, hNB, by omega⟩)
              have hxD : x ∈ D.extPositions (N + 2) := by
                change x ∈ (B.part K t 3).extPositions (N + 2)
                rw [show N + 2 = (N + 1) + 1 by omega,
                  Ctx.Context.part_extPositions_succ B K t 3
                    (Ctx.Context.one_le_of_mem_levels hNB)]
                exact hxB
              have hSideND : D.sideAt (N + 2) = s := by
                change (B.part K t 3).sideAt (N + 2) = s
                rw [show N + 2 = (N + 1) + 1 by omega,
                  Ctx.Context.part_sideAt_succ B K t 3
                    (Ctx.Context.one_le_of_mem_levels hNB)]
                exact hNsB
              have hGlobalSD : (match s with
                  | Side.lower => D.u | Side.upper => D.a) ≤ 5 := by
                simpa only [D, B, Ctx.Context.part] using le_of_eq hChosenFive
              have hRanksThree : ranks.card ≤ 3 := by
                rcases hOneSideX with hKLeftX | hKRightX
                · have hSub : ranks ⊆ Finset.Icc 1 3 := by
                    intro z hz
                    obtain ⟨q, hqActive, hzInterval⟩ := Finset.mem_biUnion.mp hz
                    have hqChild : q ∈ D.childPositions := by
                      exact (by simpa only [active, Finset.mem_filter,
                        List.mem_toFinset] using (Finset.mem_filter.mp hqActive).1)
                    have hqx := hKLeftX q (hChildD q hqChild)
                    have hEndpoint :=
                      ctx_actual_marker_opposite_rank_interval_endpoint_exclusion
                        D s (N + 2) x q hND hSideND hxD hqChild
                    rcases hEndpoint with ⟨hxq, _⟩ | ⟨_, hUpper⟩
                    · omega
                    · apply Finset.mem_Icc.mpr
                      have hzBounds := Finset.mem_Icc.mp hzInterval
                      have hzUpper := hUpper z (by
                        cases s <;> simpa only [budget] using hzInterval)
                      cases s <;> simp only at hGlobalSD hzUpper ⊢ <;> omega
                  have hh := Finset.card_le_card hSub
                  simpa only [Nat.card_Icc] using hh
                · have hSub : ranks ⊆ Finset.Icc 2 4 := by
                    intro z hz
                    obtain ⟨q, hqActive, hzInterval⟩ := Finset.mem_biUnion.mp hz
                    have hqChild : q ∈ D.childPositions := by
                      exact (by simpa only [active, Finset.mem_filter,
                        List.mem_toFinset] using (Finset.mem_filter.mp hqActive).1)
                    have hxq := hKRightX q (hChildD q hqChild)
                    have hEndpoint :=
                      ctx_actual_marker_opposite_rank_interval_endpoint_exclusion
                        D s (N + 2) x q hND hSideND hxD hqChild
                    rcases hEndpoint with ⟨_, hLower⟩ | ⟨hqx, _⟩
                    · apply Finset.mem_Icc.mpr
                      have hzBounds := Finset.mem_Icc.mp hzInterval
                      have hzLower := hLower z (by
                        cases s <;> simpa only [budget] using hzInterval)
                      exact ⟨hzLower, by omega⟩
                    · omega
                  have hh := Finset.card_le_card hSub
                  simpa only [Nat.card_Icc] using hh
              have hDThree : (∀ fuel, boundFuel fuel D ≤ 3) ∧ D.bound ≤ 3 :=
                ⟨fun fuel => (hRankBound.1 fuel).trans hRanksThree,
                  hRankBound.2.trans hRanksThree⟩
              have hDTwoOfOuter
                  (hOuter : (x < y ∧ ∀ q ∈ K, q < x) ∨
                    (y < x ∧ ∀ q ∈ K, x < q)) :
                  (∀ fuel, boundFuel fuel D ≤ 2) ∧ D.bound ≤ 2 := by
                have hMD : M + 2 ∈ D.levels := by
                  change M + 2 ∈ (B.part K t 3).levels
                  rw [Ctx.Context.part_levels]
                  exact List.mem_cons_of_mem _
                    (List.mem_map.mpr ⟨M + 1, hMB, by omega⟩)
                have hyD : y ∈ D.extPositions (M + 2) := by
                  change y ∈ (B.part K t 3).extPositions (M + 2)
                  rw [show M + 2 = (M + 1) + 1 by omega,
                    Ctx.Context.part_extPositions_succ B K t 3
                      (Ctx.Context.one_le_of_mem_levels hMB)]
                  exact hyB
                have hSideMD : D.sideAt (M + 2) = s := by
                  change (B.part K t 3).sideAt (M + 2) = s
                  rw [show M + 2 = (M + 1) + 1 by omega,
                    Ctx.Context.part_sideAt_succ B K t 3
                      (Ctx.Context.one_le_of_mem_levels hMB)]
                  exact hMsB
                have hNOn : N + 2 ∈ D.levelsOn s 0 :=
                  List.mem_filter.mpr ⟨hND, by simp [hSideND]⟩
                have hMOn : M + 2 ∈ D.levelsOn s 0 :=
                  List.mem_filter.mpr ⟨hMD, by simp [hSideMD]⟩
                have hSorted : (D.levelsOn s 0).Pairwise (· < ·) := by
                  apply List.Pairwise.filter
                  exact List.pairwise_lt_range.map (fun i ↦ i + 1)
                    (fun i j h ↦ by dsimp; omega)
                have hTwo : [N + 2, M + 2].Sublist (D.levelsOn s 0) := by
                  have hs : [N + 2, M + 2].Pairwise (· < ·) := by
                    simp [hNM]
                  have hsub : [N + 2, M + 2] ⊆ D.levelsOn s 0 := by
                    intro j hj
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
                    rcases hj with rfl | rfl
                    · exact hNOn
                    · exact hMOn
                  have he : (D.levelsOn s 0).filter (· ∈ [N + 2, M + 2]) =
                      [N + 2, M + 2] := by
                    apply (hSorted.filter _).eq_of_mem_iff hs
                    intro j
                    simp only [List.mem_filter, decide_eq_true_eq]
                    exact ⟨And.right, fun hj => ⟨hsub hj, hj⟩⟩
                  rw [← he]
                  exact List.filter_sublist
                have hSortN : (D.extPositions (N + 2)).Pairwise (· ≤ ·) :=
                  (List.pairwise_lt_range.filter _).imp le_of_lt
                have hTwoRight (q : ℕ) (hqx : q < x) (hxy : x < y) :
                    2 ≤ D.rightExt s 0 q := by
                  have hm : x ∈ (D.extPositions (N + 2)).filter (q < ·) := by
                    simp [hxD, hqx]
                  have hnonempty := List.ne_nil_of_mem hm
                  let w := ((D.extPositions (N + 2)).filter (q < ·)).head hnonempty
                  have hw : ((D.extPositions (N + 2)).filter (q < ·)).head? = some w :=
                    List.head?_eq_some_head hnonempty
                  have hwx : w ≤ x := (hSortN.filter _).rel_head hm
                  have hmOld : y ∈ (D.extPositions (M + 2)).filter (w < ·) := by
                    simp only [List.mem_filter, decide_eq_true_eq]
                    exact ⟨hyD, by omega⟩
                  have hneOld := List.ne_nil_of_mem hmOld
                  have hv := Ctx.le_getD_max?_of_mem
                    (L := (D.levelsOn s 0).sublists.map
                      (fun ls => (ls.foldl (Ctx.Context.rightStep D) (q, 0)).2))
                    (List.mem_map.mpr ⟨[N + 2, M + 2],
                      List.mem_sublists.mpr hTwo, rfl⟩)
                  change _ ≤ D.rightExt s 0 q at hv
                  simpa only [List.foldl_cons, List.foldl_nil,
                    Ctx.Context.rightStep, hw,
                    List.head?_eq_some_head hneOld] using hv
                have hTwoLeft (q : ℕ) (hxq : x < q) (hyx : y < x) :
                    2 ≤ D.leftExt s 0 q := by
                  have hm : x ∈ (D.extPositions (N + 2)).filter (· < q) := by
                    simp [hxD, hxq]
                  have hnonempty := List.ne_nil_of_mem hm
                  let w := ((D.extPositions (N + 2)).filter (· < q)).getLast hnonempty
                  have hw : ((D.extPositions (N + 2)).filter (· < q)).getLast? = some w :=
                    List.getLast?_eq_some_getLast hnonempty
                  have hxw : x ≤ w := (hSortN.filter _).rel_getLast hm
                  have hmOld : y ∈ (D.extPositions (M + 2)).filter (· < w) := by
                    simp only [List.mem_filter, decide_eq_true_eq]
                    exact ⟨hyD, by omega⟩
                  have hneOld := List.ne_nil_of_mem hmOld
                  have hv := Ctx.le_getD_max?_of_mem
                    (L := (D.levelsOn s 0).sublists.map
                      (fun ls => (ls.foldl (Ctx.Context.leftStep D) (q, 0)).2))
                    (List.mem_map.mpr ⟨[N + 2, M + 2],
                      List.mem_sublists.mpr hTwo, rfl⟩)
                  change _ ≤ D.leftExt s 0 q at hv
                  simpa only [List.foldl_cons, List.foldl_nil,
                    Ctx.Context.leftStep, hw,
                    List.getLast?_eq_some_getLast hneOld] using hv
                have hRanksTwo : ranks.card ≤ 2 := by
                  rcases hOuter with ⟨hxy, hKLeft⟩ | ⟨hyx, hKRight⟩
                  · have hSub : ranks ⊆ Finset.Icc 1 2 := by
                      intro z hz
                      obtain ⟨q, hqActive, hzInterval⟩ := Finset.mem_biUnion.mp hz
                      have hqChild : q ∈ D.childPositions := by
                        exact (by simpa only [active, Finset.mem_filter,
                          List.mem_toFinset] using (Finset.mem_filter.mp hqActive).1)
                      have hright := hTwoRight q
                        (hKLeft q (hChildD q hqChild)) hxy
                      have hzBounds := Finset.mem_Icc.mp hzInterval
                      apply Finset.mem_Icc.mpr
                      cases s <;>
                        simp only [budget] at hGlobalSD hzBounds ⊢ <;> omega
                    have hh := Finset.card_le_card hSub
                    simpa only [Nat.card_Icc] using hh
                  · have hSub : ranks ⊆ Finset.Icc 3 4 := by
                      intro z hz
                      obtain ⟨q, hqActive, hzInterval⟩ := Finset.mem_biUnion.mp hz
                      have hqChild : q ∈ D.childPositions := by
                        exact (by simpa only [active, Finset.mem_filter,
                          List.mem_toFinset] using (Finset.mem_filter.mp hqActive).1)
                      have hleft := hTwoLeft q
                        (hKRight q (hChildD q hqChild)) hyx
                      have hzBounds := Finset.mem_Icc.mp hzInterval
                      apply Finset.mem_Icc.mpr
                      cases s <;>
                        simp only [budget] at hGlobalSD hzBounds ⊢ <;> omega
                    have hh := Finset.card_le_card hSub
                    simpa only [Nat.card_Icc] using hh
                exact ⟨fun fuel => (hRankBound.1 fuel).trans hRanksTwo,
                  hRankBound.2.trans hRanksTwo⟩
              have hCNineOfInner
                  (hInner : (x < y ∧ ∀ q ∈ K, x < q) ∨
                    (y < x ∧ ∀ q ∈ K, q < x)) :
                  (∀ fuel, boundFuel fuel (B.part R s 2) ≤ 9) ∧
                    (B.part R s 2).bound ≤ 9 := by
                let C := B.part R s 2
                change (∀ fuel, boundFuel fuel C ≤ 9) ∧ C.bound ≤ 9
                have hPosC := ctx_part_positive_letters B R s 2
                have hOneC : 1 ∈ C.levels := by
                  simp only [C, Ctx.Context.part_levels, List.mem_cons, true_or]
                have hpC : p ∈ C.extPositions 1 := by
                  change p ∈ (B.part R s 2).extPositions 1
                  rw [Ctx.Context.part_extPositions_one hPosB]
                  exact List.mem_filter.mpr ⟨hpB, by simpa using hpNotR⟩
                have hSideOneC : C.sideAt 1 = s :=
                  Ctx.Context.part_sideAt_one_of_mem hPosB R s 2 hpC
                have hNC : N + 2 ∈ C.levels := by
                  change N + 2 ∈ (B.part R s 2).levels
                  rw [Ctx.Context.part_levels]
                  exact List.mem_cons_of_mem _
                    (List.mem_map.mpr ⟨N + 1, hNB, by omega⟩)
                have hMC : M + 2 ∈ C.levels := by
                  change M + 2 ∈ (B.part R s 2).levels
                  rw [Ctx.Context.part_levels]
                  exact List.mem_cons_of_mem _
                    (List.mem_map.mpr ⟨M + 1, hMB, by omega⟩)
                have hxC : x ∈ C.extPositions (N + 2) := by
                  change x ∈ (B.part R s 2).extPositions (N + 2)
                  rw [show N + 2 = (N + 1) + 1 by omega,
                    Ctx.Context.part_extPositions_succ B R s 2
                      (Ctx.Context.one_le_of_mem_levels hNB)]
                  exact hxB
                have hyC : y ∈ C.extPositions (M + 2) := by
                  change y ∈ (B.part R s 2).extPositions (M + 2)
                  rw [show M + 2 = (M + 1) + 1 by omega,
                    Ctx.Context.part_extPositions_succ B R s 2
                      (Ctx.Context.one_le_of_mem_levels hMB)]
                  exact hyB
                have hSideNC : C.sideAt (N + 2) = s := by
                  change (B.part R s 2).sideAt (N + 2) = s
                  rw [show N + 2 = (N + 1) + 1 by omega,
                    Ctx.Context.part_sideAt_succ B R s 2
                      (Ctx.Context.one_le_of_mem_levels hNB)]
                  exact hNsB
                have hSideMC : C.sideAt (M + 2) = s := by
                  change (B.part R s 2).sideAt (M + 2) = s
                  rw [show M + 2 = (M + 1) + 1 by omega,
                    Ctx.Context.part_sideAt_succ B R s 2
                      (Ctx.Context.one_le_of_mem_levels hMB)]
                  exact hMsB
                have hGeometry : (p < x ∧ y < x) ∨ (x < p ∧ x < y) := by
                  rcases hInner with ⟨hxy, hKRight⟩ | ⟨hyx, hKLeft⟩
                  · exact Or.inr ⟨hKRight p hpK, hxy⟩
                  · exact Or.inl ⟨hKLeft p hpK, hyx⟩
                have hGlobalSC : (match s with
                    | Side.lower => C.u | Side.upper => C.a) ≤ 5 := by
                  simpa only [C, B, Ctx.Context.part] using le_of_eq hChosenFive
                have hGlobalTC : (match t with
                    | Side.lower => C.u | Side.upper => C.a) ≤ C.k := by
                  cases t <;>
                    simp only [C, B, Ctx.Context.part] at hOppFive hk ⊢ <;> omega
                have hkC : C.k = 6 := by
                  simpa only [C, B, Ctx.Context.part] using hk
                have hMaximumC : C.k - 4 ≤ C.maximumAt 1 := by
                  change (B.part R s 2).k - 4 ≤ (B.part R s 2).maximumAt 1
                  rw [Ctx.Context.part_maximumAt_one]
                  change σ.k - 4 ≤ 2
                  omega
                have hSat :=
                  ctx_nonmonotone_triple_saturated_potential_arbitrary_opposite_history
                    C hPosC s t hne 1 (N + 2) (M + 2) p x y
                    hOneC hNC hMC (by omega) (by omega)
                    hSideOneC hSideNC hSideMC hpC hxC hyC hGeometry
                    hGlobalSC hGlobalTC (by rw [hkC]; decide)
                    1 hOneC hSideOneC hMaximumC
                have hNext : (match t with
                    | Side.lower => C.u | Side.upper => C.a) ≤ C.k - 1 := by
                  cases t <;>
                    simp only [C, B, Ctx.Context.part] at hOppFive hk ⊢ <;> omega
                have hh := hSat.2.2 hNext
                have hNine : 3 * C.k - 9 = 9 := by
                  rw [hkC]
                rw [hNine] at hh
                simpa only [C] using hh
              have hCTenOfOuter
                  (hOuter : (x < y ∧ ∀ q ∈ K, q < x) ∨
                    (y < x ∧ ∀ q ∈ K, x < q)) :
                  (∀ fuel, boundFuel fuel (B.part R s 2) ≤ 10) ∧
                    (B.part R s 2).bound ≤ 10 := by
                let C := B.part R s 2
                change (∀ fuel, boundFuel fuel C ≤ 10) ∧ C.bound ≤ 10
                have hPosC := ctx_part_positive_letters B R s 2
                have hOneC : 1 ∈ C.levels := by
                  simp only [C, Ctx.Context.part_levels, List.mem_cons, true_or]
                have hpC : p ∈ C.extPositions 1 := by
                  change p ∈ (B.part R s 2).extPositions 1
                  rw [Ctx.Context.part_extPositions_one hPosB]
                  exact List.mem_filter.mpr ⟨hpB, by simpa using hpNotR⟩
                have hSideOneC : C.sideAt 1 = s :=
                  Ctx.Context.part_sideAt_one_of_mem hPosB R s 2 hpC
                have hNC : N + 2 ∈ C.levels := by
                  change N + 2 ∈ (B.part R s 2).levels
                  rw [Ctx.Context.part_levels]
                  exact List.mem_cons_of_mem _
                    (List.mem_map.mpr ⟨N + 1, hNB, by omega⟩)
                have hMC : M + 2 ∈ C.levels := by
                  change M + 2 ∈ (B.part R s 2).levels
                  rw [Ctx.Context.part_levels]
                  exact List.mem_cons_of_mem _
                    (List.mem_map.mpr ⟨M + 1, hMB, by omega⟩)
                have hxC : x ∈ C.extPositions (N + 2) := by
                  change x ∈ (B.part R s 2).extPositions (N + 2)
                  rw [show N + 2 = (N + 1) + 1 by omega,
                    Ctx.Context.part_extPositions_succ B R s 2
                      (Ctx.Context.one_le_of_mem_levels hNB)]
                  exact hxB
                have hyC : y ∈ C.extPositions (M + 2) := by
                  change y ∈ (B.part R s 2).extPositions (M + 2)
                  rw [show M + 2 = (M + 1) + 1 by omega,
                    Ctx.Context.part_extPositions_succ B R s 2
                      (Ctx.Context.one_le_of_mem_levels hMB)]
                  exact hyB
                have hSideNC : C.sideAt (N + 2) = s := by
                  change (B.part R s 2).sideAt (N + 2) = s
                  rw [show N + 2 = (N + 1) + 1 by omega,
                    Ctx.Context.part_sideAt_succ B R s 2
                      (Ctx.Context.one_le_of_mem_levels hNB)]
                  exact hNsB
                have hSideMC : C.sideAt (M + 2) = s := by
                  change (B.part R s 2).sideAt (M + 2) = s
                  rw [show M + 2 = (M + 1) + 1 by omega,
                    Ctx.Context.part_sideAt_succ B R s 2
                      (Ctx.Context.one_le_of_mem_levels hMB)]
                  exact hMsB
                have hTwoC : 2 ∈ C.levels := by
                  change 2 ∈ (B.part R s 2).levels
                  rw [Ctx.Context.part_levels]
                  exact List.mem_cons_of_mem _
                    (List.mem_map.mpr ⟨1, hOneB, by omega⟩)
                have hqC : q₀ ∈ C.extPositions 2 := by
                  change q₀ ∈ (B.part R s 2).extPositions 2
                  simpa only [show 2 = 1 + 1 by omega] using
                    (show q₀ ∈ (B.part R s 2).extPositions (1 + 1) by
                      rw [Ctx.Context.part_extPositions_succ B R s 2 (by omega)]
                      exact hqB)
                have hSideTwoC : C.sideAt 2 = t := by
                  change (B.part R s 2).sideAt 2 = t
                  rw [show 2 = 1 + 1 by omega,
                    Ctx.Context.part_sideAt_succ B R s 2 (by omega)]
                  exact hSideB
                have hGlobalSC : (match s with
                    | Side.lower => C.u | Side.upper => C.a) ≤ 5 := by
                  simpa only [C, B, Ctx.Context.part] using le_of_eq hChosenFive
                have hGlobalTC : (match t with
                    | Side.lower => C.u | Side.upper => C.a) ≤ 5 := by
                  simpa only [C, B, Ctx.Context.part] using le_of_eq hOppFive
                have hNoYoung : ∀ j ∈ C.levelsOn s 1,
                    C.extPositions j = [] := by
                  simp only [Ctx.Context.levelsOn_one, List.not_mem_nil,
                    false_implies, implies_true]
                have hOrder : (p < x ∧ x < y) ∨ (y < x ∧ x < p) := by
                  rcases hOuter with ⟨hxy, hKLeft⟩ | ⟨hyx, hKRight⟩
                  · exact Or.inl ⟨hKLeft p hpK, hxy⟩
                  · exact Or.inr ⟨hyx, hKRight p hpK⟩
                exact hThreeOrderedActualOppositeTen C hPosC
                  1 (N + 2) (M + 2) p x y 2 q₀
                  hOneC hNC hMC (by omega) (by omega)
                  hSideOneC hSideNC hSideMC hpC hxC hyC hGlobalSC hNoYoung
                  hOrder hTwoC hSideTwoC hqC hGlobalTC
              have hEndpointSaving :
                  (((x < y ∧ ∀ q ∈ K, q < x) ∨
                      (y < x ∧ ∀ q ∈ K, x < q)) ∧
                    (boundFuel f (B.part R s 2) ≤ 9 ∨
                      boundFuel g D ≤ 1)) ∨
                  (((x < y ∧ ∀ q ∈ K, x < q) ∨
                      (y < x ∧ ∀ q ∈ K, q < x)) ∧
                    (boundFuel f (B.part R s 2) ≤ 8 ∨
                      boundFuel g D ≤ 2)) := by
                -- Exact remaining middle obstruction.  The checked component
                -- envelopes are (C,D) ≤ (10,2) in the outer geometry and
                -- (C,D) ≤ (9,3) in the inner geometry.  Standalone C ≤ 8
                -- and outer D ≤ 1 are both false, so the needed fact is
                -- precisely that the two endpoint values cannot occur together.
                sorry
              have hCoupledEleven :
                  boundFuel f (B.part R s 2) + boundFuel g D ≤ 11 := by
                rcases hEndpointSaving with
                  ⟨hOuter, hCNine | hDOne⟩ | ⟨hInner, hCEight | hDTwo⟩
                · have hDTwoAll := hDTwoOfOuter hOuter
                  exact (Nat.add_le_add hCNine (hDTwoAll.1 g)).trans (by omega)
                · have hCTen := hCTenOfOuter hOuter
                  exact (Nat.add_le_add (hCTen.1 f) hDOne).trans (by omega)
                · exact (Nat.add_le_add hCEight (hDThree.1 g)).trans (by omega)
                · have hCNine := hCNineOfInner hInner
                  exact (Nat.add_le_add (hCNine.1 f) hDTwo).trans (by omega)
              simpa only [D] using hCoupledEleven
          · have hconvR : ∀ a ∈ R, ∀ b ∈ R, ∀ r ∈ B.childPositions,
                a ≤ r → r ≤ b → r ∈ R := by
              intro a haR b hbR r hrB har hrb
              by_cases hrK : r ∈ K
              · rcases hOutside b hbR with hbLeft | hbRight
                · have hh := hbLeft r hrK
                  omega
                · exact False.elim (hRight ⟨b, hbR, hbRight⟩)
              · exact (hR r).mpr ⟨hrB, hrK⟩
            have hBack := hConvexMaximumTwoCutEleven R z p hzR hzB hpB hpNotR
              (by intro r hrR; exact (hR r).mp hrR |>.1) hconvR
            have hDouble (v : Side) (c : ℕ) :
                B.part (B.childPositions.filter (· ∉ R)) v c = B.part K v c := by
              apply Ctx.Context.part_congr
              intro r hrB
              simp only [R, List.mem_filter, decide_eq_true_eq, hrB, true_and,
                not_not]
            have hh := hBack.1 f g
            rw [hDouble] at hh
            exact hh
        · have hconvR : ∀ a ∈ R, ∀ b ∈ R, ∀ r ∈ B.childPositions,
              a ≤ r → r ≤ b → r ∈ R := by
            intro a haR b hbR r hrB har hrb
            by_cases hrK : r ∈ K
            · rcases hOutside a haR with haLeft | haRight
              · exact False.elim (hLeft ⟨a, haR, haLeft⟩)
              · have hh := haRight r hrK
                omega
            · exact (hR r).mpr ⟨hrB, hrK⟩
          have hBack := hConvexMaximumTwoCutEleven R z p hzR hzB hpB hpNotR
            (by intro r hrR; exact (hR r).mp hrR |>.1) hconvR
          have hDouble (v : Side) (c : ℕ) :
              B.part (B.childPositions.filter (· ∉ R)) v c = B.part K v c := by
            apply Ctx.Context.part_congr
            intro r hrB
            simp only [R, List.mem_filter, decide_eq_true_eq, hrB, true_and,
              not_not]
          have hh := hBack.1 f g
          rw [hDouble] at hh
          exact hh
      have hOppositeBoundaryAnyMaximumNine
          (K : List ℕ) (z newMaximum : ℕ)
          (hzB : z ∈ B.childPositions) (hzNot : z ∉ K)
          (direction : Bool)
          (hBoundary : ∀ p ∈ K, if direction then p < z else z < p) :
          let C := B.part K t newMaximum
          (∀ fuel, boundFuel fuel C ≤ 9) ∧ C.bound ≤ 9 := by
        classical
        let C := B.part K t newMaximum
        let budget := (match s with
          | Side.lower => C.u | Side.upper => C.a) - 1
        let active := C.childPositions.toFinset.filter
          (fun p => 0 < C.cupLimit p p ∧ 0 < C.capLimit p p)
        let ranks := active.biUnion (fun p =>
          (let I := Finset.Icc (C.leftExt s 0 p + 1)
            (budget - C.rightExt s 0 p)
          (I.product I).filter (fun r => r.1 ≤ r.2)))
        change (∀ fuel, boundFuel fuel C ≤ 9) ∧ C.bound ≤ 9
        have hPosC := ctx_part_positive_letters B K t newMaximum
        have hOneC : 1 ∈ C.levels := by
          simp only [C, Ctx.Context.part_levels, List.mem_cons, true_or]
        have hzC : z ∈ C.extPositions 1 := by
          change z ∈ (B.part K t newMaximum).extPositions 1
          rw [Ctx.Context.part_extPositions_one hPosB]
          exact List.mem_filter.mpr ⟨hzB, by simpa⟩
        have hSideC : C.sideAt 1 = t :=
          Ctx.Context.part_sideAt_one_of_mem hPosB K t newMaximum hzC
        have hChildC (p : ℕ) (hp : p ∈ C.childPositions) : p ∈ K := by
          exact of_decide_eq_true
            (List.mem_filter.mp (show p ∈ B.childPositions.filter (· ∈ K) by
              simpa only [C, Ctx.Context.part_childPositions] using hp)).2
        have hSmall : min ((match C.sideAt 1 with
              | Side.lower => C.u | Side.upper => C.a) - 1)
              (C.k - C.maximumAt 1) ≤ 4 := by
          apply (Nat.min_le_left _ _).trans
          rw [hSideC]
          cases t <;>
            simp only [C, B, Ctx.Context.part] at hOppFive ⊢ <;> omega
        have hPair := ctx_active_boundary_marker_rank_pair_union_bound
          C hPosC 1 z hOneC hzC direction
          (by
            intro p hp _
            exact hBoundary p (hChildC p hp))
          (by
            simp only [Ctx.Context.levelsOn_one, List.not_mem_nil,
              false_implies, implies_true])
          s (by rw [hSideC]; exact Ne.symm hne) hSmall
        change (∀ fuel, boundFuel fuel C ≤ ranks.card) ∧
          C.bound ≤ ranks.card at hPair
        have hNC : N + 2 ∈ C.levels := by
          change N + 2 ∈ (B.part K t newMaximum).levels
          rw [Ctx.Context.part_levels]
          exact List.mem_cons_of_mem _
            (List.mem_map.mpr ⟨N + 1, hNB, by omega⟩)
        have hxC : x ∈ C.extPositions (N + 2) := by
          change x ∈ (B.part K t newMaximum).extPositions (N + 2)
          rw [show N + 2 = (N + 1) + 1 by omega,
            Ctx.Context.part_extPositions_succ B K t newMaximum
              (Ctx.Context.one_le_of_mem_levels hNB)]
          exact hxB
        have hSideNC : C.sideAt (N + 2) = s := by
          change (B.part K t newMaximum).sideAt (N + 2) = s
          rw [show N + 2 = (N + 1) + 1 by omega,
            Ctx.Context.part_sideAt_succ B K t newMaximum
              (Ctx.Context.one_le_of_mem_levels hNB)]
          exact hNsB
        have hGlobalC : (match s with
            | Side.lower => C.u | Side.upper => C.a) ≤ 5 := by
          simpa only [C, B, Ctx.Context.part] using le_of_eq hChosenFive
        have hNine := ctx_actual_marker_rank_pair_union_nine_bound
          C s (N + 2) x hNC hSideNC hxC hGlobalC
        change ranks.card ≤ 9 at hNine
        exact ⟨fun fuel => (hPair.1 fuel).trans hNine,
          hPair.2.trans hNine⟩
      have hSwappedExtremeBlockCut
          (K : List ℕ) (hK : K ∈ B.blocks) (f g : ℕ) :
          let R := B.childPositions.filter (· ∉ K)
          boundFuel f (B.part K s 4) + boundFuel g (B.part R t 1) ≤ 11 ∧
            boundFuel f (B.part R s 4) + boundFuel g (B.part K t 1) ≤ 11 := by
        classical
        obtain ⟨hKlen, hKne, hKsub⟩ := Ctx.Context.mem_blocks hK
        obtain ⟨p, hpK⟩ := List.exists_mem_of_ne_nil K hKne
        have hpB := hKsub p hpK
        have hremoved : ∃ z ∈ B.childPositions, z ∉ K := by
          by_contra h
          push Not at h
          have hlen := ((Ctx.Context.childPositions_nodup B).subperm h).length_le
          omega
        obtain ⟨z, hzB, hzNot⟩ := hremoved
        let R := B.childPositions.filter (· ∉ K)
        change boundFuel f (B.part K s 4) + boundFuel g (B.part R t 1) ≤ 11 ∧
          boundFuel f (B.part R s 4) + boundFuel g (B.part K t 1) ≤ 11
        refine ⟨?_, ?_⟩
        · have hPosOwn := ctx_part_positive_letters B K s 4
          have hOneOwn : 1 ∈ (B.part K s 4).levels := by
            simp only [Ctx.Context.part_levels, List.mem_cons, true_or]
          have hMaxOwn : (B.part K s 4).k - 2 ≤
              (B.part K s 4).maximumAt 1 := by
            rw [Ctx.Context.part_maximumAt_one]
            change σ.k - 2 ≤ 4
            omega
          have hOwn := ctx_bound_le_one_of_large_sibling_maximum
            (B.part K s 4) hPosOwn 1 hOneOwn hMaxOwn
          have hpOwn : p ∈ (B.part K s 4).childPositions := by
            simp only [Ctx.Context.part_childPositions, List.mem_filter,
              decide_eq_true_eq]
            exact ⟨hpB, hpK⟩
          by_cases hSmallS : ∀ q ∈ (B.part R t 1).childPositions,
              0 < (B.part R t 1).cupLimit q q →
              0 < (B.part R t 1).capLimit q q →
              (match s with
                | Side.lower => (B.part R t 1).cupLimit q q
                | Side.upper => (B.part R t 1).capLimit q q) ≤ 2
          · have hCut :=
                ctx_extreme_cut_six_eleven_of_small_chosen_maxima_capacity_two
                  B hPosB s t hne (le_of_eq hChosenFive)
                  (by
                    cases t <;>
                      simp only [B, Ctx.Context.part] at hoppositeLower ⊢ <;>
                      exact hoppositeLower)
                  (le_of_eq hOppFive) hMaxB K 4 1 p hpOwn
                  (by change 4 + 2 = σ.k; omega)
                  (by change σ.k = 6; exact hk)
            have hh := hCut hSmallS
            simpa only [R] using hh.1 f g
          · push_neg at hSmallS
            obtain ⟨highS, hHighSChild, hHighSCup, hHighSCap,
              hHighSNot⟩ := hSmallS
            have hHighSThree : 3 ≤ (match s with
                | Side.lower => (B.part R t 1).cupLimit highS highS
                | Side.upper => (B.part R t 1).capLimit highS highS) := by
              omega
            have hR (r : ℕ) : r ∈ R ↔ r ∈ B.childPositions ∧ r ∉ K := by
              simp only [R, List.mem_filter, decide_eq_true_eq]
            have hpNotR : p ∉ R := by simp [R, hpK]
            have hOutside (r : ℕ) (hrR : r ∈ R) :
                (∀ q ∈ K, r < q) ∨ (∀ q ∈ K, q < r) := by
              have hrData := (hR r).mp hrR
              by_cases hrp : r < p
              · left
                intro q hqK
                by_contra hbad
                exact hrData.2
                  (hBlockConvex K hK q hqK p hpK r hrData.1 (by omega) (by omega))
              · right
                intro q hqK
                by_contra hbad
                exact hrData.2
                  (hBlockConvex K hK p hpK q hqK r hrData.1 (by omega) (by omega))
            by_cases hLeft : ∃ a ∈ R, ∀ q ∈ K, a < q
            · obtain ⟨a, haR, haLeft⟩ := hLeft
              by_cases hRight : ∃ b ∈ R, ∀ q ∈ K, q < b
              · obtain ⟨b, hbR, hbRight⟩ := hRight
                by_cases hStraddles :
                    (∃ u ∈ K, u < q₀) ∧ (∃ v ∈ K, q₀ < v)
                · obtain ⟨⟨u, huK, huq⟩, ⟨v, hvK, hqv⟩⟩ := hStraddles
                  have huB := hKsub u huK
                  have hvB := hKsub v hvK
                  have hOutsideK : ∀ r ∈ B.childPositions,
                      r ∉ K → r < u ∨ v < r := by
                    intro r hrB hrNot
                    by_contra hbad
                    push_neg at hbad
                    exact hrNot
                      (hBlockConvex K hK u huK v hvK r hrB hbad.1 hbad.2)
                  have hComp := hStraddlingCompanionSeven 1 K u v huK hvK
                    huB hvB huq hqv hOutsideK
                  exact (Nat.add_le_add (hOwn.1 f) (hComp.1 g)).trans (by omega)
                · -- Exact remaining extreme obstruction: R has two nonempty
                  -- arms around K, while the whole block K lies on one side of
                  -- the actual opposite marker q₀.
                  have hKNeQ (u : ℕ) (huK : u ∈ K) : u ≠ q₀ := by
                    intro heq
                    subst u
                    have hc := of_decide_eq_true
                      (List.mem_filter.mp (hKsub q₀ huK)).2
                    have he := (List.mem_filter.mp hqB).2
                    simp [hc] at he
                  have hpq : p ≠ q₀ := hKNeQ p hpK
                  have hOneSideQ :
                      (∀ u ∈ K, u < q₀) ∨ (∀ u ∈ K, q₀ < u) := by
                    rcases lt_or_gt_of_ne hpq with hpq | hqp
                    · left
                      intro u huK
                      by_contra hbad
                      exact hStraddles
                        ⟨⟨p, hpK, hpq⟩,
                          ⟨u, huK, by have := hKNeQ u huK; omega⟩⟩
                    · right
                      intro u huK
                      by_contra hbad
                      exact hStraddles
                        ⟨⟨u, huK, by have := hKNeQ u huK; omega⟩,
                          ⟨p, hpK, hqp⟩⟩
                  have hCompTen : boundFuel g (B.part R t 1) ≤ 10 := by
                    let C := B.part R t 1
                    change boundFuel g C ≤ 10
                    have hPosC := ctx_part_positive_letters B R t 1
                    have hOneC : 1 ∈ C.levels := by
                      simp only [C, Ctx.Context.part_levels, List.mem_cons, true_or]
                    have hpC : p ∈ C.extPositions 1 := by
                      change p ∈ (B.part R t 1).extPositions 1
                      rw [Ctx.Context.part_extPositions_one hPosB]
                      exact List.mem_filter.mpr ⟨hpB, by simp [R, hpK]⟩
                    have hSideOneC : C.sideAt 1 = t :=
                      Ctx.Context.part_sideAt_one_of_mem hPosB R t 1 hpC
                    have hTwoC : 2 ∈ C.levels := by
                      change 2 ∈ (B.part R t 1).levels
                      rw [Ctx.Context.part_levels]
                      exact List.mem_cons_of_mem _
                        (List.mem_map.mpr ⟨1, hOneB, by omega⟩)
                    have hqC : q₀ ∈ C.extPositions 2 := by
                      change q₀ ∈ (B.part R t 1).extPositions 2
                      simpa only [show 2 = 1 + 1 by omega] using
                        (show q₀ ∈ (B.part R t 1).extPositions (1 + 1) by
                          rw [Ctx.Context.part_extPositions_succ B R t 1 (by omega)]
                          exact hqB)
                    have hSideTwoC : C.sideAt 2 = t := by
                      change (B.part R t 1).sideAt 2 = t
                      rw [show 2 = 1 + 1 by omega,
                        Ctx.Context.part_sideAt_succ B R t 1 (by omega)]
                      exact hSideB
                    have hGlobalT : (match t with
                        | Side.lower => C.u | Side.upper => C.a) ≤ 5 := by
                      simpa only [C, B, Ctx.Context.part] using le_of_eq hOppFive
                    have hGlobalS : (match s with
                        | Side.lower => C.u | Side.upper => C.a) ≤ 5 := by
                      simpa only [C, B, Ctx.Context.part] using le_of_eq hChosenFive
                    have hNC : N + 2 ∈ C.levels := by
                      change N + 2 ∈ (B.part R t 1).levels
                      rw [Ctx.Context.part_levels]
                      exact List.mem_cons_of_mem _
                        (List.mem_map.mpr ⟨N + 1, hNB, by omega⟩)
                    have hMC : M + 2 ∈ C.levels := by
                      change M + 2 ∈ (B.part R t 1).levels
                      rw [Ctx.Context.part_levels]
                      exact List.mem_cons_of_mem _
                        (List.mem_map.mpr ⟨M + 1, hMB, by omega⟩)
                    have hxC : x ∈ C.extPositions (N + 2) := by
                      change x ∈ (B.part R t 1).extPositions (N + 2)
                      rw [show N + 2 = (N + 1) + 1 by omega,
                        Ctx.Context.part_extPositions_succ B R t 1
                          (Ctx.Context.one_le_of_mem_levels hNB)]
                      exact hxB
                    have hyC : y ∈ C.extPositions (M + 2) := by
                      change y ∈ (B.part R t 1).extPositions (M + 2)
                      rw [show M + 2 = (M + 1) + 1 by omega,
                        Ctx.Context.part_extPositions_succ B R t 1
                          (Ctx.Context.one_le_of_mem_levels hMB)]
                      exact hyB
                    have hSideNC : C.sideAt (N + 2) = s := by
                      change (B.part R t 1).sideAt (N + 2) = s
                      rw [show N + 2 = (N + 1) + 1 by omega,
                        Ctx.Context.part_sideAt_succ B R t 1
                          (Ctx.Context.one_le_of_mem_levels hNB)]
                      exact hNsB
                    have hSideMC : C.sideAt (M + 2) = s := by
                      change (B.part R t 1).sideAt (M + 2) = s
                      rw [show M + 2 = (M + 1) + 1 by omega,
                        Ctx.Context.part_sideAt_succ B R t 1
                          (Ctx.Context.one_le_of_mem_levels hMB)]
                      exact hMsB
                    have hChosenC : ∀ j ∈ C.levelsOn s 0,
                        ∀ z ∈ C.extPositions j, z = x ∨ z = y := by
                      have hs : C.sideAt 1 ≠ s := by
                        rw [hSideOneC]
                        exact Ne.symm hne
                      intro j hj z hz
                      rw [Ctx.Context.part_levelsOn_other_zero hs] at hj
                      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
                      rw [Ctx.Context.part_extPositions_succ B R t 1
                        (Ctx.Context.one_le_of_mem_levels
                          (List.mem_filter.mp hi).1)] at hz
                      exact hChosenB i hi z hz
                    have hAtLevelC (i j z : ℕ) (hi : z ∈ C.extPositions i)
                        (hj : z ∈ C.extPositions j) : i = j := by
                      have hii := (List.mem_filter.mp hi).2
                      have hjj := (List.mem_filter.mp hj).2
                      cases he : C.letterAt z <;> simp [he] at hii hjj
                      omega
                    have hYoungS : ∀ j ∈ C.levelsOn s (N + 2),
                        C.extPositions j = [] := by
                      intro j hj
                      apply List.eq_nil_iff_forall_not_mem.mpr
                      intro z hz
                      have hjData := List.mem_filter.mp hj
                      have hPred := of_decide_eq_true hjData.2
                      have hjLt : j < N + 2 := by
                        rcases hPred.2 with hzero | hlt
                        · omega
                        · exact hlt
                      have hjOn : j ∈ C.levelsOn s 0 :=
                        List.mem_filter.mpr ⟨hjData.1, by simp [hPred.1]⟩
                      rcases hChosenC j hjOn z hz with hzx | hzy
                      · have he := hAtLevelC j (N + 2) x
                          (by simpa only [hzx] using hz) hxC
                        omega
                      · have he := hAtLevelC j (M + 2) y
                          (by simpa only [hzy] using hz) hyC
                        omega
                    by_cases hAllHighS : ∀ r ∈ C.childPositions,
                        0 < C.cupLimit r r → 0 < C.capLimit r r →
                        3 ≤ (match s with
                          | Side.lower => C.cupLimit r r
                          | Side.upper => C.capLimit r r)
                    · have hh := ctx_all_active_capacity_three_two_marker_triangle_bound
                        C hPosC s t hne (N + 2) (M + 2) x y hNC hMC
                        (by omega) hSideNC hSideMC hxC hyC hYoungS hGlobalS
                        hAllHighS
                      have hChoose : (match t with
                          | Side.lower => C.u | Side.upper => C.a).choose 2 ≤ 10 := by
                        have hc := Nat.choose_le_choose 2 hGlobalT
                        norm_num at hc ⊢
                        exact hc
                      exact (hh.1 g).trans hChoose
                    · push_neg at hAllHighS
                      obtain ⟨lowS, hLowSChild, hLowSCup, hLowSCap,
                        hLowS⟩ := hAllHighS
                      have hLowSTwo : (match s with
                          | Side.lower => C.cupLimit lowS lowS
                          | Side.upper => C.capLimit lowS lowS) ≤ 2 := by
                        omega
                      have hHighSChildC : highS ∈ C.childPositions := by
                        simpa only [C] using hHighSChild
                      have hHighSThreeC : 3 ≤ (match s with
                          | Side.lower => C.cupLimit highS highS
                          | Side.upper => C.capLimit highS highS) := by
                        simpa only [C] using hHighSThree
                      have hSeparatedS :=
                        ctx_mixed_capacity_children_separated_by_older_marker_global_five
                          C s (N + 2) (M + 2) x y highS lowS hNC hMC
                          (by omega) hSideNC hSideMC hxC hyC hGlobalS hChosenC
                          hHighSChildC hLowSChild hHighSThreeC hLowSTwo
                      by_cases hAllHigh : ∀ r ∈ C.childPositions,
                        0 < C.cupLimit r r → 0 < C.capLimit r r →
                        3 ≤ (match t with
                          | Side.lower => C.cupLimit r r
                          | Side.upper => C.capLimit r r)
                      · have hYoung : ∀ j ∈ C.levelsOn t 1,
                            C.extPositions j = [] := by
                          simp only [Ctx.Context.levelsOn_one, List.not_mem_nil,
                            false_implies, implies_true]
                        have hh := ctx_all_active_capacity_three_two_marker_triangle_bound
                          C hPosC t s (Ne.symm hne) 1 2 p q₀ hOneC hTwoC
                          (by omega) hSideOneC hSideTwoC hpC hqC hYoung hGlobalT
                          hAllHigh
                        have hChoose : (match s with
                            | Side.lower => C.u | Side.upper => C.a).choose 2 ≤ 10 := by
                          have hc := Nat.choose_le_choose 2 hGlobalS
                          norm_num at hc ⊢
                          exact hc
                        exact (hh.1 g).trans hChoose
                      · -- Exact remaining swapped-extreme obstruction: the
                        -- companion has mixed/low t-capacity, two nonempty arms
                        -- around the level-one block marker, and that marker
                        -- block lies wholly on one side of q₀ at level two.
                        push_neg at hAllHigh
                        obtain ⟨low, hLowChild, hLowCup, hLowCap, hLow⟩ := hAllHigh
                        have hLowTwo : (match t with
                            | Side.lower => C.cupLimit low low
                            | Side.upper => C.capLimit low low) ≤ 2 := by
                          omega
                        -- Sharp residual: active s-high and s-low witnesses
                        -- are separated by y (hSeparatedS), while an active
                        -- t-low witness remains; both all-high axis cases and
                        -- the all-s-low extreme cut have already closed.
                        sorry
                  exact (Nat.add_le_add (hOwn.1 f) hCompTen).trans (by omega)
              · have hBoundaryR : ∀ q ∈ R, q < p := by
                  intro q hqR
                  rcases hOutside q hqR with hqLeft | hqRight
                  · exact hqLeft p hpK
                  · exact False.elim (hRight ⟨q, hqR, hqRight⟩)
                have hComp := hOppositeBoundaryAnyMaximumNine R p 1 hpB hpNotR
                  true (by simpa only [if_true] using hBoundaryR)
                exact (Nat.add_le_add (hOwn.1 f) (hComp.1 g)).trans (by omega)
            · have hBoundaryR : ∀ q ∈ R, p < q := by
                intro q hqR
                rcases hOutside q hqR with hqLeft | hqRight
                · exact False.elim (hLeft ⟨q, hqR, hqLeft⟩)
                · exact hqRight p hpK
              have hComp := hOppositeBoundaryAnyMaximumNine R p 1 hpB hpNotR
                false hBoundaryR
              exact (Nat.add_le_add (hOwn.1 f) (hComp.1 g)).trans (by omega)
        · have hPosOwn := ctx_part_positive_letters B R s 4
          have hOneOwn : 1 ∈ (B.part R s 4).levels := by
            simp only [Ctx.Context.part_levels, List.mem_cons, true_or]
          have hMaxOwn : (B.part R s 4).k - 2 ≤
              (B.part R s 4).maximumAt 1 := by
            rw [Ctx.Context.part_maximumAt_one]
            change σ.k - 2 ≤ 4
            omega
          have hOwn := ctx_bound_le_one_of_large_sibling_maximum
            (B.part R s 4) hPosOwn 1 hOneOwn hMaxOwn
          have hBoundaryK : ∃ direction : Bool,
              ∀ q ∈ K, if direction then q < z else z < q := by
            by_cases hpz : p < z
            · refine ⟨true, ?_⟩
              intro q hqK
              simp only [if_true]
              by_contra hbad
              have hzq : z ≤ q := Nat.le_of_not_gt hbad
              exact hzNot (hBlockConvex K hK p hpK q hqK z hzB (by omega) hzq)
            · refine ⟨false, ?_⟩
              intro q hqK
              by_contra hbad
              have hqz : q ≤ z := Nat.le_of_not_gt hbad
              exact hzNot (hBlockConvex K hK q hqK p hpK z hzB hqz (by omega))
          obtain ⟨direction, hBoundaryK⟩ := hBoundaryK
          have hComp := hOppositeBoundaryAnyMaximumNine K z 1 hzB hzNot
            direction hBoundaryK
          exact (Nat.add_le_add (hOwn.1 f) (hComp.1 g)).trans (by omega)
      have hBaseB : B.base ≤ 11 := by
        have hMarkerChain (v : Side) (J z p : ℕ)
            (hJ : J ∈ B.levels) (hJv : B.sideAt J = v)
            (hz : z ∈ B.extPositions J) (hp : p ∈ B.childPositions) :
            1 ≤ B.chainExt v p p := by
          have hJOn : J ∈ B.levelsOn v 0 :=
            List.mem_filter.mpr ⟨hJ, by simp [hJv]⟩
          have hpz : p ≠ z := by
            intro heq
            subst p
            have hc := of_decide_eq_true (List.mem_filter.mp hp).2
            have he := (List.mem_filter.mp hz).2
            simp [hc] at he
          rcases lt_or_gt_of_ne hpz with hpz | hzp
          · have hm : z ∈ (B.extPositions J).filter (p < ·) := by
              simp [hz, hpz]
            have hnonempty := List.ne_nil_of_mem hm
            have hv := le_getD_max?_of_mem
              (L := (B.levelsOn v 0).sublists.map
                (fun ls => (ls.foldl (rightStep B) (p, 0)).2))
              (List.mem_map.mpr ⟨[J],
                List.mem_sublists.mpr (List.singleton_sublist.mpr hJOn), rfl⟩)
            change _ ≤ B.rightExt v 0 p at hv
            have hr : 1 ≤ B.rightExt v 0 p := by
              simpa only [List.foldl_cons, List.foldl_nil, rightStep,
                List.head?_eq_some_head hnonempty] using hv
            simp only [chainExt]
            omega
          · have hm : z ∈ (B.extPositions J).filter (· < p) := by
              simp [hz, hzp]
            have hnonempty := List.ne_nil_of_mem hm
            have hv := le_getD_max?_of_mem
              (L := (B.levelsOn v 0).sublists.map
                (fun ls => (ls.foldl (leftStep B) (p, 0)).2))
              (List.mem_map.mpr ⟨[J],
                List.mem_sublists.mpr (List.singleton_sublist.mpr hJOn), rfl⟩)
            change _ ≤ B.leftExt v 0 p at hv
            have hl : 1 ≤ B.leftExt v 0 p := by
              simpa only [List.foldl_cons, List.foldl_nil, leftStep,
                List.getLast?_eq_some_getLast hnonempty] using hv
            simp only [chainExt]
            omega
        rw [Ctx.Context.base_eq_baseOf]
        cases he : B.childPositions.head? with
        | none => exact Nat.zero_le _
        | some p =>
          change Ctx.Context.baseOf (B.cupLimit p p) (B.capLimit p p) B.k ≤ 11
          have hp := List.mem_of_mem_head? (Option.mem_def.mpr he)
          have hsChain := hMarkerChain s (N + 1) x p hNB hNsB hxB hp
          have htChain := hMarkerChain t 1 q₀ p hOneB hSideB hqB hp
          have hCup : B.cupLimit p p ≤ 3 := by
            cases s <;> cases t
            · exact (hne rfl).elim
            · change min (B.u - 1 - B.chainExt Side.lower p p)
                  (B.k - 1 - B.joinExt Side.lower p p) ≤ 3
              have hGlobal : B.u = 5 := by simpa using hChosenFive
              exact (Nat.min_le_left _ _).trans (by omega)
            · change min (B.u - 1 - B.chainExt Side.lower p p)
                  (B.k - 1 - B.joinExt Side.lower p p) ≤ 3
              have hGlobal : B.u = 5 := by simpa using hOppFive
              exact (Nat.min_le_left _ _).trans (by omega)
            · exact (hne rfl).elim
          have hCap : B.capLimit p p ≤ 3 := by
            cases s <;> cases t
            · exact (hne rfl).elim
            · change min (B.a - 1 - B.chainExt Side.upper p p)
                  (B.k - 1 - B.joinExt Side.upper p p) ≤ 3
              have hGlobal : B.a = 5 := by simpa using hOppFive
              exact (Nat.min_le_left _ _).trans (by omega)
            · change min (B.a - 1 - B.chainExt Side.upper p p)
                  (B.k - 1 - B.joinExt Side.upper p p) ≤ 3
              have hGlobal : B.a = 5 := by simpa using hChosenFive
              exact (Nat.min_le_left _ _).trans (by omega)
            · exact (hne rfl).elim
          have hh := Ctx.Context.baseOf_mono (k := B.k) hCup hCap
          have hkB : B.k = 6 := by
            change σ.k = 6
            exact hk
          rw [hkB] at hh ⊢
          exact hh.trans (by decide)
      have hRecursiveEleven :
          (∀ fuel, boundFuel fuel B ≤ 11) ∧ B.bound ≤ 11 := by
        have hFuel : ∀ fuel, boundFuel fuel B ≤ 11 := by
          intro fuel
          cases fuel with
          | zero => exact Nat.zero_le _
          | succ fuel =>
            rw [boundFuel]
            split
            · exact hBaseB
            · apply Ctx.getD_max?_le
              intro value hvalue
              simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil,
                or_false] at hvalue
              obtain ⟨K, hK, d, hd, hvalue⟩ := hvalue
              have hd' := List.mem_range.mp hd
              let R := B.childPositions.filter (· ∉ K)
              have hCuts :
                  boundFuel fuel (B.part K Side.lower (d + 1)) +
                      boundFuel fuel (B.part R Side.upper
                        (B.k - 1 - (d + 1))) ≤ 11 ∧
                    boundFuel fuel (B.part K Side.upper
                        (B.k - 1 - (d + 1))) +
                      boundFuel fuel (B.part R Side.lower (d + 1)) ≤ 11 := by
                have hkB : B.k = 6 := by
                  change σ.k = 6
                  exact hk
                have hdLe : d ≤ 3 := by
                  rw [hkB] at hd'
                  omega
                cases s <;> cases t
                · exact False.elim (hne rfl)
                · interval_cases d
                  · have hh := hExtremeBlockCut K hK fuel fuel
                    simpa only [R, hkB, Nat.add_comm] using
                      And.intro hh.1 (by simpa only [Nat.add_comm] using hh.2)
                  · have hh := hMiddleBlockCut K hK fuel fuel
                    simpa only [R, hkB, Nat.add_comm] using
                      And.intro hh.1 (by simpa only [Nat.add_comm] using hh.2)
                  · have hh := hCentralBlockCut K hK fuel fuel
                    simpa only [R, hkB, Nat.add_comm] using
                      And.intro hh.1 (by simpa only [Nat.add_comm] using hh.2)
                  · have hh := hSwappedExtremeBlockCut K hK fuel fuel
                    simpa only [R, hkB, Nat.add_comm] using
                      And.intro hh.1 (by simpa only [Nat.add_comm] using hh.2)
                · interval_cases d
                  · have hh := hSwappedExtremeBlockCut K hK fuel fuel
                    simpa only [R, hkB, Nat.add_comm] using
                      And.intro (by simpa only [Nat.add_comm] using hh.2) hh.1
                  · have hh := hCentralBlockCut K hK fuel fuel
                    simpa only [R, hkB, Nat.add_comm] using
                      And.intro (by simpa only [Nat.add_comm] using hh.2) hh.1
                  · have hh := hMiddleBlockCut K hK fuel fuel
                    simpa only [R, hkB, Nat.add_comm] using
                      And.intro (by simpa only [Nat.add_comm] using hh.2) hh.1
                  · have hh := hExtremeBlockCut K hK fuel fuel
                    simpa only [R, hkB, Nat.add_comm] using
                      And.intro (by simpa only [Nat.add_comm] using hh.2) hh.1
                · exact False.elim (hne rfl)
              rcases hvalue with rfl | rfl
              · exact hCuts.1
              · exact hCuts.2
        exact ⟨hFuel, hFuel (B.childPositions.length + 1)⟩
      have hNearYoungerBoundaryMaximumTwoSeven
          (K : List ℕ) (z : ℕ)
          (hzB : z ∈ B.childPositions) (hzNot : z ∉ K)
          (hNear : ((∀ p ∈ K, p < x) ∧ z < x) ∨
            ((∀ p ∈ K, x < p) ∧ x < z)) :
          let C := B.part K s 2
          (∀ fuel, boundFuel fuel C ≤ 7) ∧ C.bound ≤ 7 := by
        classical
        let C := B.part K s 2
        let ρ : Context := { C with
          word := (List.range C.word.length).map (fun p =>
            match C.letterAt p with
            | Letter.child => Letter.child
            | Letter.ext j v => if j = 1 then
                if p ∈ [z] then Letter.ext 1 (C.sideAt 1)
                else Letter.ext (C.maxima.length + 1) v
              else Letter.ext j v) }
        change (∀ fuel, boundFuel fuel C ≤ 7) ∧ C.bound ≤ 7
        have hPosC := ctx_part_positive_letters B K s 2
        have hOneC : 1 ∈ C.levels := by
          simp only [C, Ctx.Context.part_levels, List.mem_cons, true_or]
        have hzC : z ∈ C.extPositions 1 := by
          change z ∈ (B.part K s 2).extPositions 1
          rw [Ctx.Context.part_extPositions_one hPosB]
          exact List.mem_filter.mpr ⟨hzB, by simpa⟩
        have hSideOneC : C.sideAt 1 = s :=
          Ctx.Context.part_sideAt_one_of_mem hPosB K s 2 hzC
        have hNC : N + 2 ∈ C.levels := by
          change N + 2 ∈ (B.part K s 2).levels
          rw [Ctx.Context.part_levels]
          exact List.mem_cons_of_mem _
            (List.mem_map.mpr ⟨N + 1, hNB, by omega⟩)
        have hSideNC : C.sideAt (N + 2) = s := by
          change (B.part K s 2).sideAt (N + 2) = s
          rw [show N + 2 = (N + 1) + 1 by omega,
            Ctx.Context.part_sideAt_succ B K s 2
              (Ctx.Context.one_le_of_mem_levels hNB)]
          exact hNsB
        have hxC : x ∈ C.extPositions (N + 2) := by
          change x ∈ (B.part K s 2).extPositions (N + 2)
          rw [show N + 2 = (N + 1) + 1 by omega,
            Ctx.Context.part_extPositions_succ B K s 2
              (Ctx.Context.one_le_of_mem_levels hNB)]
          exact hxB
        have hp := ctx_single_level_occurrence_prune_bound_mono
          C hPosC 1 hOneC [z] z hzC (by simp)
        have hPosρ : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j := hp.1
        have hChildρ : ρ.childPositions = C.childPositions := hp.2.1
        have hHistρ : ∀ j ∈ C.levels,
            ρ.sideAt j = C.sideAt j ∧ ρ.maximumAt j = C.maximumAt j ∧
              ρ.extPositions j = if j = 1 then
                (C.extPositions j).filter (· ∈ [z]) else C.extPositions j :=
          hp.2.2.1
        have hFuelρ : ∀ fuel, boundFuel fuel C ≤ boundFuel fuel ρ :=
          hp.2.2.2.2.2.1
        have hBoundρ : C.bound ≤ ρ.bound := hp.2.2.2.2.2.2
        have hOneρ : 1 ∈ ρ.levels := hOneC
        have hNρ : N + 2 ∈ ρ.levels := hNC
        have hSideOneρ : ρ.sideAt 1 = s :=
          (hHistρ 1 hOneC).1.trans hSideOneC
        have hSideNρ : ρ.sideAt (N + 2) = s :=
          (hHistρ (N + 2) hNC).1.trans hSideNC
        have hzρ : z ∈ ρ.extPositions 1 := by
          rw [(hHistρ 1 hOneC).2.2, if_pos rfl]
          simp [hzC]
        have hxρ : x ∈ ρ.extPositions (N + 2) := by
          rw [(hHistρ (N + 2) hNC).2.2, if_neg (by omega)]
          exact hxC
        have hChildC (p : ℕ) (hpC : p ∈ C.childPositions) : p ∈ K := by
          exact of_decide_eq_true
            (List.mem_filter.mp (show p ∈ B.childPositions.filter (· ∈ K) by
              simpa only [C, Ctx.Context.part_childPositions] using hpC)).2
        have hAtLevel (i j p : ℕ) (hi : p ∈ B.extPositions i)
            (hj : p ∈ B.extPositions j) : i = j := by
          have hi' := (List.mem_filter.mp hi).2
          have hj' := (List.mem_filter.mp hj).2
          cases he : B.letterAt p <;> simp [he] at hi' hj'
          omega
        have hYoung (direction : Bool)
            (hzSide : if direction then z < x else x < z) :
            ∀ j ∈ ρ.levelsOn (ρ.sideAt (N + 2)) (N + 2),
              ∀ p ∈ ρ.extPositions j,
                if direction then p < x else x < p := by
          intro j hj p hpj
          have hjData := of_decide_eq_true (List.mem_filter.mp hj).2
          have hjLevelρ := (List.mem_filter.mp hj).1
          have hjLevelC : j ∈ C.levels := hjLevelρ
          by_cases hjOne : j = 1
          · subst j
            rw [(hHistρ 1 hOneC).2.2, if_pos rfl] at hpj
            have hpz := List.mem_singleton.mp
              (of_decide_eq_true (List.mem_filter.mp hpj).2)
            simpa only [hpz] using hzSide
          · have hpC : p ∈ C.extPositions j := by
              rw [(hHistρ j hjLevelC).2.2, if_neg hjOne] at hpj
              exact hpj
            have hjs : C.sideAt j = s := by
              have hsρ : ρ.sideAt j = ρ.sideAt (N + 2) := hjData.1
              rw [(hHistρ j hjLevelC).1, hSideNρ] at hsρ
              exact hsρ
            have hjOld : ∃ i ∈ B.levels, j = i + 1 := by
              change j ∈ (B.part K s 2).levels at hjLevelC
              rw [Ctx.Context.part_levels] at hjLevelC
              rcases List.mem_cons.mp hjLevelC with hj | hj
              · exact False.elim (hjOne hj)
              · obtain ⟨i, hi, hij⟩ := List.mem_map.mp hj
                exact ⟨i, hi, hij.symm⟩
            obtain ⟨i, hi, rfl⟩ := hjOld
            have hiPos := Ctx.Context.one_le_of_mem_levels hi
            have hiSide : B.sideAt i = s := by
              have hs := hjs
              change (B.part K s 2).sideAt (i + 1) = s at hs
              rw [Ctx.Context.part_sideAt_succ B K s 2 hiPos] at hs
              exact hs
            have hiOn : i ∈ B.levelsOn s 0 :=
              List.mem_filter.mpr ⟨hi, by simp [hiSide]⟩
            have hpB : p ∈ B.extPositions i := by
              change p ∈ (B.part K s 2).extPositions (i + 1) at hpC
              rw [Ctx.Context.part_extPositions_succ B K s 2 hiPos] at hpC
              exact hpC
            rcases hChosenB i hiOn p hpB with hpx | hpy
            · subst p
              have hiN := hAtLevel i (N + 1) x hpB hxB
              omega
            · subst p
              have hiM := hAtLevel i (M + 1) y hpB hyB
              omega
        have hRaw (direction : Bool)
            (hChildren : ∀ p ∈ ρ.childPositions,
              if direction then p < x else x < p)
            (hzSide : if direction then z < x else x < z) :
            (∀ fuel, boundFuel fuel ρ ≤ 7) ∧ ρ.bound ≤ 7 := by
          have hh := ctx_boundary_retained_doubled_rank_budget
            ρ hPosρ (N + 2) 1 x z hNρ hOneρ (by omega) hxρ hzρ
            (hSideOneρ.trans hSideNρ.symm) direction hChildren
            (hYoung direction hzSide) t (by rw [hSideNρ]; exact hne)
            (by
              rw [hSideNρ]
              cases s <;> simpa only [ρ, C, B, Ctx.Context.part] using
                le_of_eq hChosenFive)
            0 0 (by intros; omega) (by intros; omega)
          have hSeven : 2 * ((match t with
                | Side.lower => ρ.u | Side.upper => ρ.a) - 1 - 0 - 0) - 1 ≤ 7 := by
            cases t <;>
              simp only [ρ, C, B, Ctx.Context.part] at hOppFive ⊢ <;> omega
          exact ⟨fun fuel => (hh.1 fuel).trans hSeven, hh.2.trans hSeven⟩
        have hρ : (∀ fuel, boundFuel fuel ρ ≤ 7) ∧ ρ.bound ≤ 7 := by
          rcases hNear with ⟨hKLeft, hzx⟩ | ⟨hKRight, hxz⟩
          · exact hRaw true
              (by
                intro p hpρ
                rw [hChildρ] at hpρ
                exact hKLeft p (hChildC p hpρ)) hzx
          · exact hRaw false
              (by
                intro p hpρ
                rw [hChildρ] at hpρ
                exact hKRight p (hChildC p hpρ)) hxz
        exact ⟨fun fuel => (hFuelρ fuel).trans (hρ.1 fuel),
          hBoundρ.trans hρ.2⟩
      have hSourceLowMaximumTwoSeven
          (K : List ℕ)
          (hLowK : ∀ p ∈ K, (match s with
            | Side.lower => B.cupLimit p p
            | Side.upper => B.capLimit p p) ≤ 2) :
          let C := B.part K s 2
          (∀ fuel, boundFuel fuel C ≤ 7) ∧ C.bound ≤ 7 := by
        classical
        let C := B.part K s 2
        let P : Context := { B with
          word := (List.range B.word.length).map (fun p =>
            match B.letterAt p with
            | Letter.child => if p ∈ K then Letter.child
                else Letter.ext (B.maxima.length + 1) s
            | Letter.ext j v => Letter.ext j v) }
        change (∀ fuel, boundFuel fuel C ≤ 7) ∧ C.bound ≤ 7
        have ht := ctx_part_pruning_history_transport B hPosB K s 2
        have hPosP : ∀ p j v, P.letterAt p = Letter.ext j v → 1 ≤ j := ht.1
        have hChildP : P.childPositions = B.childPositions.filter (· ∈ K) := ht.2.1
        have hHistP : ∀ j ∈ B.levels,
            P.extPositions j = B.extPositions j ∧ P.sideAt j = B.sideAt j :=
          ht.2.2.1
        have hLevelsP : ∀ v top, P.levelsOn v top = B.levelsOn v top :=
          ht.2.2.2.1
        have hFuelP : ∀ fuel, boundFuel fuel C ≤ boundFuel fuel P :=
          ht.2.2.2.2.2.2.2.1
        have hBoundP : C.bound ≤ P.bound := ht.2.2.2.2.2.2.2.2
        have hNP : N + 1 ∈ P.levels := hNB
        have hMP : M + 1 ∈ P.levels := hMB
        have hSideNP : P.sideAt (N + 1) = s :=
          (hHistP (N + 1) hNB).2.trans hNsB
        have hSideMP : P.sideAt (M + 1) = s :=
          (hHistP (M + 1) hMB).2.trans hMsB
        have hxP : x ∈ P.extPositions (N + 1) := by
          rw [(hHistP (N + 1) hNB).1]
          exact hxB
        have hyP : y ∈ P.extPositions (M + 1) := by
          rw [(hHistP (M + 1) hMB).1]
          exact hyB
        have hChildData (p : ℕ) (hp : p ∈ P.childPositions) :
            p ∈ B.childPositions ∧ p ∈ K := by
          rw [hChildP] at hp
          exact ⟨(List.mem_filter.mp hp).1,
            of_decide_eq_true (List.mem_filter.mp hp).2⟩
        have hAtLevel (i j p : ℕ) (hi : p ∈ B.extPositions i)
            (hj : p ∈ B.extPositions j) : i = j := by
          have hi' := (List.mem_filter.mp hi).2
          have hj' := (List.mem_filter.mp hj).2
          cases he : B.letterAt p <;> simp [he] at hi' hj'
          omega
        have hBound (direction : Bool)
            (hxy : if direction then x < y else y < x)
            (hchildren : ∀ p ∈ P.childPositions,
              if direction then p < y else y < p) :
            (∀ fuel, boundFuel fuel P ≤ 7) ∧ P.bound ≤ 7 := by
          have hYoung : ∀ j ∈ P.levelsOn (P.sideAt (M + 1)) (M + 1),
              ∀ p ∈ P.extPositions j,
                if direction then p < y else y < p := by
            rw [hSideMP]
            intro j hj p hp
            rw [hLevelsP s (M + 1)] at hj
            have hjData := of_decide_eq_true (List.mem_filter.mp hj).2
            have hjOn : j ∈ B.levelsOn s 0 :=
              List.mem_filter.mpr ⟨(List.mem_filter.mp hj).1,
                by simp [hjData.1]⟩
            rw [(hHistP j (List.mem_filter.mp hj).1).1] at hp
            rcases hChosenB j hjOn p hp with hpx | hpy
            · simpa only [hpx] using hxy
            · have hjM := hAtLevel j (M + 1) y (by simpa only [hpy] using hp) hyB
              omega
          have hh := ctx_boundary_retained_doubled_rank_budget
            P hPosP (M + 1) (N + 1) y x hMP hNP (by omega) hyP hxP
            (hSideNP.trans hSideMP.symm) direction hchildren hYoung t
            (by rw [hSideMP]; exact hne)
            (by
              rw [hSideMP]
              cases s <;> simpa only [P, B, Ctx.Context.part] using
                le_of_eq hChosenFive)
            0 0 (by intros; omega) (by intros; omega)
          have hSeven : 2 * ((match t with
                | Side.lower => P.u | Side.upper => P.a) - 1 - 0 - 0) - 1 ≤ 7 := by
            cases t <;>
              simp only [P, B, Ctx.Context.part] at hOppFive ⊢ <;> omega
          exact ⟨fun fuel => (hh.1 fuel).trans hSeven, hh.2.trans hSeven⟩
        have hP : (∀ fuel, boundFuel fuel P ≤ 7) ∧ P.bound ≤ 7 := by
          rcases ctx_capacity_three_children_exterior_of_two_levels_global_five
              B s (N + 1) (M + 1) x y hNB hMB (by omega) hNsB hMsB
              hxB hyB (le_of_eq hChosenFive) with hForward | hBackward
          · apply hBound true (by simpa only [if_true] using hForward.1)
            intro p hp
            have hpData := hChildData p hp
            have hsep := ctx_mixed_capacity_children_separated_by_older_marker_global_five
              B s (N + 1) (M + 1) x y high p hNB hMB (by omega)
              hNsB hMsB hxB hyB (le_of_eq hChosenFive) hChosenB
              hHighMem hpData.1 hHigh (hLowK p hpData.2)
            rcases hsep with hh | hh
            · simpa only [if_true] using hh.2.1
            · omega
          · apply hBound false (by simpa only [if_false] using hBackward.1)
            intro p hp
            have hpData := hChildData p hp
            have hsep := ctx_mixed_capacity_children_separated_by_older_marker_global_five
              B s (N + 1) (M + 1) x y high p hNB hMB (by omega)
              hNsB hMsB hxB hyB (le_of_eq hChosenFive) hChosenB
              hHighMem hpData.1 hHigh (hLowK p hpData.2)
            rcases hsep with hh | hh
            · omega
            · simpa only [if_false] using hh.2.2
        exact ⟨fun fuel => (hFuelP fuel).trans (hP.1 fuel),
          hBoundP.trans hP.2⟩
      have hCapacityBoundaryEleven
          (hHighBoundary :
            (∀ p ∈ B.childPositions,
                3 ≤ (match s with
                  | Side.lower => B.cupLimit p p
                  | Side.upper => B.capLimit p p) → p < q₀) ∨
              (∀ p ∈ B.childPositions,
                3 ≤ (match s with
                  | Side.lower => B.cupLimit p p
                  | Side.upper => B.capLimit p p) → q₀ < p)) :
          (∀ fuel, boundFuel fuel B ≤ 11) ∧ B.bound ≤ 11 := by
        classical
        let C (p : ℕ) := match s with
          | Side.lower => B.cupLimit p p
          | Side.upper => B.capLimit p p
        let color (p : ℕ) := if C p ≤ 2 then (0 : ℕ) else 1
        let support (c : ℕ) := B.childPositions.filter (fun p => color p = c)
        let group (c : ℕ) : Context := { B with
          word := (List.range B.word.length).map (fun p => match B.letterAt p with
            | Letter.child => if p ∈ support c then Letter.child
                else Letter.ext (B.maxima.length + 1) Side.lower
            | Letter.ext j v => Letter.ext j v) }
        let G := match t with | Side.lower => B.u | Side.upper => B.a
        let active (c : ℕ) := (group c).childPositions.toFinset.filter
          (fun p => 0 < (group c).cupLimit p p ∧ 0 < (group c).capLimit p p)
        let I (c p : ℕ) := Finset.Icc ((group c).leftExt t 0 p + 1)
          (G - 1 - (group c).rightExt t 0 p)
        let Q (S : Finset ℕ) := (S.product S).filter (fun w => w.1 ≤ w.2)
        let pairs (c : ℕ) := (active c).biUnion (fun p => Q (I c p))
        have hCover : ∀ p ∈ B.childPositions,
            color p ∈ ({0, 1} : Finset ℕ) := by
          intro p hp
          dsimp only [color]
          split_ifs <;> simp
        have hColor : ∀ p ∈ B.childPositions, ∀ q ∈ B.childPositions,
            p ≤ q → (∀ r, p ≤ r → r ≤ q → r ∈ B.childPositions) →
            color p = color q := by
          intro p hp q hq hpq hinterval
          have hh := ctx_point_limits_eq_of_child_interval B p q hp hq hpq hinterval
          have hC : C p = C q := by
            cases s with
            | lower => simpa only [C] using hh.1
            | upper => simpa only [C] using hh.2
          simp only [color, hC]
        have hDecomp :=
          ctx_bound_le_sum_run_group_prunings_of_actual_marker_global_five
            B hPosB s (N + 1) x hNB hNsB hxB
            (by cases s <;> exact le_of_eq hChosenFive)
            color ({0, 1} : Finset ℕ) hCover hColor
        change (∀ fuel, boundFuel fuel B ≤
            ({0, 1} : Finset ℕ).sum (fun c => (group c).bound)) ∧
          B.bound ≤ ({0, 1} : Finset ℕ).sum
            (fun c => (group c).bound) at hDecomp
        have hTransport (c : ℕ) :=
          ctx_part_pruning_history_transport B hPosB (support c) Side.lower 0
        have hChild (c p : ℕ) : p ∈ (group c).childPositions ↔
            p ∈ B.childPositions ∧ color p = c := by
          have hh := (hTransport c).2.1
          change (group c).childPositions =
            B.childPositions.filter (· ∈ support c) at hh
          rw [hh]
          simp [support]
        have hHist (c j : ℕ) (hj : j ∈ B.levels) :
            (group c).extPositions j = B.extPositions j ∧
              (group c).sideAt j = B.sideAt j :=
          (hTransport c).2.2.1 j hj
        have hLevels (c : ℕ) (v : Side) (top : ℕ) :
            (group c).levelsOn v top = B.levelsOn v top :=
          (hTransport c).2.2.2.1 v top
        have hBoundaryLow :
            (∀ p ∈ (group 0).childPositions, p < q₀) ∨
              (∀ p ∈ (group 0).childPositions, q₀ < p) := by
          rcases hexterior with ⟨hxy, hright⟩ | ⟨hyx, hleft⟩
          · left
            intro p hp
            have hpData := (hChild 0 p).mp hp
            have hLowP : C p ≤ 2 := by
              have hc := hpData.2
              dsimp only [color] at hc
              by_cases hle : C p ≤ 2
              · exact hle
              · simp [hle] at hc
            have hsep := ctx_mixed_capacity_children_separated_by_older_marker_global_five
              B s (N + 1) (M + 1) x y high p hNB hMB (by omega)
              hNsB hMsB hxB hyB (by cases s <;> exact le_of_eq hChosenFive)
              hChosenB hHighMem hpData.1 hHigh hLowP
            have hqRight := hright q₀ hq₀
            rcases hsep with hsep | hsep <;> omega
          · right
            intro p hp
            have hpData := (hChild 0 p).mp hp
            have hLowP : C p ≤ 2 := by
              have hc := hpData.2
              dsimp only [color] at hc
              by_cases hle : C p ≤ 2
              · exact hle
              · simp [hle] at hc
            have hsep := ctx_mixed_capacity_children_separated_by_older_marker_global_five
              B s (N + 1) (M + 1) x y high p hNB hMB (by omega)
              hNsB hMsB hxB hyB (by cases s <;> exact le_of_eq hChosenFive)
              hChosenB hHighMem hpData.1 hHigh hLowP
            have hqLeft := hleft q₀ hq₀
            rcases hsep with hsep | hsep <;> omega
        have hLow : (∀ fuel, boundFuel fuel (group 0) ≤ 5) ∧
            (group 0).bound ≤ 5 := by
          have hh := ctx_two_marker_low_capacity_pruning_five_bound_of_opposite_boundary
            B hPosB s t hne (N + 1) (M + 1) x y high 1 q₀
            hNB hMB (by omega) hNsB hMsB hxB hyB
            (by cases s <;> exact le_of_eq hChosenFive)
            (by cases t <;> simpa only [B, Ctx.Context.part] using hopposite)
            hChosenB hHighMem hHigh hOneB hSideB hqB (by omega)
          have hh' := hh (by simpa [C, color, support, group] using hBoundaryLow)
          simpa [C, color, support, group] using hh'
        have hHighPairs :
            (∀ fuel, boundFuel fuel (group 1) ≤ (pairs 1).card) ∧
              (group 1).bound ≤ (pairs 1).card := by
          cases s with
          | lower =>
              cases t with
              | lower => exact (hne rfl).elim
              | upper =>
                  simpa only [C, color, support, group, G, active, I, Q, pairs] using
                    (ctx_two_marker_high_capacity_pruning_rank_pair_bound_of_high_witness
                      B hPosB Side.lower Side.upper hne (N + 1) (M + 1)
                      x y high hNB hMB (by omega) hNsB hMsB hxB hyB
                      (le_of_eq hChosenFive) hChosenB hHighMem hHigh)
          | upper =>
              cases t with
              | lower =>
                  simpa only [C, color, support, group, G, active, I, Q, pairs] using
                    (ctx_two_marker_high_capacity_pruning_rank_pair_bound_of_high_witness
                      B hPosB Side.upper Side.lower hne (N + 1) (M + 1)
                      x y high hNB hMB (by omega) hNsB hMsB hxB hyB
                      (le_of_eq hChosenFive) hChosenB hHighMem hHigh)
              | upper => exact (hne rfl).elim
        have hqGroup : q₀ ∈ (group 1).extPositions 1 := by
          rw [(hHist 1 1 hOneB).1]
          exact hqB
        have hSideGroup : (group 1).sideAt 1 = t :=
          (hHist 1 1 hOneB).2.trans hSideB
        have hOneOn : 1 ∈ (group 1).levelsOn t 0 :=
          List.mem_filter.mpr ⟨hOneB, by simp [hSideGroup]⟩
        have hOneLeft (p : ℕ) (hp : q₀ < p) :
            1 ≤ (group 1).leftExt t 0 p := by
          have hm : q₀ ∈ ((group 1).extPositions 1).filter (· < p) := by
            simp [hqGroup, hp]
          have hnonempty := List.ne_nil_of_mem hm
          have hv := le_getD_max?_of_mem
            (L := ((group 1).levelsOn t 0).sublists.map
              (fun ls => (ls.foldl (leftStep (group 1)) (p, 0)).2))
            (List.mem_map.mpr ⟨[1],
              List.mem_sublists.mpr (List.singleton_sublist.mpr hOneOn), rfl⟩)
          change _ ≤ (group 1).leftExt t 0 p at hv
          simpa only [List.foldl_cons, List.foldl_nil, leftStep,
            List.getLast?_eq_some_getLast hnonempty] using hv
        have hOneRight (p : ℕ) (hp : p < q₀) :
            1 ≤ (group 1).rightExt t 0 p := by
          have hm : q₀ ∈ ((group 1).extPositions 1).filter (p < ·) := by
            simp [hqGroup, hp]
          have hnonempty := List.ne_nil_of_mem hm
          have hv := le_getD_max?_of_mem
            (L := ((group 1).levelsOn t 0).sublists.map
              (fun ls => (ls.foldl (rightStep (group 1)) (p, 0)).2))
            (List.mem_map.mpr ⟨[1],
              List.mem_sublists.mpr (List.singleton_sublist.mpr hOneOn), rfl⟩)
          change _ ≤ (group 1).rightExt t 0 p at hv
          simpa only [List.foldl_cons, List.foldl_nil, rightStep,
            List.head?_eq_some_head hnonempty] using hv
        have hGEq : G = 5 := by
          cases t <;> simpa only [G, B, Ctx.Context.part] using hOppFive
        have hHighChild (p : ℕ) (hp : p ∈ (group 1).childPositions) :
            p ∈ B.childPositions ∧ 3 ≤ C p := by
          have hpData := (hChild 1 p).mp hp
          refine ⟨hpData.1, ?_⟩
          have hc := hpData.2
          dsimp only [color] at hc
          by_cases hle : C p ≤ 2
          · simp [hle] at hc
          · omega
        have hPairsInside (T : Finset ℕ)
            (hInside : ∀ p ∈ (group 1).childPositions, I 1 p ⊆ T) :
            pairs 1 ⊆ Q T := by
          intro w hw
          obtain ⟨p, hp, hw⟩ := Finset.mem_biUnion.mp hw
          have hpChild : p ∈ (group 1).childPositions :=
            List.mem_toFinset.mp (Finset.mem_filter.mp hp).1
          have hpair := Finset.mem_filter.mp hw
          have hcoords := Finset.mem_product.mp hpair.1
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr
              ⟨hInside p hpChild hcoords.1, hInside p hpChild hcoords.2⟩,
              hpair.2⟩
        have hPairCard : (pairs 1).card ≤ 6 := by
          rcases hHighBoundary with hleft | hright
          · let T := Finset.Icc 1 3
            have hSub : pairs 1 ⊆ Q T := hPairsInside T (by
              intro p hp r hr
              have hpData := hHighChild p hp
              have hpq := hleft p hpData.1 hpData.2
              have hrightExt := hOneRight p hpq
              have hrData := Finset.mem_Icc.mp hr
              apply Finset.mem_Icc.mpr
              exact ⟨by omega, by omega⟩)
            have hCard : (Q T).card ≤ 6 := by
              change ({w ∈ (Finset.Icc 1 3).product (Finset.Icc 1 3) |
                w.1 ≤ w.2} : Finset (ℕ × ℕ)).card ≤ 6
              decide
            exact (Finset.card_le_card hSub).trans hCard
          · let T := Finset.Icc 2 4
            have hSub : pairs 1 ⊆ Q T := hPairsInside T (by
              intro p hp r hr
              have hpData := hHighChild p hp
              have hqp := hright p hpData.1 hpData.2
              have hleftExt := hOneLeft p hqp
              have hrData := Finset.mem_Icc.mp hr
              apply Finset.mem_Icc.mpr
              exact ⟨by omega, by omega⟩)
            have hCard : (Q T).card ≤ 6 := by
              change ({w ∈ (Finset.Icc 2 4).product (Finset.Icc 2 4) |
                w.1 ≤ w.2} : Finset (ℕ × ℕ)).card ≤ 6
              decide
            exact (Finset.card_le_card hSub).trans hCard
        have hHighSix : (∀ fuel, boundFuel fuel (group 1) ≤ 6) ∧
            (group 1).bound ≤ 6 :=
          ⟨fun fuel => (hHighPairs.1 fuel).trans hPairCard,
            hHighPairs.2.trans hPairCard⟩
        have hGroups : (group 0).bound + (group 1).bound ≤ 11 := by
          omega
        constructor
        · intro fuel
          have hh := hDecomp.1 fuel
          simpa using hh.trans hGroups
        · have hh := hDecomp.2
          simpa using hh.trans hGroups
      by_cases hHighBoundary :
          (∀ p ∈ B.childPositions,
              3 ≤ (match s with
                | Side.lower => B.cupLimit p p
                | Side.upper => B.capLimit p p) → p < q₀) ∨
            (∀ p ∈ B.childPositions,
              3 ≤ (match s with
                | Side.lower => B.cupLimit p p
                | Side.upper => B.capLimit p p) → q₀ < p)
      · have hB := hCapacityBoundaryEleven hHighBoundary
        exact ⟨fun f g => (Nat.add_le_add (hA.1 f) (hB.1 g)).trans (by omega),
          (Nat.add_le_add hA.2 hB.2).trans (by omega)⟩
      · rcases not_or.mp hHighBoundary with ⟨hnotLeft, hnotRight⟩
        push_neg at hnotLeft hnotRight
        obtain ⟨highRight, hHighRightB, hHighRight, hHighRightNot⟩ := hnotLeft
        obtain ⟨highLeft, hHighLeftB, hHighLeft, hHighLeftNot⟩ := hnotRight
        have hHighRightNe : highRight ≠ q₀ := by
          intro heq
          subst highRight
          have hc := of_decide_eq_true (List.mem_filter.mp hHighRightB).2
          have he := (List.mem_filter.mp hqB).2
          simp [hc] at he
        have hHighLeftNe : highLeft ≠ q₀ := by
          intro heq
          subst highLeft
          have hc := of_decide_eq_true (List.mem_filter.mp hHighLeftB).2
          have he := (List.mem_filter.mp hqB).2
          simp [hc] at he
        have hHighStraddle : highLeft < q₀ ∧ q₀ < highRight := by
          omega
        exact ⟨fun f g =>
            (Nat.add_le_add (hA.1 f) (hRecursiveEleven.1 g)).trans (by omega),
          (Nat.add_le_add hA.2 hRecursiveEleven.2).trans (by omega)⟩

end ErdosSzekeres
