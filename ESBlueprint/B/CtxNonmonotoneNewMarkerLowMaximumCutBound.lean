import ESBlueprint.B.CtxNonmonotoneTripleSaturatedPotentialArbitraryOppositeHistory
import ESBlueprint.B.CtxNonmonotoneTripleLinearPotential
import ESBlueprint.B.CtxSmallGlobalAxisRankRegionPotential
import ESBlueprint.B.CtxPartPositiveLetters
import ESBlueprint.B.CtxActualMarkerCompanionMaximumBound
import ESBlueprint.B.CtxActualMarkerQuadraticPenultimateCutBound

namespace ErdosSzekeres

/-- Pay both parts of every non-extreme nonmonotone new-marker cut with m+3<=k. At the exact endpoint m+3=k, consume the checked ctx_actual_marker_quadratic_penultimate_cut_bound and lift its full-bound estimates to independent fuels. At m+4=k, the new level-one maximum and the checked arbitrary-opposite-history saturated theorem give the sharp 3k-8 and 3k-9 chosen-part estimates. Below that endpoint, the checked arbitrary-history nonmonotone linear theorem gives 3k-5 in the top band and 3k-8 in the next band; the checked small-global potential handles opposite global at most one. The companion is at most m squared. For m<=k-5 these estimates fit both quadratic budgets with respective slack at least 2k-12 and 2k-10. Positive source labels, two transported actual chosen markers, distinct axes, the new-marker nonmonotone geometry, chosen global at most five, opposite global at most k, k at least six, retained and removed child witnesses, and the cut coupling are explicit. Opposite indexed history, all old maxima, kept lists and inactive children are arbitrary. No retained-capacity, clear-history, exact-depth, convexity or recursive-potential premise is used. Supersedes the unregistered clear-history critical-cut request and removes all non-extreme maxima m<=k-3 for this geometry. Exact final-wrapper es searches for 'new marker nonmonotone all maxima m at most k minus 3 cut' and 'penultimate cut wrapper all fuel nonmonotone' returned no results; earlier pre-draft searches for 'nonmonotone new marker low maximum cut top next', 'new marker m plus 4 less equal k companion square', and 'nonmonotone triple arbitrary opposite history saturated' also returned no results.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_nonmonotone_new_marker_low_maximum_cut_bound (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (keep : List ℕ) (s t : Ctx.Side) (hne : s ≠ t) (m n p q N M x y : ℕ)
  (hp : p ∈ (σ.part keep s m).childPositions)
  (hq : q ∈ σ.childPositions) (hqnot : q ∉ keep)
  (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M)
  (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s)
  (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M)
  (hgeometry : (q < x ∧ y < x) ∨ (x < q ∧ x < y))
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
  (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ σ.k)
  (hk : 6 ≤ σ.k) (hcoupling : m + n = σ.k - 1) (hmaximum : m + 3 ≤ σ.k) :
  let A := σ.part keep s m
  let B := σ.part (σ.childPositions.filter (· ∉ keep)) t n
  (∀ f g, Ctx.Context.boundFuel f A + Ctx.Context.boundFuel g B ≤
    (σ.k - 1)^2 - 3 * (σ.k - 1) + 4) ∧
    A.bound + B.bound ≤ (σ.k - 1)^2 - 3 * (σ.k - 1) + 4 ∧
    ((match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ σ.k - 1 →
      (∀ f g, Ctx.Context.boundFuel f A + Ctx.Context.boundFuel g B ≤
        (σ.k - 2)^2 - (σ.k - 2) + 1) ∧
      A.bound + B.bound ≤ (σ.k - 2)^2 - (σ.k - 2) + 1) := by
  set_option maxHeartbeats 8000000 in
    let A := σ.part keep s m
    let B := σ.part (σ.childPositions.filter (· ∉ keep)) t n
    let w := (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1
    by_cases hpenultimate : m + 3 = σ.k
    · have hPenultimate := ctx_actual_marker_quadratic_penultimate_cut_bound σ hpositive
        s t hne N x hN hNs hx
        (by cases s <;> exact hglobal) (by cases t <;> exact hopposite) (by omega)
        keep m n p q hp hq hqnot hcoupling hpenultimate
      have hFuelFull (ρ : Ctx.Context) (fuel : ℕ) :
          Ctx.Context.boundFuel fuel ρ ≤ ρ.bound := by
        by_cases hf : ρ.childPositions.length + 1 ≤ fuel
        · exact (Ctx.Context.boundFuel_eq_bound ρ hf).le
        · exact Ctx.Context.boundFuel_mono
            (by omega : fuel ≤ ρ.childPositions.length + 1) ρ
      refine ⟨?_, hPenultimate.1, ?_⟩
      · intro f g
        exact (Nat.add_le_add (hFuelFull A f) (hFuelFull B g)).trans hPenultimate.1
      · intro hnext
        have hFull := hPenultimate.2 hnext
        exact ⟨fun f g =>
          (Nat.add_le_add (hFuelFull A f) (hFuelFull B g)).trans hFull, hFull⟩
    · have hmaximumFour : m + 4 ≤ σ.k := by omega
      have hPosA : ∀ r j v, A.letterAt r = Ctx.Letter.ext j v → 1 ≤ j :=
        ctx_part_positive_letters σ keep s m
      have hNpos : 1 ≤ N := Ctx.Context.one_le_of_mem_levels hN
      have hMpos : 1 ≤ M := Ctx.Context.one_le_of_mem_levels hM
      have hOne : 1 ∈ A.levels := by
        change 1 ∈ (σ.part keep s m).levels
        rw [Ctx.Context.part_levels]
        simp
      have hNA : N + 1 ∈ A.levels := by
        change N + 1 ∈ (σ.part keep s m).levels
        rw [Ctx.Context.part_levels]
        exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨N, hN, rfl⟩)
      have hMA : M + 1 ∈ A.levels := by
        change M + 1 ∈ (σ.part keep s m).levels
        rw [Ctx.Context.part_levels]
        exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨M, hM, rfl⟩)
      have hqA : q ∈ A.extPositions 1 := by
        change q ∈ (σ.part keep s m).extPositions 1
        rw [Ctx.Context.part_extPositions_one hpositive]
        exact List.mem_filter.mpr ⟨hq, by simp [hqnot]⟩
      have hxA : x ∈ A.extPositions (N + 1) := by
        change x ∈ (σ.part keep s m).extPositions (N + 1)
        rw [Ctx.Context.part_extPositions_succ σ keep s m hNpos]
        exact hx
      have hyA : y ∈ A.extPositions (M + 1) := by
        change y ∈ (σ.part keep s m).extPositions (M + 1)
        rw [Ctx.Context.part_extPositions_succ σ keep s m hMpos]
        exact hy
      have hSideOne : A.sideAt 1 = s := by
        exact Ctx.Context.part_sideAt_one_of_mem hpositive keep s m hqA
      have hNsA : A.sideAt (N + 1) = s := by
        exact (Ctx.Context.part_sideAt_succ σ keep s m hNpos).trans hNs
      have hMsA : A.sideAt (M + 1) = s := by
        exact (Ctx.Context.part_sideAt_succ σ keep s m hMpos).trans hMs
      have hGlobalA :
          (match s with | Ctx.Side.lower => A.u | Ctx.Side.upper => A.a) ≤ 5 := by
        cases s <;> exact hglobal
      have hOppositeA :
          (match t with | Ctx.Side.lower => A.u | Ctx.Side.upper => A.a) ≤ A.k := by
        cases t <;> exact hopposite
      have hAk : A.k = σ.k := by rfl
      have hCompanion := ctx_actual_marker_companion_maximum_bound σ hpositive s t hne
        N x hN hNs hx hglobal keep m n p q hp hq hqnot
      have hbudget : σ.k - n - 1 = m := by omega
      have hBFuelM (g : ℕ) : Ctx.Context.boundFuel g B ≤ m ^ 2 := by
        have h := hCompanion.1 g
        simpa only [B, hbudget] using h
      have hBBoundM : B.bound ≤ m ^ 2 := by
        have h := hCompanion.2.1
        simpa only [B, hbudget] using h
      by_cases hcritical : m + 4 = σ.k
      · have hmEq : m = σ.k - 4 := by omega
        have hMaximumOne : A.k - 4 ≤ A.maximumAt 1 := by
          rw [hAk, Ctx.Context.part_maximumAt_one]
          omega
        have hASaturated :=
          ctx_nonmonotone_triple_saturated_potential_arbitrary_opposite_history A hPosA
            s t hne 1 (N + 1) (M + 1) q x y hOne hNA hMA (by omega) (by omega)
            hSideOne hNsA hMsA hqA hxA hyA hgeometry hGlobalA
            (by cases t <;> exact hOppositeA) (by rw [hAk]; omega)
            1 hOne hSideOne hMaximumOne
        have hBFuel (g : ℕ) : Ctx.Context.boundFuel g B ≤ (σ.k - 4) ^ 2 := by
          simpa only [hmEq] using hBFuelM g
        have hBBound : B.bound ≤ (σ.k - 4) ^ 2 := by
          simpa only [hmEq] using hBBoundM
        have hATopFuel (f : ℕ) : Ctx.Context.boundFuel f A ≤ 3 * σ.k - 8 := by
          simpa only [A] using hASaturated.1 f
        have hATopBound : A.bound ≤ 3 * σ.k - 8 := by
          simpa only [A] using hASaturated.2.1
        have hNumericCritical (k : ℕ) (hk : 5 ≤ k) :
            (3 * k - 8) + (k - 4) ^ 2 = (k - 1) ^ 2 - 3 * (k - 1) + 4 ∧
            (3 * k - 9) + (k - 4) ^ 2 = (k - 2) ^ 2 - (k - 2) + 1 := by
          let z := k - 4
          have hz : 1 ≤ z := by dsimp [z]; omega
          have hk' : k = z + 4 := by dsimp [z]; omega
          have h1 : k - 1 = z + 3 := by dsimp [z]; omega
          have h2 : k - 2 = z + 2 := by dsimp [z]; omega
          have h4 : k - 4 = z := rfl
          rw [h1, h2, h4, hk']
          have hTopLeft : 3 * (z + 4) - 8 = 3 * z + 4 := by omega
          have hNextLeft : 3 * (z + 4) - 9 = 3 * z + 3 := by omega
          rw [hTopLeft, hNextLeft]
          have hsTop : 3 * (z + 3) ≤ (z + 3) ^ 2 := by
            set_option maxHeartbeats 2000000 in nlinarith only [hz]
          have hrTop := Nat.sub_add_cancel hsTop
          have hsNext : z + 2 ≤ (z + 2) ^ 2 := by
            set_option maxHeartbeats 2000000 in nlinarith only [hz]
          have hrNext := Nat.sub_add_cancel hsNext
          constructor
          · set_option maxHeartbeats 2000000 in nlinarith only [hz, hrTop]
          · set_option maxHeartbeats 2000000 in nlinarith only [hz, hrNext]
        refine ⟨?_, ?_, ?_⟩
        · intro f g
          exact (Nat.add_le_add (hATopFuel f) (hBFuel g)).trans_eq
            (hNumericCritical σ.k (by omega)).1
        · exact (Nat.add_le_add hATopBound hBBound).trans_eq
            (hNumericCritical σ.k (by omega)).1
        · intro hnext
          have hnextA :
              (match t with | Ctx.Side.lower => A.u | Ctx.Side.upper => A.a) ≤ A.k - 1 := by
            cases t <;> exact hnext
          have hANext := hASaturated.2.2 (by cases t <;> exact hnextA)
          have hANextFuel (f : ℕ) : Ctx.Context.boundFuel f A ≤ 3 * σ.k - 9 := by
            simpa only [A] using hANext.1 f
          have hANextBound : A.bound ≤ 3 * σ.k - 9 := by
            simpa only [A] using hANext.2
          constructor
          · intro f g
            exact (Nat.add_le_add (hANextFuel f) (hBFuel g)).trans_eq
              (hNumericCritical σ.k (by omega)).2
          · exact (Nat.add_le_add hANextBound hBBound).trans_eq
              (hNumericCritical σ.k (by omega)).2
      · have hlow : m ≤ σ.k - 5 := by omega
        have hBFuelLow (g : ℕ) : Ctx.Context.boundFuel g B ≤ (σ.k - 5) ^ 2 :=
          (hBFuelM g).trans (Nat.pow_le_pow_left hlow 2)
        have hBBoundLow : B.bound ≤ (σ.k - 5) ^ 2 :=
          hBBoundM.trans (Nat.pow_le_pow_left hlow 2)
        have hAEstimates :
            (∀ f, Ctx.Context.boundFuel f A ≤ 3 * σ.k - 5) ∧
            A.bound ≤ 3 * σ.k - 5 ∧
            ((match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ σ.k - 1 →
              (∀ f, Ctx.Context.boundFuel f A ≤ 3 * σ.k - 8) ∧
              A.bound ≤ 3 * σ.k - 8) := by
          by_cases hwidth : 1 ≤ w
          · have hAWidth :
                1 ≤ (match t with | Ctx.Side.lower => A.u | Ctx.Side.upper => A.a) - 1 := by
              dsimp only [w] at hwidth
              cases t <;> exact hwidth
            have hLinear := ctx_nonmonotone_triple_linear_potential A hPosA s t hne
              1 (N + 1) (M + 1) q x y hOne hNA hMA (by omega) (by omega)
              hSideOne hNsA hMsA hqA hxA hyA hgeometry hGlobalA
              (by cases t <;> exact hAWidth)
            have hLinearFuel (f : ℕ) : Ctx.Context.boundFuel f A ≤ 3 * w - 2 := by
              dsimp only [w]
              cases t <;> exact hLinear.1 f
            have hLinearBound : A.bound ≤ 3 * w - 2 := by
              dsimp only [w]
              cases t <;> exact hLinear.2
            have hwTop : w ≤ σ.k - 1 := by
              dsimp only [w]
              simpa only [Nat.sub_sub, Nat.reduceAdd] using
                Nat.sub_le_sub_right hopposite 1
            refine ⟨fun f => (hLinearFuel f).trans (by omega),
              hLinearBound.trans (by omega), ?_⟩
            intro hnext
            have hwNext : w ≤ σ.k - 2 := by
              dsimp only [w]
              cases t <;> simpa only [Nat.sub_sub, Nat.reduceAdd] using
                Nat.sub_le_sub_right hnext 1
            exact ⟨fun f => (hLinearFuel f).trans (by omega),
              hLinearBound.trans (by omega)⟩
          · have hSmallGlobal :
                (match t with | Ctx.Side.lower => A.u | Ctx.Side.upper => A.a) ≤ 3 := by
              dsimp only [w] at hwidth
              cases t
              · change ¬1 ≤ σ.u - 1 at hwidth
                change σ.u ≤ 3
                omega
              · change ¬1 ≤ σ.a - 1 at hwidth
                change σ.a ≤ 3
                omega
            have hSmall := ctx_small_global_axis_rank_region_potential A hPosA t s
              (Ne.symm hne) hSmallGlobal
            have hChosenCap :
                (match s with | Ctx.Side.lower => A.u - 1 | Ctx.Side.upper => A.a - 1) ≤ 4 := by
              cases s <;> exact Nat.sub_le_sub_right hGlobalA 1
            have hSmallFuel (f : ℕ) : Ctx.Context.boundFuel f A ≤ 4 := by
              exact ((hSmall.1 f).trans hSmall.2.2.1).trans hChosenCap
            have hSmallBound : A.bound ≤ 4 := by
              exact (hSmall.2.1.trans hSmall.2.2.1).trans hChosenCap
            exact ⟨fun f => (hSmallFuel f).trans (by omega),
              hSmallBound.trans (by omega), fun _ =>
                ⟨fun f => (hSmallFuel f).trans (by omega),
                  hSmallBound.trans (by omega)⟩⟩
        have hNumericLow (k : ℕ) (hk : 6 ≤ k) :
            (3 * k - 5) + (k - 5) ^ 2 ≤ (k - 1) ^ 2 - 3 * (k - 1) + 4 ∧
            (3 * k - 8) + (k - 5) ^ 2 ≤ (k - 2) ^ 2 - (k - 2) + 1 := by
          let z := k - 6
          have hz : 0 ≤ z := Nat.zero_le z
          have hk' : k = z + 6 := by dsimp [z]; omega
          have h1 : k - 1 = z + 5 := by dsimp [z]; omega
          have h2 : k - 2 = z + 4 := by dsimp [z]; omega
          have h5 : k - 5 = z + 1 := by dsimp [z]; omega
          rw [h1, h2, h5, hk']
          have hTopLeft : 3 * (z + 6) - 5 = 3 * z + 13 := by omega
          have hNextLeft : 3 * (z + 6) - 8 = 3 * z + 10 := by omega
          rw [hTopLeft, hNextLeft]
          have hsTop : 3 * (z + 5) ≤ (z + 5) ^ 2 := by
            set_option maxHeartbeats 2000000 in nlinarith only [hz]
          have hrTop := Nat.sub_add_cancel hsTop
          have hsNext : z + 4 ≤ (z + 4) ^ 2 := by
            set_option maxHeartbeats 2000000 in nlinarith only [hz]
          have hrNext := Nat.sub_add_cancel hsNext
          constructor
          · set_option maxHeartbeats 2000000 in nlinarith only [hz, hrTop]
          · set_option maxHeartbeats 2000000 in nlinarith only [hz, hrNext]
        refine ⟨?_, ?_, ?_⟩
        · intro f g
          exact (Nat.add_le_add (hAEstimates.1 f) (hBFuelLow g)).trans
            (hNumericLow σ.k hk).1
        · exact (Nat.add_le_add hAEstimates.2.1 hBBoundLow).trans
            (hNumericLow σ.k hk).1
        · intro hnext
          have hANext := hAEstimates.2.2 (by cases t <;> exact hnext)
          constructor
          · intro f g
            exact (Nat.add_le_add (hANext.1 f) (hBFuelLow g)).trans
              (hNumericLow σ.k hk).2
          · exact (Nat.add_le_add hANext.2 hBBoundLow).trans
              (hNumericLow σ.k hk).2


end ErdosSzekeres
