import ESBlueprint.B.CtxBoundZeroOfBothSidesLargeSiblingMaxima
import ESBlueprint.B.CtxPartTwoRunsOfNonintervalKeep
import ESBlueprint.B.CtxPartPositiveLetters

namespace ErdosSzekeres

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- For a well-formed context with at least two child runs and k=3, both orientation values of every nonempty proper interleaved child partition are zero at every legal coupling. Neither canonical keep nor complement may be an interval block. A source saturated sibling maximum and each new saturated level-one maximum annihilate proper multi-run parts. Removes the k=3 boundary from positive maximal-segment exchange while retaining arbitrary keep lists.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_part_bound_zero_of_same_side_large_sibling_maximum, ErdosSzekeres.ctx_bound_zero_of_both_sides_large_sibling_maxima, ErdosSzekeres.ctx_part_two_runs_of_noninterval_keep, ErdosSzekeres.ctx_part_positive_letters
@consumer ErdosSzekeres.ctx_bound_additive_multi_run -/
theorem ctx_interleaved_partition_value_zero_of_k_three (σ : Ctx.Context) (hwf : σ.WellFormed) (hruns : 2 ≤ σ.numRuns)
  (hk : σ.k = 3)
  (keep : List ℕ) (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions)
  (hne : keep ≠ []) (hall : keep.length < σ.childPositions.length)
  (hI : σ.childPositions.filter (fun p => p ∈ keep) ∉ σ.blocks)
  (hIc : σ.childPositions.filter (fun p => p ∉ keep) ∉ σ.blocks)
  (d : ℕ) (hd : 1 ≤ d) (hdk : d ≤ σ.k - 2) :
  (σ.part keep Ctx.Side.lower d).bound +
    (σ.part (σ.childPositions.filter (fun p => p ∉ keep))
      Ctx.Side.upper (σ.k - 1 - d)).bound = 0 ∧
  (σ.part keep Ctx.Side.upper (σ.k - 1 - d)).bound +
    (σ.part (σ.childPositions.filter (fun p => p ∉ keep))
      Ctx.Side.lower d).bound = 0 := by
  classical
  have hdOne : d = 1 := by omega
  have hotherOne : σ.k - 1 - d = 1 := by omega
  have hpositive : ∀ x l t, σ.letterAt x = Ctx.Letter.ext l t → 1 ≤ l := by
    intro x l t hx
    exact (hwf.2.2.2.2.2 x l t hx).1
  have hmarker : ∃ N s, N ∈ σ.levelsOn s 0 ∧ 1 ≤ N ∧
      σ.k - 2 ≤ σ.maximumAt N := by
    obtain ⟨p, _, _, hprev⟩ := Ctx.Context.exists_run_start_pos hruns
    cases hx : σ.letterAt (p - 1) with
    | child => exact (hprev hx).elim
    | ext N t =>
      obtain ⟨hN1, hNlen, _⟩ := hwf.2.2.2.2.2 (p - 1) N t hx
      have hidx : N - 1 < σ.maxima.length := by omega
      have hlevel : N ∈ σ.levels := by
        unfold Ctx.Context.levels
        exact List.mem_map.mpr ⟨N - 1, List.mem_range.mpr hidx, by omega⟩
      have hN : N ∈ σ.levelsOn (σ.sideAt N) 0 :=
        List.mem_filter.mpr ⟨hlevel, by simp⟩
      have hm := hwf.2.2.2.2.1 (σ.maxima[N - 1]) (List.getElem_mem hidx)
      have hM : 1 ≤ σ.maximumAt N := by
        simpa [Ctx.Context.maximumAt, List.getElem?_eq_getElem hidx] using hm.1
      exact ⟨N, σ.sideAt N, hN, hN1, by omega⟩
  obtain ⟨N, oldSide, hN, hN1, hM⟩ := hmarker
  obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil keep hne
  have hbσ : b ∈ σ.childPositions := hkeep b hb
  have hcanonicalNe : σ.childPositions.filter (fun p => p ∈ keep) ≠ [] := by
    intro he
    have hm : b ∈ σ.childPositions.filter (fun p => p ∈ keep) :=
      List.mem_filter.mpr ⟨hbσ, by simpa using hb⟩
    rw [he] at hm
    simp at hm
  have hcanonicalProper :
      (σ.childPositions.filter (fun p => p ∈ keep)).length < σ.childPositions.length :=
    lt_of_le_of_lt (Ctx.Context.length_filter_mem_le
      (block := keep) (Ctx.Context.childPositions_nodup σ)) hall
  have hex : ∃ r, r ∈ σ.childPositions ∧ r ∉ keep := by
    by_contra h
    have hsubset : ∀ r ∈ σ.childPositions, r ∈ keep := by
      intro r hr
      by_contra hn
      exact h ⟨r, hr, hn⟩
    have hcount := ((Ctx.Context.childPositions_nodup σ).subperm hsubset).length_le
    omega
  obtain ⟨r, hrσ, hrnot⟩ := hex
  let rest := σ.childPositions.filter (fun p => p ∉ keep)
  have hrrest : r ∈ rest := List.mem_filter.mpr ⟨hrσ, by simpa using hrnot⟩
  have hrestNe : rest ≠ [] := by
    intro he
    rw [he] at hrrest
    simp at hrrest
  have hrestProper : rest.length < σ.childPositions.length :=
    Ctx.Context.length_filter_not_mem_lt hne hkeep
  have hrestCanonical : σ.childPositions.filter (fun p => p ∈ rest) = rest := by
    change σ.childPositions.filter (fun p => p ∈ rest) =
      σ.childPositions.filter (fun p => p ∉ keep)
    apply List.filter_congr
    intro p hp
    simp [rest, hp]
  have hbnot : b ∉ rest := by simp [rest, hb]
  have hKeepRuns (s : Ctx.Side) : 2 ≤ (σ.part keep s 1).numRuns :=
    ctx_part_two_runs_of_noninterval_keep
      σ keep hcanonicalNe hcanonicalProper hI s 1
  have hRestRuns (s : Ctx.Side) : 2 ≤ (σ.part rest s 1).numRuns := by
    apply ctx_part_two_runs_of_noninterval_keep σ rest
    · rw [hrestCanonical]
      exact hrestNe
    · rw [hrestCanonical]
      exact hrestProper
    · rw [hrestCanonical]
      exact hIc
  have hPartZero (ks : List ℕ) (s : Ctx.Side) (q : ℕ)
      (hq : q ∈ σ.childPositions) (hqnot : q ∉ ks)
      (hRuns : 2 ≤ (σ.part ks s 1).numRuns) :
      (σ.part ks s 1).bound = 0 := by
    by_cases hsame : oldSide = s
    · apply ctx_part_bound_zero_of_same_side_large_sibling_maximum
        σ hpositive s N
      · simpa [hsame] using hN
      · exact hM
      · exact hq
      · exact hqnot
    · let τ := σ.part ks s 1
      have hnewExt : q ∈ τ.extPositions 1 := by
        rw [Ctx.Context.part_extPositions_one hpositive ks s 1]
        exact List.mem_filter.mpr ⟨hq, by simpa using hqnot⟩
      have hnewSide : τ.sideAt 1 = s :=
        Ctx.Context.part_sideAt_one_of_mem hpositive ks s 1 hnewExt
      have hnewLevel : 1 ∈ τ.levelsOn s 0 := by
        rw [Ctx.Context.part_levelsOn_self_zero hnewSide]
        simp
      have hnewMaximum : τ.k - 2 ≤ τ.maximumAt 1 := by
        change σ.k - 2 ≤ (σ.part ks s 1).maximumAt 1
        rw [Ctx.Context.part_maximumAt_one]
        omega
      have holdLevel : N + 1 ∈ τ.levelsOn oldSide 0 := by
        have hmem := (List.mem_filter.mp hN).1
        have hside : σ.sideAt N = oldSide := by
          simpa using (List.mem_filter.mp hN).2
        have hside' : τ.sideAt (N + 1) = oldSide :=
          (Ctx.Context.part_sideAt_succ σ ks s 1 hN1).trans hside
        apply List.mem_filter.mpr
        refine ⟨?_, by simp [hside']⟩
        rw [Ctx.Context.part_levels]
        exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨N, hmem, rfl⟩)
      have holdMaximum : τ.k - 2 ≤ τ.maximumAt (N + 1) := by
        change σ.k - 2 ≤ (σ.part ks s 1).maximumAt (N + 1)
        rw [Ctx.Context.part_maximumAt_succ σ ks s 1 hN1]
        exact hM
      have hpartPositive := ctx_part_positive_letters σ ks s 1
      cases s with
      | lower =>
        have holdSide : oldSide = Ctx.Side.upper := by
          cases oldSide with
          | lower => exact (hsame rfl).elim
          | upper => rfl
        exact ctx_bound_zero_of_both_sides_large_sibling_maxima
          τ hpartPositive hRuns 1 (N + 1) hnewLevel
          (by simpa [holdSide] using holdLevel) hnewMaximum holdMaximum
      | upper =>
        have holdSide : oldSide = Ctx.Side.lower := by
          cases oldSide with
          | lower => rfl
          | upper => exact (hsame rfl).elim
        exact ctx_bound_zero_of_both_sides_large_sibling_maxima
          τ hpartPositive hRuns (N + 1) 1
          (by simpa [holdSide] using holdLevel) hnewLevel holdMaximum hnewMaximum
  have hkl := hPartZero keep Ctx.Side.lower r hrσ hrnot (hKeepRuns _)
  have hku := hPartZero keep Ctx.Side.upper r hrσ hrnot (hKeepRuns _)
  have hrl := hPartZero rest Ctx.Side.lower b hbσ hbnot (hRestRuns _)
  have hru := hPartZero rest Ctx.Side.upper b hbσ hbnot (hRestRuns _)
  rw [hotherOne, hdOne]
  constructor
  · rw [hkl, hru]
  · rw [hku, hrl]

end ErdosSzekeres
