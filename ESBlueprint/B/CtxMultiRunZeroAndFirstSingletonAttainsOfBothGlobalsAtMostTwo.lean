import ESBlueprint.B.CtxBoundLeSumPointBases
import ESBlueprint.B.CtxBoundCutLe
import ESBlueprint.B.CtxBoundAttainedByEndCut

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- Every recursive fuel approximation and the full bound of an arbitrary raw context with at least two child runs and both global parameters at most two vanish. Positive physical external labels ensure that each proper cut creates an actual youngest marker on its part side; the global-two indexed-marker annihilation kills both cut terms. Covers arbitrary indexed histories, sibling maxima and positive inert barriers, without WellFormed or legal maxima. When k is at least three, the first global child yields a legal maximum-one raw singleton threshold cut attaining the zero source bound. Supplies a marker-free-history degenerate N_ends/N_root edge.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_one_level_root_bound_attained_by_singleton_cut -/
theorem ctx_multi_run_zero_and_first_singleton_attains_of_both_globals_at_most_two (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (ha : σ.a ≤ 2) (hu : σ.u ≤ 2) (hruns : 2 ≤ σ.numRuns) : (∀ fuel : ℕ, Ctx.Context.boundFuel fuel σ = 0) ∧ σ.bound = 0 ∧ (3 ≤ σ.k → ∃ p : ℕ, σ.childPositions.head? = some p ∧ p ∈ σ.childPositions ∧ 1 ≤ σ.k-2 ∧ σ.bound ≤ decomposableThreshold ((σ.part [p] Ctx.Side.lower 1).capLimit p p+1) ((σ.part [p] Ctx.Side.lower 1).cupLimit p p+1) σ.k + (σ.part (σ.childPositions.filter (fun q => q ≠ p)) Ctx.Side.upper (σ.k-1-1)).bound) := by
  classical
  have hZero (σ : Ctx.Context) (s : Ctx.Side) (N x : ℕ)
      (hN : N ∈ σ.levels) (hs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N)
      (hglobal : (match s with | Side.lower => σ.u | Side.upper => σ.a) ≤ 2) :
      (∀ fuel : ℕ, boundFuel fuel σ = 0) ∧ σ.bound = 0 := by
    classical
    have hOneLeft (ρ : Context) (v : Side) (j p q : ℕ)
        (hj : j ∈ ρ.levelsOn v 0) (hq : q ∈ ρ.extPositions j) (hqp : q < p) :
        1 ≤ ρ.leftExt v 0 p := by
      have hm : q ∈ (ρ.extPositions j).filter (· < p) := by simp [hq,hqp]
      have hnonempty := List.ne_nil_of_mem hm
      have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v 0).sublists.map
        (fun ls => (ls.foldl (leftStep ρ) (p,0)).2))
        (List.mem_map.mpr ⟨[j],List.mem_sublists.mpr (List.singleton_sublist.mpr hj),rfl⟩)
      change _ ≤ ρ.leftExt v 0 p at hv
      simpa only [List.foldl_cons,List.foldl_nil,leftStep,
        List.getLast?_eq_some_getLast hnonempty] using hv
    have hOneRight (ρ : Context) (v : Side) (j p q : ℕ)
        (hj : j ∈ ρ.levelsOn v 0) (hq : q ∈ ρ.extPositions j) (hpq : p < q) :
        1 ≤ ρ.rightExt v 0 p := by
      have hm : q ∈ (ρ.extPositions j).filter (p < ·) := by simp [hq,hpq]
      have hnonempty := List.ne_nil_of_mem hm
      have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v 0).sublists.map
        (fun ls => (ls.foldl (rightStep ρ) (p,0)).2))
        (List.mem_map.mpr ⟨[j],List.mem_sublists.mpr (List.singleton_sublist.mpr hj),rfl⟩)
      change _ ≤ ρ.rightExt v 0 p at hv
      simpa only [List.foldl_cons,List.foldl_nil,rightStep,
        List.head?_eq_some_head hnonempty] using hv
    have hNOn : N ∈ σ.levelsOn s 0 := List.mem_filter.mpr ⟨hN,by simp [hs]⟩
    have hPoint : ∀ p ∈ σ.childPositions,
        baseOf (σ.cupLimit p p) (σ.capLimit p p) σ.k = 0 := by
      intro p hp
      have hpx : p ≠ x := by
        intro he
        subst x
        have hc := of_decide_eq_true (List.mem_filter.mp hp).2
        have he := (List.mem_filter.mp hx).2
        simp [hc] at he
      have hChain : 1 ≤ σ.chainExt s p p := by
        by_cases h : p < x
        · have hright := hOneRight σ s N p x hNOn hx h
          unfold chainExt
          omega
        · have hleft := hOneLeft σ s N p x hNOn hx (by omega)
          unfold chainExt
          omega
      cases s with
      | lower =>
        dsimp only at hglobal
        have hzero : σ.cupLimit p p = 0 := by
          simp only [cupLimit]
          omega
        simp [baseOf,hzero]
      | upper =>
        dsimp only at hglobal
        have hzero : σ.capLimit p p = 0 := by
          simp only [capLimit]
          omega
        simp [baseOf,hzero]
    have hMap :
        σ.childPositions.map (fun p => baseOf (σ.cupLimit p p) (σ.capLimit p p) σ.k) =
          σ.childPositions.map (fun _ => 0) := by
      apply List.map_congr_left
      intro p hp
      exact hPoint p hp
    have hBound : σ.bound = 0 := by
      apply Nat.eq_zero_of_le_zero
      simpa only [hMap,List.sum_map_zero] using ctx_bound_le_sum_point_bases σ
    have hFuel (fuel : ℕ) : boundFuel fuel σ = 0 := by
      have hle : boundFuel fuel σ ≤ σ.bound := by
        by_cases hf : σ.childPositions.length+1 ≤ fuel
        · exact (boundFuel_eq_bound σ hf).le
        · exact boundFuel_mono (by omega : fuel ≤ σ.childPositions.length+1) σ
      rw [hBound] at hle
      exact Nat.eq_zero_of_le_zero hle
    exact ⟨hFuel,hBound⟩
  have hMissing (keep : List ℕ) (hlen : keep.length < σ.childPositions.length) :
      ∃ q, q ∈ σ.childPositions ∧ q ∉ keep := by
    by_contra h
    have hAll : σ.childPositions ⊆ keep := by
      intro q hq
      by_contra hqk
      exact h ⟨q,hq,hqk⟩
    have hle := ((childPositions_nodup σ).subperm hAll).length_le
    omega
  have hPart (keep : List ℕ) (s : Side) (m q : ℕ)
      (hq : q ∈ σ.childPositions) (hqn : q ∉ keep) :
      ∀ fuel, boundFuel fuel (σ.part keep s m) = 0 := by
    have hqData : q < σ.word.length ∧ σ.letterAt q = Letter.child := by
      simpa only [childPositions,List.mem_filter,List.mem_range,decide_eq_true_eq] using hq
    have he : (σ.part keep s m).letterAt q = Letter.ext 1 s := by
      rw [part_letterAt_of_child σ keep s m hqData.1 hqData.2]
      simp [hqn]
    have hx : q ∈ (σ.part keep s m).extPositions 1 := by
      simp only [extPositions,List.mem_filter,List.mem_range,part_word_length]
      exact ⟨hqData.1,by simp [he]⟩
    have hs : (σ.part keep s m).sideAt 1 = s :=
      part_sideAt_one_of_mem hpositive keep s m (q := q) hx
    have hN : 1 ∈ (σ.part keep s m).levels := by
      simp only [levels,List.mem_map,List.mem_range,part_maxima,List.length_cons]
      exact ⟨0,by omega,rfl⟩
    cases s with
    | lower =>
      exact (hZero (σ.part keep Side.lower m) Side.lower 1 q hN hs hx hu).1
    | upper =>
      exact (hZero (σ.part keep Side.upper m) Side.upper 1 q hN hs hx ha).1
  have hFuel : ∀ fuel, boundFuel fuel σ = 0 := by
    intro fuel
    cases fuel with
    | zero => rfl
    | succ fuel =>
      rw [boundFuel.eq_2,if_neg (by omega : ¬ σ.numRuns ≤ 1)]
      apply Nat.eq_zero_of_le_zero
      apply Ctx.getD_max?_le
      intro z hz
      simp only [List.mem_flatMap,List.mem_range,List.mem_cons,
        List.not_mem_nil,or_false] at hz
      obtain ⟨block,hb,d',hd',hz⟩ := hz
      obtain ⟨hbLen,hbNe,hbSub⟩ := mem_blocks hb
      obtain ⟨q,hq,hqn⟩ := hMissing block hbLen
      have hRestLen := length_filter_not_mem_lt hbNe hbSub
      obtain ⟨r,hr,hrn⟩ := hMissing
        (σ.childPositions.filter (fun p => p ∉ block)) hRestLen
      rcases hz with rfl | rfl
      · rw [hPart block Side.lower (d'+1) q hq hqn fuel,
          hPart (σ.childPositions.filter (fun p => p ∉ block)) Side.upper
            (σ.k-1-(d'+1)) r hr hrn fuel]
      · rw [hPart block Side.upper (σ.k-1-(d'+1)) q hq hqn fuel,
          hPart (σ.childPositions.filter (fun p => p ∉ block)) Side.lower
            (d'+1) r hr hrn fuel]
  have hBound : σ.bound = 0 := hFuel _
  refine ⟨hFuel,hBound,?_⟩
  intro hk
  have hlen := numRuns_le_length σ
  cases hcp : σ.childPositions with
  | nil =>
    rw [hcp] at hlen
    simp only [List.length_nil] at hlen
    omega
  | cons p ps =>
    refine ⟨p,rfl,by simp,by omega,?_⟩
    rw [hBound]
    exact Nat.zero_le _

end ErdosSzekeres
