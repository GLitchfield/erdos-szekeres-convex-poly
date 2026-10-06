import ESBlueprint.B.CtxBoundLeSumPointBases
import ESBlueprint.B.CtxBoundAttainedByEndCut

set_option maxHeartbeats 6000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Every fuel approximation and full bound of a proper part vanish when a raw positive-label context has an indexed sibling maximum at least k-2 and opposite global parameter at most two. A specified omitted source child makes the part proper; kept positions and new coupling are arbitrary. No multi-run, well-formedness, occupied-level or legal coupling premise. Exposes the checked internal proper-part argument of R16's closed high-maximum root theorem for reuse in both singleton and complementary source summands of X.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_bound_le_sum_point_bases, ErdosSzekeres.ctx_part_limits_le
@consumer ErdosSzekeres.ctx_one_level_root_singleton_base_exchange -/
theorem ctx_proper_part_zero_of_large_sibling_maximum_and_opposite_global_two (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (N : ℕ) (hN : N ∈ σ.levels) (hmaximum : σ.k - 2 ≤ σ.maximumAt N) (hopposite : (match σ.sideAt N with | Ctx.Side.lower => σ.a | Ctx.Side.upper => σ.u) ≤ 2) (keep : List ℕ) (t : Ctx.Side) (m q : ℕ) (hq : q ∈ σ.childPositions) (hremoved : q ∉ keep) : (∀ fuel : ℕ, Ctx.Context.boundFuel fuel (σ.part keep t m) = 0) ∧ (σ.part keep t m).bound = 0 := by
  classical
  let s := σ.sideAt N
  let lim (ρ : Context) (p : ℕ) := match s with
    | Side.lower => ρ.cupLimit p p
    | Side.upper => ρ.capLimit p p
  have hLimPart (ρ : Context) (keep : List ℕ) (t : Side) (m p : ℕ) :
      lim (ρ.part keep t m) p ≤ lim ρ p := by
    have h := ctx_part_limits_le ρ keep t m p p
    cases hs : s with
    | lower => simpa only [lim, hs] using h.1
    | upper => simpa only [lim, hs] using h.2
  have hLevelPart (ρ : Context) (keep : List ℕ) (t : Side) (m L : ℕ)
      (hL : L ∈ ρ.levelsOn s 0) :
      L + 1 ∈ (ρ.part keep t m).levelsOn s 0 ∧
        (ρ.part keep t m).maximumAt (L + 1) = ρ.maximumAt L := by
    have hmem := (List.mem_filter.mp hL).1
    have h1 := (one_le_of_mem_levelsOn hL).1
    have hside : ρ.sideAt L = s := by simpa using (List.mem_filter.mp hL).2
    have hside' : (ρ.part keep t m).sideAt (L + 1) = s :=
      (part_sideAt_succ ρ keep t m h1).trans hside
    refine ⟨?_, part_maximumAt_succ ρ keep t m h1⟩
    apply List.mem_filter.mpr
    refine ⟨?_, by simp [hside']⟩
    rw [part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨L, hmem, rfl⟩)
  have hZeroLim : ∀ fuel (ρ : Context),
      (∀ p ∈ ρ.childPositions, lim ρ p = 0) → boundFuel fuel ρ = 0 := by
    intro fuel
    induction fuel with
    | zero => intro ρ _; rfl
    | succ fuel ih =>
      intro ρ hZ
      have hParts (keep : List ℕ) (t : Side) (m : ℕ) : boundFuel fuel (ρ.part keep t m) = 0 := by
        apply ih
        intro p hp
        rw [part_childPositions] at hp
        have hz := hZ p (List.mem_filter.mp hp).1
        have hle := hLimPart ρ keep t m p
        omega
      rw [boundFuel]
      split
      · rw [base_eq_baseOf]
        cases hh : ρ.childPositions.head? with
        | none => rfl
        | some p =>
          have hz := hZ p (List.mem_of_mem_head? (Option.mem_def.mpr hh))
          cases hs : s <;> simp only [lim, hs] at hz <;> simp [baseOf, hz]
      · apply Nat.eq_zero_of_le_zero
        apply Ctx.getD_max?_le
        intro x hx
        simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hx
        obtain ⟨keep, _, d, _, hx⟩ := hx
        rcases hx with rfl | rfl <;> simp only [hParts, Nat.add_zero, le_refl]
  have hKill (ρ : Context)
      (hPos : ∀ x l t, ρ.letterAt x = Letter.ext l t → 1 ≤ l)
      (L : ℕ) (hL : L ∈ ρ.levelsOn s 0) (hM : ρ.k - 2 ≤ ρ.maximumAt L)
      (keep : List ℕ) (m r : ℕ) (hr : r ∈ ρ.childPositions) (hremoved : r ∉ keep) :
      ∀ p ∈ (ρ.part keep s m).childPositions, lim (ρ.part keep s m) p = 0 := by
    intro p hp
    let τ := ρ.part keep s m
    have hpkeep : p ∈ keep := by
      rw [part_childPositions] at hp
      simpa using (List.mem_filter.mp hp).2
    have hne : p ≠ r := by intro h; subst p; exact hremoved hpkeep
    have hrnew : r ∈ τ.extPositions 1 := by
      rw [part_extPositions_one hPos keep s m]
      exact List.mem_filter.mpr ⟨hr, by simpa using hremoved⟩
    have hside : τ.sideAt 1 = s := part_sideAt_one_of_mem hPos keep s m hrnew
    have h1 := (one_le_of_mem_levelsOn hL).1
    have hone : 1 ∈ τ.levelsOn s (L + 1) := by
      rw [part_levelsOn_self_succ hside h1]
      simp
    have hsub : [1].Sublist (τ.levelsOn s (L + 1)) := List.singleton_sublist.mpr hone
    have hExt : 1 ≤ τ.leftExt s (L + 1) p + τ.rightExt s (L + 1) p := by
      by_cases hrp : r < p
      · have hnon : ((τ.extPositions 1).filter (· < p)) ≠ [] := by
          intro hn
          have hm : r ∈ (τ.extPositions 1).filter (· < p) :=
            List.mem_filter.mpr ⟨hrnew, by simpa using hrp⟩
          rw [hn] at hm
          cases hm
        have hv := Ctx.le_getD_max?_of_mem
          (L := (τ.levelsOn s (L + 1)).sublists.map
            (fun ls => (ls.foldl (leftStep τ) (p, 0)).2))
          (List.mem_map.mpr ⟨[1], List.mem_sublists.mpr hsub, rfl⟩)
        change ([1].foldl (leftStep τ) (p, 0)).2 ≤ τ.leftExt s (L + 1) p at hv
        simp only [List.foldl_cons, List.foldl_nil, leftStep,
          List.getLast?_eq_some_getLast hnon] at hv
        omega
      · have hpr : p < r := by omega
        have hnon : ((τ.extPositions 1).filter (p < ·)) ≠ [] := by
          intro hn
          have hm : r ∈ (τ.extPositions 1).filter (p < ·) :=
            List.mem_filter.mpr ⟨hrnew, by simpa using hpr⟩
          rw [hn] at hm
          cases hm
        have hv := Ctx.le_getD_max?_of_mem
          (L := (τ.levelsOn s (L + 1)).sublists.map
            (fun ls => (ls.foldl (rightStep τ) (p, 0)).2))
          (List.mem_map.mpr ⟨[1], List.mem_sublists.mpr hsub, rfl⟩)
        change ([1].foldl (rightStep τ) (p, 0)).2 ≤ τ.rightExt s (L + 1) p at hv
        simp only [List.foldl_cons, List.foldl_nil, rightStep,
          List.head?_eq_some_head hnon] at hv
        omega
    have hlevel := hLevelPart ρ keep s m L hL
    have hj := le_joinExt_of_mem_levelsOn hlevel.1 p p
    rw [hlevel.2] at hj
    have hjoin : ρ.k - 1 ≤ τ.joinExt s p p := by
      change 1 ≤ (ρ.part keep s m).leftExt s (L + 1) p +
        (ρ.part keep s m).rightExt s (L + 1) p at hExt
      change ρ.k - 1 ≤ (ρ.part keep s m).joinExt s p p
      omega
    have hk : τ.k = ρ.k := rfl
    change lim τ p = 0
    cases hs : s <;> simp only [lim, hs, cupLimit, capLimit, hk] <;>
      simp only [hs] at hjoin <;> omega
  have hMarkerZero (σ : Ctx.Context) (s : Ctx.Side) (N x : ℕ)
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
  have hStart : N ∈ σ.levelsOn s 0 := by simp [levelsOn,hN,s]
  have hPart (keep : List ℕ) (t : Side) (m q : ℕ)
      (hq : q ∈ σ.childPositions) (hqn : q ∉ keep) :
      ∀ fuel, boundFuel fuel (σ.part keep t m) = 0 := by
    intro fuel
    by_cases ht : t = s
    · subst t
      exact hZeroLim fuel (σ.part keep s m)
        (hKill σ hpositive N hStart hmaximum keep m q hq hqn)
    · have hqData : q < σ.word.length ∧ σ.letterAt q = Letter.child := by
        simpa only [childPositions,List.mem_filter,List.mem_range,decide_eq_true_eq] using hq
      have he : (σ.part keep t m).letterAt q = Letter.ext 1 t := by
        rw [part_letterAt_of_child σ keep t m hqData.1 hqData.2]
        simp [hqn]
      have hx : q ∈ (σ.part keep t m).extPositions 1 := by
        simp only [extPositions,List.mem_filter,List.mem_range,part_word_length]
        exact ⟨hqData.1,by simp [he]⟩
      have hs : (σ.part keep t m).sideAt 1 = t :=
        part_sideAt_one_of_mem hpositive keep t m (q := q) hx
      have hNewN : 1 ∈ (σ.part keep t m).levels := by
        simp only [levels,List.mem_map,List.mem_range,part_maxima,List.length_cons]
        exact ⟨0,by omega,rfl⟩
      cases t with
      | lower =>
        have hu : σ.u ≤ 2 := by
          cases hSide : σ.sideAt N with
          | lower => exact False.elim (ht hSide.symm)
          | upper => simpa only [hSide] using hopposite
        exact (hMarkerZero (σ.part keep Side.lower m) Side.lower 1 q
          hNewN hs hx hu).1 fuel
      | upper =>
        have ha : σ.a ≤ 2 := by
          cases hSide : σ.sideAt N with
          | lower => simpa only [hSide] using hopposite
          | upper => exact False.elim (ht hSide.symm)
        exact (hMarkerZero (σ.part keep Side.upper m) Side.upper 1 q
          hNewN hs hx ha).1 fuel
  exact ⟨hPart keep t m q hq hremoved, hPart keep t m q hq hremoved _⟩


end ErdosSzekeres
