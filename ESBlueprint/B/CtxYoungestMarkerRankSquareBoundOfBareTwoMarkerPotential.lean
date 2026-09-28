import ESBlueprint.B.CtxSingleLevelOccurrencePruneBoundMono
import ESBlueprint.B.CtxBoundMonoOfMarkerInclusion
import ESBlueprint.B.CtxSmallGlobalAxisRankPairPotential
import ESBlueprint.B.CtxSmallOppositeGlobalMarkerSquareBound
import ESBlueprint.B.CtxBracketedPivotComplementCutSquareOfBoundedBareSquare

set_option maxHeartbeats 20000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Reduce the original youngest-marker exact rank-union square bound, with chosen global at most five and arbitrary histories/maxima/inactive children, to one explicit unproved bare two-marker triangular-plus-linear potential. The premise only concerns all-active positive contexts with zero indexed maxima, every indexed side chosen, precisely two actual marker positions at ordered distinct levels, and opposite width at least four. Four local proof components normalize this remaining cut, exhaust both axis assignments of all proper interval cuts, and enable strong induction on width. No square or two-marker conjecture is asserted without the stated premise.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_youngest_marker_rank_square_bound_of_bare_two_marker_potential (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (N x : ℕ)
  (hN : N ∈ σ.levels) (hNs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
  (hyoung : ∀ j ∈ σ.levelsOn s N, σ.extPositions j = [])
  (htwo : ∀ (ρ : Ctx.Context) (J K a b : ℕ),
    (∀ p j v, ρ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) →
    (∀ j ∈ ρ.levels, ρ.maximumAt j = 0) →
    (∀ j ∈ ρ.levels, ρ.sideAt j = s) →
    J ∈ ρ.levels → K ∈ ρ.levels → J < K →
    a ∈ ρ.extPositions J → b ∈ ρ.extPositions K →
    (∀ j ∈ ρ.levels, ∀ p ∈ ρ.extPositions j, p = a ∨ p = b) →
    (match s with | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a) ≤ 5 →
    (∀ p ∈ ρ.childPositions, 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p) →
    let w := (match t with | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a) - 1
    4 ≤ w → ρ.bound ≤ (w + 1).choose 2 + w - 1) :
  let global := match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a
  let active := σ.childPositions.toFinset.filter
    (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
  let ranks := active.biUnion (fun p =>
    Finset.Icc (σ.leftExt t 0 p + 1) (global - 1 - σ.rightExt t 0 p))
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ ranks.card ^ 2) ∧ σ.bound ≤ ranks.card ^ 2 := by
  classical
  have ctx_active_zero_maxima_upper_normalize (σ : Ctx.Context)
    (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
    (hsmall : ∀ p ∈ σ.childPositions, min (σ.cupLimit p p) (σ.capLimit p p) ≤ 3) :
    let active := fun (ρ : Ctx.Context) => ρ.childPositions.toFinset.filter
      (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
    let keep := σ.childPositions.filter (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
    let τ : Ctx.Context := { σ with
      word := (List.range σ.word.length).map (fun p => match (generalizing := false) σ.letterAt p with
        | Ctx.Letter.child => if p ∈ keep then Ctx.Letter.child
            else Ctx.Letter.ext (σ.maxima.length + 1) Ctx.Side.lower
        | Ctx.Letter.ext j v => Ctx.Letter.ext j v)
      maxima := List.replicate σ.maxima.length 0 }
    (∀ p j v, τ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) ∧
      τ.childPositions = keep ∧
      (∀ p ∈ τ.childPositions, 0 < τ.cupLimit p p ∧ 0 < τ.capLimit p p) ∧
      active τ = active σ ∧
      (∀ j ∈ σ.levels, τ.extPositions j = σ.extPositions j ∧
        τ.sideAt j = σ.sideAt j ∧ τ.maximumAt j = 0) ∧
      (∀ s top p, τ.leftExt s top p = σ.leftExt s top p ∧
        τ.rightExt s top p = σ.rightExt s top p) ∧
      (∀ p q, σ.cupLimit p q ≤ τ.cupLimit p q ∧ σ.capLimit p q ≤ τ.capLimit p q) ∧
      (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ τ.bound) ∧ σ.bound ≤ τ.bound := by
    classical
    let active (υ : Context) := υ.childPositions.toFinset.filter
      (fun p => 0 < υ.cupLimit p p ∧ 0 < υ.capLimit p p)
    let keep := σ.childPositions.filter (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
    let ρ : Context := { σ with
      word := (List.range σ.word.length).map (fun p => match σ.letterAt p with
        | Letter.child => if p ∈ keep then Letter.child else Letter.ext (σ.maxima.length + 1) Side.lower
        | Letter.ext j v => Letter.ext j v) }
    let τ : Context := { ρ with maxima := List.replicate σ.maxima.length 0 }
    change (∀ p j v, τ.letterAt p = Letter.ext j v → 1 ≤ j) ∧
      τ.childPositions = keep ∧
      (∀ p ∈ τ.childPositions, 0 < τ.cupLimit p p ∧ 0 < τ.capLimit p p) ∧
      active τ = active σ ∧
      (∀ j ∈ σ.levels, τ.extPositions j = σ.extPositions j ∧
        τ.sideAt j = σ.sideAt j ∧ τ.maximumAt j = 0) ∧
      (∀ s top p, τ.leftExt s top p = σ.leftExt s top p ∧
        τ.rightExt s top p = σ.rightExt s top p) ∧
      (∀ p q, σ.cupLimit p q ≤ τ.cupLimit p q ∧ σ.capLimit p q ≤ τ.capLimit p q) ∧
      (∀ fuel, boundFuel fuel σ ≤ τ.bound) ∧ σ.bound ≤ τ.bound
    have hp := ctx_part_pruning_history_transport σ hpositive keep Side.lower 0
    have hρPos : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j := hp.1
    have hρChild : ρ.childPositions = σ.childPositions.filter (· ∈ keep) := hp.2.1
    have hρHistory : ∀ j ∈ σ.levels, ρ.extPositions j = σ.extPositions j ∧
        ρ.sideAt j = σ.sideAt j := hp.2.2.1
    have hρPure : ∀ s top p, ρ.leftExt s top p = σ.leftExt s top p ∧
        ρ.rightExt s top p = σ.rightExt s top p := hp.2.2.2.2.1
    have hρLimits : ∀ p q, ρ.cupLimit p q = σ.cupLimit p q ∧
        ρ.capLimit p q = σ.capLimit p q := hp.2.2.2.2.2.1
    have hPos : ∀ p j v, τ.letterAt p = Letter.ext j v → 1 ≤ j := hρPos
    have hDepth : ρ.maxima.length = τ.maxima.length := by simp [τ, ρ]
    have hτLevels : τ.levels = ρ.levels := by simp only [levels, ← hDepth]
    have hτLevelsOn (s : Side) (top : ℕ) : τ.levelsOn s top = ρ.levelsOn s top := by
      simp only [levelsOn, hτLevels]
      rfl
    have hZero (j : ℕ) : τ.maximumAt j = 0 := by
      simp only [maximumAt, τ, List.getElem?_replicate]
      split_ifs <;> rfl
    have hComparison := ctx_bound_mono_of_marker_inclusion ρ τ hρPos hPos
      le_rfl le_rfl rfl rfl (fun _ => Iff.rfl) hDepth
      (fun j _ => ⟨rfl, fun _ h => h, by rw [hZero]; exact Nat.zero_le _⟩)
    have hLimits (p q : ℕ) : σ.cupLimit p q ≤ τ.cupLimit p q ∧ σ.capLimit p q ≤ τ.capLimit p q := by
      rw [← (hρLimits p q).1, ← (hρLimits p q).2]
      exact hComparison.1 p q
    have hChild : τ.childPositions = keep := by
      change ρ.childPositions = keep
      rw [hρChild]
      apply List.filter_congr
      intro p hp
      simp [keep, hp]
    have hAllActive : ∀ p ∈ τ.childPositions, 0 < τ.cupLimit p p ∧ 0 < τ.capLimit p p := by
      intro p hp
      rw [hChild] at hp
      have ha : 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p :=
        of_decide_eq_true (List.mem_filter.mp hp).2
      exact ⟨lt_of_lt_of_le ha.1 (hLimits p p).1, lt_of_lt_of_le ha.2 (hLimits p p).2⟩
    have hActive : active τ = active σ := by
      ext p
      simp only [active, Finset.mem_filter, List.mem_toFinset]
      constructor
      · intro hp
        rw [hChild] at hp
        exact ⟨(List.mem_filter.mp hp.1).1, of_decide_eq_true (List.mem_filter.mp hp.1).2⟩
      · intro hp
        have hm : p ∈ τ.childPositions := by rw [hChild]; simp [keep, hp.1, hp.2]
        exact ⟨hm, hAllActive p hm⟩
    have hPure (s : Side) (top p : ℕ) : τ.leftExt s top p = σ.leftExt s top p ∧
        τ.rightExt s top p = σ.rightExt s top p := by
      have ht : τ.leftExt s top p = ρ.leftExt s top p ∧
          τ.rightExt s top p = ρ.rightExt s top p := by
        simp only [leftExt_eq, rightExt_eq, hτLevelsOn]
        exact ⟨rfl, rfl⟩
      exact ⟨ht.1.trans (hρPure s top p).1, ht.2.trans (hρPure s top p).2⟩
    have hPrune := ctx_bound_le_inactive_prune_capacity_three σ hpositive hsmall
    change (∀ fuel, boundFuel fuel σ ≤ ρ.bound) ∧ σ.bound ≤ ρ.bound at hPrune
    refine ⟨hPos, hChild, hAllActive, hActive, ?_, hPure, hLimits,
      fun fuel => (hPrune.1 fuel).trans hComparison.2.2, hPrune.2.trans hComparison.2.2⟩
    intro j hj
    exact ⟨(hρHistory j hj).1, (hρHistory j hj).2, hZero j⟩

  have ctx_two_chosen_markers_bound_of_bare_two_marker_potential (σ : Ctx.Context)
    (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
    (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ)
    (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M)
    (hsides : ∀ j ∈ σ.levels, σ.sideAt j = s)
    (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M)
    (hother : ∀ j ∈ σ.levels, j ≠ N → ∀ p ∈ σ.extPositions j, p = y)
    (hglobal : (match (generalizing := false) s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
    (hwidth : 4 ≤ (match (generalizing := false) t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1)
    (htwo : ∀ (ρ : Ctx.Context) (J K a b : ℕ),
      (∀ p j v, ρ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) →
      (∀ j ∈ ρ.levels, ρ.maximumAt j = 0) →
      (∀ j ∈ ρ.levels, ρ.sideAt j = s) →
      J ∈ ρ.levels → K ∈ ρ.levels → J < K →
      a ∈ ρ.extPositions J → b ∈ ρ.extPositions K →
      (∀ j ∈ ρ.levels, ∀ p ∈ ρ.extPositions j, p = a ∨ p = b) →
      (match (generalizing := false) s with | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a) ≤ 5 →
      (∀ p ∈ ρ.childPositions, 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p) →
      let w := (match (generalizing := false) t with | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a) - 1
      4 ≤ w → ρ.bound ≤ (w + 1).choose 2 + w - 1) :
    let w := (match (generalizing := false) t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1
    (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ (w + 1).choose 2 + w - 1) ∧
      σ.bound ≤ (w + 1).choose 2 + w - 1 := by
    classical
    let w := (match t with | Side.lower => σ.u | Side.upper => σ.a) - 1
    let τ : Context := { σ with word := (List.range σ.word.length).map (fun p =>
      match σ.letterAt p with
      | Letter.child => Letter.child
      | Letter.ext j v => if j = N then
          if p ∈ [x] then Letter.ext N (σ.sideAt N) else Letter.ext (σ.maxima.length + 1) v
          else Letter.ext j v) }
    change (∀ fuel, boundFuel fuel σ ≤ (w + 1).choose 2 + w - 1) ∧
      σ.bound ≤ (w + 1).choose 2 + w - 1
    have hp := ctx_single_level_occurrence_prune_bound_mono σ hpositive N hN [x] x hx (by simp)
    have hPosτ : ∀ p j v, τ.letterAt p = Letter.ext j v → 1 ≤ j := hp.1
    have hHistτ : ∀ j ∈ σ.levels, τ.sideAt j = σ.sideAt j ∧ τ.maximumAt j = σ.maximumAt j ∧
        τ.extPositions j = if j = N then (σ.extPositions j).filter (· ∈ [x]) else σ.extPositions j :=
      hp.2.2.1
    have hSidesτ : ∀ j ∈ τ.levels, τ.sideAt j = s := by
      intro j hj
      exact ((hHistτ j hj).1).trans (hsides j hj)
    have hXτ : x ∈ τ.extPositions N := by
      rw [(hHistτ N hN).2.2, if_pos rfl]
      simp [hx]
    have hYτ : y ∈ τ.extPositions M := by
      rw [(hHistτ M hM).2.2, if_neg (show M ≠ N by omega)]
      exact hy
    have hOnlyτ : ∀ j ∈ τ.levels, ∀ p ∈ τ.extPositions j, p = x ∨ p = y := by
      intro j hj p hp
      rw [(hHistτ j hj).2.2] at hp
      by_cases hjN : j = N
      · rw [if_pos hjN] at hp
        have hm := of_decide_eq_true (List.mem_filter.mp hp).2
        exact Or.inl (List.mem_singleton.mp hm)
      · rw [if_neg hjN] at hp
        exact Or.inr (hother j hj hjN p hp)
    have hOneLeft (ρ : Context) (v : Side) (j p q : ℕ)
        (hj : j ∈ ρ.levelsOn v 0) (hq : q ∈ ρ.extPositions j) (hqp : q < p) :
        1 ≤ ρ.leftExt v 0 p := by
      have hm : q ∈ (ρ.extPositions j).filter (· < p) := by simp [hq, hqp]
      have hnonempty := List.ne_nil_of_mem hm
      have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v 0).sublists.map
        (fun ls => (ls.foldl (leftStep ρ) (p, 0)).2))
        (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
      change _ ≤ ρ.leftExt v 0 p at hv
      simpa only [List.foldl_cons, List.foldl_nil, leftStep,
        List.getLast?_eq_some_getLast hnonempty] using hv
    have hOneRight (ρ : Context) (v : Side) (j p q : ℕ)
        (hj : j ∈ ρ.levelsOn v 0) (hq : q ∈ ρ.extPositions j) (hpq : p < q) :
        1 ≤ ρ.rightExt v 0 p := by
      have hm : q ∈ (ρ.extPositions j).filter (p < ·) := by simp [hq, hpq]
      have hnonempty := List.ne_nil_of_mem hm
      have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v 0).sublists.map
        (fun ls => (ls.foldl (rightStep ρ) (p, 0)).2))
        (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
      change _ ≤ ρ.rightExt v 0 p at hv
      simpa only [List.foldl_cons, List.foldl_nil, rightStep,
        List.head?_eq_some_head hnonempty] using hv
    have hNOnτ : N ∈ τ.levelsOn s 0 := List.mem_filter.mpr ⟨hN, by simp [hSidesτ N hN]⟩
    have hNeτ (p : ℕ) (hp : p ∈ τ.childPositions) : p ≠ x := by
      intro he
      subst p
      have hc := of_decide_eq_true (List.mem_filter.mp hp).2
      have he := (List.mem_filter.mp hXτ).2
      simp [hc] at he
    have hSmallτ : ∀ p ∈ τ.childPositions, min (τ.cupLimit p p) (τ.capLimit p p) ≤ 3 := by
      intro p hp
      have hn := hNeτ p hp
      have hg : (match s with | Side.lower => τ.u | Side.upper => τ.a) ≤ 5 := hglobal
      by_cases hpx : p < x
      · have he := hOneRight τ s N p x hNOnτ hXτ hpx
        cases s <;> simp only [cupLimit, capLimit, chainExt] at hg ⊢ <;> omega
      · have he := hOneLeft τ s N p x hNOnτ hXτ (by omega)
        cases s <;> simp only [cupLimit, capLimit, chainExt] at hg ⊢ <;> omega
    let live := τ.childPositions.filter (fun p => 0 < τ.cupLimit p p ∧ 0 < τ.capLimit p p)
    let ρ : Context := { τ with
      word := (List.range τ.word.length).map (fun p => match τ.letterAt p with
        | Letter.child => if p ∈ live then Letter.child else Letter.ext (τ.maxima.length + 1) Side.lower
        | Letter.ext j v => Letter.ext j v)
      maxima := List.replicate τ.maxima.length 0 }
    have hz := ctx_active_zero_maxima_upper_normalize τ hPosτ hSmallτ
    have hPosρ : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j := hz.1
    have hActiveρ : ∀ p ∈ ρ.childPositions, 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p := hz.2.2.1
    have hHistρ : ∀ j ∈ τ.levels, ρ.extPositions j = τ.extPositions j ∧
        ρ.sideAt j = τ.sideAt j ∧ ρ.maximumAt j = 0 := hz.2.2.2.2.1
    have hDepth : τ.maxima.length = ρ.maxima.length := by simp [ρ]
    have hLevels : ρ.levels = τ.levels := by simp only [levels, ← hDepth]
    have hNρ : N ∈ ρ.levels := by rw [hLevels]; exact hN
    have hMρ : M ∈ ρ.levels := by rw [hLevels]; exact hM
    have hZeroρ : ∀ j ∈ ρ.levels, ρ.maximumAt j = 0 := by
      intro j hj
      rw [hLevels] at hj
      exact (hHistρ j hj).2.2
    have hSidesρ : ∀ j ∈ ρ.levels, ρ.sideAt j = s := by
      intro j hj
      rw [hLevels] at hj
      exact (hHistρ j hj).2.1.trans (hSidesτ j hj)
    have hXρ : x ∈ ρ.extPositions N := by rw [(hHistρ N hN).1]; exact hXτ
    have hYρ : y ∈ ρ.extPositions M := by rw [(hHistρ M hM).1]; exact hYτ
    have hOnlyρ : ∀ j ∈ ρ.levels, ∀ p ∈ ρ.extPositions j, p = x ∨ p = y := by
      intro j hj p hp
      rw [hLevels] at hj
      rw [(hHistρ j hj).1] at hp
      exact hOnlyτ j hj p hp
    have hFinal : ρ.bound ≤ (w + 1).choose 2 + w - 1 :=
      htwo ρ N M x y hPosρ hZeroρ hSidesρ hNρ hMρ hNM hXρ hYρ hOnlyρ hglobal hActiveρ hwidth
    have hFuelPrune : ∀ fuel, boundFuel fuel σ ≤ boundFuel fuel τ := hp.2.2.2.2.2.1
    have hFullPrune : σ.bound ≤ τ.bound := hp.2.2.2.2.2.2
    have hFuelZero : ∀ fuel, boundFuel fuel τ ≤ ρ.bound := hz.2.2.2.2.2.2.2.1
    have hFullZero : τ.bound ≤ ρ.bound := hz.2.2.2.2.2.2.2.2
    exact ⟨fun fuel => (hFuelPrune fuel).trans ((hFuelZero fuel).trans hFinal),
      hFullPrune.trans (hFullZero.trans hFinal)⟩

  have ctx_exterior_pivot_complement_cut_square_of_bare_two_marker_potential (σ : Ctx.Context)
    (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
    (s t : Ctx.Side) (hne : s ≠ t) (N x : ℕ)
    (hN : N ∈ σ.levels) (hNs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N)
    (hsides : ∀ j ∈ σ.levels, σ.sideAt j = s)
    (hglobal : (match (generalizing := false) s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
    (hyoung : ∀ j ∈ σ.levelsOn s N, σ.extPositions j = [])
    (hclear : σ.levelsOn t 0 = [])
    (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ p ∈ σ.extPositions j, p = x)
    (hwidth : 4 ≤ (match (generalizing := false) t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1)
    (keep : List ℕ) (q₀ l r m n : ℕ)
    (hq₀ : q₀ ∈ keep) (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions)
    (hl : l ∈ σ.childPositions) (hr : r ∈ σ.childPositions)
    (hlnot : l ∉ keep) (hrnot : r ∉ keep)
    (hinside : ∀ p ∈ keep, l < p ∧ p < r)
    (houtside : (∀ p ∈ keep, p < x) ∨ (∀ p ∈ keep, x < p))
    (htwo : ∀ (ρ : Ctx.Context) (J K a b : ℕ),
      (∀ p j v, ρ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) →
      (∀ j ∈ ρ.levels, ρ.maximumAt j = 0) →
      (∀ j ∈ ρ.levels, ρ.sideAt j = s) →
      J ∈ ρ.levels → K ∈ ρ.levels → J < K →
      a ∈ ρ.extPositions J → b ∈ ρ.extPositions K →
      (∀ j ∈ ρ.levels, ∀ p ∈ ρ.extPositions j, p = a ∨ p = b) →
      (match (generalizing := false) s with | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a) ≤ 5 →
      (∀ p ∈ ρ.childPositions, 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p) →
      let w := (match (generalizing := false) t with | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a) - 1
      4 ≤ w → ρ.bound ≤ (w + 1).choose 2 + w - 1) :
    let w := (match (generalizing := false) t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1
    let rest := σ.childPositions.filter (· ∉ keep)
    (∀ f g, Ctx.Context.boundFuel f (σ.part rest s m) +
      Ctx.Context.boundFuel g (σ.part keep t n) ≤ w ^ 2) ∧
      (σ.part rest s m).bound + (σ.part keep t n).bound ≤ w ^ 2 := by
    classical
    let w := (match t with | Side.lower => σ.u | Side.upper => σ.a) - 1
    let rest := σ.childPositions.filter (· ∉ keep)
    let α := σ.part rest s m
    let β := σ.part keep t n
    change (∀ f g, boundFuel f α + boundFuel g β ≤ w ^ 2) ∧ α.bound + β.bound ≤ w ^ 2
    have hRest (p : ℕ) : p ∈ rest ↔ p ∈ σ.childPositions ∧ p ∉ keep := by
      simp only [rest, List.mem_filter, decide_eq_true_eq]
    have hChildα (p : ℕ) : p ∈ α.childPositions ↔ p ∈ rest := by
      simp only [α, part_childPositions, rest, List.mem_filter, decide_eq_true_eq]
      tauto
    have hChildβ (p : ℕ) : p ∈ β.childPositions ↔ p ∈ σ.childPositions ∧ p ∈ keep := by
      simp only [β, part_childPositions, List.mem_filter, decide_eq_true_eq]
    have hExtα (p : ℕ) : p ∈ α.extPositions 1 ↔ p ∈ σ.childPositions ∧ p ∈ keep := by
      rw [part_extPositions_one hpositive]
      simp only [rest, List.mem_filter, decide_eq_true_eq]
      tauto
    have hExtβ (p : ℕ) : p ∈ β.extPositions 1 ↔ p ∈ rest := by
      rw [part_extPositions_one hpositive]
    have hQα : q₀ ∈ α.extPositions 1 := (hExtα q₀).mpr ⟨hkeep q₀ hq₀, hq₀⟩
    have hLβ : l ∈ β.extPositions 1 := (hExtβ l).mpr ((hRest l).mpr ⟨hl, hlnot⟩)
    have hRβ : r ∈ β.extPositions 1 := (hExtβ r).mpr ((hRest r).mpr ⟨hr, hrnot⟩)
    have hSideα : α.sideAt 1 = s := part_sideAt_one_of_mem hpositive rest s m hQα
    have hSideβ : β.sideAt 1 = t := part_sideAt_one_of_mem hpositive keep t n hLβ
    have hPositivePart (ks : List ℕ) (v : Side) (q₀ : ℕ) :
        ∀ p j z, (σ.part ks v q₀).letterAt p = Letter.ext j z → 1 ≤ j := by
      intro p j z hp
      have hpl : p < σ.word.length := by
        by_contra h
        have hh := letterAt_of_length_le (σ.part ks v q₀)
          (show (σ.part ks v q₀).word.length ≤ p by rw [part_word_length]; omega)
        rw [hh] at hp
        cases hp
      cases he : σ.letterAt p with
      | child =>
        rw [part_letterAt_of_child σ ks v q₀ hpl he] at hp
        split at hp
        · cases hp
        · cases hp; omega
      | ext oldLevel oldSide =>
        rw [part_letterAt_of_ext σ ks v q₀ hpl he] at hp
        cases hp; omega
    have hPosα := hPositivePart rest s m
    have hPosβ := hPositivePart keep t n
    have hOneα : 1 ∈ α.levels := by simp only [α, part_levels, List.mem_cons, true_or]
    have hNpos := one_le_of_mem_levels hN
    have hNα : N + 1 ∈ α.levels := by
      rw [part_levels]
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨N, hN, rfl⟩)
    have hNβ : N + 1 ∈ β.levels := by
      rw [part_levels]
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨N, hN, rfl⟩)
    have hNsα : α.sideAt (N + 1) = s := (part_sideAt_succ σ rest s m hNpos).trans hNs
    have hNsβ : β.sideAt (N + 1) = s := (part_sideAt_succ σ keep t n hNpos).trans hNs
    have hXα : x ∈ α.extPositions (N + 1) := by rw [part_extPositions_succ σ rest s m hNpos]; exact hx
    have hXβ : x ∈ β.extPositions (N + 1) := by rw [part_extPositions_succ σ keep t n hNpos]; exact hx
    have hYoungβ : ∀ j ∈ β.levelsOn s (N + 1), β.extPositions j = [] := by
      have hs : β.sideAt 1 ≠ s := by rw [hSideβ]; exact Ne.symm hne
      have he := part_levelsOn_other_succ hs hNpos
      intro j hj
      rw [he] at hj
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
      rw [part_extPositions_succ σ keep t n (one_le_of_mem_levels (List.mem_filter.mp hi).1), hyoung i hi]
    have hLevelsβ : β.levelsOn t 0 = [1] := by
      rw [part_levelsOn_self_zero hSideβ, hclear]
      rfl
    have hw : 4 ≤ w := hwidth
    let activeβ := β.childPositions.toFinset.filter
      (fun p => 0 < β.cupLimit p p ∧ 0 < β.capLimit p p)
    let Iβ (p : ℕ) := Finset.Icc (β.leftExt t 0 p + 1) (w - β.rightExt t 0 p)
    let ranksβ := activeβ.biUnion Iβ
    let J := Finset.Icc 2 (w - 1)
    have hIntervalβ (p : ℕ) (hp : p ∈ β.childPositions) : Iβ p = J := by
      have hpk := ((hChildβ p).mp hp).2
      have hpl := (hinside p hpk).1
      have hpr := (hinside p hpk).2
      have hMemL : l ∈ (β.extPositions 1).filter (· < p) := by simp [hLβ, hpl]
      have hMemR : r ∈ (β.extPositions 1).filter (p < ·) := by simp [hRβ, hpr]
      have hNEL := List.ne_nil_of_mem hMemL
      have hNER := List.ne_nil_of_mem hMemR
      have hLeft : β.leftExt t 0 p = 1 := by
        unfold leftExt
        rw [hLevelsβ]
        change ([0, (match ((β.extPositions 1).filter (· < p)).getLast? with
          | some q => (q, 1) | none => (p, 0)).2].max?).getD 0 = 1
        rw [List.getLast?_eq_some_getLast hNEL]
        rfl
      have hRight : β.rightExt t 0 p = 1 := by
        unfold rightExt
        rw [hLevelsβ]
        change ([0, (match ((β.extPositions 1).filter (p < ·)).head? with
          | some q => (q, 1) | none => (p, 0)).2].max?).getD 0 = 1
        rw [List.head?_eq_some_head hNER]
        rfl
      simp only [Iβ, J, hLeft, hRight]
    have hJCard : J.card = w - 2 := by simp only [J, Nat.card_Icc]; omega
    have hRanksβSub : ranksβ ⊆ J := by
      intro z hz
      obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
      rw [hIntervalβ p (List.mem_toFinset.mp (Finset.mem_filter.mp hp).1)] at hz
      exact hz
    have hRanksβCard : ranksβ.card ≤ w - 2 := by
      rw [← hJCard]
      exact Finset.card_le_card hRanksβSub
    have hOldα : ∀ j ∈ α.levelsOn s 0, 1 < j → ∀ p ∈ α.extPositions j, p = x := by
      intro j hj hj1 p hp
      rw [part_levelsOn_self_zero hSideα] at hj
      rcases List.mem_cons.mp hj with rfl | hj
      · omega
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
        rw [part_extPositions_succ σ rest s m (one_le_of_mem_levels (List.mem_filter.mp hi).1)] at hp
        exact hchosen i hi p hp
    have hSidesα : ∀ j ∈ α.levels, α.sideAt j = s := by
      intro j hj
      rw [part_levels] at hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hSideα
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
        exact (part_sideAt_succ σ rest s m (one_le_of_mem_levels hi)).trans (hsides i hi)
    have hOtherα : ∀ j ∈ α.levels, j ≠ 1 → ∀ p ∈ α.extPositions j, p = x := by
      intro j hj hj1 p hp
      have hjOn : j ∈ α.levelsOn s 0 := List.mem_filter.mpr ⟨hj, by simp [hSidesα j hj]⟩
      have hjPos := one_le_of_mem_levels hj
      exact hOldα j hjOn (by omega) p hp
    have hOwn : (∀ fuel, boundFuel fuel α ≤ (w + 1).choose 2 + w - 1) ∧
        α.bound ≤ (w + 1).choose 2 + w - 1 :=
      ctx_two_chosen_markers_bound_of_bare_two_marker_potential α hPosα s t hne
        1 (N + 1) q₀ x hOneα hNα (by omega) hSidesα hQα hXα hOtherα hglobal hwidth htwo
    let Q (S : Finset ℕ) := (S.product S).filter (fun z => z.1 ≤ z.2)
    let pairsβ := activeβ.biUnion (fun p => Q (Iβ p))
    have hPairsβSub : pairsβ ⊆ Q J := by
      intro z hz
      obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
      rw [hIntervalβ p (List.mem_toFinset.mp (Finset.mem_filter.mp hp).1)] at hz
      exact hz
    have hCardPairs (T : Finset ℕ) : (Q T).card = (T.card + 1).choose 2 := by
      rw [← Finset.card_sym2]
      apply Finset.card_bij (fun z _ => Sym2.mk z.1 z.2)
      · intro z hz
        exact Finset.mk_mem_sym2_iff.mpr (Finset.mem_product.mp (Finset.mem_filter.mp hz).1)
      · intro p hp q hq he
        have hpl := (Finset.mem_filter.mp hp).2
        have hql := (Finset.mem_filter.mp hq).2
        rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Prod.ext h1 h2
        · apply Prod.ext <;> omega
      · intro z hz
        induction z using Sym2.ind with
        | h a b =>
          obtain ⟨ha, hb⟩ := Finset.mk_mem_sym2_iff.mp hz
          by_cases hab : a ≤ b
          · exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩, rfl⟩
          · exact ⟨(b, a), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hb, ha⟩, by omega⟩,
              Sym2.eq_swap⟩
    have hPairsβCard : pairsβ.card ≤ (w - 1).choose 2 := by
      have hh := Finset.card_le_card hPairsβSub
      rw [hCardPairs, hJCard] at hh
      have hw1 : w - 2 + 1 = w - 1 := by omega
      rw [hw1] at hh
      exact hh
    obtain ⟨direction, hBoundary⟩ : ∃ direction : Bool, ∀ p ∈ β.childPositions,
        if direction then p < x else x < p := by
      rcases houtside with h | h
      · exact ⟨true, fun p hp => h p ((hChildβ p).mp hp).2⟩
      · exact ⟨false, fun p hp => h p ((hChildβ p).mp hp).2⟩
    have hSmallβ : min ((match β.sideAt (N + 1) with | Side.lower => β.u | Side.upper => β.a) - 1)
        (β.k - β.maximumAt (N + 1)) ≤ 4 := by
      rw [hNsβ]
      change min ((match s with | Side.lower => σ.u | Side.upper => σ.a) - 1) _ ≤ 4
      omega
    have hOther : (∀ fuel, boundFuel fuel β ≤ (w - 1).choose 2) ∧ β.bound ≤ (w - 1).choose 2 := by
      have hh := ctx_active_boundary_marker_rank_pair_union_bound β hPosβ (N + 1) x hNβ hXβ
        direction (by intro p hp hact; exact hBoundary p hp)
        (by
          intro j hj p hp
          rw [hNsβ] at hj
          rw [hYoungβ j hj] at hp
          exact False.elim (List.not_mem_nil hp))
        t (by rw [hNsβ]; exact hne) hSmallβ
      change (∀ fuel, boundFuel fuel β ≤ pairsβ.card) ∧ β.bound ≤ pairsβ.card at hh
      exact ⟨fun fuel => (hh.1 fuel).trans hPairsβCard, hh.2.trans hPairsβCard⟩
    have hTwoChoose (n : ℕ) : 2 * (n + 1).choose 2 = n * n + n := by
      induction n with
      | zero => norm_num
      | succ n ih =>
        rw [Nat.choose_succ_succ, Nat.choose_one_right]
        nlinarith
    have hBudget : ((w + 1).choose 2 + w - 1) + (w - 1).choose 2 = w ^ 2 := by
      have h1 := hTwoChoose w
      have h2 := hTwoChoose (w - 2)
      have hw1 : w - 2 + 1 = w - 1 := by omega
      have hw2 : w - 2 + 2 = w := by omega
      have hp1 : (w + 1).choose 2 + w - 1 + 1 = (w + 1).choose 2 + w := by omega
      rw [hw1] at h2
      nlinarith
    constructor
    · intro f g
      exact (Nat.add_le_add (hOwn.1 f) (hOther.1 g)).trans_eq hBudget
    · exact (Nat.add_le_add hOwn.2 hOther.2).trans_eq hBudget

  have ctx_bare_marker_square_width_step_of_two_marker_potential (σ : Ctx.Context)
    (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
    (s t : Ctx.Side) (hne : s ≠ t) (N x : ℕ)
    (hzero : ∀ j ∈ σ.levels, σ.maximumAt j = 0)
    (hsides : ∀ j ∈ σ.levels, σ.sideAt j = s)
    (hN : N ∈ σ.levels) (hx : x ∈ σ.extPositions N)
    (hactual : ∀ j ∈ σ.levels, ∀ p ∈ σ.extPositions j, p = x)
    (hglobal : (match (generalizing := false) s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
    (hactive : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
    (hwidth : 4 ≤ (match (generalizing := false) t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1)
    (htwo : ∀ (ρ : Ctx.Context) (J K a b : ℕ),
      (∀ p j v, ρ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) →
      (∀ j ∈ ρ.levels, ρ.maximumAt j = 0) →
      (∀ j ∈ ρ.levels, ρ.sideAt j = s) →
      J ∈ ρ.levels → K ∈ ρ.levels → J < K →
      a ∈ ρ.extPositions J → b ∈ ρ.extPositions K →
      (∀ j ∈ ρ.levels, ∀ p ∈ ρ.extPositions j, p = a ∨ p = b) →
      (match (generalizing := false) s with | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a) ≤ 5 →
      (∀ p ∈ ρ.childPositions, 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p) →
      let w := (match (generalizing := false) t with | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a) - 1
      4 ≤ w → ρ.bound ≤ (w + 1).choose 2 + w - 1)
    (hsmaller : ∀ (ρ : Ctx.Context) (J y : ℕ),
      (∀ p j v, ρ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) →
      (∀ j ∈ ρ.levels, ρ.maximumAt j = 0) →
      (∀ j ∈ ρ.levels, ρ.sideAt j = s) →
      J ∈ ρ.levels → y ∈ ρ.extPositions J →
      (∀ j ∈ ρ.levels, ∀ p ∈ ρ.extPositions j, p = y) →
      (match (generalizing := false) s with | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a) ≤ 5 →
      (∀ p ∈ ρ.childPositions, 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p) →
      let v := (match (generalizing := false) t with | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a) - 1
      v < (match (generalizing := false) t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1 → ρ.bound ≤ v ^ 2) :
    let w := (match (generalizing := false) t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1
    (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ w ^ 2) ∧ σ.bound ≤ w ^ 2 := by
    classical
    have hOneLeft (ρ : Context) (v : Side) (j p q : ℕ)
        (hj : j ∈ ρ.levelsOn v 0) (hq : q ∈ ρ.extPositions j) (hqp : q < p) :
        1 ≤ ρ.leftExt v 0 p := by
      have hm : q ∈ (ρ.extPositions j).filter (· < p) := by simp [hq, hqp]
      have hnonempty := List.ne_nil_of_mem hm
      have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v 0).sublists.map
        (fun ls => (ls.foldl (leftStep ρ) (p, 0)).2))
        (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
      change _ ≤ ρ.leftExt v 0 p at hv
      simpa only [List.foldl_cons, List.foldl_nil, leftStep,
        List.getLast?_eq_some_getLast hnonempty] using hv
    have hOneRight (ρ : Context) (v : Side) (j p q : ℕ)
        (hj : j ∈ ρ.levelsOn v 0) (hq : q ∈ ρ.extPositions j) (hpq : p < q) :
        1 ≤ ρ.rightExt v 0 p := by
      have hm : q ∈ (ρ.extPositions j).filter (p < ·) := by simp [hq, hpq]
      have hnonempty := List.ne_nil_of_mem hm
      have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v 0).sublists.map
        (fun ls => (ls.foldl (rightStep ρ) (p, 0)).2))
        (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
      change _ ≤ ρ.rightExt v 0 p at hv
      simpa only [List.foldl_cons, List.foldl_nil, rightStep,
        List.head?_eq_some_head hnonempty] using hv
    let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
    let C (ρ : Context) (v : Side) (p : ℕ) := match v with
      | Side.lower => ρ.cupLimit p p | Side.upper => ρ.capLimit p p
    let w := G σ t - 1
    let Convex (ρ : Context) (ks : List ℕ) := ∀ a ∈ ks, ∀ b ∈ ks,
      ∀ z ∈ ρ.childPositions, a ≤ z → z ≤ b → z ∈ ks
    change (∀ fuel, boundFuel fuel σ ≤ w ^ 2) ∧ σ.bound ≤ w ^ 2
    have hw : 4 ≤ w := hwidth
    have hNs : σ.sideAt N = s := hsides N hN
    have hNpos := one_le_of_mem_levels hN
    have hNOn : N ∈ σ.levelsOn s 0 := List.mem_filter.mpr ⟨hN, by simp [hNs]⟩
    have hBaseThree (p k : ℕ) (hp : p ≤ k - 1) : baseOf 3 p k ≤ (p + 1).choose 2 := by
      by_cases hp0 : p = 0
      · subst p
        simp [baseOf]
      by_cases hp1 : p = 1
      · subst p
        norm_num [baseOf]
      have hp2 : 2 ≤ p := by omega
      simp only [baseOf, if_neg (show ¬(3 = 0 ∨ p = 0) by omega),
        if_neg (show ¬(3 = 1 ∨ p = 1) by omega)]
      by_cases hpk : p + 2 ≤ k
      · rw [decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
        have hrow : p + 1 + (3 + 1) - 4 = p + 1 := by omega
        have hcol : p + 1 - 2 = (p + 1) - 2 := rfl
        rw [hrow]
        exact (Nat.choose_symm (show 2 ≤ p + 1 by omega)).le
      · have hk : k = p + 1 := by omega
        subst k
        rw [decomposableThreshold_eq_window (by omega) (by omega) (by omega)]
        have hwindow : decomposableBinomialWindow (p + 1) (3 + 1) (p + 1) =
            1 + (p - 1) + (p - 1).choose 2 := by
          have hr : p + 1 - 2 = p - 1 := by omega
          norm_num [decomposableBinomialWindow, hr, Finset.sum_Icc_succ_top]
        rw [hwindow]
        have hp' : p = (p - 1) + 1 := by omega
        have hpascal : (p + 1).choose 2 = (p - 1).choose 2 + (p - 1) + p := by
          calc
            (p + 1).choose 2 = p + p.choose 2 := by simp [Nat.choose_succ_succ']
            _ = (p - 1).choose 2 + (p - 1) + p := by
              conv_lhs => arg 2; rw [hp']
              simp [Nat.choose_succ_succ']
              omega
        omega
    have hBaseLower (c p k : ℕ) (hc : c ≤ 3) (hp : p ≤ k - 1) :
        baseOf c p k ≤ (p + 1).choose 2 :=
      (baseOf_mono hc le_rfl).trans (hBaseThree p k hp)
    have hBaseSwap (x y k : ℕ) (hx : x ≤ k - 1) (hy : y ≤ k - 1) :
        baseOf x y k = baseOf y x k := by
      have hz (r : ℕ) : baseOf 0 r k = 0 := by simp [baseOf]
      have hz' (r : ℕ) : baseOf r 0 k = 0 := by simp [baseOf]
      apply Nat.le_antisymm
      · have hh := ctx_base_cross_axis_transfer 0 y x x k le_rfl hx (by omega)
        simpa only [Nat.zero_add, hz, hz', Nat.add_zero] using hh
      · have hh := ctx_base_cross_axis_transfer 0 x y y k le_rfl hy (by omega)
        simpa only [Nat.zero_add, hz, hz', Nat.add_zero] using hh
    have hBaseUpper (c p k : ℕ) (hp : p ≤ 3) (hc : c ≤ k - 1) (hpk : p ≤ k - 1) :
        baseOf c p k ≤ (c + 1).choose 2 := by
      rw [hBaseSwap c p k hc hpk]
      exact hBaseLower p c k hp hc
    have hBlockConvex (ρ : Context) (ks : List ℕ) (hk : ks ∈ ρ.blocks) : Convex ρ ks := by
      obtain ⟨i, l, _, _, hwindow⟩ := exists_take_drop_of_mem_blocks hk
      have hinfix : ks <:+: ρ.childPositions := by
        refine ⟨ρ.childPositions.take i, (ρ.childPositions.drop i).drop (l+1), ?_⟩
        rw [hwindow, List.append_assoc, List.take_append_drop, List.take_append_drop]
      obtain ⟨pre, post, he⟩ := hinfix
      have he' : pre ++ (ks ++ post) = ρ.childPositions := by simpa only [List.append_assoc] using he
      have hs : (pre ++ (ks ++ post)).Pairwise (· < ·) := by
        rw [he']
        exact childPositions_pairwise ρ
      have hbefore : ∀ a ∈ pre, ∀ b ∈ ks, a < b := by
        intro a ha b hb
        exact (List.pairwise_append.mp hs).2.2 a ha b (List.mem_append_left post hb)
      have hafter : ∀ a ∈ ks, ∀ b ∈ post, a < b :=
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
    have hNe (p : ℕ) (hp : p ∈ σ.childPositions) : p ≠ x := by
      intro he
      subst p
      have hc := of_decide_eq_true (List.mem_filter.mp hp).2
      have he := (List.mem_filter.mp hx).2
      simp [hc] at he
    have hSmallChosen (p : ℕ) (hp : p ∈ σ.childPositions) : C σ s p ≤ 3 := by
      have hn := hNe p hp
      by_cases hpx : p < x
      · have he := hOneRight σ s N p x hNOn hx hpx
        cases s <;> simp only [C, cupLimit, capLimit, chainExt] at hglobal ⊢ <;> omega
      · have he := hOneLeft σ s N p x hNOn hx (by omega)
        cases s <;> simp only [C, cupLimit, capLimit, chainExt] at hglobal ⊢ <;> omega
    have hOppCap (p : ℕ) : C σ t p ≤ w := by
      cases t <;> simp only [C, w, G, cupLimit, capLimit] <;> omega
    have hTwoChoose (n : ℕ) : 2 * (n + 1).choose 2 = n * n + n := by
      induction n with
      | zero => norm_num
      | succ n ih =>
        rw [Nat.choose_succ_succ, Nat.choose_one_right]
        nlinarith
    have hTriangle : (w + 1).choose 2 ≤ w ^ 2 := by
      have hh := hTwoChoose w
      nlinarith
    have hBase : σ.base ≤ w ^ 2 := by
      rw [base_eq_baseOf]
      cases he : σ.childPositions.head? with
      | none => exact Nat.zero_le _
      | some p =>
        have hp := List.mem_of_mem_head? (Option.mem_def.mpr he)
        have hc := hSmallChosen p hp
        have hcupk : σ.cupLimit p p ≤ σ.k - 1 := by dsimp only [cupLimit]; omega
        have hcapk : σ.capLimit p p ≤ σ.k - 1 := by dsimp only [capLimit]; omega
        have hleaf : baseOf (σ.cupLimit p p) (σ.capLimit p p) σ.k ≤ (C σ t p + 1).choose 2 := by
          cases s <;> cases t
          · exact False.elim (hne rfl)
          · exact hBaseLower _ _ _ hc hcapk
          · exact hBaseUpper _ _ _ hc hcupk hcapk
          · exact False.elim (hne rfl)
        exact hleaf.trans ((Nat.choose_le_choose 2 (Nat.add_le_add_right (hOppCap p) 1)).trans hTriangle)
    have hclear : σ.levelsOn t 0 = [] := by
      unfold levelsOn
      apply List.filter_eq_nil_iff.mpr
      intro j hj hbad
      have ht := of_decide_eq_true hbad
      exact hne ((hsides j hj).symm.trans ht.1)
    have hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ p ∈ σ.extPositions j, p = x := by
      intro j hj p hp
      exact hactual j (List.mem_filter.mp hj).1 p hp
    have hyoung : ∀ j ∈ σ.levelsOn s N, σ.extPositions j = [] := by
      intro j hj
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro p hp
      have he := hactual j (List.mem_filter.mp hj).1 p hp
      subst p
      have hxj := (List.mem_filter.mp hp).2
      have hxN := (List.mem_filter.mp hx).2
      have hjN : j = N := by
        cases hletter : σ.letterAt x <;> simp [hletter] at hxj hxN
        omega
      have hlt := of_decide_eq_true (List.mem_filter.mp hj).2
      omega
    have hLower (d : ℕ) (hd : 0 < d) (ρ : Context) (J y : ℕ)
        (hpos : ∀ p j v, ρ.letterAt p = Letter.ext j v → 1 ≤ j)
        (hz : ∀ j ∈ ρ.levels, ρ.maximumAt j = 0)
        (hs : ∀ j ∈ ρ.levels, ρ.sideAt j = s)
        (hJ : J ∈ ρ.levels) (hy : y ∈ ρ.extPositions J)
        (ha : ∀ j ∈ ρ.levels, ∀ p ∈ ρ.extPositions j, p = y)
        (hg : G ρ s ≤ 5)
        (hact : ∀ p ∈ ρ.childPositions, 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
        (hv : G ρ t - 1 ≤ w - d) : ρ.bound ≤ (G ρ t - 1) ^ 2 := by
      exact hsmaller ρ J y hpos hz hs hJ hy ha hg hact (by change G ρ t - 1 < w; omega)
    have hCut (keep : List ℕ) (hk : keep ∈ σ.blocks) (m n f g : ℕ) :
        (boundFuel f (σ.part keep s m) +
          boundFuel g (σ.part (σ.childPositions.filter (· ∉ keep)) t n) ≤ w ^ 2) ∧
        (boundFuel f (σ.part (σ.childPositions.filter (· ∉ keep)) s m) +
          boundFuel g (σ.part keep t n) ≤ w ^ 2) := by
      obtain ⟨hkl, hkne, hksub⟩ := mem_blocks hk
      obtain ⟨q₀, hq₀⟩ := List.exists_mem_of_ne_nil _ hkne
      have hremoved : ∃ q ∈ σ.childPositions, q ∉ keep := by
        by_contra h
        push Not at h
        have hlen := ((childPositions_nodup σ).subperm h).length_le
        omega
      obtain ⟨r₀, hr₀, hrnot⟩ := hremoved
      let rest := σ.childPositions.filter (· ∉ keep)
      have hrest (p : ℕ) : p ∈ rest ↔ p ∈ σ.childPositions ∧ p ∉ keep := by simp [rest]
      have hrrest : r₀ ∈ rest := (hrest r₀).mpr ⟨hr₀, hrnot⟩
      have hqnot : q₀ ∉ rest := by simp [rest, hq₀]
      have hconv := hBlockConvex σ keep hk
      have hOutside (p : ℕ) (hp : p ∈ rest) :
          (∀ q ∈ keep, p < q) ∨ (∀ q ∈ keep, q < p) := by
        have hpc := (hrest p).mp hp
        by_cases hpq : p < q₀
        · left
          intro q hq
          by_contra hbad
          exact hpc.2 (hconv q hq q₀ hq₀ p hpc.1 (by omega) (by omega))
        · right
          intro q hq
          by_contra hbad
          exact hpc.2 (hconv q₀ hq₀ q hq p hpc.1 (by omega) (by omega))
      have hEnd (direction : Bool)
          (he : ∀ p ∈ keep, ∀ q ∈ σ.childPositions, q ∉ keep →
            if direction then p < q else q < p) :
          (boundFuel f (σ.part keep s m) + boundFuel g (σ.part rest t n) ≤ w ^ 2) ∧
          (boundFuel f (σ.part rest s m) + boundFuel g (σ.part keep t n) ≤ w ^ 2) := by
        have hforward := ctx_endpoint_cut_square_of_bounded_bare_square σ hpositive s t hne N x
          hN hNs hx hglobal hyoung hclear hchosen (by change 2 ≤ w; omega)
          keep q₀ r₀ m n direction hq₀ hksub hr₀ hrnot he (hLower 1 (by omega))
        have hreverse : ∀ p ∈ rest, ∀ q ∈ σ.childPositions, q ∉ rest →
            if !direction then p < q else q < p := by
          intro p hp q hq hqn
          have hpk := (hrest p).mp hp
          have hqk : q ∈ keep := by simpa [rest, hq] using hqn
          have hh := he q hqk p hpk.1 hpk.2
          cases direction <;> simpa using hh
        have hbackward := ctx_endpoint_cut_square_of_bounded_bare_square σ hpositive s t hne N x
          hN hNs hx hglobal hyoung hclear hchosen (by change 2 ≤ w; omega)
          rest r₀ q₀ m n (!direction) hrrest (fun p hp => ((hrest p).mp hp).1)
          (hksub q₀ hq₀) hqnot hreverse (hLower 1 (by omega))
        have hdouble : σ.part (σ.childPositions.filter (· ∉ rest)) t n = σ.part keep t n := by
          apply part_congr
          intro p hp
          simp [rest, hp]
        exact ⟨hforward.1 f g, by simpa only [hdouble] using hbackward.1 f g⟩
      by_cases hL : ∃ l ∈ rest, ∀ p ∈ keep, l < p
      · obtain ⟨l, hlrest, hlbefore⟩ := hL
        by_cases hR : ∃ r ∈ rest, ∀ p ∈ keep, p < r
        · obtain ⟨r, hrrest, hrafter⟩ := hR
          have hl := (hrest l).mp hlrest
          have hr := (hrest r).mp hrrest
          have hinside : ∀ p ∈ keep, l < p ∧ p < r := fun p hp => ⟨hlbefore p hp, hrafter p hp⟩
          have hforward := ctx_internal_interval_cut_square_of_empty_opposite_history σ hpositive
            s t hne N x hN hNs hx hglobal hyoung hclear (by change 2 ≤ w; omega)
            keep q₀ l r m n hq₀ hksub hl.1 hr.1 hl.2 hr.2 hinside hconv
          refine ⟨hforward.1 f g, ?_⟩
          by_cases hA : ∃ a ∈ keep, a < x
          · obtain ⟨a, ha, hax⟩ := hA
            by_cases hB : ∃ b ∈ keep, x < b
            · obtain ⟨b, hb, hxb⟩ := hB
              exact (ctx_bracketed_pivot_complement_cut_square_of_bounded_bare_square σ hpositive
                s t hne N x hN hNs hx hglobal hyoung hclear hchosen (by change 2 ≤ w; omega)
                keep a b l r m n ha hb hax hxb hksub hl.1 hr.1 hl.2 hr.2 hinside hconv
                (hLower 2 (by omega))).1 f g
            · have hout : ∀ p ∈ keep, p < x := by
                intro p hp
                have hn := hNe p (hksub p hp)
                have hn' : ¬x < p := fun hh => hB ⟨p, hp, hh⟩
                omega
              exact (ctx_exterior_pivot_complement_cut_square_of_bare_two_marker_potential σ hpositive
                s t hne N x hN hNs hx hsides hglobal hyoung hclear hchosen hwidth
                keep q₀ l r m n hq₀ hksub hl.1 hr.1 hl.2 hr.2 hinside (Or.inl hout) htwo).1 f g
          · have hout : ∀ p ∈ keep, x < p := by
              intro p hp
              have hn := hNe p (hksub p hp)
              have hn' : ¬p < x := fun hh => hA ⟨p, hp, hh⟩
              omega
            exact (ctx_exterior_pivot_complement_cut_square_of_bare_two_marker_potential σ hpositive
              s t hne N x hN hNs hx hsides hglobal hyoung hclear hchosen hwidth
              keep q₀ l r m n hq₀ hksub hl.1 hr.1 hl.2 hr.2 hinside (Or.inr hout) htwo).1 f g
        · apply hEnd false
          intro p hp q hq hqnot
          have hqr : q ∈ rest := (hrest q).mpr ⟨hq, hqnot⟩
          rcases hOutside q hqr with hh | hh
          · exact hh p hp
          · exact False.elim (hR ⟨q, hqr, hh⟩)
      · apply hEnd true
        intro p hp q hq hqnot
        have hqr : q ∈ rest := (hrest q).mpr ⟨hq, hqnot⟩
        rcases hOutside q hqr with hh | hh
        · exact False.elim (hL ⟨q, hqr, hh⟩)
        · exact hh p hp
    have hFuel (fuel : ℕ) : boundFuel fuel σ ≤ w ^ 2 := by
      cases fuel with
      | zero => exact Nat.zero_le _
      | succ fuel =>
        rw [boundFuel]
        split
        · exact hBase
        · apply Ctx.getD_max?_le
          intro z hz
          simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hz
          obtain ⟨keep, hkeep, d, _, hz⟩ := hz
          let rest := σ.childPositions.filter (· ∉ keep)
          have hforward (a b : ℕ) : boundFuel fuel (σ.part keep s a) +
              boundFuel fuel (σ.part rest t b) ≤ w ^ 2 := (hCut keep hkeep a b fuel fuel).1
          have hbackward (a b : ℕ) : boundFuel fuel (σ.part rest s a) +
              boundFuel fuel (σ.part keep t b) ≤ w ^ 2 := (hCut keep hkeep a b fuel fuel).2
          have hboth (a b : ℕ) :
              (boundFuel fuel (σ.part keep Side.lower a) +
                boundFuel fuel (σ.part rest Side.upper b) ≤ w ^ 2) ∧
              (boundFuel fuel (σ.part keep Side.upper b) +
                boundFuel fuel (σ.part rest Side.lower a) ≤ w ^ 2) := by
            cases s <;> cases t
            · exact False.elim (hne rfl)
            · exact ⟨hforward a b, by simpa only [Nat.add_comm] using hbackward a b⟩
            · exact ⟨by simpa only [Nat.add_comm] using hbackward b a, hforward b a⟩
            · exact False.elim (hne rfl)
          rcases hz with rfl | rfl
          · exact (hboth (d + 1) (σ.k - 1 - (d + 1))).1
          · exact (hboth (d + 1) (σ.k - 1 - (d + 1))).2
    exact ⟨hFuel, hFuel (σ.childPositions.length + 1)⟩

  let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
  have hByWidth : ∀ v : ℕ, ∀ (ρ : Context) (J y : ℕ), G ρ t - 1 = v →
      (∀ p j z, ρ.letterAt p = Letter.ext j z → 1 ≤ j) →
      (∀ j ∈ ρ.levels, ρ.maximumAt j = 0) →
      (∀ j ∈ ρ.levels, ρ.sideAt j = s) →
      J ∈ ρ.levels → y ∈ ρ.extPositions J →
      (∀ j ∈ ρ.levels, ∀ p ∈ ρ.extPositions j, p = y) →
      G ρ s ≤ 5 →
      (∀ p ∈ ρ.childPositions, 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p) →
      ρ.bound ≤ v ^ 2 := by
    intro v
    induction v using Nat.strong_induction_on with
    | h v ih =>
      intro ρ J y heq hpos hz hs hJ hy ha hg hact
      by_cases hv : v ≤ 3
      · have hsmall : G ρ t ≤ 4 := by omega
        have hh := (ctx_small_opposite_global_marker_square_bound ρ hpos s t hne J y
          hJ (hs J hJ) hy hg hsmall).2
        change ρ.bound ≤ (G ρ t - 1) ^ 2 at hh
        simpa only [heq] using hh
      · have hstep := ctx_bare_marker_square_width_step_of_two_marker_potential ρ hpos
          s t hne J y hz hs hJ hy ha hg hact (by change 4 ≤ G ρ t - 1; omega) htwo
          (by
            intro τ K z hτpos hτzero hτside hK hzi hτactual hτglobal hτactive
            dsimp only
            intro hτwidth
            change G τ t - 1 < G ρ t - 1 at hτwidth
            exact ih (G τ t - 1) (by omega) τ K z rfl
              hτpos hτzero hτside hK hzi hτactual hτglobal hτactive)
        change (∀ fuel, boundFuel fuel ρ ≤ (G ρ t - 1) ^ 2) ∧
          ρ.bound ≤ (G ρ t - 1) ^ 2 at hstep
        simpa only [heq] using hstep.2
  apply ctx_youngest_marker_rank_square_bound_of_bounded_bare_square σ hpositive
    s t hne N x hN hNs hx hglobal hyoung
  intro ρ J y hpos hz hs hJ hy ha hg hact _
  exact hByWidth (G ρ t - 1) ρ J y rfl hpos hz hs hJ hy ha hg hact

end ErdosSzekeres
