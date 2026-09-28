import ESBlueprint.B.CtxBoundMonoOfMarkerInclusion
import ESBlueprint.B.CtxPartPruningHistoryTransport
import ESBlueprint.B.CtxYoungestMarkerTripleFaceBoundOfAnchoredSquare

set_option maxHeartbeats 20000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Prune occurrences of one indexed level while retaining an actual witness and assigning every retained occurrence its original indexed sideAt. Replace removed positions with unindexed letters, preserving the child pattern and all parameters/maxima. Exposes positive labels, exact filtered positions on that level, unchanged other indexed positions and sides, unchanged opposite-axis pure traces at every cutoff, and endpoint/fuel/full bound monotonicity. Packages the existing marker-inclusion comparison for clipping distant new-level occurrences before a boundary normalization. Canonical retained tags and the retained-witness hypothesis ensure sideAt does not change, even for raw contexts with inconsistent occurrence tags.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_single_level_occurrence_prune_bound_mono (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (N : ℕ) (hN : N ∈ σ.levels)
  (keep : List ℕ) (w : ℕ) (hw : w ∈ σ.extPositions N) (hwkeep : w ∈ keep) :
  let τ : Ctx.Context := { σ with word := (List.range σ.word.length).map (fun p =>
    match σ.letterAt p with
    | Ctx.Letter.child => Ctx.Letter.child
    | Ctx.Letter.ext j v => if j = N then
        if p ∈ keep then Ctx.Letter.ext N (σ.sideAt N) else Ctx.Letter.ext (σ.maxima.length + 1) v
        else Ctx.Letter.ext j v) }
  (∀ p j v, τ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) ∧
    τ.childPositions = σ.childPositions ∧
    (∀ j ∈ σ.levels, τ.sideAt j = σ.sideAt j ∧ τ.maximumAt j = σ.maximumAt j ∧
      τ.extPositions j = if j = N then (σ.extPositions j).filter (· ∈ keep) else σ.extPositions j) ∧
    (∀ t : Ctx.Side, σ.sideAt N ≠ t → ∀ top p,
      τ.leftExt t top p = σ.leftExt t top p ∧ τ.rightExt t top p = σ.rightExt t top p) ∧
    (∀ p q, σ.cupLimit p q ≤ τ.cupLimit p q ∧ σ.capLimit p q ≤ τ.capLimit p q) ∧
    (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ Ctx.Context.boundFuel fuel τ) ∧ σ.bound ≤ τ.bound := by
  classical
  let τ : Context := { σ with word := (List.range σ.word.length).map (fun p =>
    match σ.letterAt p with
    | Letter.child => Letter.child
    | Letter.ext j v => if j = N then
        if p ∈ keep then Letter.ext N (σ.sideAt N) else Letter.ext (σ.maxima.length + 1) v
        else Letter.ext j v) }
  change (∀ p j v, τ.letterAt p = Letter.ext j v → 1 ≤ j) ∧
    τ.childPositions = σ.childPositions ∧
    (∀ j ∈ σ.levels, τ.sideAt j = σ.sideAt j ∧ τ.maximumAt j = σ.maximumAt j ∧
      τ.extPositions j = if j = N then (σ.extPositions j).filter (· ∈ keep) else σ.extPositions j) ∧
    (∀ t : Side, σ.sideAt N ≠ t → ∀ top p,
      τ.leftExt t top p = σ.leftExt t top p ∧ τ.rightExt t top p = σ.rightExt t top p) ∧
    (∀ p q, σ.cupLimit p q ≤ τ.cupLimit p q ∧ σ.capLimit p q ≤ τ.capLimit p q) ∧
    (∀ fuel, boundFuel fuel σ ≤ boundFuel fuel τ) ∧ σ.bound ≤ τ.bound
  have hLen : τ.word.length = σ.word.length := by simp [τ]
  have hLetter (p : ℕ) (hp : p < σ.word.length) :
      τ.letterAt p = (match σ.letterAt p with
        | Letter.child => Letter.child
        | Letter.ext j v => if j = N then
            if p ∈ keep then Letter.ext N (σ.sideAt N) else Letter.ext (σ.maxima.length + 1) v
            else Letter.ext j v) := by
    simp only [τ, letterAt, List.getElem?_map, List.getElem?_range hp,
      Option.map_some, Option.getD_some]
  have hIsChild (p : ℕ) : τ.letterAt p = Letter.child ↔ σ.letterAt p = Letter.child := by
    by_cases hp : p < σ.word.length
    · rw [hLetter p hp]
      cases σ.letterAt p with
      | child => rfl
      | ext i v => by_cases hi : i = N <;> by_cases hk : p ∈ keep <;> simp [hi, hk]
    · rw [letterAt_of_length_le σ (by omega),
        letterAt_of_length_le τ (by rw [hLen]; omega)]
  have hChild : τ.childPositions = σ.childPositions := by
    simp only [childPositions, hLen, hIsChild]
  have hPos : ∀ p j v, τ.letterAt p = Letter.ext j v → 1 ≤ j := by
    intro p j v hp
    have hpl : p < σ.word.length := by
      by_contra h
      rw [letterAt_of_length_le τ (by rw [hLen]; omega)] at hp
      cases hp
    rw [hLetter p hpl] at hp
    cases he : σ.letterAt p with
    | child => simp only [he] at hp; cases hp
    | ext i z =>
      have hi := hpositive p i z he
      simp only [he] at hp
      split_ifs at hp
      · have hij := (Letter.ext.inj hp).1
        omega
      · have hij := (Letter.ext.inj hp).1
        omega
      · have hij := (Letter.ext.inj hp).1
        omega
  have hDepthBound (j : ℕ) (hj : j ∈ σ.levels) : j ≤ σ.maxima.length := by
    simp only [levels, List.mem_map, List.mem_range] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    omega
  have hExt (j : ℕ) (hj : j ∈ σ.levels) :
      τ.extPositions j = if j = N then (σ.extPositions j).filter (· ∈ keep) else σ.extPositions j := by
    have hDj : σ.maxima.length + 1 ≠ j := by have h := hDepthBound j hj; omega
    by_cases hjN : j = N
    · subst j
      simp only [if_pos rfl, extPositions, hLen, List.filter_filter]
      apply List.filter_congr
      intro p hp
      rw [hLetter p (List.mem_range.mp hp)]
      cases he : σ.letterAt p with
      | child => simp [he]
      | ext i v =>
        by_cases hi : i = N <;> by_cases hk : p ∈ keep <;> simp [he, hi, hk, hDj]
    · simp only [if_neg hjN, extPositions, hLen]
      apply List.filter_congr
      intro p hp
      rw [hLetter p (List.mem_range.mp hp)]
      cases he : σ.letterAt p with
      | child => rfl
      | ext i v =>
        by_cases hi : i = N <;> by_cases hk : p ∈ keep <;> simp [he, hi, hk, hDj, Ne.symm hjN]
  have hSide (j : ℕ) (hj : j ∈ σ.levels) : τ.sideAt j = σ.sideAt j := by
    by_cases hjN : j = N
    · subst j
      have hw' : w ∈ τ.extPositions N := by rw [hExt N hN, if_pos rfl]; simp [hw, hwkeep]
      have hn := List.ne_nil_of_mem hw'
      let p := (τ.extPositions N).head hn
      have hp : p ∈ τ.extPositions N := List.head_mem hn
      have hp' : p ∈ σ.extPositions N ∧ p ∈ keep := by
        rw [hExt N hN, if_pos rfl] at hp
        exact ⟨(List.mem_filter.mp hp).1, of_decide_eq_true (List.mem_filter.mp hp).2⟩
      have hpl := List.mem_range.mp (List.mem_filter.mp hp'.1).1
      have he : τ.letterAt p = Letter.ext N (σ.sideAt N) := by
        rw [hLetter p hpl]
        cases hs : σ.letterAt p with
        | child => simp [extPositions, hs] at hp'
        | ext i v =>
          have hi : i = N := by
            have hz := (List.mem_filter.mp hp'.1).2
            simpa only [hs, decide_eq_true_eq] using hz
          subst i
          simp [hp'.2]
      simp only [sideAt, List.head?_eq_some_head hn]
      change (match τ.letterAt p with | Letter.ext _ v => v | _ => Side.lower) = σ.sideAt N
      rw [he]
    · simp only [sideAt, hExt j hj, if_neg hjN]
      cases hh : (σ.extPositions j).head? with
      | none => rfl
      | some p =>
        have hp := List.mem_of_mem_head? hh
        have hpl := List.mem_range.mp (List.mem_filter.mp hp).1
        dsimp only
        rw [hLetter p hpl]
        cases he : σ.letterAt p with
        | child => simp [extPositions, he] at hp
        | ext i v =>
          have hi : i = j := by
            have hz := (List.mem_filter.mp hp).2
            simpa only [he, decide_eq_true_eq] using hz
          subst i
          simp [hjN]
  have hHistory : ∀ j ∈ σ.levels, τ.sideAt j = σ.sideAt j ∧
      τ.extPositions j ⊆ σ.extPositions j ∧ τ.maximumAt j ≤ σ.maximumAt j := by
    intro j hj
    refine ⟨hSide j hj, ?_, le_rfl⟩
    rw [hExt j hj]
    split_ifs
    · exact fun _ h => (List.mem_filter.mp h).1
    · exact fun _ h => h
  have hMono := ctx_bound_mono_of_marker_inclusion σ τ hpositive hPos le_rfl le_rfl rfl
    hLen.symm (fun p => (hIsChild p).symm) rfl hHistory
  have hLevelsOn (t : Side) (top : ℕ) : τ.levelsOn t top = σ.levelsOn t top := by
    change σ.levels.filter _ = σ.levels.filter _
    apply List.filter_congr
    intro j hj
    rw [hSide j hj]
  have hOpposite (t : Side) (ht : σ.sideAt N ≠ t) (top p : ℕ) :
      τ.leftExt t top p = σ.leftExt t top p ∧ τ.rightExt t top p = σ.rightExt t top p := by
    have hE (j : ℕ) (hj : j ∈ σ.levelsOn t top) : τ.extPositions j = σ.extPositions j := by
      have hjl := (List.mem_filter.mp hj).1
      have hjs : σ.sideAt j = t ∧ (top = 0 ∨ j < top) :=
        of_decide_eq_true (List.mem_filter.mp hj).2
      have hjN : j ≠ N := by intro he; subst j; exact ht hjs.1
      rw [hExt j hjl, if_neg hjN]
    have hfold : ∀ (ls : List ℕ), (∀ j ∈ ls, j ∈ σ.levelsOn t top) → ∀ z,
        ls.foldl (leftStep τ) z = ls.foldl (leftStep σ) z ∧
        ls.foldl (rightStep τ) z = ls.foldl (rightStep σ) z := by
      intro ls
      induction ls with
      | nil => intro _ z; exact ⟨rfl, rfl⟩
      | cons j ls ih =>
        intro hj z
        have hr := ih (fun i hi => hj i (by simp [hi]))
        simp only [List.foldl_cons, leftStep, rightStep, hE j (hj j (by simp))]
        exact ⟨(hr _).1, (hr _).2⟩
    simp only [leftExt_eq, rightExt_eq, hLevelsOn]
    constructor <;> congr 2 <;> apply List.map_congr_left <;> intro ls hls
    · exact congrArg Prod.snd (hfold ls (fun j hj => (List.mem_sublists.mp hls).subset hj) _).1
    · exact congrArg Prod.snd (hfold ls (fun j hj => (List.mem_sublists.mp hls).subset hj) _).2
  exact ⟨hPos, hChild, fun j hj => ⟨hSide j hj, rfl, hExt j hj⟩,
    hOpposite, hMono⟩

end ErdosSzekeres
