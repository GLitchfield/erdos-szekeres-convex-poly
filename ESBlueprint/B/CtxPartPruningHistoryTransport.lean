import ESBlueprint.B.CtxEraseLevelBoundMono

set_option maxHeartbeats 6000000
set_option maxRecDepth 10000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Exact pruning transport for a context part. Replace removed children by positive unindexed external letters, preserving all indexed history, side lists, pure extension traces and endpoint capacities; the active support is exactly the retained subset. Every fuel approximation of the part and its full bound are at most those of this pruned original-history context, by erasing the newly added level. No global-capacity, activity, interval, nonempty, or coupling restrictions are needed. Exposes the pruning construction used locally in zero-capacity comparison, adding exact active-support and all-fuel transport for reuse. Removes the inactive-companion induction obstruction in the one-level exterior potential proof: apply the prior-fuel hypothesis to the pruned context, whose occupied-zone and rank sets only decrease.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_part_pruning_history_transport (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (keep : List ℕ) (v : Ctx.Side) (m : ℕ) :
  let τ : Ctx.Context := { σ with
    word := (List.range σ.word.length).map (fun p => match σ.letterAt p with
      | Ctx.Letter.child => if p ∈ keep then Ctx.Letter.child
          else Ctx.Letter.ext (σ.maxima.length + 1) v
      | Ctx.Letter.ext j s => Ctx.Letter.ext j s) }
  let active := fun (ρ : Ctx.Context) => ρ.childPositions.toFinset.filter
    (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
  (∀ p j s, τ.letterAt p = Ctx.Letter.ext j s → 1 ≤ j) ∧
    τ.childPositions = σ.childPositions.filter (· ∈ keep) ∧
    (∀ j ∈ σ.levels, τ.extPositions j = σ.extPositions j ∧ τ.sideAt j = σ.sideAt j) ∧
    (∀ s top, τ.levelsOn s top = σ.levelsOn s top) ∧
    (∀ s top p, τ.leftExt s top p = σ.leftExt s top p ∧
      τ.rightExt s top p = σ.rightExt s top p) ∧
    (∀ p q, τ.cupLimit p q = σ.cupLimit p q ∧ τ.capLimit p q = σ.capLimit p q) ∧
    active τ = (active σ).filter (· ∈ keep) ∧
    (∀ fuel, Ctx.Context.boundFuel fuel (σ.part keep v m) ≤ Ctx.Context.boundFuel fuel τ) ∧
    (σ.part keep v m).bound ≤ τ.bound := by
  classical
  let prune (ρ : Context) (keep : List ℕ) (v : Side) : Context := { ρ with
    word := (List.range ρ.word.length).map (fun p => match ρ.letterAt p with
      | Letter.child => if p ∈ keep then Letter.child else Letter.ext (ρ.maxima.length + 1) v
      | Letter.ext j s => Letter.ext j s) }
  have hPLen (ρ : Context) (keep : List ℕ) (v : Side) :
      (prune ρ keep v).word.length = ρ.word.length := by simp [prune]
  have hPLetter (ρ : Context) (keep : List ℕ) (v : Side) (p : ℕ) (hp : p < ρ.word.length) :
      (prune ρ keep v).letterAt p = (match ρ.letterAt p with
      | Letter.child => if p ∈ keep then Letter.child else Letter.ext (ρ.maxima.length + 1) v
      | Letter.ext j s => Letter.ext j s) := by
    simp only [prune, letterAt, List.getElem?_map, List.getElem?_range hp,
      Option.map_some, Option.getD_some]
  have hPChild (ρ : Context) (keep : List ℕ) (v : Side) :
      (prune ρ keep v).childPositions = ρ.childPositions.filter (· ∈ keep) := by
    simp only [childPositions, hPLen, List.filter_filter]
    apply List.filter_congr
    intro p hp
    rw [hPLetter ρ keep v p (List.mem_range.mp hp)]
    cases ρ.letterAt p <;> simp
  have hPPos (ρ : Context) (keep : List ℕ) (v : Side)
      (hpos : ∀ p j s, ρ.letterAt p = Letter.ext j s → 1 ≤ j) :
      ∀ p j s, (prune ρ keep v).letterAt p = Letter.ext j s → 1 ≤ j := by
    intro p j s hp
    have hpl : p < ρ.word.length := by
      by_contra h
      have he := letterAt_of_length_le (prune ρ keep v)
        (show (prune ρ keep v).word.length ≤ p by rw [hPLen]; omega)
      rw [he] at hp
      cases hp
    rw [hPLetter ρ keep v p hpl] at hp
    cases he : ρ.letterAt p with
    | child =>
      by_cases hpk : p ∈ keep
      · simp [he, hpk] at hp
      · simp only [he, if_neg hpk, Letter.ext.injEq] at hp
        omega
    | ext i w =>
      have hi := hpos p i w he
      simp only [he, Letter.ext.injEq] at hp
      omega
  have hPExt (ρ : Context) (keep : List ℕ) (v : Side) (j : ℕ) (hj : j ∈ ρ.levels) :
      (prune ρ keep v).extPositions j = ρ.extPositions j := by
    have hjD : j ≤ ρ.maxima.length := by
      simp only [levels, List.mem_map, List.mem_range] at hj
      obtain ⟨i, hi, rfl⟩ := hj; omega
    simp only [extPositions, hPLen]
    apply List.filter_congr
    intro p hp
    rw [hPLetter ρ keep v p (List.mem_range.mp hp)]
    cases ρ.letterAt p with
    | child => split_ifs <;> simp [show ρ.maxima.length + 1 ≠ j by omega]
    | ext i w => rfl
  have hPSide (ρ : Context) (keep : List ℕ) (v : Side) (j : ℕ) (hj : j ∈ ρ.levels) :
      (prune ρ keep v).sideAt j = ρ.sideAt j := by
    simp only [sideAt, hPExt ρ keep v j hj]
    cases hh : (ρ.extPositions j).head? with
    | none => rfl
    | some p =>
      have hp := List.mem_of_mem_head? hh
      have hpl := List.mem_range.mp (List.mem_filter.mp hp).1
      dsimp only
      rw [hPLetter ρ keep v p hpl]
      cases he : ρ.letterAt p with
      | child => simp [extPositions, he] at hp
      | ext i s => rfl
  have hPLevels (ρ : Context) (keep : List ℕ) (v s : Side) (top : ℕ) :
      (prune ρ keep v).levelsOn s top = ρ.levelsOn s top := by
    change ρ.levels.filter _ = ρ.levels.filter _
    apply List.filter_congr
    intro j hj
    rw [hPSide ρ keep v j hj]
  have hPExtensions (ρ : Context) (keep : List ℕ) (v s : Side) (top x : ℕ) :
      (prune ρ keep v).leftExt s top x = ρ.leftExt s top x ∧
      (prune ρ keep v).rightExt s top x = ρ.rightExt s top x := by
    have hfold : ∀ (ls : List ℕ), (∀ j ∈ ls, j ∈ ρ.levels) → ∀ z,
        ls.foldl (leftStep (prune ρ keep v)) z = ls.foldl (leftStep ρ) z ∧
        ls.foldl (rightStep (prune ρ keep v)) z = ls.foldl (rightStep ρ) z := by
      intro ls
      induction ls with
      | nil => intro _ z; exact ⟨rfl, rfl⟩
      | cons j ls ih =>
        intro hj z
        have ht := ih (fun i hi => hj i (by simp [hi]))
        simp only [List.foldl_cons, leftStep, rightStep, hPExt ρ keep v j (hj j (by simp))]
        exact ⟨(ht _).1, (ht _).2⟩
    simp only [leftExt_eq, rightExt_eq, hPLevels ρ keep v]
    constructor <;> congr 2 <;> apply List.map_congr_left <;> intro ls hls
    · exact congrArg Prod.snd (hfold ls
        (fun j hj => (List.mem_filter.mp ((List.mem_sublists.mp hls).subset hj)).1) _).1
    · exact congrArg Prod.snd (hfold ls
        (fun j hj => (List.mem_filter.mp ((List.mem_sublists.mp hls).subset hj)).1) _).2
  have hPLimits (ρ : Context) (keep : List ℕ) (v : Side) (p q : ℕ) :
      (prune ρ keep v).cupLimit p q = ρ.cupLimit p q ∧
      (prune ρ keep v).capLimit p q = ρ.capLimit p q := by
    have hchain (s : Side) : (prune ρ keep v).chainExt s p q = ρ.chainExt s p q := by
      simp only [chainExt, (hPExtensions ρ keep v s 0 p).1, (hPExtensions ρ keep v s 0 q).2]
    have hjoin (s : Side) : (prune ρ keep v).joinExt s p q = ρ.joinExt s p q := by
      simp only [joinExt, hchain, hPLevels ρ keep v]
      congr 3
      apply List.map_congr_left
      intro j _
      simp only [(hPExtensions ρ keep v s j p).1, (hPExtensions ρ keep v s j q).2]
      rfl
    simp only [cupLimit, capLimit, hchain, hjoin]
    exact ⟨rfl, rfl⟩
  have hPruneBounds (ρ : Context) (keep : List ℕ) (v : Side) (m : ℕ)
      (hpos : ∀ p j s, ρ.letterAt p = Letter.ext j s → 1 ≤ j) :
      (∀ fuel, boundFuel fuel (ρ.part keep v m) ≤ boundFuel fuel (prune ρ keep v)) ∧
        (ρ.part keep v m).bound ≤ (prune ρ keep v).bound := by
    have h1 : 1 ∈ (ρ.part keep v m).levels := by simp only [part_levels]; simp
    have h := ctx_erase_level_bound_mono (ρ.part keep v m) 1 h1
    have he : ({ ρ.part keep v m with
        word := (ρ.part keep v m).word.map (fun x => match x with
          | Letter.child => Letter.child
          | Letter.ext j s => Letter.ext
              (if j = 1 then (ρ.part keep v m).maxima.length else if 1 < j then j - 1 else j) s)
        maxima := (ρ.part keep v m).maxima.eraseIdx (1 - 1) } : Context) = prune ρ keep v := by
      simp only [part, prune, List.map_map, List.length_cons, Nat.sub_self, List.eraseIdx_zero]
      congr 1
      apply List.map_congr_left
      intro p _
      cases hl : ρ.letterAt p with
      | child => simp only [Function.comp_apply, hl]; split_ifs <;> simp
      | ext j s =>
        have hj := hpos p j s hl
        simp only [Function.comp_apply, hl]
        simp [show j ≠ 0 by omega, show 1 < j + 1 by omega]
    exact ⟨fun fuel => (h.2.1 fuel).trans_eq (congrArg (boundFuel fuel) he),
      h.2.2.trans_eq (congrArg Context.bound he)⟩
  let active (ρ : Context) : Finset ℕ := ρ.childPositions.toFinset.filter
    (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
  change (∀ p j s, (prune σ keep v).letterAt p = Letter.ext j s → 1 ≤ j) ∧
    (prune σ keep v).childPositions = σ.childPositions.filter (· ∈ keep) ∧
    (∀ j ∈ σ.levels, (prune σ keep v).extPositions j = σ.extPositions j ∧
      (prune σ keep v).sideAt j = σ.sideAt j) ∧
    (∀ s top, (prune σ keep v).levelsOn s top = σ.levelsOn s top) ∧
    (∀ s top p, (prune σ keep v).leftExt s top p = σ.leftExt s top p ∧
      (prune σ keep v).rightExt s top p = σ.rightExt s top p) ∧
    (∀ p q, (prune σ keep v).cupLimit p q = σ.cupLimit p q ∧
      (prune σ keep v).capLimit p q = σ.capLimit p q) ∧
    active (prune σ keep v) = (active σ).filter (· ∈ keep) ∧
    (∀ fuel, boundFuel fuel (σ.part keep v m) ≤ boundFuel fuel (prune σ keep v)) ∧
    (σ.part keep v m).bound ≤ (prune σ keep v).bound
  refine ⟨hPPos σ keep v hpositive, hPChild σ keep v,
    (fun j hj => ⟨hPExt σ keep v j hj, hPSide σ keep v j hj⟩),
    hPLevels σ keep v, hPExtensions σ keep v, hPLimits σ keep v, ?_,
    hPruneBounds σ keep v m hpositive⟩
  ext p
  simp only [active, Finset.mem_filter, List.mem_toFinset, hPChild,
    List.mem_filter, decide_eq_true_eq, (hPLimits σ keep v p p).1,
    (hPLimits σ keep v p p).2]
  tauto

end ErdosSzekeres
