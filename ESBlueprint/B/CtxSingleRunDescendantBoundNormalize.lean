import ESBlueprint.B.CtxSingleRunDescendantLimitsNormalize

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- Exact recursive-bound normalization for every descendant prefix inside a single ancestor child run. Absorb all older external levels into the ancestor cup/cap parameters and keep only the new active maxima. Preserves boundFuel at every fuel and the complete bound. Assumes descendant children and new external positions stay in the ancestor run and all external labels are positive; no well-formedness assumption on the normalized raw context is needed. Removes arbitrary external history from the unbounded outer-block comparison.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_single_run_descendant_bound_normalize (σ : Ctx.Context) (b N : ℕ)
  (hpos : σ.childPositions = List.range' b N)
  (π : Ctx.Context) (D : ℕ)
  (hπ : π.a = σ.a ∧ π.u = σ.u ∧ π.k = σ.k ∧
    π.maxima.length = D + σ.maxima.length ∧
    (∀ l, 1 ≤ l → π.extPositions (l + D) = σ.extPositions l) ∧
    (∀ l, 1 ≤ l → π.sideAt (l + D) = σ.sideAt l) ∧
    (∀ l, 1 ≤ l → π.maximumAt (l + D) = σ.maximumAt l))
  (hnew : ∀ l x, 1 ≤ l → l ≤ D → x ∈ π.extPositions l → x ∈ σ.childPositions)
  (hchild : ∀ x ∈ π.childPositions, x ∈ σ.childPositions)
  (hpositive : ∀ x l s, π.letterAt x = Ctx.Letter.ext l s → 1 ≤ l) :
  let τ : Ctx.Context := { π with a := σ.capLimit b b + 1, u := σ.cupLimit b b + 1, maxima := π.maxima.take D }
  (∀ fuel : ℕ, Ctx.Context.boundFuel fuel π = Ctx.Context.boundFuel fuel τ) ∧ π.bound = τ.bound := by
  classical
  dsimp only
  let norm (ρ : Context) (E : ℕ) : Context :=
    { ρ with a := σ.capLimit b b + 1, u := σ.cupLimit b b + 1, maxima := ρ.maxima.take E }
  let Hist (ρ : Context) (E : ℕ) : Prop :=
    ρ.a = σ.a ∧ ρ.u = σ.u ∧ ρ.k = σ.k ∧
      ρ.maxima.length = E + σ.maxima.length ∧
      (∀ l, 1 ≤ l → ρ.extPositions (l + E) = σ.extPositions l) ∧
      (∀ l, 1 ≤ l → ρ.sideAt (l + E) = σ.sideAt l) ∧
      (∀ l, 1 ≤ l → ρ.maximumAt (l + E) = σ.maximumAt l)
  change (∀ fuel, boundFuel fuel π = boundFuel fuel (norm π D)) ∧ π.bound = (norm π D).bound
  have hNormPart (ρ : Context) (E : ℕ) (keep : List ℕ) (s : Side) (m : ℕ) :
      norm (ρ.part keep s m) (E + 1) = (norm ρ E).part keep s m := by
    rfl
  have hHistPart (ρ : Context) (E : ℕ) (hH : Hist ρ E)
      (keep : List ℕ) (s : Side) (m : ℕ) : Hist (ρ.part keep s m) (E + 1) := by
    obtain ⟨ha, hu, hk, hlen, hext, hside, hmaximum⟩ := hH
    refine ⟨ha, hu, hk, ?_, ?_, ?_, ?_⟩
    · change (m :: ρ.maxima).length = E + 1 + σ.maxima.length
      simp only [List.length_cons, hlen]
      omega
    · intro l hl
      rw [show l + (E + 1) = (l + E) + 1 by omega,
        part_extPositions_succ ρ keep s m (by omega : 1 ≤ l + E), hext l hl]
    · intro l hl
      rw [show l + (E + 1) = (l + E) + 1 by omega,
        part_sideAt_succ ρ keep s m (by omega : 1 ≤ l + E), hside l hl]
    · intro l hl
      rw [show l + (E + 1) = (l + E) + 1 by omega,
        part_maximumAt_succ ρ keep s m (by omega : 1 ≤ l + E), hmaximum l hl]
  have hChildPart (ρ : Context) (hC : ∀ x ∈ ρ.childPositions, x ∈ σ.childPositions)
      (keep : List ℕ) (s : Side) (m : ℕ) :
      ∀ x ∈ (ρ.part keep s m).childPositions, x ∈ σ.childPositions := by
    intro x hx
    rw [part_childPositions] at hx
    exact hC x (List.mem_filter.mp hx).1
  have hPositivePart (ρ : Context) (keep : List ℕ) (s : Side) (m : ℕ) :
      ∀ x l t, (ρ.part keep s m).letterAt x = Letter.ext l t → 1 ≤ l := by
    intro x l t hx
    have hxl : x < ρ.word.length := by
      by_contra h
      have hn := letterAt_of_length_le (ρ.part keep s m)
        (show (ρ.part keep s m).word.length ≤ x by rw [part_word_length]; omega)
      rw [hn] at hx
      cases hx
    cases he : ρ.letterAt x with
    | child =>
      rw [part_letterAt_of_child ρ keep s m hxl he] at hx
      split at hx
      · cases hx
      · cases hx
        omega
    | ext oldLevel oldSide =>
      rw [part_letterAt_of_ext ρ keep s m hxl he] at hx
      cases hx
      omega
  have hNewPart (ρ : Context) (E : ℕ)
      (hNew : ∀ l x, 1 ≤ l → l ≤ E → x ∈ ρ.extPositions l → x ∈ σ.childPositions)
      (hC : ∀ x ∈ ρ.childPositions, x ∈ σ.childPositions)
      (hPos : ∀ x l s, ρ.letterAt x = Letter.ext l s → 1 ≤ l)
      (keep : List ℕ) (s : Side) (m : ℕ) :
      ∀ l x, 1 ≤ l → l ≤ E + 1 → x ∈ (ρ.part keep s m).extPositions l → x ∈ σ.childPositions := by
    intro l x hl hlE hx
    by_cases hOne : l = 1
    · subst l
      rw [part_extPositions_one hPos keep s m] at hx
      exact hC x (List.mem_filter.mp hx).1
    · have hOld : 1 ≤ l - 1 := by omega
      rw [show l = (l - 1) + 1 by omega, part_extPositions_succ ρ keep s m hOld] at hx
      exact hNew (l - 1) x hOld (by omega) hx
  have hBase (ρ : Context) (E : ℕ) (hH : Hist ρ E)
      (hNew : ∀ l x, 1 ≤ l → l ≤ E → x ∈ ρ.extPositions l → x ∈ σ.childPositions)
      (hC : ∀ x ∈ ρ.childPositions, x ∈ σ.childPositions) : ρ.base = (norm ρ E).base := by
    rw [base_eq_baseOf, base_eq_baseOf]
    have hps : (norm ρ E).childPositions = ρ.childPositions := rfl
    rw [hps]
    cases hh : ρ.childPositions.head? with
    | none => rfl
    | some p =>
      have hp := hC p (List.mem_of_mem_head? (Option.mem_def.mpr hh))
      have hLimits := ctx_single_run_descendant_limits_normalize σ b N hpos ρ E hH hNew p p hp hp
      change baseOf (ρ.cupLimit p p) (ρ.capLimit p p) ρ.k =
        baseOf ((norm ρ E).cupLimit p p) ((norm ρ E).capLimit p p) (norm ρ E).k
      rw [hLimits.1, hLimits.2]
  have hFuel : ∀ fuel (ρ : Context) (E : ℕ), Hist ρ E →
      (∀ l x, 1 ≤ l → l ≤ E → x ∈ ρ.extPositions l → x ∈ σ.childPositions) →
      (∀ x ∈ ρ.childPositions, x ∈ σ.childPositions) →
      (∀ x l s, ρ.letterAt x = Letter.ext l s → 1 ≤ l) →
      boundFuel fuel ρ = boundFuel fuel (norm ρ E) := by
    intro fuel
    induction fuel with
    | zero => intro ρ E _ _ _ _; rfl
    | succ fuel ih =>
      intro ρ E hH hNew hC hPos
      have hParts : ∀ keep s m,
          boundFuel fuel (ρ.part keep s m) = boundFuel fuel ((norm ρ E).part keep s m) := by
        intro keep s m
        have hv := ih (ρ.part keep s m) (E + 1) (hHistPart ρ E hH keep s m)
          (hNewPart ρ E hNew hC hPos keep s m) (hChildPart ρ hC keep s m)
          (hPositivePart ρ keep s m)
        rw [hNormPart] at hv
        exact hv
      simp only [boundFuel]
      have hruns : (norm ρ E).numRuns = ρ.numRuns := rfl
      rw [hruns]
      split_ifs with hr
      · exact hBase ρ E hH hNew hC
      · have hps : (norm ρ E).childPositions = ρ.childPositions := rfl
        have hblocks : (norm ρ E).blocks = ρ.blocks := rfl
        have hk : (norm ρ E).k = ρ.k := rfl
        rw [hps, hblocks, hk]
        apply congrArg (fun xs : List ℕ => (xs.max?).getD 0)
        apply List.flatMap_congr
        intro block _
        apply List.flatMap_congr
        intro d _
        simp only [hParts]
  have hAll : ∀ fuel, boundFuel fuel π = boundFuel fuel (norm π D) :=
    fun fuel => hFuel fuel π D hπ hnew hchild hpositive
  refine ⟨hAll, ?_⟩
  unfold bound
  have hps : (norm π D).childPositions = π.childPositions := rfl
  rw [hps]
  exact hAll _

end ErdosSzekeres
