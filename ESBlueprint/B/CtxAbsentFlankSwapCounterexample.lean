import ErdosSzekeres.DecomposableContext

namespace ErdosSzekeres

/-- Actual-presence is necessary for same-side opposite-flank swapping: a WellFormed two-child context with no external letters satisfies both positional flank predicates vacuously and all maxima legality conditions, but the exact label/maxima normalization from the accepted FLANK-SWAP formula changes its bound10 to4. This certifies the earlier diagnostic hypothesis boundary without changing the accepted presence-restricted theorem.
@node
@ws B
@kind formalization
@dangling-ok R19 FLANK-SWAP scope verification: certifies the documented absent-level counterexample and necessity of actual-presence hypotheses; literal one-run contexts reduce to finite threshold arithmetic. -/
theorem ctx_absent_flank_swap_counterexample : let σ : Ctx.Context := ⟨5, 5, 6, [Ctx.Letter.child, Ctx.Letter.child], [1, 2]⟩
  let M := max (σ.maximumAt 1) (1 + σ.maximumAt 2)
  let τ : Ctx.Context := { σ with
    word := σ.word.map (fun x ↦ match x with
      | Ctx.Letter.child => Ctx.Letter.child
      | Ctx.Letter.ext j s => Ctx.Letter.ext (if j = 1 then 2 else if j = 2 then 1 else j) s)
    maxima := (σ.maxima.set 0 (if σ.sideAt 1 = σ.sideAt 2 then M else σ.maximumAt 2)).set 1
      (if σ.sideAt 1 = σ.sideAt 2 then M - 1 else σ.maximumAt 1) }
  σ.WellFormed ∧ τ.WellFormed ∧ 2 ≤ σ.maxima.length ∧
  σ.extPositions 1 = [] ∧ σ.extPositions 2 = [] ∧
  ((∀ p ∈ σ.extPositions 1, ∀ q ∈ σ.childPositions, p < q) ∧
   (∀ p ∈ σ.extPositions 2, ∀ q ∈ σ.childPositions, q < p)) ∧
  σ.sideAt 1 = σ.sideAt 2 ∧
  (1 ≤ M - 1 ∧ M ≤ σ.k - 2) ∧
  σ.bound = 10 ∧ τ.bound = 4 := by
  dsimp only
  let σ : Ctx.Context := ⟨5, 5, 6, [Ctx.Letter.child, Ctx.Letter.child], [1, 2]⟩
  let τ : Ctx.Context := ⟨5, 5, 6, [Ctx.Letter.child, Ctx.Letter.child], [3, 2]⟩
  have hwf (ms : List ℕ) (hm : ∀ m ∈ ms, 1 ≤ m ∧ m ≤ 4) :
      (⟨5, 5, 6, [Ctx.Letter.child, Ctx.Letter.child], ms⟩ : Ctx.Context).WellFormed := by
    refine ⟨by change 2 ≤ 5; decide, by change 2 ≤ 5; decide,
      by change 5 ≤ 6; decide, by change 5 ≤ 6; decide, hm, ?_⟩
    intro p l s hp
    have hc :
        (⟨5, 5, 6, [Ctx.Letter.child, Ctx.Letter.child], ms⟩ : Ctx.Context).letterAt p =
          Ctx.Letter.child := by
      change ((List.replicate 2 Ctx.Letter.child)[p]?).getD Ctx.Letter.child =
        Ctx.Letter.child
      rw [List.getElem?_replicate]
      split <;> rfl
    rw [hc] at hp
    cases hp
  have hfirst : σ.extPositions 1 = [] := rfl
  have hsecond : σ.extPositions 2 = [] := rfl
  refine ⟨hwf [1, 2] (by simp), hwf [3, 2] (by simp), by decide +kernel,
    hfirst, hsecond, ?_, by rfl, by decide +kernel, ?_, ?_⟩
  · change ((∀ p ∈ σ.extPositions 1, ∀ q ∈ σ.childPositions, p < q) ∧
      (∀ p ∈ σ.extPositions 2, ∀ q ∈ σ.childPositions, q < p))
    exact ⟨by simp [hfirst], by simp [hsecond]⟩
  · change σ.bound = 10
    decide +kernel
  · change τ.bound = 4
    decide +kernel

end ErdosSzekeres
