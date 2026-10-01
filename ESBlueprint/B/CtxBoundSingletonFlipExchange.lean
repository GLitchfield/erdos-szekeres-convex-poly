import ErdosSzekeres.DecomposableContextLemmas

namespace ErdosSzekeres

/-- For every coupling and orientation of a nonempty proper interleaved child partition of a well-formed multi-run context, some singleton segment can be flipped without lowering its partition value after freely reoptimizing the admissible coupling and orientation. Interleaving is tested on the canonical filtered keep set and its complement. The singleton has all existing immediate child-order neighbours on the other side. R15 requested narrowing; the eight-child pattern 00110011 is an explicit diagnostic obstruction, so this conjecture is expected to be refuted rather than assumed proved.
@node
@ws B
@kind conjecture
@consumer ErdosSzekeres.ctx_bound_additive_multi_run
@falsifier ctx_bound_singleton_flip.py -/
theorem ctx_bound_singleton_flip_exchange (σ : Ctx.Context) (hwf : σ.WellFormed) (hruns : 2 ≤ σ.numRuns)
    (keep : List ℕ) (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions)
    (hne : keep ≠ []) (hall : keep.length < σ.childPositions.length)
    (hinter : σ.childPositions.filter (fun p ↦ p ∈ keep) ∉ σ.blocks)
    (hco : σ.childPositions.filter (fun p ↦ p ∉ keep) ∉ σ.blocks)
    (d : ℕ) (hd : 1 ≤ d) (hdk : d ≤ σ.k - 2) (o : Bool) :
    let value := fun (K : List ℕ) (e : ℕ) (b : Bool) ↦
      if b then
        (σ.part K Ctx.Side.upper (σ.k - 1 - e)).bound +
          (σ.part (σ.childPositions.filter (fun p ↦ p ∉ K)) Ctx.Side.lower e).bound
      else
        (σ.part K Ctx.Side.lower e).bound +
          (σ.part (σ.childPositions.filter (fun p ↦ p ∉ K))
            Ctx.Side.upper (σ.k - 1 - e)).bound
    ∃ i : Fin σ.childPositions.length,
      (∀ j : Fin σ.childPositions.length,
        j.val + 1 = i.val ∨ i.val + 1 = j.val →
          (σ.childPositions[j] ∈ keep ↔ σ.childPositions[i] ∉ keep)) ∧
      ∃ e : ℕ, 1 ≤ e ∧ e ≤ σ.k - 2 ∧ ∃ b : Bool,
        value keep d o ≤ value
          (σ.childPositions.filter (fun p ↦
            (p ∈ keep ∧ p ≠ σ.childPositions[i]) ∨
              (p ∉ keep ∧ p = σ.childPositions[i]))) e b := by
  sorry

end ErdosSzekeres
