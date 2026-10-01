import ErdosSzekeres.DecomposableContextLemmas
import ESBlueprint.B.CtxBoundMaximalSegmentFlipExchangeOfZeroValue

namespace ErdosSzekeres

/-- R15 corrected exchange: for any well-formed multi-run context and proper interleaved keep set, some nonempty maximal homogeneous segment in child order can be toggled without decreasing the specified partition value, after freely reoptimizing coupling and orientation. The decomposition and opposite boundary labels express maximality. Segment length is unrestricted; singleton exchange is structurally false on 00110011. This corrected statement is a new node so existing statements remain unchanged.
@node
@ws B
@kind conjecture
@consumer ErdosSzekeres.ctx_bound_additive_multi_run
@falsifier ctx_bound_maximal_segment_flip.py -/
theorem ctx_bound_maximal_segment_flip_exchange (σ : Ctx.Context) (hwf : σ.WellFormed) (hruns : 2 ≤ σ.numRuns)
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
    ∃ L S R : List ℕ, σ.childPositions = L ++ S ++ R ∧ S ≠ [] ∧
      ∃ c : Bool, (∀ p ∈ S, decide (p ∈ keep) = c) ∧
        (∀ p, L.getLast? = some p → decide (p ∈ keep) = !c) ∧
        (∀ p, R.head? = some p → decide (p ∈ keep) = !c) ∧
        ∃ e : ℕ, 1 ≤ e ∧ e ≤ σ.k - 2 ∧ ∃ b : Bool,
          value keep d o ≤ value
            (σ.childPositions.filter (fun p ↦
              (p ∈ keep ∧ p ∉ S) ∨ (p ∉ keep ∧ p ∈ S))) e b := by
  classical
  dsimp only
  let original :=
    if o then
      (σ.part keep Ctx.Side.upper (σ.k - 1 - d)).bound +
        (σ.part (σ.childPositions.filter (fun p ↦ p ∉ keep)) Ctx.Side.lower d).bound
    else
      (σ.part keep Ctx.Side.lower d).bound +
        (σ.part (σ.childPositions.filter (fun p ↦ p ∉ keep))
          Ctx.Side.upper (σ.k - 1 - d)).bound
  by_cases hzero : original = 0
  · have hps : σ.childPositions ≠ [] := by
      intro hnil
      rcases keep with _ | ⟨p, ps⟩
      · exact hne rfl
      · have hp := hkeep p (List.mem_cons_self ..)
        simp [hnil] at hp
    exact ctx_bound_maximal_segment_flip_exchange_of_zero_value
      σ keep hps d hd hdk o hzero
  · have hpositive : 0 < original := Nat.pos_of_ne_zero hzero
    -- Remaining R15 obligation: a dominating maximal-segment flip for positive value.
    sorry

end ErdosSzekeres
