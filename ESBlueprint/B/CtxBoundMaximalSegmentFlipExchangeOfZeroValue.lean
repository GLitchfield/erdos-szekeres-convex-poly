import ErdosSzekeres.DecomposableContextLemmas

namespace ErdosSzekeres

/-- Zero-value maximal-segment exchange: in any context with a nonempty child list and a legal coupling, a zero original partition value is dominated after toggling the first maximal homogeneous child-membership segment. No well-formedness, multi-run or interleaving assumption is needed. The proof constructs the maximal prefix by list induction and uses natural-number nonnegativity.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_multi_run -/
theorem ctx_bound_maximal_segment_flip_exchange_of_zero_value (σ : Ctx.Context) (keep : List ℕ) (hne : σ.childPositions ≠ [])
    (d : ℕ) (hd : 1 ≤ d) (hdk : d ≤ σ.k - 2) (o : Bool)
    (hzero :
      (if o then
        (σ.part keep Ctx.Side.upper (σ.k - 1 - d)).bound +
          (σ.part (σ.childPositions.filter (fun p ↦ p ∉ keep)) Ctx.Side.lower d).bound
      else
        (σ.part keep Ctx.Side.lower d).bound +
          (σ.part (σ.childPositions.filter (fun p ↦ p ∉ keep))
            Ctx.Side.upper (σ.k - 1 - d)).bound) = 0) :
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
  let f : ℕ → Bool := fun p ↦ decide (p ∈ keep)
  have hprefix : ∀ (p : ℕ) (ps : List ℕ),
      ∃ S R : List ℕ, p :: ps = S ++ R ∧ S ≠ [] ∧
        (∀ q ∈ S, f q = f p) ∧
        (∀ q, R.head? = some q → f q = !(f p)) := by
    intro p ps
    induction ps generalizing p with
    | nil =>
        refine ⟨[p], [], rfl, by simp, ?_, ?_⟩
        · intro q hq
          simp only [List.mem_singleton] at hq
          subst q
          rfl
        · intro q hq
          cases hq
    | cons q qs ih =>
        by_cases h : f p = f q
        · obtain ⟨S, R, hdec, hS, hm, hr⟩ := ih q
          refine ⟨p :: S, R, ?_, by simp, ?_, ?_⟩
          · simpa only [List.cons_append] using congrArg (List.cons p) hdec
          · intro x hx
            rcases List.mem_cons.1 hx with rfl | hx
            · rfl
            · exact (hm x hx).trans h.symm
          · intro x hx
            simpa only [h] using hr x hx
        · refine ⟨[p], q :: qs, rfl, by simp, ?_, ?_⟩
          · intro x hx
            simp only [List.mem_singleton] at hx
            subst x
            rfl
          · intro x hx
            simp only [List.head?_cons, Option.some.injEq] at hx
            subst x
            cases hp : f p <;> cases hq : f q <;> simp_all
  cases hk : σ.childPositions with
  | nil => exact False.elim (hne hk)
  | cons p ps =>
      obtain ⟨S, R, hdec, hS, hm, hr⟩ := hprefix p ps
      refine ⟨[], S, R, ?_, hS, f p, hm, ?_, hr, d, hd, hdk, o, ?_⟩
      · simpa only [List.nil_append] using hdec
      · intro q hq
        cases hq
      · rw [hk] at hzero
        rw [hzero]
        exact Nat.zero_le _

end ErdosSzekeres
