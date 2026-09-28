import ESBlueprint.B.CtxBaseUnitTransfer

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- Ordered compensation between different leaf axes: a loss of t cap units at a leaf with cup limit p is compensated by t cup units at a leaf with cap limit P at least p. Valid throughout the classical and active Pascal-window regimes, including zero limits. Supplies the numeric leaf comparison for mixed-side strip exchanges; the required geometric capacity profiles must still be established at each application.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_attained_by_end_cut -/
theorem ctx_base_cross_axis_transfer (c t p P k : ℕ) (hp : p ≤ P) (hP : P ≤ k - 1) (hct : c + t ≤ k - 1) :
  Ctx.Context.baseOf p (c + t) k + Ctx.Context.baseOf c P k ≤
    Ctx.Context.baseOf p c k + Ctx.Context.baseOf (c + t) P k := by
  have hsym (x y k : ℕ) (hx : x ≤ k - 1) (hy : y ≤ k - 1) :
      Ctx.Context.baseOf x y k = Ctx.Context.baseOf y x k := by
    as_aux_lemma =>
      have hthreshold (a u : ℕ) (ha : 2 ≤ a) (hu : 2 ≤ u)
          (hak : a ≤ k) (huk : u ≤ k) :
          decomposableThreshold a u k = decomposableThreshold u a k := by
        by_cases hsmall : a + u ≤ k + 3
        · rw [decomposableThreshold_eq_choose ha hu hsmall,
            decomposableThreshold_eq_choose hu ha (by omega)]
          have hrow : u + a - 4 = a + u - 4 := by omega
          rw [hrow]
          exact Nat.choose_symm_of_eq_add (by omega)
        · rw [decomposableThreshold_eq_window ha hu (by omega),
            decomposableThreshold_eq_window hu ha (by omega)]
          unfold decomposableBinomialWindow
          apply Finset.sum_bij (fun j _ => k - 2 - j)
          · intro j hj
            simp only [Finset.mem_Icc] at hj ⊢
            omega
          · intro i hi j hj heq
            simp only [Finset.mem_Icc] at hi hj
            omega
          · intro j hj
            simp only [Finset.mem_Icc] at hj
            refine ⟨k - 2 - j, ?_, ?_⟩
            · simp only [Finset.mem_Icc]
              omega
            · omega
          · intro j hj
            simp only [Finset.mem_Icc] at hj
            exact (Nat.choose_symm (by omega : j ≤ k - 2)).symm
      by_cases hz : x = 0 ∨ y = 0
      · simp [Ctx.Context.baseOf, hz, or_comm]
      by_cases hunit : x = 1 ∨ y = 1
      · simp [Ctx.Context.baseOf, hz, hunit, or_comm]
      simp only [Ctx.Context.baseOf, if_neg hz, if_neg hunit,
        if_neg (show ¬(y = 0 ∨ x = 0) by tauto),
        if_neg (show ¬(y = 1 ∨ x = 1) by tauto)]
      exact hthreshold (y + 1) (x + 1) (by omega) (by omega) (by omega) (by omega)
  have hmulti (c t p P k : ℕ) (hp : p ≤ P) (hP : P ≤ k - 1)
      (hct : c + t ≤ k - 1) :
      Ctx.Context.baseOf (c + t) p k + Ctx.Context.baseOf c P k ≤
        Ctx.Context.baseOf c p k + Ctx.Context.baseOf (c + t) P k := by
    as_aux_lemma =>
      induction t with
      | zero => simp
      | succ t ih =>
        have hi := ih (by omega)
        have hu := ctx_base_unit_transfer (c + t) p P k hp hP (by omega)
        simp only [Nat.succ_eq_add_one, Nat.add_assoc] at *
        omega
  rw [hsym p (c + t) k (by omega) hct, hsym p c k (by omega) (by omega)]
  exact hmulti c t p P k hp hP hct

end ErdosSzekeres
