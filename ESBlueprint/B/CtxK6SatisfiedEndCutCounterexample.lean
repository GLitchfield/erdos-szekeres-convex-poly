import ESBlueprint.B.CtxBoundCutLe
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace ErdosSzekeres

/-- The R19 k6 middle-of-run context SSS1L3L2LS at(5,5,6), maxima111, is WellFormed and satisfies the constraints of the constant-right coloring on four vertices, yet every global-end singleton cut is strictly below its bound. The middle p1/upper/c3 cut certifies bound at least8; all16 end cuts are at most7. This refutes end-only normal forms even with Satisfies, while full external-history realization and exact bound8 remain separate questions. Recursive capacity is distinct from the number of child letters.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_bound_cut_le
@dangling-ok Verifies the k6 middle-child obstruction requested in R19 and excludes the inherited end-only route even under satisfied coloring constraints -/
theorem ctx_k6_satisfied_end_cut_counterexample :
let σ : Ctx.Context :=
  ⟨5, 5, 6,
    [Ctx.Letter.child, Ctx.Letter.child, Ctx.Letter.child,
     Ctx.Letter.ext 1 Ctx.Side.lower, Ctx.Letter.ext 3 Ctx.Side.lower,
     Ctx.Letter.ext 2 Ctx.Side.lower, Ctx.Letter.child], [1, 1, 1]⟩
σ.WellFormed ∧
Ctx.Satisfies (fun _ : OrderedTriple 4 => Turn.right) (Finset.univ : Finset (Fin 4)) σ ∧
8 ≤ σ.bound ∧
∀ p ∈ σ.childPositions,
  ((∀ q ∈ σ.childPositions, p ≤ q) ∨ (∀ q ∈ σ.childPositions, q ≤ p)) →
  ∀ d, 1 ≤ d → d ≤ σ.k - 2 →
  ((σ.part [p] Ctx.Side.lower d).bound +
    (σ.part (σ.childPositions.filter (fun q => q ≠ p)) Ctx.Side.upper (σ.k - 1 - d)).bound < σ.bound) ∧
  ((σ.part [p] Ctx.Side.upper (σ.k - 1 - d)).bound +
    (σ.part (σ.childPositions.filter (fun q => q ≠ p)) Ctx.Side.lower d).bound < σ.bound) := by
  classical
  let σ : Ctx.Context :=
    ⟨5, 5, 6,
      [Ctx.Letter.child, Ctx.Letter.child, Ctx.Letter.child,
       Ctx.Letter.ext 1 Ctx.Side.lower, Ctx.Letter.ext 3 Ctx.Side.lower,
       Ctx.Letter.ext 2 Ctx.Side.lower, Ctx.Letter.child], [1, 1, 1]⟩
  let χ : TripleColoring 4 := fun _ => Turn.right
  change σ.WellFormed ∧ Ctx.Satisfies χ (Finset.univ : Finset (Fin 4)) σ ∧
    8 ≤ σ.bound ∧ _
  have hwf : σ.WellFormed := by
    refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
    · simp [σ]
    · intro p l s hletter
      have hp : p < 7 := by
        by_contra hp
        rw [Ctx.Context.letterAt_of_length_le σ
          (show σ.word.length ≤ p by simp [σ]; omega)] at hletter
        cases hletter
      interval_cases p <;> simp [σ, Ctx.Context.letterAt] at hletter
      all_goals
        rcases hletter with ⟨rfl, rfl⟩
        decide
  have hpositions : σ.childPositions = [0, 1, 2, 6] := by decide +kernel
  have hrank (v : Fin 4) : ((Finset.univ : Finset (Fin 4)).filter (· < v)).card = v.val := by
    have heq : (Finset.univ : Finset (Fin 4)).filter (· < v) = Finset.Iio v := by
      ext w
      simp
    rw [heq, Fin.card_Iio]
  have hlimits : ∀ v w : Fin 4, v ≤ w →
      2 ≤ σ.cupLimit ((σ.childPositions[v.val]?).getD 0) ((σ.childPositions[w.val]?).getD 0) ∧
      σ.capLimit ((σ.childPositions[v.val]?).getD 0) ((σ.childPositions[w.val]?).getD 0) = 4 := by
    intro v w
    fin_cases v <;> fin_cases w <;> decide +kernel
  have hcupSmall (C : Finset (Fin 4)) (hcup : IsCupSet χ C) : C.card ≤ 2 := by
    by_contra hnot
    have hthree : 3 ≤ C.card := by omega
    let f : Fin C.card ↪o Fin 4 := C.orderEmbOfFin rfl
    let I : Fin C.card := ⟨0, by omega⟩
    let J : Fin C.card := ⟨1, by omega⟩
    let K : Fin C.card := ⟨2, by omega⟩
    have hIJ : I < J := by change (0 : ℕ) < 1; omega
    have hJK : J < K := by change (1 : ℕ) < 2; omega
    have hcolor := hcup ⟨f I, f J, f K, f.strictMono hIJ, f.strictMono hJK⟩
      (Finset.orderEmbOfFin_mem C rfl I) (Finset.orderEmbOfFin_mem C rfl J)
      (Finset.orderEmbOfFin_mem C rfl K)
    change Turn.right = Turn.left at hcolor
    cases hcolor
  have hs : Ctx.Satisfies χ (Finset.univ : Finset (Fin 4)) σ := by
    refine ⟨?_, ?_⟩
    · simp [hpositions]
    · intro C hCS hC
      have hcard : C.card ≤ 4 := by
        simpa using (Finset.card_le_card hCS)
      have hminmax : C.min' hC ≤ C.max' hC :=
        Finset.min'_le C (C.max' hC) (Finset.max'_mem C hC)
      have hl := hlimits (C.min' hC) (C.max' hC) hminmax
      dsimp only
      rw [hrank, hrank]
      refine ⟨fun hc => (hcupSmall C hc).trans hl.1, ?_, ?_⟩
      · intro _
        rw [hl.2]
        exact hcard
      · intro _
        change C.card ≤ 5
        omega
  run_tac Lean.logInfo "K6 certificate: WellFormed and satisfied coloring checked (stage 1/3)"
  have hruns : 2 ≤ σ.numRuns := by decide +kernel
  have hbound : 8 ≤ σ.bound := by
    let τ := σ.part (σ.childPositions.filter (fun p => p ∉ [1])) Ctx.Side.lower 2
    let ρ := τ.part (τ.childPositions.filter (fun p => p ∉ [6])) Ctx.Side.upper 2
    have hρ : 2 ≤ ρ.bound := by
      have hle := (ctx_bound_cut_le ρ (by decide +kernel) [0] (by decide +kernel) 1
        (by decide) (by decide)).1
      have hvalue :
          (ρ.part [0] Ctx.Side.lower 1).bound +
            (ρ.part (ρ.childPositions.filter (fun p => p ∉ [0])) Ctx.Side.upper
              (ρ.k - 1 - 1)).bound = 2 := by decide +kernel
      rw [hvalue] at hle
      exact hle
    have hτ : 6 ≤ τ.bound := by
      have hle := (ctx_bound_cut_le τ (by decide +kernel) [6] (by decide +kernel) 3
        (by decide) (by decide)).1
      have hleaf : (τ.part [6] Ctx.Side.lower 3).bound = 4 := by decide +kernel
      change (τ.part [6] Ctx.Side.lower 3).bound + ρ.bound ≤ τ.bound at hle
      rw [hleaf] at hle
      exact (Nat.add_le_add_left hρ 4).trans hle
    have hle := (ctx_bound_cut_le σ hruns [1] (by decide +kernel) 2
      (by decide) (by decide)).2
    have hleaf : (σ.part [1] Ctx.Side.upper (σ.k - 1 - 2)).bound = 2 := by decide +kernel
    change (σ.part [1] Ctx.Side.upper (σ.k - 1 - 2)).bound + τ.bound ≤ σ.bound at hle
    rw [hleaf] at hle
    exact (Nat.add_le_add_left hτ 2).trans hle
  run_tac Lean.logInfo "K6 certificate: middle cut sum 8 and parent lower bound checked (stage 2/3)"
  refine ⟨hwf, hs, hbound, ?_⟩
  intro p hp hextreme d hd1 hd2
  have hp6 : p ≤ 6 := by
    rw [hpositions] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> omega
  have hpEnds : p = 0 ∨ p = 6 := by
    rcases hextreme with hfirst | hlast
    · have h := hfirst 0 (by rw [hpositions]; simp)
      exact Or.inl (by omega)
    · have h := hlast 6 (by rw [hpositions]; simp)
      exact Or.inr (by omega)
  have hd4 : d ≤ 4 := hd2
  rcases hpEnds with hpEq | hpEq
  all_goals
    have hsmall :
        (σ.part [p] Ctx.Side.lower d).bound +
          (σ.part (σ.childPositions.filter (fun q => q ≠ p)) Ctx.Side.upper (σ.k - 1 - d)).bound ≤ 7 ∧
        (σ.part [p] Ctx.Side.upper (σ.k - 1 - d)).bound +
          (σ.part (σ.childPositions.filter (fun q => q ≠ p)) Ctx.Side.lower d).bound ≤ 7 := by
      subst p
      interval_cases d <;> constructor <;> decide +kernel
    run_tac Lean.logInfo "K6 certificate: one endpoint, all 4 couplings checked (2 endpoints total, stage 3/3)"
    have hseven : 7 < σ.bound := lt_of_lt_of_le (by decide : 7 < 8) hbound
    exact ⟨lt_of_le_of_lt hsmall.1 hseven, lt_of_le_of_lt hsmall.2 hseven⟩

end ErdosSzekeres
