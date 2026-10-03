import ErdosSzekeres.DecomposableContextLemmas
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin

namespace ErdosSzekeres

/-- Feasibility is not preserved by arbitrary legal formal cuts: the WellFormed satisfied k6 context SSS1L3L2LS/maxima111 at(5,5,6) has the proper p0 upper3 cut with both parts WellFormed, but its lower2 remainder has children1,2,6 and cupLimit1,2=1. No coloring or ambient finite set can satisfy that remainder because its first two vertices form a vacuous cup. This certifies a missing invariant for feasible-domain induction without claiming feasible singleton attainment is false.
@node
@ws B
@kind formalization
@dangling-ok R19 feasibility-obstruction certificate: explains why a Satisfies restriction alone is not an invariant of abstract recursive parts; finite parent limits and pair-rank argument avoid the stalled sibling-penalty route. -/
theorem ctx_satisfies_arbitrary_part_counterexample :
let σ : Ctx.Context :=
  ⟨5, 5, 6,
    [Ctx.Letter.child, Ctx.Letter.child, Ctx.Letter.child,
     Ctx.Letter.ext 1 Ctx.Side.lower, Ctx.Letter.ext 3 Ctx.Side.lower,
     Ctx.Letter.ext 2 Ctx.Side.lower, Ctx.Letter.child], [1, 1, 1]⟩
let α := σ.part [0] Ctx.Side.upper 3
let γ := σ.part (σ.childPositions.filter (fun q => q ≠ 0))
  Ctx.Side.lower (σ.k - 1 - 3)
σ.WellFormed ∧ σ.childPositions = [0, 1, 2, 6] ∧ 2 ≤ σ.numRuns ∧
1 ≤ (3 : ℕ) ∧ 3 ≤ σ.k - 2 ∧
Ctx.Satisfies (fun _ : OrderedTriple 4 => Turn.right) (Finset.univ : Finset (Fin 4)) σ ∧
α.WellFormed ∧ γ.WellFormed ∧ γ.childPositions = [1, 2, 6] ∧
γ.cupLimit 1 2 = 1 ∧
∀ (n : ℕ) (χ : TripleColoring n) (S : Finset (Fin n)), ¬ Ctx.Satisfies χ S γ := by
  classical
  let σ : Ctx.Context :=
    ⟨5, 5, 6,
      [Ctx.Letter.child, Ctx.Letter.child, Ctx.Letter.child,
       Ctx.Letter.ext 1 Ctx.Side.lower, Ctx.Letter.ext 3 Ctx.Side.lower,
       Ctx.Letter.ext 2 Ctx.Side.lower, Ctx.Letter.child], [1, 1, 1]⟩
  let α := σ.part [0] Ctx.Side.upper 3
  let γ := σ.part (σ.childPositions.filter (fun q => q ≠ 0))
    Ctx.Side.lower (σ.k - 1 - 3)
  let χ₀ : TripleColoring 4 := fun _ => Turn.right
  change σ.WellFormed ∧ σ.childPositions = [0, 1, 2, 6] ∧ 2 ≤ σ.numRuns ∧
    1 ≤ (3 : ℕ) ∧ 3 ≤ σ.k - 2 ∧
    Ctx.Satisfies χ₀ (Finset.univ : Finset (Fin 4)) σ ∧
    α.WellFormed ∧ γ.WellFormed ∧ γ.childPositions = [1, 2, 6] ∧
    γ.cupLimit 1 2 = 1 ∧ _
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
  have hrank₀ (v : Fin 4) : ((Finset.univ : Finset (Fin 4)).filter (· < v)).card = v.val := by
    have heq : (Finset.univ : Finset (Fin 4)).filter (· < v) = Finset.Iio v := by
      ext w
      simp
    rw [heq, Fin.card_Iio]
  have hlimits : ∀ v w : Fin 4, v ≤ w →
      2 ≤ σ.cupLimit ((σ.childPositions[v.val]?).getD 0) ((σ.childPositions[w.val]?).getD 0) ∧
      σ.capLimit ((σ.childPositions[v.val]?).getD 0) ((σ.childPositions[w.val]?).getD 0) = 4 := by
    intro v w
    fin_cases v <;> fin_cases w <;> decide +kernel
  have hcupSmall (C : Finset (Fin 4)) (hcup : IsCupSet χ₀ C) : C.card ≤ 2 := by
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
  have hs : Ctx.Satisfies χ₀ (Finset.univ : Finset (Fin 4)) σ := by
    refine ⟨?_, ?_⟩
    · simp [hpositions]
    · intro C hCS hC
      have hcard : C.card ≤ 4 := by simpa using (Finset.card_le_card hCS)
      have hminmax : C.min' hC ≤ C.max' hC :=
        Finset.min'_le C (C.max' hC) (Finset.max'_mem C hC)
      have hl := hlimits (C.min' hC) (C.max' hC) hminmax
      dsimp only
      rw [hrank₀, hrank₀]
      refine ⟨fun hc => (hcupSmall C hc).trans hl.1, ?_, ?_⟩
      · intro _
        rw [hl.2]
        exact hcard
      · intro _
        change C.card ≤ 5
        omega
  have hαwf : α.WellFormed :=
    hwf.part [0] Ctx.Side.upper (m := 3) (by decide) (by decide)
  have hγwf : γ.WellFormed :=
    hwf.part (σ.childPositions.filter (fun q => q ≠ 0)) Ctx.Side.lower
      (m := σ.k - 1 - 3) (by decide) (by decide)
  have hγpositions : γ.childPositions = [1, 2, 6] := by decide +kernel
  have hγlimit : γ.cupLimit 1 2 = 1 := by decide +kernel
  refine ⟨hwf, hpositions, by decide, by decide, by decide, hs,
    hαwf, hγwf, hγpositions, hγlimit, ?_⟩
  intro n χ S hbad
  have hcard : S.card = 3 := by
    have h := hbad.1
    rw [hγpositions] at h
    simpa using h.symm
  let f : Fin S.card ↪o Fin n := S.orderEmbOfFin rfl
  have hmem (t : Fin S.card) : f t ∈ S := Finset.orderEmbOfFin_mem S rfl t
  have hrank (t : Fin S.card) : (S.filter (fun v => v < f t)).card = t.val := by
    have heq : S.filter (fun v => v < f t) = (Finset.Iio t).image f := by
      ext v
      constructor
      · intro hv
        obtain ⟨hvS, hvlt⟩ := Finset.mem_filter.mp hv
        have hrange : v ∈ Set.range f := by
          simpa only [f, Finset.range_orderEmbOfFin, Finset.mem_coe] using hvS
        obtain ⟨z, rfl⟩ := hrange
        exact Finset.mem_image.mpr ⟨z, Finset.mem_Iio.mpr (f.lt_iff_lt.mp hvlt), rfl⟩
      · intro hv
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hv
        exact Finset.mem_filter.mpr ⟨hmem z, f.strictMono (Finset.mem_Iio.mp hz)⟩
    rw [heq, Finset.card_image_of_injective _ f.injective, Fin.card_Iio]
  let I : Fin S.card := ⟨0, by omega⟩
  let J : Fin S.card := ⟨1, by omega⟩
  have hIJ : I < J := by change (0 : ℕ) < 1; omega
  have hxy : f I < f J := f.strictMono hIJ
  have hposI : (γ.childPositions[(S.filter (fun v => v < f I)).card]?).getD 0 = 1 := by
    rw [hrank, hγpositions]
    rfl
  have hposJ : (γ.childPositions[(S.filter (fun v => v < f J)).card]?).getD 0 = 2 := by
    rw [hrank, hγpositions]
    rfl
  have hsub : ({f I, f J} : Finset (Fin n)) ⊆ S := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact hmem I
    · exact hmem J
  have hne : ({f I, f J} : Finset (Fin n)).Nonempty := Finset.insert_nonempty _ _
  have hcupPair : IsCupSet χ {f I, f J} := by
    intro t hi hj hk
    have hsub : ({t.i, t.j, t.k} : Finset (Fin n)) ⊆ {f I, f J} := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl
      · exact hi
      · exact hj
      · exact hk
    have hcard := Finset.card_le_card hsub
    have hik : t.i ≠ t.k := ne_of_lt (t.hij.trans t.hjk)
    simp [t.hij.ne, t.hjk.ne, hik, hxy.ne] at hcard
  have hcup := (hbad.2 {f I, f J} hsub hne).1 hcupPair
  dsimp only at hcup
  simp only [Finset.card_pair hxy.ne, Finset.min'_pair, Finset.max'_pair,
    min_eq_left hxy.le, max_eq_right hxy.le] at hcup
  change 2 ≤ γ.cupLimit
    ((γ.childPositions[(S.filter (fun v => v < f I)).card]?).getD 0)
    ((γ.childPositions[(S.filter (fun v => v < f J)).card]?).getD 0) at hcup
  rw [hposI, hposJ, hγlimit] at hcup
  omega

end ErdosSzekeres
