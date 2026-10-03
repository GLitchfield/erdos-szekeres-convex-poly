import ErdosSzekeres.DecomposableContextLemmas
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin

namespace ErdosSzekeres

/-- The exact depth-four full-PEEL counterexample 3U4LSS1L2USS with globals(4,4,5) and maxima1111 cannot satisfy the coloring-context constraints for any ambient coloring or finite set. Its first two child positions have cup limit one, whereas their ambient two-point subset is a cup and must have limit at least two. R19 scope verification of the accepted raw-context refutation; no new PEEL conjecture.
@node
@ws B
@kind formalization
@dangling-ok Verifies scope of the R19 raw-context PEEL refutation; distinguishes WellFormed recursion states from satisfied coloring histories -/
theorem ctx_singleton_attainment_counterexample_not_satisfiable {n : ℕ} (χ : TripleColoring n) (S : Finset (Fin n)) :
let σ : Ctx.Context :=
  ⟨4, 4, 5,
    [Ctx.Letter.ext 3 Ctx.Side.upper, Ctx.Letter.ext 4 Ctx.Side.lower,
     Ctx.Letter.child, Ctx.Letter.child, Ctx.Letter.ext 1 Ctx.Side.lower,
     Ctx.Letter.ext 2 Ctx.Side.upper, Ctx.Letter.child, Ctx.Letter.child],
    [1, 1, 1, 1]⟩
¬ Ctx.Satisfies χ S σ := by
  classical
  let σ : Ctx.Context :=
    ⟨4, 4, 5,
      [Ctx.Letter.ext 3 Ctx.Side.upper, Ctx.Letter.ext 4 Ctx.Side.lower,
       Ctx.Letter.child, Ctx.Letter.child, Ctx.Letter.ext 1 Ctx.Side.lower,
       Ctx.Letter.ext 2 Ctx.Side.upper, Ctx.Letter.child, Ctx.Letter.child],
      [1, 1, 1, 1]⟩
  change ¬ Ctx.Satisfies χ S σ
  intro hs
  have hps : σ.childPositions = [2, 3, 6, 7] := by decide +kernel
  have hcard : S.card = 4 := by
    have h := hs.1
    rw [hps] at h
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
  have hposI : (σ.childPositions[(S.filter (fun v => v < f I)).card]?).getD 0 = 2 := by
    rw [hrank, hps]
    rfl
  have hposJ : (σ.childPositions[(S.filter (fun v => v < f J)).card]?).getD 0 = 3 := by
    rw [hrank, hps]
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
  have hcup := (hs.2 {f I, f J} hsub hne).1 hcupPair
  dsimp only at hcup
  simp only [Finset.card_pair hxy.ne, Finset.min'_pair, Finset.max'_pair,
    min_eq_left hxy.le, max_eq_right hxy.le, hposI, hposJ] at hcup
  have hlimit : σ.cupLimit 2 3 = 1 := by decide +kernel
  omega

end ErdosSzekeres
