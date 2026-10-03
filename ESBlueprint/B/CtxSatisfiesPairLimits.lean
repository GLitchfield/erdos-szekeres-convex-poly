import ErdosSzekeres.DecomposableContextLemmas
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.GetD
import Mathlib.Order.Interval.Finset.Fin

namespace ErdosSzekeres

/-- Every ordered pair of distinct child positions in a satisfied coloring context has cup and cap limits at least two. Any two-point subset is simultaneously a cup and cap, and the ordered finite-set enumeration realizes every child index in the Satisfies rank map. No WellFormed or global parameter premise is needed. Supplies a necessary feasibility constraint that separates raw context normal forms from contexts of actual colorings; R19 verification of the refuted full PEEL witness. Search satisfies pair limits found no duplicate; isCupSet_pair found the existing core vacuous-pair lemma.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_multi_run -/
theorem ctx_satisfies_pair_limits {n : ℕ} (χ : TripleColoring n) (S : Finset (Fin n)) (σ : Ctx.Context)
(hs : Ctx.Satisfies χ S σ) (p q : ℕ)
(hp : p ∈ σ.childPositions) (hq : q ∈ σ.childPositions) (hpq : p < q) :
2 ≤ σ.cupLimit p q ∧ 2 ≤ σ.capLimit p q := by
  classical
  have hlength := hs.1
  obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
  obtain ⟨j, hj, hqj⟩ := List.mem_iff_getElem.mp hq
  have hsorted : σ.childPositions.Pairwise (· < ·) := by
    unfold Ctx.Context.childPositions
    exact List.pairwise_lt_range.filter _
  have hij : i < j := by
    by_contra hnot
    have hji : j ≤ i := by omega
    rcases eq_or_lt_of_le hji with heq | hji
    · subst j
      omega
    · have hqp := (List.pairwise_iff_getElem.mp hsorted) j i hj hi hji
      rw [hpi, hqj] at hqp
      omega
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
  let I : Fin S.card := ⟨i, by omega⟩
  let J : Fin S.card := ⟨j, by omega⟩
  have hIJ : I < J := hij
  have hxy : f I < f J := f.strictMono hIJ
  have hposI : (σ.childPositions[(S.filter (fun v => v < f I)).card]?).getD 0 = p := by
    rw [hrank]
    change σ.childPositions.getD i 0 = p
    rw [List.getD_eq_getElem σ.childPositions 0 hi]
    exact hpi
  have hposJ : (σ.childPositions[(S.filter (fun v => v < f J)).card]?).getD 0 = q := by
    rw [hrank]
    change σ.childPositions.getD j 0 = q
    rw [List.getD_eq_getElem σ.childPositions 0 hj]
    exact hqj
  have hsub : ({f I, f J} : Finset (Fin n)) ⊆ S := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact hmem I
    · exact hmem J
  have hne : ({f I, f J} : Finset (Fin n)).Nonempty := Finset.insert_nonempty _ _
  have hboth := hs.2 {f I, f J} hsub hne
  have hnotriple (t : OrderedTriple n) (hi : t.i ∈ ({f I, f J} : Finset (Fin n)))
      (hj : t.j ∈ ({f I, f J} : Finset (Fin n)))
      (hk : t.k ∈ ({f I, f J} : Finset (Fin n))) : False := by
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
  have hcup := hboth.1 (fun t hi hj hk => (hnotriple t hi hj hk).elim)
  have hcap := hboth.2.1 (fun t hi hj hk => (hnotriple t hi hj hk).elim)
  dsimp only at hcup hcap
  simp only [Finset.card_pair hxy.ne, Finset.min'_pair, Finset.max'_pair,
    min_eq_left hxy.le, max_eq_right hxy.le, hposI, hposJ] at hcup hcap
  exact ⟨hcup, hcap⟩

end ErdosSzekeres
