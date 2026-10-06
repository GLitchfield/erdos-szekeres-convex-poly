import ErdosSzekeres.StructuralChargingCore

namespace ErdosSzekeres

/-- Every finite support has exact longest ending and starting cup rank profiles, each attained by an endpoint-containing cup and maximal over all such cups. No OneChange or cap-free assumption is needed; finite endpoint-cup families contain the singleton and have cardinality maxima.
@node
@ws B
@kind formalization
@dangling-ok Approved R20 reusable rank-profile foundation supplying the hypotheses of layer and cross-gap tools for a5 cases; coupled cut remains open -/
theorem existsEndingAndStartingCupRankProfiles {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)} :
    ∃ endingRank startingRank : Fin n → ℕ,
      (∀ x ∈ s, ∃ C : Finset (Fin n), C ⊆ s ∧ C.card = endingRank x ∧
        IsCupSet χ C ∧ x ∈ C ∧ (∀ y ∈ C, y ≤ x)) ∧
      (∀ x ∈ s, ∀ C : Finset (Fin n), C ⊆ s → IsCupSet χ C →
        x ∈ C → (∀ y ∈ C, y ≤ x) → C.card ≤ endingRank x) ∧
      (∀ x ∈ s, ∃ C : Finset (Fin n), C ⊆ s ∧ C.card = startingRank x ∧
        IsCupSet χ C ∧ x ∈ C ∧ (∀ y ∈ C, x ≤ y)) ∧
      (∀ x ∈ s, ∀ C : Finset (Fin n), C ⊆ s → IsCupSet χ C →
        x ∈ C → (∀ y ∈ C, x ≤ y) → C.card ≤ startingRank x) := by
  classical
  have singletonCup (x : Fin n) : IsCupSet χ ({x} : Finset (Fin n)) := by
    intro t hi hj hk
    have hij := t.hij
    simp only [Finset.mem_singleton] at hi hj hk
    omega
  have profile (endpoint : Fin n → Fin n → Prop)
      (hreflexive : ∀ x, endpoint x x) :
      ∃ rank : Fin n → ℕ,
        (∀ x ∈ s, ∃ C : Finset (Fin n), C ⊆ s ∧ C.card = rank x ∧
          IsCupSet χ C ∧ x ∈ C ∧ (∀ y ∈ C, endpoint x y)) ∧
        (∀ x ∈ s, ∀ C : Finset (Fin n), C ⊆ s → IsCupSet χ C →
          x ∈ C → (∀ y ∈ C, endpoint x y) → C.card ≤ rank x) := by
    have point (x : Fin n) (hx : x ∈ s) :
        ∃ C : Finset (Fin n), C ⊆ s ∧ IsCupSet χ C ∧ x ∈ C ∧
          (∀ y ∈ C, endpoint x y) ∧
          (∀ D : Finset (Fin n), D ⊆ s → IsCupSet χ D → x ∈ D →
            (∀ y ∈ D, endpoint x y) → D.card ≤ C.card) := by
      let candidates := s.powerset.filter (fun C =>
        IsCupSet χ C ∧ x ∈ C ∧ ∀ y ∈ C, endpoint x y)
      have hsingle : ({x} : Finset (Fin n)) ∈ candidates := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_,
          singletonCup x, by simp, ?_⟩
        · simpa using hx
        · intro y hy
          simpa only [Finset.mem_singleton.mp hy] using hreflexive x
      obtain ⟨C, hC, hmax⟩ := Finset.exists_max_image candidates Finset.card ⟨{x}, hsingle⟩
      obtain ⟨hCpower, hCcup, hxC, hend⟩ := Finset.mem_filter.mp hC
      refine ⟨C, Finset.mem_powerset.mp hCpower, hCcup, hxC, hend, ?_⟩
      intro D hDsub hDcup hxD hDend
      exact hmax D (Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr hDsub, hDcup, hxD, hDend⟩)
    let rank : Fin n → ℕ := fun x =>
      if hx : x ∈ s then (Classical.choose (point x hx)).card else 0
    refine ⟨rank, ?_, ?_⟩
    · intro x hx
      obtain ⟨hsub, hcup, hmem, hend, _⟩ := Classical.choose_spec (point x hx)
      refine ⟨Classical.choose (point x hx), hsub, ?_, hcup, hmem, hend⟩
      simp only [rank, dif_pos hx]
    · intro x hx C hsub hcup hmem hend
      have hmax := (Classical.choose_spec (point x hx)).2.2.2.2
      simpa only [rank, dif_pos hx] using hmax C hsub hcup hmem hend
  obtain ⟨endingRank, hending, hendingMax⟩ :=
    profile (fun x y => y ≤ x) (fun _ => le_rfl)
  obtain ⟨startingRank, hstarting, hstartingMax⟩ :=
    profile (fun x y => x ≤ y) (fun _ => le_rfl)
  exact ⟨endingRank, startingRank, hending, hendingMax, hstarting, hstartingMax⟩


end ErdosSzekeres
