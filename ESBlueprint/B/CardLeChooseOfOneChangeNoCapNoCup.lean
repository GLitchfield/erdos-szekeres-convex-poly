import ESBlueprint.B.ExistsCapStartPeelOfOneChangeNoCapSuccNoCup

namespace ErdosSzekeres

/-- The classical all-triples binomial cup-cap bound under the one-change signotope law for all cap and cup parameters at least two, proved by the generic cap-start peel and Pascal induction.
@node
@ws B
@kind formalization
@dangling-ok R23 generic counting foundation for the six singleton gate -/
theorem card_le_choose_of_oneChange_no_cap_no_cup {n c v : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)} (hc : 2 ≤ c) (hv : 2 ≤ v) (hone : OneChangeOn χ s) (hnoCap : ¬ContainsCapSet χ s c) (hnoCup : ¬ContainsCupSet χ s v) : s.card ≤ Nat.choose (c + v - 4) (c - 2) := by
  classical
  have hsmall {S : Finset (Fin n)} (hS : S.card ≤ 2) (d : Turn) :
      ∀ t : OrderedTriple n, t.i ∈ S → t.j ∈ S → t.k ∈ S → χ t = d := by
    intro t hi hj hk
    exfalso
    have hsub : ({t.i, t.j, t.k} : Finset (Fin n)) ⊆ S := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hi, hj, hk⟩
    have hcard : ({t.i, t.j, t.k} : Finset (Fin n)).card = 3 := by
      simp [ne_of_lt t.hij, ne_of_lt t.hjk, ne_of_lt (t.hij.trans t.hjk)]
    have := Finset.card_le_card hsub
    omega
  have aux : ∀ a b : ℕ, ∀ S : Finset (Fin n), OneChangeOn χ S →
      ¬ContainsCapSet χ S (a + 2) → ¬ContainsCupSet χ S (b + 2) →
      S.card ≤ Nat.choose (a + b) a := by
    refine Nat.pincerRecursion ?_ ?_ ?_
    · intro a S _ _ hcup
      have hbound : S.card ≤ 1 := by
        by_contra h
        obtain ⟨D, hDS, hDcard⟩ := Finset.exists_subset_card_eq (by omega : 2 ≤ S.card)
        exact hcup ⟨D, hDS, hDcard, hsmall (by omega) Turn.left⟩
      simpa using hbound
    · intro b S _ hcap _
      have hbound : S.card ≤ 1 := by
        by_contra h
        obtain ⟨D, hDS, hDcard⟩ := Finset.exists_subset_card_eq (by omega : 2 ≤ S.card)
        exact hcap ⟨D, hDS, hDcard, hsmall (by omega) Turn.right⟩
      simpa using hbound
    · intro a b ih₁ ih₂ S hS hcap hcup
      have hcap' : ¬ContainsCapSet χ S (a + 2 + 1) := by
        simpa only [Nat.add_assoc] using hcap
      obtain ⟨Z, hZS, _, hrestCap, hZcup⟩ :=
        exists_capStartPeel_of_oneChange_no_capSucc_no_cup
          (by omega : 2 ≤ a + 2) (by omega : 2 ≤ b + 1 + 2) hS hcap' hcup
      have hrestS : S \ Z ⊆ S := Finset.sdiff_subset
      have hrestCup : ¬ContainsCupSet χ (S \ Z) (b + 1 + 2) :=
        fun h ↦ hcup (FinsetPolygon.ContainsCupSet.mono h hrestS)
      have hZcap : ¬ContainsCapSet χ Z (a + 1 + 2) :=
        fun h ↦ hcap (FinsetPolygon.ContainsCapSet.mono h hZS)
      have hZcup' : ¬ContainsCupSet χ Z (b + 2) := by
        simpa only [show b + 1 + 2 - 1 = b + 2 by omega] using hZcup
      have hrestBound := ih₁ (S \ Z) (hS.mono hrestS) hrestCap hrestCup
      have hZbound := ih₂ Z (hS.mono hZS) hZcap hZcup'
      have hcard := Finset.card_sdiff_add_card_eq_card hZS
      have hp : Nat.choose (a + 1 + (b + 1)) (a + 1) =
          Nat.choose (a + (b + 1)) a + Nat.choose (a + 1 + b) (a + 1) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          Nat.choose_succ_succ' (a + b + 1) a
      simp only [Nat.succ_eq_add_one] at hrestBound hZbound ⊢
      omega
  have hc' : c - 2 + 2 = c := by omega
  have hv' : v - 2 + 2 = v := by omega
  have hsum : c - 2 + (v - 2) = c + v - 4 := by omega
  have h := aux (c - 2) (v - 2) s hone
    (by simpa only [hc'] using hnoCap) (by simpa only [hv'] using hnoCup)
  simpa only [hsum] using h


end ErdosSzekeres
