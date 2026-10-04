import ErdosSzekeres.E3FiniteReduction
import ESBlueprint.B.CardLeChooseOfOneChangeNoCapNoCup
import ErdosSzekeres.StructuralChargingCore

namespace ErdosSzekeres

/-- Baek-Balko Theorem 8 for every decomposable state follows from the Band Decomposition Lemma: a decomposable set with no strong k-set, cup <= alpha and cap <= beta (alpha+beta >= k) splits into bands j in [k-1-beta, alpha-1] with no (j+2)-cup and no (k-j)-cap. Each band is bounded by the classical cup-cap theorem C(k-2,j), and the band bounds sum to the decomposable threshold.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.card_le_choose_of_oneChange_no_cap_no_cup
@consumer ErdosSzekeres.decomposableStateUpper_all -/
theorem decomposableStateUpper_all_of_bands (hBDL : ∀ {n k α β : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)}, IsDecomposableOn χ s → ¬ContainsStrongPolygonSet χ s k → ¬ContainsCupSet χ s (α + 1) → ¬ContainsCapSet χ s (β + 1) → k ≤ α + β → ∃ b : Fin n → ℕ, (∀ x ∈ s, k - 1 - β ≤ b x ∧ b x ≤ α - 1) ∧ ∀ j, j < k → ¬ContainsCupSet χ (s.filter (fun x => b x = j)) (j + 2) ∧ ¬ContainsCapSet χ (s.filter (fun x => b x = j)) (k - j)) (a u k : ℕ) (ha : 1 ≤ a) (hu : 1 ≤ u) (hak : a ≤ k) (huk : u ≤ k) : DecomposableStateUpper a u k := by
  intro n χ s hdec hlt
  have hone : OneChangeOn χ s := fun hij hjk hkl hi hj hk hl =>
    hdec.turnSequenceAllowed hij hjk hkl hi hj hk hl
  rcases Nat.lt_or_ge a 2 with ha2 | ha2
  · obtain rfl : a = 1 := by omega
    exact Or.inl (containsCapSet_one hdec.nonempty)
  rcases Nat.lt_or_ge u 2 with hu2 | hu2
  · obtain rfl : u = 1 := by omega
    exact Or.inr (Or.inl (containsCupSet_one hdec.nonempty))
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨hnoCap, hnoCup, hnoStrong⟩ := hcon
  rcases Nat.lt_or_ge (k + 3) (a + u) with hwin | hbase
  · -- Window regime: bands `j ∈ [k-a, u-2]`, each bounded by `C(k-2, j)`.
    rw [decomposableThreshold_eq_window ha2 hu2 (by omega),
      decomposableBinomialWindow] at hlt
    obtain ⟨b, hrange, hband⟩ := @hBDL n k (u - 1) (a - 1) χ s hdec hnoStrong
      (by rwa [Nat.sub_add_cancel hu]) (by rwa [Nat.sub_add_cancel ha]) (by omega)
    have hmaps : (s : Set (Fin n)).MapsTo b (Finset.Icc (k - a) (u - 2)) := by
      intro x hx
      obtain ⟨h1, h2⟩ := hrange x (Finset.mem_coe.mp hx)
      rw [Finset.mem_coe, Finset.mem_Icc]
      omega
    have hcard := Finset.card_eq_sum_card_fiberwise hmaps
    have hle : ∀ j ∈ Finset.Icc (k - a) (u - 2),
        (s.filter (fun x => b x = j)).card ≤ Nat.choose (k - 2) j := by
      intro j hj
      rw [Finset.mem_Icc] at hj
      obtain ⟨hcupj, hcapj⟩ := hband j (by omega)
      have h := @card_le_choose_of_oneChange_no_cap_no_cup n (k - j) (j + 2) χ
        (s.filter (fun x => b x = j)) (by omega) (by omega)
        (hone.mono (Finset.filter_subset _ _)) hcapj hcupj
      rw [show k - j + (j + 2) - 4 = k - 2 by omega,
        show k - j - 2 = k - 2 - j by omega, Nat.choose_symm (by omega)] at h
      exact h
    have hsum := Finset.sum_le_sum hle
    omega
  · -- Classic regime: the all-triples binomial bound with `c = a`, `v = u`.
    rw [decomposableThreshold_eq_choose ha2 hu2 hbase] at hlt
    have := card_le_choose_of_oneChange_no_cap_no_cup ha2 hu2 hone hnoCap hnoCup
    omega

end ErdosSzekeres
