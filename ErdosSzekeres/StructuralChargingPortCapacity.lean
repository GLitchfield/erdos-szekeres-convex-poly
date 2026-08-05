module

public import ErdosSzekeres.StructuralChargingIntervals

@[expose] public section

/-!
# Endpoint-port capacity for ordered crossing caps

This file records the local quantitative invariant surviving the crossing-cap
counterexamples.  At a deep-below split, every lower vertex of a crossing cap
is a sweep endpoint.  In a weakly ordered family, one underlying vertex can
serve at most twice: once as a right endpoint and once as a left endpoint.
-/

namespace ErdosSzekeres

open HasDeepBelowSplit

/-- A common vertex of two weakly ordered finite sets is the right endpoint of
the earlier set and the left endpoint of the later set. -/
theorem FinsetWeaklyBefore.shared_vertex_endpoints {n : ℕ}
    {earlier later : Finset (Fin n)} (h : FinsetWeaklyBefore earlier later)
    {q : Fin n} (hqEarlier : q ∈ earlier) (hqLater : q ∈ later) :
    IsRightSweepEndpoint earlier q ∧ IsLeftSweepEndpoint later q := by
  constructor
  · intro x hx
    exact h x hx q hqLater
  · intro y hy
    exact h q hqEarlier y hy

/-- A finite set with the same left and right sweep endpoint has at most one
element. -/
theorem card_le_one_of_sweep_endpoints {n : ℕ} {s : Finset (Fin n)} {q : Fin n}
    (hleft : IsLeftSweepEndpoint s q) (hright : IsRightSweepEndpoint s q) :
    s.card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  exact le_antisymm ((hright x hx).trans (hleft y hy))
    ((hright y hy).trans (hleft x hx))

/-- In a weakly ordered family of sets of cardinality at least two, any vertex
belongs to at most two members.  This is the pure order-theoretic port-capacity
law behind the crossing-cap application. -/
theorem ordered_family_vertex_capacity_two {m n : ℕ}
    (sets : Fin m → Finset (Fin n))
    (hcard : ∀ i, 2 ≤ (sets i).card)
    (hordered : ∀ {i j}, i < j → FinsetWeaklyBefore (sets i) (sets j))
    (q : Fin n) :
    (Finset.univ.filter fun i ↦ q ∈ sets i).card ≤ 2 := by
  by_contra hnot
  have hthree : 2 < (Finset.univ.filter fun i ↦ q ∈ sets i).card := by omega
  obtain ⟨i, hi, j, hj, k, hk, hij, hik, hjk⟩ :=
    Finset.two_lt_card.mp hthree
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj hk
  have horders :
      (i < j ∧ j < k) ∨ (i < k ∧ k < j) ∨ (j < i ∧ i < k) ∨
        (j < k ∧ k < i) ∨ (k < i ∧ i < j) ∨ (k < j ∧ j < i) := by
    omega
  rcases horders with hijjk | hikj | hjik | hjki | hkij | hkji
  · have hleft := (hordered hijjk.1).shared_vertex_endpoints hi hj |>.2
    have hright := (hordered hijjk.2).shared_vertex_endpoints hj hk |>.1
    have := card_le_one_of_sweep_endpoints hleft hright
    have htwo := hcard j
    omega
  · have hleft := (hordered hikj.1).shared_vertex_endpoints hi hk |>.2
    have hright := (hordered hikj.2).shared_vertex_endpoints hk hj |>.1
    have := card_le_one_of_sweep_endpoints hleft hright
    have htwo := hcard k
    omega
  · have hleft := (hordered hjik.1).shared_vertex_endpoints hj hi |>.2
    have hright := (hordered hjik.2).shared_vertex_endpoints hi hk |>.1
    have := card_le_one_of_sweep_endpoints hleft hright
    have htwo := hcard i
    omega
  · have hleft := (hordered hjki.1).shared_vertex_endpoints hj hk |>.2
    have hright := (hordered hjki.2).shared_vertex_endpoints hk hi |>.1
    have := card_le_one_of_sweep_endpoints hleft hright
    have htwo := hcard k
    omega
  · have hleft := (hordered hkij.1).shared_vertex_endpoints hk hi |>.2
    have hright := (hordered hkij.2).shared_vertex_endpoints hi hj |>.1
    have := card_le_one_of_sweep_endpoints hleft hright
    have htwo := hcard i
    omega
  · have hleft := (hordered hkji.1).shared_vertex_endpoints hk hj |>.2
    have hright := (hordered hkji.2).shared_vertex_endpoints hj hi |>.1
    have := card_le_one_of_sweep_endpoints hleft hright
    have htwo := hcard j
    omega

/-- Ordered crossing caps at a deep-below split use lower-child endpoint ports,
share a port only in the forced right/left directions, and have multiplicity
at most two at each lower vertex. -/
theorem HasDeepBelowSplit.ordered_crossing_caps_lower_port_capacity
    {m n : ℕ} {χ : TripleColoring n} {lower upper : Finset (Fin n)}
    (h : HasDeepBelowSplit χ lower upper)
    (caps : Fin m → Finset (Fin n))
    (hsub : ∀ i, caps i ⊆ lower ∪ upper)
    (hcard : ∀ i, 2 ≤ (caps i).card)
    (hcap : ∀ i, IsCapSet χ (caps i))
    (_hcrossLower : ∀ i, ((caps i) ∩ lower).Nonempty)
    (hcrossUpper : ∀ i, ((caps i) ∩ upper).Nonempty)
    (hordered : ∀ {i j}, i < j → FinsetWeaklyBefore (caps i) (caps j)) :
    (∀ i q, q ∈ caps i ∩ lower → IsSweepEndpoint (caps i) q) ∧
      (∀ {i j q}, i < j → q ∈ caps i → q ∈ caps j →
        IsRightSweepEndpoint (caps i) q ∧ IsLeftSweepEndpoint (caps j) q) ∧
      ∀ q ∈ lower, (Finset.univ.filter fun i ↦ q ∈ caps i).card ≤ 2 := by
  constructor
  · intro i q hq
    exact h.lower_mem_cap_isSweepEndpoint (hsub i) (hcap i) (hcrossUpper i)
      (Finset.mem_inter.mp hq).1 (Finset.mem_inter.mp hq).2
  constructor
  · intro i j q hij hqi hqj
    exact (hordered hij).shared_vertex_endpoints hqi hqj
  · intro q _
    exact ordered_family_vertex_capacity_two caps hcard hordered q

/-- Summed form of lower endpoint-port capacity: an ordered family of crossing
caps consumes at most two lower ports per lower-child vertex. -/
theorem HasDeepBelowSplit.sum_crossing_caps_lower_card_le
    {m n : ℕ} {χ : TripleColoring n} {lower upper : Finset (Fin n)}
    (h : HasDeepBelowSplit χ lower upper)
    (caps : Fin m → Finset (Fin n))
    (hsub : ∀ i, caps i ⊆ lower ∪ upper)
    (hcard : ∀ i, 2 ≤ (caps i).card)
    (hcap : ∀ i, IsCapSet χ (caps i))
    (hcrossLower : ∀ i, ((caps i) ∩ lower).Nonempty)
    (hcrossUpper : ∀ i, ((caps i) ∩ upper).Nonempty)
    (hordered : ∀ {i j}, i < j → FinsetWeaklyBefore (caps i) (caps j)) :
    (∑ i, ((caps i) ∩ lower).card) ≤ 2 * lower.card := by
  have hcapacity :=
    h.ordered_crossing_caps_lower_port_capacity caps hsub hcard hcap
      hcrossLower hcrossUpper hordered
  calc
    (∑ i, ((caps i) ∩ lower).card) =
        ∑ i, ∑ q ∈ lower, if q ∈ caps i then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.card_filter]
      congr 1
      ext q
      simp [and_comm]
    _ = ∑ q ∈ lower, ∑ i, if q ∈ caps i then 1 else 0 :=
      Finset.sum_comm
    _ = ∑ q ∈ lower, (Finset.univ.filter fun i ↦ q ∈ caps i).card := by
      apply Finset.sum_congr rfl
      intro q _
      exact (Finset.card_filter (fun i ↦ q ∈ caps i) Finset.univ).symm
    _ ≤ ∑ _q ∈ lower, 2 := by
      apply Finset.sum_le_sum
      intro q hq
      exact hcapacity.2.2 q hq
    _ = 2 * lower.card := by simp [Nat.mul_comm]

end ErdosSzekeres

end
