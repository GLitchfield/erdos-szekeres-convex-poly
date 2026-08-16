module

public import ErdosSzekeres.SukChainRunConsumer
public import ErdosSzekeres.SukAntichainUnionConsumer

@[expose] public section

/-!
# Global Suk branch integration

This module eliminates the finite chain/antichain disjunction by composing
the two independently compiled branch consumers.
-/

namespace ErdosSzekeres

noncomputable section

/-- The global finite Suk parameters force a convex subset in the original
raw-pool carrier, whichever side of the chain/antichain split occurs. -/
theorem SukConsecutiveRawPools.containsConvexSubset_of_globalParameters
    {L chainSize antiSize t m n K capSize : ℕ}
    {anchors : ℕ → Point 2}
    {pools : ℕ → Finset (Point 2)}
    (hraw : SukConsecutiveRawPools L anchors pools)
    (hchainSize : 1 ≤ chainSize)
    (hantiSize : 1 ≤ antiSize)
    (ht : 1 ≤ t)
    (hm : 2 ≤ m)
    (hL : (2 * t - 1) * m ≤ L)
    (hpoolCard : ∀ i, i < L →
      (chainSize - 1) * (antiSize - 1) < (pools i).card)
    (hK : 2 ≤ K)
    (hfinalDeficit : 2 ≤ n - ((m - 1) * K))
    (hfinalSize : n ≤ m * K)
    (hchainCard : ∀ u, u < m →
      Nat.choose (n + K - 4) ((u + 1) * K - 2) < chainSize)
    (hcapSize : 2 ≤ capSize)
    (hantiThreshold :
      Nat.choose (n + capSize - 4) (n - 2) < antiSize)
    (hantiTotal : n ≤ t * capSize) :
    ContainsConvexSubset (SukConsecutivePoolCarrier L pools) n := by
  have hn : 2 ≤ n := by
    omega
  rcases hraw.containsConvexSubset_or_antichainPacking
      hchainSize hantiSize ht hm hL hpoolCard hK hfinalDeficit
      hfinalSize hchainCard with hconvex | hpacking
  · exact hconvex
  · obtain ⟨selected, hselectedCard, hselected, hanti⟩ := hpacking
    have hsize : n ≤ selected.card * capSize := by
      rw [hselectedCard]
      exact hantiTotal
    exact hraw.antichainPacking_containsConvexSubset
      hn hcapSize hantiThreshold hselected hanti hsize

end

end ErdosSzekeres

end
