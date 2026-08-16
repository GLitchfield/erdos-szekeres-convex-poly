module

public import ErdosSzekeres.SukAdjacentChainRecurrence

@[expose] public section

/-!
# Indexed iteration of Suk's chain-rich pool recurrence

This module iterates the source-faithful adjacent-pool recurrence across a
finite interval of consecutive support pools.  Every completed convex subset
and every carried cap is internal to the proof of the final carrier theorem.
-/

namespace ErdosSzekeres

noncomputable section

/-- Consecutive raw adjacent-pool data, inspected only below `L`. -/
def SukConsecutiveChainPools
    (L : ℕ) (anchors : ℕ → Point 2)
    (pools : ℕ → Finset (Point 2)) : Prop :=
  ∀ i, i + 1 < L →
    SukAdjacentChainPools
      (anchors i) (anchors (i + 1)) (anchors (i + 2))
      (anchors (i + 3)) (anchors (i + 4))
      (pools i) (pools (i + 1))

/-- The finite union of the first `L` support pools. -/
def SukConsecutivePoolCarrier
    (L : ℕ) (pools : ℕ → Finset (Point 2)) : Finset (Point 2) :=
  (Finset.range L).biUnion pools

/-- A smaller selection can be extracted from a full anchor-extended cap. -/
theorem SukRegionHasFullAnchoredCap.containsConvexSubset_of_le
    {anchor : Point 2} {pool : Finset (Point 2)} {n k : ℕ}
    (hcap : SukRegionHasFullAnchoredCap anchor pool k) (hnk : n ≤ k) :
    ContainsConvexSubset pool n := by
  rcases hcap with ⟨selected, hselectedSubset, hselectedCard, hconvex⟩
  have hnSelected : n ≤ selected.card := by
    rw [hselectedCard]
    exact hnk
  obtain ⟨chosen, hchosenSubset, hchosenCard⟩ :=
    Finset.exists_subset_card_eq hnSelected
  refine ⟨chosen, hchosenSubset.trans hselectedSubset, hchosenCard, ?_⟩
  exact hconvex.mono
    (hchosenSubset.trans (Finset.subset_insert anchor selected))

private theorem containsConvexSubset_mono
    {s t : Finset (Point 2)} {n : ℕ}
    (h : ContainsConvexSubset s n) (hst : s ⊆ t) :
    ContainsConvexSubset t n := by
  rcases h with ⟨selected, hselectedSubset, hselectedCard, hconvex⟩
  exact ⟨selected, hselectedSubset.trans hst, hselectedCard, hconvex⟩

private theorem pool_subset_consecutiveCarrier
    {L i : ℕ} {pools : ℕ → Finset (Point 2)} (hi : i < L) :
    pools i ⊆ SukConsecutivePoolCarrier L pools := by
  exact Finset.subset_biUnion_of_mem pools (Finset.mem_range.mpr hi)

/-- Consecutive source-sized chain-rich pools contain the target convex
subset in their finite carrier. -/
theorem sukConsecutiveChainPools_containsConvexSubset
    (L n K : ℕ) (anchors : ℕ → Point 2)
    (pools : ℕ → Finset (Point 2))
    (hL : 2 ≤ L) (hK : 2 ≤ K)
    (hpools : SukConsecutiveChainPools L anchors pools)
    (hfinalDeficit : 2 ≤ n - ((L - 1) * K))
    (hfinalSize : n ≤ L * K)
    (hcard : ∀ i, i < L →
      Nat.choose (n + K - 4) ((i + 1) * K - 2) < (pools i).card) :
    ContainsConvexSubset (SukConsecutivePoolCarrier L pools) n := by
  have hn : 2 ≤ n := by
    omega
  have hstate : ∀ i, i < L →
      ContainsConvexSubset (SukConsecutivePoolCarrier L pools) n ∨
        SukRegionHasFullAnchoredCap
          (anchors (i + 2)) (pools i) ((i + 1) * K) := by
    intro i
    induction i with
    | zero =>
        intro _
        have hadjacent := hpools 0 (by omega)
        let hgeometry : SukRegionGeometry
            (anchors 0) (anchors 1) (anchors 2) (anchors 3) (pools 0) := {
          anchorsCap := hadjacent.anchorsCap.leftFour
          generalPosition := by
            apply hadjacent.generalPosition.mono
            intro p hp
            simp only [Finset.mem_insert, Finset.mem_union] at hp ⊢
            rcases hp with rfl | rfl | rfl | rfl | hp
            · exact Or.inl rfl
            · exact Or.inr (Or.inl rfl)
            · exact Or.inr (Or.inr (Or.inl rfl))
            · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
            · exact Or.inr
                (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hp)))))
          region := by
            intro p hp
            exact hadjacent.leftRegion hp
        }
        have hbaseSymmetry :
            Nat.choose (n + K - 4) (n - 2) =
              Nat.choose (n + K - 4) (K - 2) := by
          simpa using
            (sukAdjacentPool_choose_threshold n K 0
              (Nat.zero_le n) (by simpa using hn) (by simpa using hK)).2
        have hbaseCard :
            Nat.choose (n + K - 4) (n - 2) < (pools 0).card := by
          rw [hbaseSymmetry]
          simpa using hcard 0 (by omega)
        rcases sukRegionGeometry_base_fullAnchoredCap
            (anchors 0) (anchors 1) (anchors 2) (anchors 3)
            (pools 0) hgeometry
            (by
              intro p hp q hq hpq
              exact hadjacent.leftChain hp hq hpq)
            n K hn hK hbaseCard with hdone | hcap
        · exact Or.inl <| containsConvexSubset_mono hdone
            (pool_subset_consecutiveCarrier (by omega))
        · exact Or.inr (by simpa using hcap)
    | succ i ih =>
        intro hiNext
        rcases ih (by omega) with hdone | hleft
        · exact Or.inl hdone
        · have hadjacent := hpools i hiNext
          have hindexLe : i + 1 ≤ L - 1 := by
            omega
          have hcarryLe : (i + 1) * K ≤ (L - 1) * K :=
            Nat.mul_le_mul_right K hindexLe
          have hcarryTarget : (i + 1) * K ≤ n := by
            omega
          have hdeficit : 2 ≤ n - ((i + 1) * K) := by
            omega
          have hnextCarry : 2 ≤ (i + 1) * K + K := by
            omega
          have hstepSymmetry :
              Nat.choose (n + K - 4) (n - (i + 1) * K - 2) =
                Nat.choose (n + K - 4) ((i + 1) * K + K - 2) :=
            (sukAdjacentPool_choose_threshold n K ((i + 1) * K)
              hcarryTarget hdeficit hnextCarry).2
          have hstepCard :
              Nat.choose (n + K - 4) (n - (i + 1) * K - 2) <
                (pools (i + 1)).card := by
            rw [hstepSymmetry]
            simpa [Nat.add_mul] using hcard (i + 1) hiNext
          rcases sukAdjacentPool_fullCapStep
              (anchors i) (anchors (i + 1)) (anchors (i + 2))
              (anchors (i + 3)) (anchors (i + 4))
              (pools i) (pools (i + 1)) n K ((i + 1) * K)
              hadjacent hleft hcarryTarget (by omega) hdeficit hnextCarry
              hstepCard with hdone | hcap
          · apply Or.inl
            apply containsConvexSubset_mono hdone
            apply Finset.union_subset
            · exact pool_subset_consecutiveCarrier (by omega)
            · exact pool_subset_consecutiveCarrier hiNext
          · apply Or.inr
            convert hcap using 1
            all_goals ring
  have hlastIndex : L - 1 < L := by
    omega
  rcases hstate (L - 1) hlastIndex with hdone | hcap
  · exact hdone
  · have hLpos : 1 ≤ L := by
      omega
    have hlastSucc : L - 1 + 1 = L := Nat.sub_add_cancel hLpos
    have hnLast : n ≤ (L - 1 + 1) * K := by
      rw [hlastSucc]
      exact hfinalSize
    exact containsConvexSubset_mono
      (hcap.containsConvexSubset_of_le hnLast)
      (pool_subset_consecutiveCarrier hlastIndex)

end

end ErdosSzekeres

end
