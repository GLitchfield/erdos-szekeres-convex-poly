module

public import ErdosSzekeres.Decomposable

@[expose] public section

/-!
# Witness-level structural charging

This file develops incompatibilities among actual cup and cap witnesses at a
deep-below root. It deliberately carries no quotient or profile state.
-/

namespace ErdosSzekeres

/-- The witness-level upper-child alternative selected by the structural
charging review. -/
def UpperChildGapTrichotomy455 {n : ℕ} (χ : TripleColoring n)
    (upper : Finset (Fin n)) (q : Fin n) : Prop :=
  ContainsCapSet χ upper 4 ∨ ContainsCupSet χ upper 5 ∨
    ContainsStrongPolygonSet χ upper 5 ∨
      ∃ cap : Finset (Fin n), cap ⊆ upper ∧ cap.card = 3 ∧
        IsCapSet χ cap ∧ HasDeepBelowSplit.IsSweepEndpoint cap q

/-- The open structural target: the gap trichotomy for seven decomposable
upper vertices at a singleton deep-below root. -/
def UpperChildGapTrichotomyAtSeven : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n} {upper : Finset (Fin n)} {q : Fin n},
    IsDecomposableOn χ upper → HasDeepBelowSplit χ {q} upper →
      upper.card = 7 → UpperChildGapTrichotomy455 χ upper q

/-- The rank-three one-change law restricted to one finite vertex set. -/
def OneChangeOn {n : ℕ} (χ : TripleColoring n) (s : Finset (Fin n)) : Prop :=
  ∀ {i j k l : Fin n}, (hij : i < j) → (hjk : j < k) → (hkl : k < l) →
    i ∈ s → j ∈ s → k ∈ s → l ∈ s →
      TurnSequenceAllowed
        (χ ⟨i, j, k, hij, hjk⟩)
        (χ ⟨i, j, l, hij, hjk.trans hkl⟩)
        (χ ⟨i, k, l, hij.trans hjk, hkl⟩)
        (χ ⟨j, k, l, hjk, hkl⟩)

/-- Strong four-subsets of a finite ordered vertex set. -/
noncomputable def StrongQuadruplesIn {n : ℕ} (χ : TripleColoring n)
    (s : Finset (Fin n)) : Finset (Finset (Fin n)) := by
  classical
  exact (s.powersetCard 4).filter (IsStrongPolygonSet χ)

@[simp] theorem mem_strongQuadruplesIn {n : ℕ}
    {χ : TripleColoring n} {s q : Finset (Fin n)} :
    q ∈ StrongQuadruplesIn χ s ↔
      q ⊆ s ∧ q.card = 4 ∧ IsStrongPolygonSet χ q := by
  classical
  simp [StrongQuadruplesIn, and_assoc]

/-- An allowed four-turn word has an equal first pair or an equal last pair. -/
theorem TurnSequenceAllowed.first_eq_or_last_eq
    {A B C D : Turn} (h : TurnSequenceAllowed A B C D) :
    A = B ∨ C = D := by
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

/-- Strongness of an ordered four-set is exactly its two outer equalities. -/
theorem isStrongPolygonSet_four_iff
    {n : ℕ} {χ : TripleColoring n} {a b c d : Fin n}
    (hab : a < b) (hbc : b < c) (hcd : c < d) :
    IsStrongPolygonSet χ {a, b, c, d} ↔
      (χ ⟨a, b, c, hab, hbc⟩ =
          χ ⟨a, b, d, hab, hbc.trans hcd⟩ ∧
        χ ⟨a, c, d, hab.trans hbc, hcd⟩ =
          χ ⟨b, c, d, hbc, hcd⟩) := by
  constructor
  · intro h
    exact h hab hbc hcd (by simp) (by simp) (by simp) (by simp)
  · intro h i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl <;>
          rcases hl with rfl | rfl | rfl | rfl <;> omega

/-- A family of strong sets covering every four-subset makes the target set
strong. -/
theorem isStrongPolygonSet_of_quadruple_cover
    {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)}
    {cover : Finset (Finset (Fin n))}
    (hstrong : ∀ t ∈ cover, IsStrongPolygonSet χ t)
    (hcover : ∀ q ∈ s.powersetCard 4, ∃ t ∈ cover, q ⊆ t) :
    IsStrongPolygonSet χ s := by
  intro i j k l hij hjk hkl hi hj hk hl
  have hquad : ({i, j, k, l} : Finset (Fin n)) ∈ s.powersetCard 4 := by
    rw [Finset.mem_powersetCard]
    constructor
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hi
      · exact hj
      · exact hk
      · exact hl
    · simp [ne_of_lt hij, ne_of_lt (hij.trans hjk),
        ne_of_lt (hij.trans (hjk.trans hkl)), ne_of_lt hjk,
        ne_of_lt (hjk.trans hkl), ne_of_lt hkl]
  obtain ⟨t, ht, hsub⟩ := hcover {i, j, k, l} hquad
  exact hstrong t ht hij hjk hkl
    (hsub (by simp)) (hsub (by simp)) (hsub (by simp)) (hsub (by simp))

private def turnChange (x y : Turn) : ℕ :=
  if x = y then 0 else 1

private def turnBit : Turn → ZMod 2
  | .left => 0
  | .right => 1

private theorem turnChange_cast (x y : Turn) :
    (turnChange x y : ZMod 2) = turnBit x + turnBit y := by
  cases x <;> cases y
  · rfl
  · rfl
  · rfl
  · change (0 : ZMod 2) = 1 + 1
    rw [← Nat.cast_one, ← Nat.cast_one, ← Nat.cast_add,
      ZMod.natCast_self]

private theorem turnChange_comm (x y : Turn) :
    turnChange x y = turnChange y x := by
  simp [turnChange, eq_comm]

private theorem turnChange_triangle_even (x y z : Turn) :
    Even (turnChange x y + turnChange y z + turnChange z x) := by
  rw [← ZMod.natCast_eq_zero_iff_even]
  push_cast
  simp only [turnChange_cast]
  ring_nf
  have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
  simp [htwo]

private theorem turnChange_cycle_four_even (w x y z : Turn) :
    Even (turnChange w x + turnChange x y + turnChange y z + turnChange z w) := by
  rw [← ZMod.natCast_eq_zero_iff_even]
  push_cast
  simp only [turnChange_cast]
  ring_nf
  have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
  simp [htwo]

private def outerDefect (A B C D : Turn) : ℕ :=
  turnChange A B + turnChange C D

private theorem outerDefect_eq_badIndicator
    {A B C D : Turn} (h : TurnSequenceAllowed A B C D) :
    outerDefect A B C D = if ¬(A = B ∧ C = D) then 1 else 0 := by
  rcases h.first_eq_or_last_eq with hab | hcd
  · subst B
    simp [outerDefect, turnChange]
  · subst D
    simp [outerDefect, turnChange]

private theorem powersetCard_four_ordered_five
    {n : ℕ} {a b c d e : Fin n}
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hde : d < e) :
    ({a, b, c, d, e} : Finset (Fin n)).powersetCard 4 =
      {{a, b, c, d}, {a, b, c, e}, {a, b, d, e},
        {a, c, d, e}, {b, c, d, e}} := by
  classical
  let s : Finset (Fin n) := {a, b, c, d, e}
  let q0 : Finset (Fin n) := {a, b, c, d}
  let q1 : Finset (Fin n) := {a, b, c, e}
  let q2 : Finset (Fin n) := {a, b, d, e}
  let q3 : Finset (Fin n) := {a, c, d, e}
  let q4 : Finset (Fin n) := {b, c, d, e}
  have hac := hab.trans hbc
  have had := hac.trans hcd
  have hae := had.trans hde
  have hbd := hbc.trans hcd
  have hbe := hbd.trans hde
  have hce := hcd.trans hde
  have hsCard : s.card = 5 := by
    simp [s, hab.ne, hac.ne, had.ne, hae.ne, hbc.ne, hbd.ne,
      hbe.ne, hcd.ne, hce.ne, hde.ne]
  change s.powersetCard 4 = {q0, q1, q2, q3, q4}
  ext q
  constructor
  · intro hq
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hq
    have hnot : ¬s ⊆ q := by
      intro hsq
      have hle := Finset.card_le_card hsq
      omega
    obtain ⟨x, hxs, hxq⟩ := Finset.not_subset.mp hnot
    have hqsub : q ⊆ s.erase x := by
      intro y hy
      exact Finset.mem_erase.mpr ⟨by
        intro hyx
        subst y
        exact hxq hy, hsub hy⟩
    have heraseCard : (s.erase x).card = 4 := by
      rw [Finset.card_erase_of_mem hxs, hsCard]
    have hqeq : q = s.erase x :=
      Finset.eq_of_subset_of_card_le hqsub (by omega)
    rw [hqeq]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at hxs
    rcases hxs with rfl | rfl | rfl | rfl | rfl
    · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
      ext y
      simp only [s, q4, Finset.mem_erase, Finset.mem_insert,
        Finset.mem_singleton]
      omega
    · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
      ext y
      simp only [s, q3, Finset.mem_erase, Finset.mem_insert,
        Finset.mem_singleton]
      omega
    · refine Or.inr (Or.inr (Or.inl ?_))
      ext y
      simp only [s, q2, Finset.mem_erase, Finset.mem_insert,
        Finset.mem_singleton]
      omega
    · refine Or.inr (Or.inl ?_)
      ext y
      simp only [s, q1, Finset.mem_erase, Finset.mem_insert,
        Finset.mem_singleton]
      omega
    · refine Or.inl ?_
      ext y
      simp only [s, q0, Finset.mem_erase, Finset.mem_insert,
        Finset.mem_singleton]
      omega
  · intro hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;>
      simp [s, q0, q1, q2, q3, q4, hab.ne, hac.ne, had.ne, hae.ne,
        hbc.ne, hbd.ne, hbe.ne, hcd.ne, hce.ne, hde.ne]

/-- Five ordered vertices satisfying the one-change law have an odd number
of strong four-subsets. -/
theorem odd_card_strongQuadruplesIn_ordered_five
    {n : ℕ} {χ : TripleColoring n} {a b c d e : Fin n}
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hde : d < e)
    (hone : OneChangeOn χ {a, b, c, d, e}) :
    Odd (StrongQuadruplesIn χ {a, b, c, d, e}).card := by
  classical
  let s : Finset (Fin n) := {a, b, c, d, e}
  let q0 : Finset (Fin n) := {a, b, c, d}
  let q1 : Finset (Fin n) := {a, b, c, e}
  let q2 : Finset (Fin n) := {a, b, d, e}
  let q3 : Finset (Fin n) := {a, c, d, e}
  let q4 : Finset (Fin n) := {b, c, d, e}
  change OneChangeOn χ s at hone
  change Odd (StrongQuadruplesIn χ s).card
  have hac := hab.trans hbc
  have had := hac.trans hcd
  have hae := had.trans hde
  have hbd := hbc.trans hcd
  have hbe := hbd.trans hde
  have hce := hcd.trans hde
  let A : Turn := χ ⟨a, b, c, hab, hbc⟩
  let B : Turn := χ ⟨a, b, d, hab, hbd⟩
  let C : Turn := χ ⟨a, b, e, hab, hbe⟩
  let D : Turn := χ ⟨a, c, d, hac, hcd⟩
  let E : Turn := χ ⟨a, c, e, hac, hce⟩
  let F : Turn := χ ⟨a, d, e, had, hde⟩
  let G : Turn := χ ⟨b, c, d, hbc, hcd⟩
  let H : Turn := χ ⟨b, c, e, hbc, hce⟩
  let I : Turn := χ ⟨b, d, e, hbd, hde⟩
  let J : Turn := χ ⟨c, d, e, hcd, hde⟩
  have hone0 : TurnSequenceAllowed A B D G := by
    simpa [A, B, D, G] using hone hab hbc hcd
      (by simp [s]) (by simp [s]) (by simp [s]) (by simp [s])
  have hone1 : TurnSequenceAllowed A C E H := by
    simpa [A, C, E, H] using hone hab hbc hce
      (by simp [s]) (by simp [s]) (by simp [s]) (by simp [s])
  have hone2 : TurnSequenceAllowed B C F I := by
    simpa [B, C, F, I] using hone hab hbd hde
      (by simp [s]) (by simp [s]) (by simp [s]) (by simp [s])
  have hone3 : TurnSequenceAllowed D E F J := by
    simpa [D, E, F, J] using hone hac hcd hde
      (by simp [s]) (by simp [s]) (by simp [s]) (by simp [s])
  have hone4 : TurnSequenceAllowed G H I J := by
    simpa [G, H, I, J] using hone hbc hcd hde
      (by simp [s]) (by simp [s]) (by simp [s]) (by simp [s])
  have hstrong0 : IsStrongPolygonSet χ q0 ↔ A = B ∧ D = G := by
    simpa [q0, A, B, D, G] using
      (isStrongPolygonSet_four_iff (χ := χ) hab hbc hcd)
  have hstrong1 : IsStrongPolygonSet χ q1 ↔ A = C ∧ E = H := by
    simpa [q1, A, C, E, H] using
      (isStrongPolygonSet_four_iff (χ := χ) hab hbc hce)
  have hstrong2 : IsStrongPolygonSet χ q2 ↔ B = C ∧ F = I := by
    simpa [q2, B, C, F, I] using
      (isStrongPolygonSet_four_iff (χ := χ) hab hbd hde)
  have hstrong3 : IsStrongPolygonSet χ q3 ↔ D = E ∧ F = J := by
    simpa [q3, D, E, F, J] using
      (isStrongPolygonSet_four_iff (χ := χ) hac hcd hde)
  have hstrong4 : IsStrongPolygonSet χ q4 ↔ G = H ∧ I = J := by
    simpa [q4, G, H, I, J] using
      (isStrongPolygonSet_four_iff (χ := χ) hbc hcd hde)
  have hdefect0 : outerDefect A B D G =
      if ¬IsStrongPolygonSet χ q0 then 1 else 0 := by
    by_cases hs : IsStrongPolygonSet χ q0
    · obtain ⟨hAB, hDG⟩ := hstrong0.mp hs
      simp [hs, outerDefect, turnChange, hAB, hDG]
    · have hn : ¬(A = B ∧ D = G) := fun h => hs (hstrong0.mpr h)
      simpa [hs, hn] using outerDefect_eq_badIndicator hone0
  have hdefect1 : outerDefect A C E H =
      if ¬IsStrongPolygonSet χ q1 then 1 else 0 := by
    by_cases hs : IsStrongPolygonSet χ q1
    · obtain ⟨hAC, hEH⟩ := hstrong1.mp hs
      simp [hs, outerDefect, turnChange, hAC, hEH]
    · have hn : ¬(A = C ∧ E = H) := fun h => hs (hstrong1.mpr h)
      simpa [hs, hn] using outerDefect_eq_badIndicator hone1
  have hdefect2 : outerDefect B C F I =
      if ¬IsStrongPolygonSet χ q2 then 1 else 0 := by
    by_cases hs : IsStrongPolygonSet χ q2
    · obtain ⟨hBC, hFI⟩ := hstrong2.mp hs
      simp [hs, outerDefect, turnChange, hBC, hFI]
    · have hn : ¬(B = C ∧ F = I) := fun h => hs (hstrong2.mpr h)
      simpa [hs, hn] using outerDefect_eq_badIndicator hone2
  have hdefect3 : outerDefect D E F J =
      if ¬IsStrongPolygonSet χ q3 then 1 else 0 := by
    by_cases hs : IsStrongPolygonSet χ q3
    · obtain ⟨hDE, hFJ⟩ := hstrong3.mp hs
      simp [hs, outerDefect, turnChange, hDE, hFJ]
    · have hn : ¬(D = E ∧ F = J) := fun h => hs (hstrong3.mpr h)
      simpa [hs, hn] using outerDefect_eq_badIndicator hone3
  have hdefect4 : outerDefect G H I J =
      if ¬IsStrongPolygonSet χ q4 then 1 else 0 := by
    by_cases hs : IsStrongPolygonSet χ q4
    · obtain ⟨hGH, hIJ⟩ := hstrong4.mp hs
      simp [hs, outerDefect, turnChange, hGH, hIJ]
    · have hn : ¬(G = H ∧ I = J) := fun h => hs (hstrong4.mpr h)
      simpa [hs, hn] using outerDefect_eq_badIndicator hone4
  have hcycle1 := turnChange_triangle_even A B C
  have hcycle2 := turnChange_cycle_four_even D G H E
  have hcycle3 := turnChange_triangle_even F I J
  have hcycles : Even
      ((turnChange A B + turnChange B C + turnChange C A) +
        (turnChange D G + turnChange G H + turnChange H E + turnChange E D) +
        (turnChange F I + turnChange I J + turnChange J F)) := by
    rcases hcycle1 with ⟨u, hu⟩
    rcases hcycle2 with ⟨v, hv⟩
    rcases hcycle3 with ⟨w, hw⟩
    refine ⟨u + v + w, ?_⟩
    omega
  have hdefectSum :
      outerDefect A B D G + outerDefect A C E H +
          outerDefect B C F I + outerDefect D E F J +
          outerDefect G H I J =
        (turnChange A B + turnChange B C + turnChange C A) +
          (turnChange D G + turnChange G H + turnChange H E + turnChange E D) +
          (turnChange F I + turnChange I J + turnChange J F) := by
    simp only [outerDefect]
    rw [turnChange_comm A C, turnChange_comm E H,
      turnChange_comm D E, turnChange_comm F J]
    ac_rfl
  have htotalDefect : Even
      (outerDefect A B D G + outerDefect A C E H +
        outerDefect B C F I + outerDefect D E F J +
        outerDefect G H I J) := by
    rw [hdefectSum]
    exact hcycles
  have finset_ne_of_mem_not_mem
      {u v : Finset (Fin n)} {x : Fin n}
      (hu : x ∈ u) (hv : x ∉ v) : u ≠ v := by
    intro huv
    exact hv (huv ▸ hu)
  have hq01 : q0 ≠ q1 := finset_ne_of_mem_not_mem
    (x := d) (by simp [q0])
    (by simp [q1, ne_of_gt had, ne_of_gt hbd, ne_of_gt hcd, hde.ne])
  have hq02 : q0 ≠ q2 := finset_ne_of_mem_not_mem
    (x := c) (by simp [q0])
    (by simp [q2, ne_of_gt hac, ne_of_gt hbc, hcd.ne, hce.ne])
  have hq03 : q0 ≠ q3 := finset_ne_of_mem_not_mem
    (x := b) (by simp [q0])
    (by simp [q3, ne_of_gt hab, hbc.ne, hbd.ne, hbe.ne])
  have hq04 : q0 ≠ q4 := finset_ne_of_mem_not_mem
    (x := a) (by simp [q0])
    (by simp [q4, hab.ne, hac.ne, had.ne, hae.ne])
  have hq12 : q1 ≠ q2 := finset_ne_of_mem_not_mem
    (x := c) (by simp [q1])
    (by simp [q2, ne_of_gt hac, ne_of_gt hbc, hcd.ne, hce.ne])
  have hq13 : q1 ≠ q3 := finset_ne_of_mem_not_mem
    (x := b) (by simp [q1])
    (by simp [q3, ne_of_gt hab, hbc.ne, hbd.ne, hbe.ne])
  have hq14 : q1 ≠ q4 := finset_ne_of_mem_not_mem
    (x := a) (by simp [q1])
    (by simp [q4, hab.ne, hac.ne, had.ne, hae.ne])
  have hq23 : q2 ≠ q3 := finset_ne_of_mem_not_mem
    (x := b) (by simp [q2])
    (by simp [q3, ne_of_gt hab, hbc.ne, hbd.ne, hbe.ne])
  have hq24 : q2 ≠ q4 := finset_ne_of_mem_not_mem
    (x := a) (by simp [q2])
    (by simp [q4, hab.ne, hac.ne, had.ne, hae.ne])
  have hq34 : q3 ≠ q4 := finset_ne_of_mem_not_mem
    (x := a) (by simp [q3])
    (by simp [q4, hab.ne, hac.ne, had.ne, hae.ne])
  have hpowerset : s.powersetCard 4 = {q0, q1, q2, q3, q4} := by
    simpa [s, q0, q1, q2, q3, q4] using
      powersetCard_four_ordered_five hab hbc hcd hde
  let bad := (s.powersetCard 4).filter fun q ↦ ¬IsStrongPolygonSet χ q
  have hbadCard : bad.card =
      (if ¬IsStrongPolygonSet χ q0 then 1 else 0) +
        (if ¬IsStrongPolygonSet χ q1 then 1 else 0) +
        (if ¬IsStrongPolygonSet χ q2 then 1 else 0) +
        (if ¬IsStrongPolygonSet χ q3 then 1 else 0) +
        (if ¬IsStrongPolygonSet χ q4 then 1 else 0) := by
    by_cases h0 : IsStrongPolygonSet χ q0 <;>
      by_cases h1 : IsStrongPolygonSet χ q1 <;>
        by_cases h2 : IsStrongPolygonSet χ q2 <;>
          by_cases h3 : IsStrongPolygonSet χ q3 <;>
            by_cases h4 : IsStrongPolygonSet χ q4 <;>
              simp [bad, hpowerset, Finset.filter_insert,
                Finset.filter_singleton, h0, h1, h2, h3, h4,
                hq01, hq02, hq03, hq04, hq12, hq13, hq14, hq23, hq24, hq34]
  have hbadDefect : bad.card =
      outerDefect A B D G + outerDefect A C E H +
        outerDefect B C F I + outerDefect D E F J +
        outerDefect G H I J := by
    rw [hbadCard, ← hdefect0, ← hdefect1, ← hdefect2,
      ← hdefect3, ← hdefect4]
  have hbadEven : Even bad.card := by
    rw [hbadDefect]
    exact htotalDefect
  have hfullCard : (s.powersetCard 4).card = 5 := by
    rw [hpowerset]
    simp [hq01, hq02, hq03, hq04, hq12, hq13, hq14, hq23, hq24, hq34]
  have hpartition : (StrongQuadruplesIn χ s).card + bad.card = 5 := by
    simpa [StrongQuadruplesIn, bad, hfullCard] using
      (Finset.card_filter_add_card_filter_not
        (s := s.powersetCard 4) (p := IsStrongPolygonSet χ))
  rcases hbadEven with ⟨k, hk⟩
  refine ⟨2 - k, ?_⟩
  omega

/-- The irreducible structural core selected by the route review: two
consecutive cup blocks of sizes three and four force the `(4,5,5)` outcome. -/
def CupBlocks34Force455 : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)},
    Disjoint left right → (∀ x ∈ left, ∀ y ∈ right, x < y) →
      ((left.card = 3 ∧ right.card = 4) ∨
        (left.card = 4 ∧ right.card = 3)) →
      IsCupSet χ left → IsCupSet χ right → OneChangeOn χ (left ∪ right) →
      ContainsCapSet χ (left ∪ right) 4 ∨
        ContainsCupSet χ (left ∪ right) 5 ∨
        ContainsStrongPolygonSet χ (left ∪ right) 5

/-- A right-turning ordered triple is a three-cap on its vertex set. -/
theorem isCapSet_three {n : ℕ} {χ : TripleColoring n}
    (t : OrderedTriple n) (hcolor : χ t = Turn.right) :
    IsCapSet χ {t.i, t.j, t.k} := by
  have htij : t.i < t.j := t.hij
  have htjk : t.j < t.k := t.hjk
  rintro ⟨a, b, c, hab, hbc⟩ ha hb hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc
  rcases ha with rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl <;>
      rcases hc with rfl | rfl | rfl <;> try omega

/-- If no upper three-cap has `q` as a sweep endpoint, the upper vertices on
each side of `q` are cups. -/
theorem gap_sides_are_cups_of_no_endpoint_cap_three {n : ℕ}
    {χ : TripleColoring n} {upper : Finset (Fin n)} {q : Fin n}
    (hno : ¬∃ cap : Finset (Fin n), cap ⊆ upper ∧ cap.card = 3 ∧
      IsCapSet χ cap ∧ HasDeepBelowSplit.IsSweepEndpoint cap q) :
    IsCupSet χ (upper.filter (· < q)) ∧
      IsCupSet χ (upper.filter (q < ·)) := by
  constructor
  · intro t hi hj hk
    cases hcolor : χ t with
    | left => rfl
    | right =>
        exfalso
        apply hno
        refine ⟨{t.i, t.j, t.k}, ?_, ?_, isCapSet_three t hcolor, Or.inr ?_⟩
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl
          · exact (Finset.mem_filter.mp hi).1
          · exact (Finset.mem_filter.mp hj).1
          · exact (Finset.mem_filter.mp hk).1
        · simp [ne_of_lt t.hij, ne_of_lt t.hjk,
            ne_of_lt (t.hij.trans t.hjk)]
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl
          · exact (Finset.mem_filter.mp hi).2.le
          · exact (Finset.mem_filter.mp hj).2.le
          · exact (Finset.mem_filter.mp hk).2.le
  · intro t hi hj hk
    cases hcolor : χ t with
    | left => rfl
    | right =>
        exfalso
        apply hno
        refine ⟨{t.i, t.j, t.k}, ?_, ?_, isCapSet_three t hcolor, Or.inl ?_⟩
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl
          · exact (Finset.mem_filter.mp hi).1
          · exact (Finset.mem_filter.mp hj).1
          · exact (Finset.mem_filter.mp hk).1
        · simp [ne_of_lt t.hij, ne_of_lt t.hjk,
            ne_of_lt (t.hij.trans t.hjk)]
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl
          · exact (Finset.mem_filter.mp hi).2.le
          · exact (Finset.mem_filter.mp hj).2.le
          · exact (Finset.mem_filter.mp hk).2.le

/-- A cup subset has at most four vertices when the ambient set has no
five-cup. -/
theorem card_le_four_of_isCupSet_of_no_five_cup {n : ℕ}
    {χ : TripleColoring n} {s upper : Finset (Fin n)}
    (hsub : s ⊆ upper) (hcup : IsCupSet χ s)
    (hno : ¬ContainsCupSet χ upper 5) : s.card ≤ 4 := by
  by_contra hcard
  have hfive : 5 ≤ s.card := by omega
  obtain ⟨five, hfiveSub, hfiveCard⟩ := Finset.exists_subset_card_eq hfive
  apply hno
  exact ⟨five, hfiveSub.trans hsub, hfiveCard,
    FinsetPolygon.IsCupSet.mono hcup hfiveSub⟩

/-- Seven vertices split by an external anchor into two cups of size at most
four must have side sizes three and four. -/
theorem gap_cup_blocks_three_four {n : ℕ} {χ : TripleColoring n}
    {upper : Finset (Fin n)} {q : Fin n} (hq : q ∉ upper)
    (hcard : upper.card = 7) (hnoCup : ¬ContainsCupSet χ upper 5)
    (hcups : IsCupSet χ (upper.filter (· < q)) ∧
      IsCupSet χ (upper.filter (q < ·))) :
    (((upper.filter (· < q)).card = 3 ∧
        (upper.filter (q < ·)).card = 4) ∨
      ((upper.filter (· < q)).card = 4 ∧
        (upper.filter (q < ·)).card = 3)) := by
  let left := upper.filter (· < q)
  let right := upper.filter (q < ·)
  have hunion : left ∪ right = upper := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (Finset.mem_filter.mp hx).1
      · exact (Finset.mem_filter.mp hx).1
    · intro hx
      have hxq : x ≠ q := by rintro rfl; exact hq hx
      rcases lt_or_gt_of_ne hxq with hxlt | hxgt
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, hxlt⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, hxgt⟩)
  have hdisjoint : Disjoint left right := by
    rw [Finset.disjoint_left]
    intro x hxLeft hxRight
    have hxlt := (Finset.mem_filter.mp hxLeft).2
    have hxgt := (Finset.mem_filter.mp hxRight).2
    omega
  have hleftSub : left ⊆ upper := Finset.filter_subset _ _
  have hrightSub : right ⊆ upper := Finset.filter_subset _ _
  have hleftCard : left.card ≤ 4 :=
    card_le_four_of_isCupSet_of_no_five_cup hleftSub hcups.1 hnoCup
  have hrightCard : right.card ≤ 4 :=
    card_le_four_of_isCupSet_of_no_five_cup hrightSub hcups.2 hnoCup
  have hsum : left.card + right.card = 7 := by
    rw [← Finset.card_union_of_disjoint hdisjoint, hunion, hcard]
  change (left.card = 3 ∧ right.card = 4) ∨
    (left.card = 4 ∧ right.card = 3)
  omega

/-- The two-cup-block core implies the reviewed seven-vertex upper-child gap
trichotomy without a finite certificate. -/
theorem upperChildGapTrichotomyAtSeven_of_cupBlocks34
    (hblocks : CupBlocks34Force455) : UpperChildGapTrichotomyAtSeven := by
  intro n χ upper q hdecomposable hroot hcard
  by_cases hcap : ContainsCapSet χ upper 4
  · exact Or.inl hcap
  by_cases hcup : ContainsCupSet χ upper 5
  · exact Or.inr (Or.inl hcup)
  by_cases hstrong : ContainsStrongPolygonSet χ upper 5
  · exact Or.inr (Or.inr (Or.inl hstrong))
  by_cases hendpoint : ∃ cap : Finset (Fin n), cap ⊆ upper ∧
      cap.card = 3 ∧ IsCapSet χ cap ∧
        HasDeepBelowSplit.IsSweepEndpoint cap q
  · exact Or.inr (Or.inr (Or.inr hendpoint))
  have hq : q ∉ upper := by
    intro hqUpper
    exact (Finset.disjoint_left.mp hroot.disjoint) (by simp) hqUpper
  let left := upper.filter (· < q)
  let right := upper.filter (q < ·)
  have hcups : IsCupSet χ left ∧ IsCupSet χ right :=
    gap_sides_are_cups_of_no_endpoint_cap_three hendpoint
  have hcards : (left.card = 3 ∧ right.card = 4) ∨
      (left.card = 4 ∧ right.card = 3) :=
    gap_cup_blocks_three_four hq hcard hcup hcups
  have hunion : left ∪ right = upper := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (Finset.mem_filter.mp hx).1
      · exact (Finset.mem_filter.mp hx).1
    · intro hx
      have hxq : x ≠ q := by rintro rfl; exact hq hx
      rcases lt_or_gt_of_ne hxq with hxlt | hxgt
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, hxlt⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, hxgt⟩)
  have hdisjoint : Disjoint left right := by
    rw [Finset.disjoint_left]
    intro x hxLeft hxRight
    have hxlt := (Finset.mem_filter.mp hxLeft).2
    have hxgt := (Finset.mem_filter.mp hxRight).2
    omega
  have horder : ∀ x ∈ left, ∀ y ∈ right, x < y := by
    intro x hx y hy
    have hxq := (Finset.mem_filter.mp hx).2
    have hqy := (Finset.mem_filter.mp hy).2
    exact hxq.trans hqy
  have honeChange : OneChangeOn χ (left ∪ right) := by
    intro i j k l hij hjk hkl hi hj hk hl
    exact hdecomposable.turnSequenceAllowed hij hjk hkl
      (hunion ▸ hi) (hunion ▸ hj) (hunion ▸ hk) (hunion ▸ hl)
  have hout := hblocks hdisjoint horder hcards hcups.1 hcups.2 honeChange
  rw [hunion] at hout
  rcases hout with hcap' | hcup' | hstrong'
  · exact (hcap hcap').elim
  · exact (hcup hcup').elim
  · exact (hstrong hstrong').elim

namespace HasDeepBelowSplit

/-- Opposite children cannot simultaneously carry positive saturated chains
when both one-vertex extensions are forbidden. -/
theorem not_both_saturated_cup_cap {n : ℕ} {χ : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (h : HasDeepBelowSplit χ lower upper)
    {cup cap : Finset (Fin n)} {r s : ℕ}
    (hcupSub : cup ⊆ lower) (hcupCard : cup.card = r)
    (hcup : IsCupSet χ cup)
    (hcapSub : cap ⊆ upper) (hcapCard : cap.card = s)
    (hcap : IsCapSet χ cap) (_hr : 0 < r) (hs : 0 < s)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) (r + 1))
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) (s + 1)) : False := by
  have hcapNonempty : cap.Nonempty := Finset.card_pos.mp (by omega)
  let q := cap.min' hcapNonempty
  have hqCap : q ∈ cap := Finset.min'_mem cap hcapNonempty
  have hqUpper : q ∈ upper := hcapSub hqCap
  obtain ⟨⟨x, hxCup, hxq⟩, _⟩ := h.cup_straddles_upper_of_not_containsCupSet_succ
    hcupSub hcupCard hcup hqUpper hnoCup
  have hxLower : x ∈ lower := hcupSub hxCup
  obtain ⟨⟨a, haCap, hax⟩, _⟩ := h.cap_straddles_lower_of_not_containsCapSet_succ
    hcapSub hcapCard hcap hxLower hnoCap
  have hqa : q ≤ a := Finset.min'_le cap a haCap
  omega

/-- Every branch of the upper-child gap trichotomy gives the desired
singleton-root `(4,5,5)` alternative. -/
theorem singleton_root_state455_of_upperChildGap {n : ℕ}
    {χ : TripleColoring n} {upper : Finset (Fin n)} {q : Fin n}
    (h : HasDeepBelowSplit χ {q} upper)
    (hgap : UpperChildGapTrichotomy455 χ upper q) :
    ContainsCapSet χ ({q} ∪ upper) 4 ∨
      ContainsCupSet χ ({q} ∪ upper) 5 ∨
      ContainsStrongPolygonSet χ ({q} ∪ upper) 5 := by
  rcases hgap with hcap | hcup | hstrong | ⟨cap, hcapSub, hcapCard, hcap, hendpoint⟩
  · exact Or.inl (FinsetPolygon.ContainsCapSet.mono hcap Finset.subset_union_right)
  · exact Or.inr (Or.inl
      (FinsetPolygon.ContainsCupSet.mono hcup Finset.subset_union_right))
  · exact Or.inr (Or.inr
      (FinsetPolygon.ContainsStrongPolygonSet.mono
        hstrong Finset.subset_union_right))
  · left
    simpa using h.containsCapSet_succ_of_lower_endpoint
      hcapSub hcapCard hcap (by simp) hendpoint

/-- The seven-vertex gap trichotomy mechanically yields the certificate-free
singleton-root cardinal bound. -/
theorem singleton_root_card_le_seven_of_gapTrichotomy
    (hgap : UpperChildGapTrichotomyAtSeven) {n : ℕ}
    {χ : TripleColoring n} {upper : Finset (Fin n)} {q : Fin n}
    (hupper : IsDecomposableOn χ upper)
    (h : HasDeepBelowSplit χ {q} upper)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ upper) 4)
    (hnoCup : ¬ContainsCupSet χ ({q} ∪ upper) 5)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ upper) 5) :
    ({q} ∪ upper).card ≤ 7 := by
  by_contra hcard
  have hcardEq : ({q} ∪ upper).card = 1 + upper.card := by
    rw [Finset.card_union_of_disjoint h.disjoint]
    simp
  have hseven : 7 ≤ upper.card := by omega
  obtain ⟨seven, hsevenSub, hsevenCard⟩ := Finset.exists_subset_card_eq hseven
  have hsevenNonempty : seven.Nonempty := Finset.card_pos.mp (by omega)
  have hsevenDecomposable : IsDecomposableOn χ seven :=
    hupper.subset hsevenSub hsevenNonempty
  have hsevenSplit : HasDeepBelowSplit χ {q} seven :=
    h.mono Finset.Subset.rfl hsevenSub
  have hsmall := singleton_root_state455_of_upperChildGap hsevenSplit
    (hgap hsevenDecomposable hsevenSplit hsevenCard)
  have hsmallSub : {q} ∪ seven ⊆ {q} ∪ upper :=
    Finset.union_subset_union Finset.Subset.rfl hsevenSub
  rcases hsmall with hcap | hcup | hstrong
  · exact hnoCap (FinsetPolygon.ContainsCapSet.mono hcap hsmallSub)
  · exact hnoCup (FinsetPolygon.ContainsCupSet.mono hcup hsmallSub)
  · exact hnoStrong
      (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong hsmallSub)

end HasDeepBelowSplit
end ErdosSzekeres

end
