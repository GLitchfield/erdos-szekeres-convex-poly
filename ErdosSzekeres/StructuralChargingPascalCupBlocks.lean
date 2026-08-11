module

public import ErdosSzekeres.StructuralChargingPascalTailGates

@[expose] public section

/-!
# A uniform cup-block interface for diagonal Pascal tails

For the diagonal family `(4,k,k)`, all established singleton-tail proofs are
instances of the same ordered-block pattern.  This file states that pattern
without asserting it, proves its exact quantitative consequence, and connects
it to the parameter-uniform Pascal-tail consumer.
-/

namespace ErdosSzekeres

/-- Two cup extensions of the same ordered core, one at each extreme, glue to
a cup.  The only new triples use both extreme vertices; a second core vertex
and the one-change law force their color. -/
theorem isCupSet_insert_two_of_extreme_cup_extensions
    {n : ℕ} {χ : TripleColoring n}
    {core : Finset (Fin n)} {x y : Fin n}
    (hcard : 2 ≤ core.card)
    (hx : x ∉ core) (hy : y ∉ core)
    (hleft : ∀ z ∈ core, x < z)
    (hright : ∀ z ∈ core, z < y)
    (hcupX : IsCupSet χ (insert x core))
    (hcupY : IsCupSet χ (insert y core))
    (hone : OneChangeOn χ (insert x (insert y core))) :
    IsCupSet χ (insert x (insert y core)) := by
  have hcoreNonempty : core.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨z₀, hz₀⟩ := hcoreNonempty
  have hxy : x < y := (hleft z₀ hz₀).trans (hright z₀ hz₀)
  have hxLe {z : Fin n} (hz : z ∈ insert x (insert y core)) : x ≤ z := by
    simp only [Finset.mem_insert] at hz
    rcases hz with rfl | rfl | hz
    · exact le_rfl
    · exact hxy.le
    · exact (hleft z hz).le
  have hleY {z : Fin n} (hz : z ∈ insert x (insert y core)) : z ≤ y := by
    simp only [Finset.mem_insert] at hz
    rcases hz with rfl | rfl | hz
    · exact hxy.le
    · exact le_rfl
    · exact (hright z hz).le
  have hcoreOfMem {z : Fin n}
      (hz : z ∈ insert x (insert y core)) (hzx : z ≠ x) (hzy : z ≠ y) :
      z ∈ core := by
    simpa [hzx, hzy] using hz
  intro t hi hj hk
  have hiNotY : t.i ≠ y := by
    intro hiy
    have hyj : y < t.j := by simpa [hiy] using t.hij
    exact (not_lt_of_ge (hleY hj)) hyj
  have hjNotX : t.j ≠ x := by
    intro hjx
    have hix : t.i < x := by simpa [hjx] using t.hij
    exact (not_lt_of_ge (hxLe hi)) hix
  have hjNotY : t.j ≠ y := by
    intro hjy
    have hyk : y < t.k := by simpa [hjy] using t.hjk
    exact (not_lt_of_ge (hleY hk)) hyk
  have hkNotX : t.k ≠ x := by
    intro hkx
    have hjx : t.j < x := by simpa [hkx] using t.hjk
    exact (not_lt_of_ge (hxLe hj)) hjx
  have hjCore : t.j ∈ core := hcoreOfMem hj hjNotX hjNotY
  by_cases hiX : t.i = x
  · by_cases hkY : t.k = y
    · obtain ⟨w, hwCore, hwne⟩ := core.exists_mem_ne (by omega) t.j
      have hxj : x < t.j := by simpa [hiX] using t.hij
      have hjy : t.j < y := by simpa [hkY] using t.hjk
      have ht : t = ⟨x, t.j, y, hxj, hjy⟩ := by
        cases t
        simp_all
      have hxMem : x ∈ insert x (insert y core) := Finset.mem_insert_self _ _
      have hyMem : y ∈ insert x (insert y core) :=
        Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      have hjMem : t.j ∈ insert x (insert y core) := by simp [hjCore]
      have hwMem : w ∈ insert x (insert y core) := by simp [hwCore]
      rcases lt_or_gt_of_ne hwne.symm with hjw | hwj
      · have hwy : w < y := hright w hwCore
        have ha : χ ⟨x, t.j, w, hxj, hjw⟩ = Turn.left :=
          hcupX _ (by simp) (by simp [hjCore]) (by simp [hwCore])
        have hd : χ ⟨t.j, w, y, hjw, hwy⟩ = Turn.left :=
          hcupY _ (by simp [hjCore]) (by simp [hwCore]) (by simp)
        have hall :=
          (hone hxj hjw hwy hxMem hjMem hwMem hyMem).all_eq_of_outer_eq
            (ha.trans hd.symm)
        have hb : χ ⟨x, t.j, y, hxj, hjy⟩ = Turn.left :=
          hall.1.symm.trans ha
        rw [ht]
        exact hb
      · have hxw : x < w := hleft w hwCore
        have ha : χ ⟨x, w, t.j, hxw, hwj⟩ = Turn.left :=
          hcupX _ (by simp) (by simp [hwCore]) (by simp [hjCore])
        have hd : χ ⟨w, t.j, y, hwj, hjy⟩ = Turn.left :=
          hcupY _ (by simp [hwCore]) (by simp [hjCore]) (by simp)
        have hall :=
          (hone hxw hwj hjy hxMem hwMem hjMem hyMem).all_eq_of_outer_eq
            (ha.trans hd.symm)
        have hc : χ ⟨x, t.j, y, hxj, hjy⟩ = Turn.left := by
          rw [← hall.2.1, ← hall.1, ha]
        rw [ht]
        exact hc
    · have hkCore : t.k ∈ core := hcoreOfMem hk hkNotX hkY
      exact hcupX t (by simp [hiX]) (by simp [hjCore]) (by simp [hkCore])
  · have hiCore : t.i ∈ core := hcoreOfMem hi hiX hiNotY
    by_cases hkY : t.k = y
    · exact hcupY t (by simp [hiCore]) (by simp [hjCore]) (by simp [hkY])
    · have hkCore : t.k ∈ core := hcoreOfMem hk hkNotX hkY
      exact hcupX t (by simp [hiCore]) (by simp [hjCore]) (by simp [hkCore])

/-- The parameterized ordered cup-block statement suggested by the certified
`3+4`, `4+5`, `5+6`, and `6+7` developments.  It is deliberately a contract:
proving it uniformly is the remaining mathematical obligation. -/
def DiagonalCupBlocksForce4kk (k : ℕ) : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)},
    Disjoint left right → (∀ x ∈ left, ∀ y ∈ right, x < y) →
      ((left.card = k - 2 ∧ right.card = k - 1) ∨
        (left.card = k - 1 ∧ right.card = k - 2)) →
      IsCupSet χ left → IsCupSet χ right → OneChangeOn χ (left ∪ right) →
      ContainsCapSet χ (left ∪ right) 4 ∨
        ContainsCupSet χ (left ∪ right) k ∨
        ContainsStrongPolygonSet χ (left ∪ right) k

/-- On the diagonal `(4,k,k)`, replacing the width-`choose (k-3) 2` lower
Pascal tail by a singleton leaves exactly `2k-3` reservoir vertices. -/
theorem lowerPascalTailReservoir_four_diagonal
    {k : ℕ} (hk : 5 ≤ k) :
    lowerPascalTailReservoir 4 k k = 2 * k - 3 := by
  rw [lowerPascalTailReservoir,
    decomposableThreshold_eq_window (by omega) (by omega) (by omega)]
  unfold decomposableBinomialWindow
  obtain ⟨m, rfl⟩ : ∃ m, k = 5 + m := Nat.exists_eq_add_of_le hk
  have h1 : 5 + m - 4 = m + 1 := by omega
  have h2 : 5 + m - 2 = m + 3 := by omega
  have h3 : 5 + m - 3 = m + 2 := by omega
  rw [h1, h2, h3]
  have htop : m + 3 = (m + 2) + 1 := by omega
  rw [htop, Finset.sum_Icc_succ_top (by omega)]
  simp only [Nat.choose_self]
  have htop' : m + 2 = (m + 1) + 1 := by omega
  rw [htop', Finset.sum_Icc_succ_top (by omega)]
  simp only [Nat.choose_succ_self_right]
  simp only [Finset.Icc_self, Finset.sum_singleton]
  have hcTop : m + 1 + 1 + 1 = m + 3 := by omega
  have hcArg : m + 1 = m + 3 - 2 := by omega
  rw [hcTop, hcArg]
  have hcSub : m + 3 - 2 + 1 = m + 2 := by omega
  rw [hcSub]
  norm_num only
  rw [Nat.choose_symm (by omega : 2 ≤ m + 3)]
  have hcSucc : m + 3 = (m + 2) + 1 := by omega
  rw [hcSucc, Nat.choose_succ_succ']
  simp only [Nat.choose_one_right]
  norm_num only
  omega

/-- A uniform `(k-2)+(k-1)` cup-block theorem bounds every target-free
ordered pair of cup sides by `2k-4`. -/
theorem diagonal_cup_block_card_add_le
    {k : ℕ} (hk : 5 ≤ k) (hblocks : DiagonalCupBlocksForce4kk k)
    {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)}
    (hdisjoint : Disjoint left right)
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hleft : IsCupSet χ left) (hright : IsCupSet χ right)
    (hone : OneChangeOn χ (left ∪ right))
    (hnoCap : ¬ContainsCapSet χ (left ∪ right) 4)
    (hnoCup : ¬ContainsCupSet χ (left ∪ right) k)
    (hnoStrong : ¬ContainsStrongPolygonSet χ (left ∪ right) k) :
    left.card + right.card ≤ 2 * k - 4 := by
  have hleftCard : left.card ≤ k - 1 := by
    by_contra hcard
    have hkSub : k ≤ left.card := by omega
    obtain ⟨cup, hcupSub, hcupCard⟩ := Finset.exists_subset_card_eq hkSub
    apply hnoCup
    exact ⟨cup, hcupSub.trans Finset.subset_union_left, hcupCard,
      FinsetPolygon.IsCupSet.mono hleft hcupSub⟩
  have hrightCard : right.card ≤ k - 1 := by
    by_contra hcard
    have hkSub : k ≤ right.card := by omega
    obtain ⟨cup, hcupSub, hcupCard⟩ := Finset.exists_subset_card_eq hkSub
    apply hnoCup
    exact ⟨cup, hcupSub.trans Finset.subset_union_right, hcupCard,
      FinsetPolygon.IsCupSet.mono hright hcupSub⟩
  by_contra hsum
  have hsizes :
      (k - 2 ≤ left.card ∧ k - 1 ≤ right.card) ∨
        (k - 1 ≤ left.card ∧ k - 2 ≤ right.card) := by
    omega
  rcases hsizes with hsizes | hsizes
  · obtain ⟨left', hleftSub, hleftCard'⟩ :=
      Finset.exists_subset_card_eq hsizes.1
    obtain ⟨right', hrightSub, hrightCard'⟩ :=
      Finset.exists_subset_card_eq hsizes.2
    have hout := hblocks (hdisjoint.mono hleftSub hrightSub)
      (fun x hx y hy ↦ horder x (hleftSub hx) y (hrightSub hy))
      (Or.inl ⟨hleftCard', hrightCard'⟩)
      (FinsetPolygon.IsCupSet.mono hleft hleftSub)
      (FinsetPolygon.IsCupSet.mono hright hrightSub)
      (hone.mono (Finset.union_subset_union hleftSub hrightSub))
    have hsub : left' ∪ right' ⊆ left ∪ right :=
      Finset.union_subset_union hleftSub hrightSub
    rcases hout with hcap | hcup | hstrong
    · exact hnoCap (FinsetPolygon.ContainsCapSet.mono hcap hsub)
    · exact hnoCup (FinsetPolygon.ContainsCupSet.mono hcup hsub)
    · exact hnoStrong (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong hsub)
  · obtain ⟨left', hleftSub, hleftCard'⟩ :=
      Finset.exists_subset_card_eq hsizes.1
    obtain ⟨right', hrightSub, hrightCard'⟩ :=
      Finset.exists_subset_card_eq hsizes.2
    have hout := hblocks (hdisjoint.mono hleftSub hrightSub)
      (fun x hx y hy ↦ horder x (hleftSub hx) y (hrightSub hy))
      (Or.inr ⟨hleftCard', hrightCard'⟩)
      (FinsetPolygon.IsCupSet.mono hleft hleftSub)
      (FinsetPolygon.IsCupSet.mono hright hrightSub)
      (hone.mono (Finset.union_subset_union hleftSub hrightSub))
    have hsub : left' ∪ right' ⊆ left ∪ right :=
      Finset.union_subset_union hleftSub hrightSub
    rcases hout with hcap | hcup | hstrong
    · exact hnoCap (FinsetPolygon.ContainsCapSet.mono hcap hsub)
    · exact hnoCup (FinsetPolygon.ContainsCupSet.mono hcup hsub)
    · exact hnoStrong (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong hsub)

/-- Once the diagonal Pascal reservoir has its expected linear cardinality,
the uniform cup-block contract supplies exactly the two-side bound required by
the generic Pascal-tail dispatcher. -/
theorem pascalTailTwoSideBound_four_diagonal_of_cupBlocks
    {k : ℕ} (hk : 5 ≤ k)
    (hblocks : DiagonalCupBlocksForce4kk k) :
    PascalTailTwoSideBound 4 k k := by
  intro n χ left right hdisjoint horder hleftCap hrightCap hone
    hnoCap hnoCup hnoStrong
  have hcard := diagonal_cup_block_card_add_le hk hblocks hdisjoint horder
    (by
      intro t hi hj hl
      cases hcolor : χ t with
      | left => rfl
      | right =>
          exfalso
          apply hleftCap
          exact ⟨{t.i, t.j, t.k}, by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl
            · exact hi
            · exact hj
            · exact hl,
            by simp [ne_of_lt t.hij, ne_of_lt t.hjk,
              ne_of_lt (t.hij.trans t.hjk)], isCapSet_three t hcolor⟩)
    (by
      intro t hi hj hl
      cases hcolor : χ t with
      | left => rfl
      | right =>
          exfalso
          apply hrightCap
          exact ⟨{t.i, t.j, t.k}, by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl
            · exact hi
            · exact hj
            · exact hl,
            by simp [ne_of_lt t.hij, ne_of_lt t.hjk,
              ne_of_lt (t.hij.trans t.hjk)], isCapSet_three t hcolor⟩)
    hone hnoCap hnoCup hnoStrong
  rw [lowerPascalTailReservoir_four_diagonal hk]
  omega

/-- The same contract closes the singleton lower-tail gate at every diagonal
parameter for which the elementary reservoir identity is available. -/
theorem singletonLowerPascalTailGate_four_diagonal_of_cupBlocks
    {k : ℕ} (hk : 5 ≤ k)
    (hblocks : DiagonalCupBlocksForce4kk k) :
    SingletonLowerPascalTailGate 4 k k :=
  singletonLowerPascalTailGate_of_twoSideBound (by omega)
    (pascalTailTwoSideBound_four_diagonal_of_cupBlocks hk hblocks)

/-- The four certified adjacent-block theorems are instances of the uniform
diagonal contract. -/
theorem diagonalCupBlocksForce4kk_five :
    DiagonalCupBlocksForce4kk 5 := by
  intro n χ left right hdisjoint horder hcards hleft hright hone
  exact cupBlocks34Force455 hdisjoint horder (by norm_num at hcards ⊢; exact hcards)
    hleft hright hone

theorem diagonalCupBlocksForce4kk_six :
    DiagonalCupBlocksForce4kk 6 := by
  intro n χ left right hdisjoint horder hcards hleft hright hone
  exact cupBlocks45Force466 hdisjoint horder (by norm_num at hcards ⊢; exact hcards)
    hleft hright hone

theorem diagonalCupBlocksForce4kk_seven :
    DiagonalCupBlocksForce4kk 7 := by
  intro n χ left right hdisjoint horder hcards hleft hright hone
  exact cupBlocks56Force477 hdisjoint horder (by norm_num at hcards ⊢; exact hcards)
    hleft hright hone

theorem diagonalCupBlocksForce4kk_eight :
    DiagonalCupBlocksForce4kk 8 := by
  intro n χ left right hdisjoint horder hcards hleft hright hone
  exact cupBlocks67Force488 hdisjoint horder (by norm_num at hcards ⊢; exact hcards)
    hleft hright hone

/-- The diagonal adjacent-block staircase is completely proved through
`k = 8`; `k = 9` is its first genuinely new instance. -/
theorem diagonalCupBlocksForce4kk_of_five_le_of_le_eight
    {k : ℕ} (hkLower : 5 ≤ k) (hkUpper : k ≤ 8) :
    DiagonalCupBlocksForce4kk k := by
  interval_cases k
  · exact diagonalCupBlocksForce4kk_five
  · exact diagonalCupBlocksForce4kk_six
  · exact diagonalCupBlocksForce4kk_seven
  · exact diagonalCupBlocksForce4kk_eight

/-- The previously omitted `(4,7,7)` positive control follows uniformly from
the certified `5+6` cup-block theorem. -/
theorem singletonLowerPascalTailGate_477 :
    SingletonLowerPascalTailGate 4 7 7 :=
  singletonLowerPascalTailGate_four_diagonal_of_cupBlocks (by omega)
    diagonalCupBlocksForce4kk_seven

/-- All diagonal singleton lower-tail gates from `k=5` through `k=8` are
instances of one compiled theorem. -/
theorem singletonLowerPascalTailGate_four_diagonal_of_five_le_of_le_eight
    {k : ℕ} (hkLower : 5 ≤ k) (hkUpper : k ≤ 8) :
    SingletonLowerPascalTailGate 4 k k :=
  singletonLowerPascalTailGate_four_diagonal_of_cupBlocks hkLower
    (diagonalCupBlocksForce4kk_of_five_le_of_le_eight hkLower hkUpper)

end ErdosSzekeres

end
