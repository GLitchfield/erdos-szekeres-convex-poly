module

public import Mathlib.Order.Preorder.Finite
public import Mathlib.Order.Antichain
public import Mathlib.Data.Finset.Card

@[expose] public section

/-!
# A finite height--width inequality

This file supplies the exact finite form of the chain--antichain estimate used
in Suk's quantitative Erdős--Szekeres argument.  It is deliberately stated for
an arbitrary finite subset of a partial order, independently of the later
geometric construction of that order.
-/

namespace ErdosSzekeres

noncomputable section

/-- The maximal elements of a finite subset of a partial order. -/
def finiteMaximals {α : Type*} [PartialOrder α] (s : Finset α) : Finset α :=
  by
    classical
    exact s.filter fun x => Maximal (· ∈ s) x

@[simp] theorem mem_finiteMaximals {α : Type*} [PartialOrder α]
    {s : Finset α} {x : α} :
    x ∈ finiteMaximals s ↔ Maximal (· ∈ s) x := by
  classical
  simp only [finiteMaximals, Finset.mem_filter]
  constructor
  · exact fun hx => hx.2
  · exact fun hx => ⟨hx.1, hx⟩

theorem finiteMaximals_subset {α : Type*} [PartialOrder α]
    (s : Finset α) : finiteMaximals s ⊆ s := by
  classical
  intro x hx
  exact (mem_finiteMaximals.mp hx).1

/-- Distinct maximal elements of a finite partial order are incomparable. -/
theorem finiteMaximals_isAntichain {α : Type*} [PartialOrder α]
    (s : Finset α) :
    IsAntichain (· ≤ ·) (finiteMaximals s : Set α) := by
  classical
  intro x hx y hy hxy hle
  have hxMax := mem_finiteMaximals.mp hx
  have hyMem := (mem_finiteMaximals.mp hy).1
  exact hxy (le_antisymm hle (hxMax.2 hyMem hle))

/-- A finite nonempty chain has a member above all its other members. -/
theorem finiteChain_exists_top {α : Type*} [PartialOrder α]
    {s : Finset α} (hs : s.Nonempty)
    (hchain : IsChain (· ≤ ·) (s : Set α)) :
    ∃ x ∈ s, ∀ y ∈ s, y ≤ x := by
  classical
  obtain ⟨x, hxMax⟩ := (s : Set α).toFinite.exists_maximal hs
  refine ⟨x, hxMax.1, ?_⟩
  intro y hy
  by_cases hyx : y = x
  · simp [hyx]
  rcases hchain hy hxMax.1 hyx with hyxLe | hxyLe
  · exact hyxLe
  · exact hxMax.2 hy hxyLe

/-- Finite Dilworth/Mirsky height--width estimate in the threshold form used
by Suk: more than `height * width` elements force a chain larger than
`height` or an antichain larger than `width`. -/
theorem finiteDilworth_chain_or_antichain
    {α : Type*} [PartialOrder α] (s : Finset α)
    (height width : ℕ) (hcard : height * width < s.card) :
    ∃ t : Finset α, t ⊆ s ∧
      ((height < t.card ∧ IsChain (· ≤ ·) (t : Set α)) ∨
        (width < t.card ∧ IsAntichain (· ≤ ·) (t : Set α))) := by
  classical
  induction height generalizing s with
  | zero =>
      have hs : s.Nonempty := Finset.card_pos.mp (by simpa using hcard)
      obtain ⟨x, hx⟩ := hs
      refine ⟨{x}, by simp [hx], Or.inl ⟨by simp, ?_⟩⟩
      simp
  | succ height ih =>
      let maxima := finiteMaximals s
      have hmaximaSub : maxima ⊆ s := finiteMaximals_subset s
      have hmaximaAnti : IsAntichain (· ≤ ·) (maxima : Set α) :=
        finiteMaximals_isAntichain s
      by_cases hwide : width < maxima.card
      · exact ⟨maxima, hmaximaSub, Or.inr ⟨hwide, hmaximaAnti⟩⟩
      have hmaximaCard : maxima.card ≤ width := Nat.le_of_not_gt hwide
      let rest := s \ maxima
      have hrestCard : height * width < rest.card := by
        rw [show rest.card = s.card - maxima.card by
          exact Finset.card_sdiff_of_subset hmaximaSub]
        simp only [Nat.succ_mul] at hcard
        omega
      obtain ⟨t, htRest, htChain | htAnti⟩ := ih rest hrestCard
      · have htNonempty : t.Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨x, hx, htop⟩ := finiteChain_exists_top htNonempty htChain.2
        have hxS : x ∈ s := Finset.sdiff_subset (htRest hx)
        obtain ⟨y, hxy, hyMax⟩ := s.exists_le_maximal hxS
        have hyMaxima : y ∈ maxima := mem_finiteMaximals.mpr hyMax
        have hyNotT : y ∉ t := by
          intro hyt
          exact (Finset.mem_sdiff.mp (htRest hyt)).2 hyMaxima
        refine ⟨insert y t, ?_, Or.inl ⟨?_, ?_⟩⟩
        · intro z hz
          rcases Finset.mem_insert.mp hz with rfl | hzt
          · exact hyMax.1
          · exact Finset.sdiff_subset (htRest hzt)
        · rw [Finset.card_insert_of_notMem hyNotT]
          omega
        · rw [Finset.coe_insert]
          apply htChain.2.insert
          intro z hz hyz
          exact Or.inr ((htop z hz).trans hxy)
      · exact ⟨t, htRest.trans Finset.sdiff_subset, Or.inr htAnti⟩

end

end ErdosSzekeres

end
