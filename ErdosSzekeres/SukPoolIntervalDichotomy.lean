module

public import ErdosSzekeres.Basic

@[expose] public section

/-!
# A path dichotomy for Suk support pools

This file isolates the finite path argument used after applying Dilworth's theorem in each
support pool.  It contains no geometric assumptions: a predicate marks the antichain-rich pools,
and its complement marks the chain-rich pools.
-/

namespace ErdosSzekeres

/-- Distinct selected path vertices are separated by at least one unselected vertex. -/
def PairwiseNonadjacent {L : ℕ} (selected : Finset (Fin L)) : Prop :=
  ∀ ⦃i⦄, i ∈ selected → ∀ ⦃j⦄, j ∈ selected → i ≠ j →
    i.val + 1 < j.val ∨ j.val + 1 < i.val

/-- There is an interval of `m` consecutive path vertices on which `anti` is false. -/
def ConsecutiveNotAntiRun {L : ℕ} (anti : Fin L → Prop) (m : ℕ) : Prop :=
  ∃ (start : ℕ) (hstart : start + m ≤ L),
    ∀ r : Fin m, ¬ anti ⟨start + r.val, by omega⟩

private theorem spacedBlock_end_le
    {L t m : ℕ} (hsharp : t * (m + 1) - 1 ≤ L) (k : Fin t) :
    k.val * (m + 1) + m ≤ L := by
  have hkmul : (k.val + 1) * (m + 1) ≤ t * (m + 1) :=
    Nat.mul_le_mul_right (m + 1) (by omega)
  have hrewrite : k.val * (m + 1) + m + 1 = (k.val + 1) * (m + 1) := by
    ring
  have hlt : k.val * (m + 1) + m < t * (m + 1) := by
    omega
  exact (Nat.le_sub_one_of_lt hlt).trans hsharp

private def spacedBlockPoint
    {L t m : ℕ} (hsharp : t * (m + 1) - 1 ≤ L) (k : Fin t) (r : Fin m) :
    Fin L :=
  ⟨k.val * (m + 1) + r.val, by
    have hend := spacedBlock_end_le hsharp k
    omega⟩

private theorem spacedBlockPoint_separated
    {L t m : ℕ} (hsharp : t * (m + 1) - 1 ≤ L)
    {a b : Fin t} (hab : a < b) (ra rb : Fin m) :
    (spacedBlockPoint hsharp a ra).val + 1 <
      (spacedBlockPoint hsharp b rb).val := by
  have hawitness : a.val * (m + 1) + ra.val + 1 ≤ a.val * (m + 1) + m := by
    omega
  have habmul : (a.val + 1) * (m + 1) ≤ b.val * (m + 1) :=
    Nat.mul_le_mul_right (m + 1) (by omega)
  have hrewrite : a.val * (m + 1) + m + 1 = (a.val + 1) * (m + 1) := by
    ring
  have hgap : a.val * (m + 1) + m < b.val * (m + 1) := by
    omega
  change a.val * (m + 1) + ra.val + 1 < b.val * (m + 1) + rb.val
  omega

private theorem exists_pairwise_nonadjacent_of_sharp_length
    (L t m : ℕ)
    (hsharp : t * (m + 1) - 1 ≤ L)
    (anti : Fin L → Prop) [DecidablePred anti]
    (hnoRun : ¬ConsecutiveNotAntiRun anti m) :
    ∃ selected : Finset (Fin L),
      selected.card = t ∧
        (∀ i ∈ selected, anti i) ∧
        PairwiseNonadjacent selected := by
  classical
  have hhit : ∀ k : Fin t, ∃ r : Fin m, anti (spacedBlockPoint hsharp k r) := by
    intro k
    by_contra hnone
    apply hnoRun
    refine ⟨k.val * (m + 1), spacedBlock_end_le hsharp k, ?_⟩
    intro r hanti
    apply hnone
    exact ⟨r, by simpa [spacedBlockPoint] using hanti⟩
  choose r hr using hhit
  let f : Fin t → Fin L := fun k ↦ spacedBlockPoint hsharp k (r k)
  have hfSeparated : ∀ ⦃a b : Fin t⦄, a < b → (f a).val + 1 < (f b).val := by
    intro a b hab
    exact spacedBlockPoint_separated hsharp hab (r a) (r b)
  have hfStrict : StrictMono f := by
    intro a b hab
    change (f a).val < (f b).val
    have := hfSeparated hab
    omega
  let selected := Finset.univ.image f
  refine ⟨selected, ?_, ?_, ?_⟩
  · simp [selected, Finset.card_image_of_injective _ hfStrict.injective]
  · intro i hi
    simp only [selected, Finset.mem_image, Finset.mem_univ, true_and] at hi
    obtain ⟨k, rfl⟩ := hi
    simpa [f] using hr k
  · intro i hi j hj hij
    simp only [selected, Finset.mem_image, Finset.mem_univ, true_and] at hi hj
    obtain ⟨a, rfl⟩ := hi
    obtain ⟨b, rfl⟩ := hj
    have hab : a ≠ b := fun hab ↦ hij (congrArg f hab)
    rcases lt_or_gt_of_ne hab with hab | hba
    · exact Or.inl (hfSeparated hab)
    · exact Or.inr (hfSeparated hba)

/-- If both alternatives fail, the Boolean path is shorter than the exact spaced-block
threshold.  The independent finite controls exhibit matching words of length one less. -/
theorem sukPoolInterval_extremal_length_lt
    (L t m : ℕ)
    (anti : Fin L → Prop) [DecidablePred anti]
    (hnoSelected : ¬∃ selected : Finset (Fin L),
      selected.card = t ∧
        (∀ i ∈ selected, anti i) ∧
        PairwiseNonadjacent selected)
    (hnoRun : ¬ConsecutiveNotAntiRun anti m) :
    L < t * (m + 1) - 1 := by
  by_contra hnot
  exact hnoSelected <|
    exists_pairwise_nonadjacent_of_sharp_length L t m (Nat.le_of_not_gt hnot) anti hnoRun

private theorem sharp_threshold_le_source_threshold
    (t m : ℕ) (ht : 1 ≤ t) (hm : 1 ≤ m) :
    t * (m + 1) - 1 ≤ (2 * t - 1) * m := by
  have hmul : t - 1 ≤ (t - 1) * m := by
    simpa using Nat.mul_le_mul_left (t - 1) hm
  calc
    t * (m + 1) - 1 = t * m + (t - 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    _ ≤ t * m + (t - 1) * m := Nat.add_le_add_left hmul _
    _ = (2 * t - 1) * m := by
      have : 2 * t - 1 = t + (t - 1) := by omega
      rw [this, Nat.add_mul]

/-- A long Boolean path contains either `t` antichain-rich pools separated by an unused pool,
or an interval of `m` consecutive chain-rich pools. -/
theorem exists_pairwise_nonadjacent_or_consecutive_run
    (L t m : ℕ) (ht : 1 ≤ t) (hm : 1 ≤ m)
    (hL : (2 * t - 1) * m ≤ L)
    (anti : Fin L → Prop) [DecidablePred anti] :
    (∃ selected : Finset (Fin L),
      selected.card = t ∧
        (∀ i ∈ selected, anti i) ∧
        PairwiseNonadjacent selected) ∨
      ConsecutiveNotAntiRun anti m := by
  by_cases hrun : ConsecutiveNotAntiRun anti m
  · exact Or.inr hrun
  · apply Or.inl
    apply exists_pairwise_nonadjacent_of_sharp_length L t m
    · exact (sharp_threshold_le_source_threshold t m ht hm).trans hL
    · exact hrun

end ErdosSzekeres

end
