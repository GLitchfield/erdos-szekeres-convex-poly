import ESBlueprint.B.ExistsCupStartLayersOfOneChangeNoCapFour

namespace ErdosSzekeres

/-- A one-change set avoiding four-caps and cups of size v has at most choose v two points: its attained cup-start ranks are below v and every rank layer has at most its rank many points.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.singletonLowerPascalTailGate_five_pred_of_six_le -/
theorem card_le_choose_of_oneChange_no_capFour_no_cup {n v : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)} (hone : OneChangeOn χ s) (hnoCap : ¬ContainsCapSet χ s 4) (hnoCup : ¬ContainsCupSet χ s v) : s.card ≤ Nat.choose v 2 := by
  classical
  obtain ⟨β, hatt, _, hrow⟩ := exists_cupStartLayers_of_oneChange_no_capFour hone hnoCap
  have hsmall : ∀ C : Finset (Fin n), C ⊆ s → IsCupSet χ C → C.card < v := by
    intro C hCsub hCcup
    by_contra h
    obtain ⟨D, hDC, hDcard⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt h)
    exact hnoCup ⟨D, hDC.trans hCsub, hDcard, FinsetPolygon.IsCupSet.mono hCcup hDC⟩
  have hrange : ∀ x ∈ s, β x ∈ Finset.range v := by
    intro x hx
    obtain ⟨C, hCsub, _, hCcup, _, hCcard⟩ := hatt x hx
    apply Finset.mem_range.mpr
    rw [← hCcard]
    exact hsmall C hCsub hCcup
  have hsum : ∀ w : ℕ, (∑ j ∈ Finset.range w, j) = Nat.choose w 2 := by
    intro w
    induction w with
    | zero => simp
    | succ w ih =>
      rw [Finset.sum_range_succ, ih]
      have hp : Nat.choose (w + 1) 2 = w + Nat.choose w 2 := by
        simpa only [Nat.choose_one_right] using Nat.choose_succ_succ' w 1
      omega
  calc
    s.card = ∑ j ∈ Finset.range v, (s.filter (fun x ↦ β x = j)).card :=
      Finset.card_eq_sum_card_fiberwise hrange
    _ ≤ ∑ j ∈ Finset.range v, j := Finset.sum_le_sum (fun j _ ↦ (hrow j).2)
    _ = Nat.choose v 2 := hsum v

end ErdosSzekeres
