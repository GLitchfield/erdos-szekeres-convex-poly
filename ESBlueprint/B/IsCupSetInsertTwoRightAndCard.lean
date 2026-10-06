import ErdosSzekeres.StructuralChargingCore

namespace ErdosSzekeres

/-- M2 mirror: two new points of an ordered right cup above two selected right vertices extend an ambient cup by exactly two points. Apply the same-side shielding move twice; OneChange is the only ambient color condition, and absence from the original cup gives exact growth.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.TurnSequenceAllowed.all_eq_of_outer_eq, ErdosSzekeres.OneChangeOn.mono
@dangling-ok Approved R20 standalone double-suffix cup-extension move with explicit growth, reusable for two-side strong-set extensions -/
theorem isCupSet_insert_two_right_and_card {n : ℕ} {χ : TripleColoring n} {left right C : Finset (Fin n)} {p q a b : Fin n} (horder : ∀ u ∈ left, ∀ v ∈ right, u < v) (hright : IsCupSet χ right) (hcup : IsCupSet χ C) (hone : OneChangeOn χ (left ∪ right)) (hsub : C ⊆ left ∪ right) (hp : p ∈ right) (hq : q ∈ right) (ha : a ∈ C) (haR : a ∈ right) (hb : b ∈ C) (hbR : b ∈ right) (hab : a < b) (hbp : b < p) (hpq : p < q) (hnotp : p ∉ C) (hnotq : q ∉ C) : IsCupSet χ (insert q (insert p C)) ∧ (insert q (insert p C)).card = C.card + 2 := by
  classical
  have chain {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)} {c : Turn}
      (hone : OneChangeOn χ s)
      (hlocal : ∀ t : OrderedTriple n, t.i ∈ s → t.j ∈ s → t.k ∈ s →
        (∀ x ∈ s, t.i < x → x < t.j → False) →
        (∀ x ∈ s, t.j < x → x < t.k → False) → χ t = c) :
      ∀ t : OrderedTriple n, t.i ∈ s → t.j ∈ s → t.k ∈ s → χ t = c := by
    have aux : ∀ span : ℕ, ∀ (i j l : Fin n), l.val - i.val = span →
        (hij : i < j) → (hjl : j < l) → i ∈ s → j ∈ s → l ∈ s →
        χ ⟨i, j, l, hij, hjl⟩ = c := by
      intro span
      induction span using Nat.strong_induction_on with
      | h span ih =>
          intro i j l hspan hij hjl hi hj hl
          by_cases hgap : ∃ x ∈ s, i < x ∧ x < j
          · obtain ⟨x, hx, hix, hxj⟩ := hgap
            have hfirst := ih (j.val - i.val) (by omega) i x j rfl hix hxj hi hx hj
            have hlast := ih (l.val - x.val) (by omega) x j l rfl hxj hjl hx hj hl
            have hall := (hone hix hxj hjl hi hx hj hl).all_eq_of_outer_eq
              (hfirst.trans hlast.symm)
            exact hall.2.2.trans hlast
          · by_cases hgap' : ∃ x ∈ s, j < x ∧ x < l
            · obtain ⟨x, hx, hjx, hxl⟩ := hgap'
              have hfirst := ih (x.val - i.val) (by omega) i j x rfl hij hjx hi hj hx
              have hlast := ih (l.val - j.val) (by omega) j x l rfl hjx hxl hj hx hl
              have hall := (hone hij hjx hxl hi hj hx hl).all_eq_of_outer_eq
                (hfirst.trans hlast.symm)
              exact hall.1.symm.trans hfirst
            · exact hlocal _ hi hj hl
                (fun x hx hix hxj ↦ hgap ⟨x, hx, hix, hxj⟩)
                (fun x hx hjx hxl ↦ hgap' ⟨x, hx, hjx, hxl⟩)
    intro t hi hj hl
    exact aux (t.k.val - t.i.val) t.i t.j t.k rfl t.hij t.hjk hi hj hl
  have insertRight {n : ℕ} {χ : TripleColoring n}
      {left right C : Finset (Fin n)} {p a b : Fin n}
      (horder : ∀ u ∈ left, ∀ v ∈ right, u < v)
      (hright : IsCupSet χ right) (hcup : IsCupSet χ C)
      (hone : OneChangeOn χ (left ∪ right)) (hsub : C ⊆ left ∪ right)
      (hp : p ∈ right) (ha : a ∈ C) (haR : a ∈ right)
      (hb : b ∈ C) (hbR : b ∈ right) (hab : a < b) (hbp : b < p) :
      IsCupSet χ (insert p C) := by
    have hnew : insert p C ⊆ left ∪ right :=
      Finset.insert_subset_iff.mpr ⟨Finset.mem_union_right left hp, hsub⟩
    have rightOfGe (z : Fin n) (hz : z ∈ insert p C) (haz : a ≤ z) : z ∈ right := by
      rcases Finset.mem_union.mp (hnew hz) with hzL | hzR
      · exact False.elim ((not_lt_of_ge haz) (horder z hzL a haR))
      · exact hzR
    apply chain (hone.mono hnew)
    intro t hi hj hk hgap1 hgap2
    have finish (hai : a ≤ t.i) : χ t = Turn.left := by
      exact hright t (rightOfGe t.i hi hai) (rightOfGe t.j hj (hai.trans t.hij.le))
        (rightOfGe t.k hk (hai.trans (t.hij.trans t.hjk).le))
    by_cases hkp : t.k = p
    · apply finish
      by_contra hai
      have hia : t.i < a := lt_of_not_ge hai
      have hbj : b ≤ t.j := by
        by_contra hbj
        exact hgap2 b (by simp [hb]) (lt_of_not_ge hbj) (by simpa [hkp] using hbp)
      exact hgap1 a (by simp [ha]) hia (hab.trans_le hbj)
    · have hkC : t.k ∈ C := by simpa [hkp] using hk
      by_cases hjp : t.j = p
      · apply finish
        have hbi : b ≤ t.i := by
          by_contra hbi
          exact hgap1 b (by simp [hb]) (lt_of_not_ge hbi) (by simpa [hjp] using hbp)
        exact hab.le.trans hbi
      · have hjC : t.j ∈ C := by simpa [hjp] using hj
        by_cases hip : t.i = p
        · exact finish (by simpa [hip] using (hab.trans hbp).le)
        · exact hcup t (by simpa [hip] using hi) hjC hkC
  have hpCup := insertRight horder hright hcup hone hsub hp ha haR hb hbR hab hbp
  have hpSub : insert p C ⊆ left ∪ right :=
    Finset.insert_subset_iff.mpr ⟨Finset.mem_union_right left hp, hsub⟩
  have hqCup := insertRight horder hright hpCup hone hpSub hq
    (Finset.mem_insert_of_mem ha) haR (Finset.mem_insert_of_mem hb) hbR
    hab (hbp.trans hpq)
  refine ⟨hqCup, ?_⟩
  have hqNot : q ∉ insert p C := by simp [hpq.ne', hnotq]
  rw [Finset.card_insert_of_notMem hqNot, Finset.card_insert_of_notMem hnotp]


end ErdosSzekeres
