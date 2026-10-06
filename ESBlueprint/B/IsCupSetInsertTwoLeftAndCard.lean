import ErdosSzekeres.StructuralChargingCore

namespace ErdosSzekeres

/-- M2: two new points of an ordered left cup below two selected left vertices extend an ambient cup by exactly two points. Apply the same-side shielding move twice; OneChange is the only ambient color condition, and absence from the original cup gives exact growth.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.TurnSequenceAllowed.all_eq_of_outer_eq, ErdosSzekeres.OneChangeOn.mono
@dangling-ok Approved R20 standalone double-prefix cup-extension move with explicit growth, reusable for two-side strong-set extensions -/
theorem isCupSet_insert_two_left_and_card {n : ℕ} {χ : TripleColoring n} {left right C : Finset (Fin n)} {p q a b : Fin n} (horder : ∀ u ∈ left, ∀ v ∈ right, u < v) (hleft : IsCupSet χ left) (hcup : IsCupSet χ C) (hone : OneChangeOn χ (left ∪ right)) (hsub : C ⊆ left ∪ right) (hp : p ∈ left) (hq : q ∈ left) (ha : a ∈ C) (haL : a ∈ left) (hb : b ∈ C) (hbL : b ∈ left) (hpq : p < q) (hqa : q < a) (hab : a < b) (hnotp : p ∉ C) (hnotq : q ∉ C) : IsCupSet χ (insert p (insert q C)) ∧ (insert p (insert q C)).card = C.card + 2 := by
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
  have insertLeft {n : ℕ} {χ : TripleColoring n}
      {left right C : Finset (Fin n)} {p a b : Fin n}
      (horder : ∀ u ∈ left, ∀ v ∈ right, u < v)
      (hleft : IsCupSet χ left) (hcup : IsCupSet χ C)
      (hone : OneChangeOn χ (left ∪ right)) (hsub : C ⊆ left ∪ right)
      (hp : p ∈ left) (ha : a ∈ C) (haL : a ∈ left)
      (hb : b ∈ C) (hbL : b ∈ left) (hpa : p < a) (hab : a < b) :
      IsCupSet χ (insert p C) := by
    have hnew : insert p C ⊆ left ∪ right :=
      Finset.insert_subset_iff.mpr ⟨Finset.mem_union_left right hp, hsub⟩
    have leftOfLe (z : Fin n) (hz : z ∈ insert p C) (hzb : z ≤ b) : z ∈ left := by
      rcases Finset.mem_union.mp (hnew hz) with hzL | hzR
      · exact hzL
      · exact False.elim ((not_lt_of_ge hzb) (horder b hbL z hzR))
    apply chain (hone.mono hnew)
    intro t hi hj hk hgap1 hgap2
    have finish (hkb : t.k ≤ b) : χ t = Turn.left := by
      exact hleft t (leftOfLe t.i hi ((t.hij.trans t.hjk).le.trans hkb))
        (leftOfLe t.j hj (t.hjk.le.trans hkb)) (leftOfLe t.k hk hkb)
    by_cases hip : t.i = p
    · apply finish
      by_contra hkb
      have hbk : b < t.k := lt_of_not_ge hkb
      have hja : t.j ≤ a := by
        by_contra hja
        exact hgap1 a (by simp [ha]) (by simpa [hip] using hpa) (lt_of_not_ge hja)
      exact hgap2 b (by simp [hb]) (hja.trans_lt hab) hbk
    · have hiC : t.i ∈ C := by simpa [hip] using hi
      by_cases hjp : t.j = p
      · apply finish
        have hka : t.k ≤ a := by
          by_contra hka
          exact hgap2 a (by simp [ha]) (by simpa [hjp] using hpa) (lt_of_not_ge hka)
        exact hka.trans hab.le
      · have hjC : t.j ∈ C := by simpa [hjp] using hj
        by_cases hkp : t.k = p
        · exact finish (by simpa [hkp] using (hpa.trans hab).le)
        · exact hcup t hiC hjC (by simpa [hkp] using hk)
  have hqCup := insertLeft horder hleft hcup hone hsub hq ha haL hb hbL hqa hab
  have hqSub : insert q C ⊆ left ∪ right :=
    Finset.insert_subset_iff.mpr ⟨Finset.mem_union_left right hq, hsub⟩
  have hpCup := insertLeft horder hleft hqCup hone hqSub hp
    (Finset.mem_insert_of_mem ha) haL (Finset.mem_insert_of_mem hb) hbL
    (hpq.trans hqa) hab
  refine ⟨hpCup, ?_⟩
  have hpNot : p ∉ insert q C := by simp [hpq.ne, hnotp]
  rw [Finset.card_insert_of_notMem hpNot, Finset.card_insert_of_notMem hnotq]


end ErdosSzekeres
