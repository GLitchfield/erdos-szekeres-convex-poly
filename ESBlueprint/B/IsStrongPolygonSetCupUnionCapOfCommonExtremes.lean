import ErdosSzekeres.StructuralChargingCore

namespace ErdosSzekeres

/-- General H3 converse: a cup and a cap sharing both extreme endpoints have a strong union under OneChange. Interior colors anchored at the endpoints determine all mixed triples; arbitrary numbers of cap-interior vertices are allowed. This reconstructs strong sets from two hulls without a cap-size bound or a realization assumption.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn, ErdosSzekeres.TurnSequenceAllowed
@dangling-ok R20 reusable multi-apex shape converse with explicit anchored-color proof idea in PROGRESS.md; coupled a5 cut remains open -/
theorem isStrongPolygonSet_cup_union_cap_of_common_extremes {n : ℕ} {χ : TripleColoring n} {C D : Finset (Fin n)} {l r : Fin n} (hcup : IsCupSet χ C) (hcap : IsCapSet χ D) (hlC : l ∈ C) (hrC : r ∈ C) (hlD : l ∈ D) (hrD : r ∈ D) (hmin : ∀ x ∈ C ∪ D, l ≤ x) (hmax : ∀ x ∈ C ∪ D, x ≤ r) (hlr : l < r) (hone : OneChangeOn χ (C ∪ D)) : IsStrongPolygonSet χ (C ∪ D) := by
  classical
  have switch {a b c d : Turn} (h : TurnSequenceAllowed a b c d) (hne : b ≠ c) :
      a = b ∧ c = d := by
    rcases h with h | h | h | h | h | h | h | h <;>
      rcases h with ⟨rfl, rfl, rfl, rfl⟩ <;> simp at hne ⊢
  have hl : l ∈ C ∪ D := Finset.mem_union_left D hlC
  have hr : r ∈ C ∪ D := Finset.mem_union_left D hrC
  -- The two anchored mixed turns agree with their middle-point labels.
  have pair (a b : Fin n) (hla : l < a) (hab : a < b) (hbr : b < r)
      (ha : a ∈ C ∪ D) (hb : b ∈ C ∪ D) :
      χ ⟨l, a, b, hla, hab⟩ = χ ⟨l, a, r, hla, hab.trans hbr⟩ ∧
        χ ⟨a, b, r, hab, hbr⟩ = χ ⟨l, b, r, hla.trans hab, hbr⟩ := by
    rcases Finset.mem_union.mp ha with haC | haD <;>
      rcases Finset.mem_union.mp hb with hbC | hbD
    · exact ⟨(hcup _ hlC haC hbC).trans (hcup _ hlC haC hrC).symm,
        (hcup _ haC hbC hrC).trans (hcup _ hlC hbC hrC).symm⟩
    · have hfirst := hcup ⟨l, a, r, hla, hab.trans hbr⟩ hlC haC hrC
      have hlast := hcap ⟨l, b, r, hla.trans hab, hbr⟩ hlD hbD hrD
      have hne : χ ⟨l, a, r, hla, hab.trans hbr⟩ ≠
          χ ⟨l, b, r, hla.trans hab, hbr⟩ := by
        rw [hfirst, hlast]
        decide
      have hpin := switch (hone hla hab hbr hl ha hb hr) hne
      exact ⟨hpin.1, hpin.2.symm⟩
    · have hfirst := hcap ⟨l, a, r, hla, hab.trans hbr⟩ hlD haD hrD
      have hlast := hcup ⟨l, b, r, hla.trans hab, hbr⟩ hlC hbC hrC
      have hne : χ ⟨l, a, r, hla, hab.trans hbr⟩ ≠
          χ ⟨l, b, r, hla.trans hab, hbr⟩ := by
        rw [hfirst, hlast]
        decide
      have hpin := switch (hone hla hab hbr hl ha hb hr) hne
      exact ⟨hpin.1, hpin.2.symm⟩
    · exact ⟨(hcap _ hlD haD hbD).trans (hcap _ hlD haD hrD).symm,
        (hcap _ haD hbD hrD).trans (hcap _ hlD hbD hrD).symm⟩
  have cupOfAnchor (x : Fin n) (hx : x ∈ C ∪ D) (hlx : l < x) (hxr : x < r)
      (hcolor : χ ⟨l, x, r, hlx, hxr⟩ = Turn.left) : x ∈ C := by
    rcases Finset.mem_union.mp hx with hxC | hxD
    · exact hxC
    · have hright := hcap ⟨l, x, r, hlx, hxr⟩ hlD hxD hrD
      have hbad : Turn.right = Turn.left := hright.symm.trans hcolor
      cases hbad
  have capOfAnchor (x : Fin n) (hx : x ∈ C ∪ D) (hlx : l < x) (hxr : x < r)
      (hcolor : χ ⟨l, x, r, hlx, hxr⟩ = Turn.right) : x ∈ D := by
    rcases Finset.mem_union.mp hx with hxC | hxD
    · have hleft := hcup ⟨l, x, r, hlx, hxr⟩ hlC hxC hrC
      have hbad : Turn.left = Turn.right := hleft.symm.trans hcolor
      cases hbad
    · exact hxD
  have middleColor (i j k : Fin n) (hij : i < j) (hjk : j < k)
      (hi : i ∈ C ∪ D) (hj : j ∈ C ∪ D) (hk : k ∈ C ∪ D) :
      χ ⟨i, j, k, hij, hjk⟩ =
        χ ⟨l, j, r, (hmin i hi).trans_lt hij, hjk.trans_le (hmax k hk)⟩ := by
    have hlj : l < j := (hmin i hi).trans_lt hij
    have hjr : j < r := hjk.trans_le (hmax k hk)
    rcases eq_or_lt_of_le (hmin i hi) with hieq | hli
    · subst i
      rcases eq_or_lt_of_le (hmax k hk) with hkeq | hkr
      · subst k
        rfl
      · exact (pair j k hij hjk hkr hj hk).1
    · rcases eq_or_lt_of_le (hmax k hk) with hkeq | hkr
      · subst k
        exact (pair i j hli hij hjk hi hj).2
      · have hlk : l < k := hlj.trans hjk
        have hir : i < r := hij.trans hjr
        have hijPair := pair i j hli hij hjr hi hj
        have hikPair := pair i k hli (hij.trans hjk) hkr hi hk
        have hjkPair := pair j k hlj hjk hkr hj hk
        by_cases hsame1 : χ ⟨l, i, r, hli, hir⟩ = χ ⟨l, j, r, hlj, hjr⟩
        · by_cases hsame2 : χ ⟨l, j, r, hlj, hjr⟩ = χ ⟨l, k, r, hlk, hkr⟩
          · rcases Finset.mem_union.mp hj with hjC | hjD
            · have hjLeft := hcup ⟨l, j, r, hlj, hjr⟩ hlC hjC hrC
              have hiC := cupOfAnchor i hi hli hir (hsame1.trans hjLeft)
              have hkC := cupOfAnchor k hk hlk hkr (hsame2.symm.trans hjLeft)
              exact (hcup ⟨i, j, k, hij, hjk⟩ hiC hjC hkC).trans hjLeft.symm
            · have hjRight := hcap ⟨l, j, r, hlj, hjr⟩ hlD hjD hrD
              have hiD := capOfAnchor i hi hli hir (hsame1.trans hjRight)
              have hkD := capOfAnchor k hk hlk hkr (hsame2.symm.trans hjRight)
              exact (hcap ⟨i, j, k, hij, hjk⟩ hiD hjD hkD).trans hjRight.symm
          · have hne : χ ⟨i, j, r, hij, hjr⟩ ≠
                χ ⟨i, k, r, hij.trans hjk, hkr⟩ := by
              rw [hijPair.2, hikPair.2]
              exact hsame2
            exact (switch (hone hij hjk hkr hi hj hk hr) hne).1.trans hijPair.2
        · have hne : χ ⟨l, i, k, hli, hij.trans hjk⟩ ≠
              χ ⟨l, j, k, hlj, hjk⟩ := by
            rw [hikPair.1, hjkPair.1]
            exact hsame1
          exact (switch (hone hli hij hjk hl hi hj hk) hne).2.symm.trans hjkPair.1
  apply FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mpr
  intro i i' j k k' hij hi'j hjk hjk' hi hi' hj hk hk'
  exact (middleColor i j k hij hjk hi hj hk).trans
    (middleColor i' j k' hi'j hjk' hi' hj hk').symm


end ErdosSzekeres
