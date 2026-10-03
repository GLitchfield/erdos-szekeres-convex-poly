import ErdosSzekeres.StructuralChargingCore

namespace ErdosSzekeres

/-- In a one-change colouring, a cup and cap with the same distinct extrema form a strong polygon set, and their intersection consists exactly of those extrema. Boundary one-change forces every triple colour from the membership of its middle point.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.singletonLowerPascalTailGate_five_pred_of_six_le -/
theorem isStrongPolygonSet_union_of_cup_cap_common_extremes {n : ℕ} {χ : TripleColoring n} {C D : Finset (Fin n)} {l r : Fin n} (hlr : l < r) (hlC : l ∈ C) (hrC : r ∈ C) (hlD : l ∈ D) (hrD : r ∈ D) (hspan : ∀ x ∈ C ∪ D, l ≤ x ∧ x ≤ r) (hcup : IsCupSet χ C) (hcap : IsCapSet χ D) (hone : OneChangeOn χ (C ∪ D)) : IsStrongPolygonSet χ (C ∪ D) ∧ C ∩ D = {l, r} := by
  classical
  have hinter : C ∩ D = {l, r} := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxC, hxD⟩ := Finset.mem_inter.mp hx
      by_cases hxl : x = l
      · simp [hxl]
      by_cases hxr : x = r
      · simp [hxr]
      have hs := hspan x (Finset.mem_union_left _ hxC)
      have hlx : l < x := by omega
      have hxr' : x < r := by omega
      have hleft := hcup ⟨l, x, r, hlx, hxr'⟩ hlC hxC hrC
      have hright := hcap ⟨l, x, r, hlx, hxr'⟩ hlD hxD hrD
      have hfalse : Turn.left = Turn.right := hleft.symm.trans hright
      cases hfalse
    · intro hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hlC, hlD⟩
      · exact Finset.mem_inter.mpr ⟨hrC, hrD⟩
  let colour (x : Fin n) := if x ∈ C then Turn.left else Turn.right
  have hlS : l ∈ C ∪ D := Finset.mem_union_left _ hlC
  have hrS : r ∈ C ∪ D := Finset.mem_union_left _ hrC
  have hanchor {x : Fin n} (hx : x ∈ C ∪ D) (hlx : l < x) (hxr : x < r) :
      χ ⟨l, x, r, hlx, hxr⟩ = colour x := by
    by_cases hxC : x ∈ C
    · simpa only [colour, if_pos hxC] using hcup ⟨l, x, r, hlx, hxr⟩ hlC hxC hrC
    · have hxD : x ∈ D := (Finset.mem_union.mp hx).resolve_left hxC
      simpa only [colour, if_neg hxC] using hcap ⟨l, x, r, hlx, hxr⟩ hlD hxD hrD
  have hswitch {a b c d : Turn} (h : TurnSequenceAllowed a b c d) (hbc : b ≠ c) :
      a = b ∧ c = d := by
    cases a <;> cases b <;> cases c <;> cases d <;> simp_all [TurnSequenceAllowed]
  have hboundary {x y : Fin n} (hx : x ∈ C ∪ D) (hy : y ∈ C ∪ D)
      (hlx : l < x) (hxy : x < y) (hyr : y < r) :
      χ ⟨l, x, y, hlx, hxy⟩ = colour x ∧
        χ ⟨x, y, r, hxy, hyr⟩ = colour y := by
    by_cases hsame : colour x = colour y
    · by_cases hxC : x ∈ C
      · have hyC : y ∈ C := by
          by_contra hyC
          simp only [colour, if_pos hxC, if_neg hyC] at hsame
          cases hsame
        constructor
        · simpa only [colour, if_pos hxC] using (hcup ⟨l, x, y, hlx, hxy⟩ hlC hxC hyC)
        · simpa only [colour, if_pos hyC] using (hcup ⟨x, y, r, hxy, hyr⟩ hxC hyC hrC)
      · have hyC : y ∉ C := by
          intro hyC
          simp only [colour, if_neg hxC, if_pos hyC] at hsame
          cases hsame
        have hxD := (Finset.mem_union.mp hx).resolve_left hxC
        have hyD := (Finset.mem_union.mp hy).resolve_left hyC
        constructor
        · simpa only [colour, if_neg hxC] using (hcap ⟨l, x, y, hlx, hxy⟩ hlD hxD hyD)
        · simpa only [colour, if_neg hyC] using (hcap ⟨x, y, r, hxy, hyr⟩ hxD hyD hrD)
    · have hb := hanchor hx hlx (hxy.trans hyr)
      have hc := hanchor hy (hlx.trans hxy) hyr
      have hbc : χ ⟨l, x, r, hlx, hxy.trans hyr⟩ ≠
          χ ⟨l, y, r, hlx.trans hxy, hyr⟩ := by
        rw [hb, hc]
        exact hsame
      have hs := hswitch (hone hlx hxy hyr hlS hx hy hrS) hbc
      exact ⟨hs.1.trans hb, hs.2.symm.trans hc⟩
  have htriple : ∀ t : OrderedTriple n,
      t.i ∈ C ∪ D → t.j ∈ C ∪ D → t.k ∈ C ∪ D → χ t = colour t.j := by
    intro t hi hj hk
    have hspanI := hspan t.i hi
    have hspanK := hspan t.k hk
    have hlj : l < t.j := hspanI.1.trans_lt t.hij
    have hjr : t.j < r := t.hjk.trans_le hspanK.2
    by_cases hiL : t.i = l
    · by_cases hkR : t.k = r
      · change χ ⟨t.i, t.j, t.k, t.hij, t.hjk⟩ = colour t.j
        simpa only [hiL, hkR] using hanchor hj hlj hjr
      · have hkr : t.k < r := by omega
        change χ ⟨t.i, t.j, t.k, t.hij, t.hjk⟩ = colour t.j
        simpa only [hiL] using (hboundary hj hk hlj t.hjk hkr).1
    have hli : l < t.i := by omega
    by_cases hkR : t.k = r
    · change χ ⟨t.i, t.j, t.k, t.hij, t.hjk⟩ = colour t.j
      simpa only [hkR] using (hboundary hi hj hli t.hij hjr).2
    have hkr : t.k < r := by omega
    by_cases hsameIJ : colour t.i = colour t.j
    · by_cases hsameJK : colour t.j = colour t.k
      · by_cases hiC : t.i ∈ C
        · have hjC : t.j ∈ C := by
            by_contra hjC
            simp only [colour, if_pos hiC, if_neg hjC] at hsameIJ
            cases hsameIJ
          have hkC : t.k ∈ C := by
            by_contra hkC
            simp only [colour, if_pos hjC, if_neg hkC] at hsameJK
            cases hsameJK
          simpa only [colour, if_pos hjC] using hcup t hiC hjC hkC
        · have hjC : t.j ∉ C := by
            intro hjC
            simp only [colour, if_neg hiC, if_pos hjC] at hsameIJ
            cases hsameIJ
          have hkC : t.k ∉ C := by
            intro hkC
            simp only [colour, if_neg hjC, if_pos hkC] at hsameJK
            cases hsameJK
          simpa only [colour, if_neg hjC] using hcap t
            ((Finset.mem_union.mp hi).resolve_left hiC)
            ((Finset.mem_union.mp hj).resolve_left hjC)
            ((Finset.mem_union.mp hk).resolve_left hkC)
      · have hb := (hboundary hi hj hli t.hij hjr).2
        have hd := (hboundary hj hk hlj t.hjk hkr).2
        have hbd : χ ⟨t.i, t.j, r, t.hij, hjr⟩ ≠
            χ ⟨t.j, t.k, r, t.hjk, hkr⟩ := by
          rw [hb, hd]
          exact hsameJK
        have heq := TurnSequenceAllowed.first_eq_second_of_second_ne_fourth
          (hone t.hij t.hjk hkr hi hj hk hrS) hbd
        exact heq.trans hb
    · have ha := (hboundary hi hj hli t.hij hjr).1
      have hc := (hboundary hj hk hlj t.hjk hkr).1
      have hac : χ ⟨l, t.i, t.j, hli, t.hij⟩ ≠
          χ ⟨l, t.j, t.k, hlj, t.hjk⟩ := by
        rw [ha, hc]
        exact hsameIJ
      have heq := TurnSequenceAllowed.third_eq_fourth_of_first_ne_third
        (hone hli t.hij t.hjk hlS hi hj hk) hac
      exact heq.symm.trans hc
  refine ⟨?_, hinter⟩
  intro i j k x hij hjk hkx hi hj hk hx
  exact ⟨(htriple ⟨i, j, k, hij, hjk⟩ hi hj hk).trans
      (htriple ⟨i, j, x, hij, hjk.trans hkx⟩ hi hj hx).symm,
    (htriple ⟨i, k, x, hij.trans hjk, hkx⟩ hi hk hx).trans
      (htriple ⟨j, k, x, hjk, hkx⟩ hj hk hx).symm⟩

end ErdosSzekeres
