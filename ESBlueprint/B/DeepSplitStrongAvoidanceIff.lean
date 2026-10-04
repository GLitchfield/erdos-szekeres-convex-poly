import ErdosSzekeres.Decomposable

namespace ErdosSzekeres

/-- At an arbitrary deep-below split, avoidance of a strong (s+1)-polygon is equivalent to avoidance in each child and the cardinal coupling bound for every lower cup and upper cap. This includes empty chains and children and is the exact strong-coupling component of profile gluing.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.HasDeepBelowSplit.isStrongPolygonSet_iff_inter_cup_cap, ErdosSzekeres.HasDeepBelowSplit.containsStrongPolygonSet_of_cup_cap
@dangling-ok General strong-coupling component of R24 exact compatible-profile composition and construction induction; full endpoint-profile gluing and loss invariant remain separate open obligations. -/
theorem deepSplit_strong_avoidance_iff {n s : ℕ} {χ : TripleColoring n} {lower upper : Finset (Fin n)} (hdeep : HasDeepBelowSplit χ lower upper) : (¬ ContainsStrongPolygonSet χ (lower ∪ upper) (s + 1)) ↔ ((¬ ContainsStrongPolygonSet χ lower (s + 1)) ∧ (¬ ContainsStrongPolygonSet χ upper (s + 1)) ∧ ∀ C D : Finset (Fin n), C ⊆ lower → D ⊆ upper → IsCupSet χ C → IsCapSet χ D → C.card + D.card ≤ s) := by
  classical
  constructor
  · intro hroot
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨P, hPL, hPc, hP⟩
      exact hroot ⟨P, hPL.trans Finset.subset_union_left, hPc, hP⟩
    · rintro ⟨P, hPU, hPc, hP⟩
      exact hroot ⟨P, hPU.trans Finset.subset_union_right, hPc, hP⟩
    · intro C D hCL hDU hC hD
      by_contra hn
      apply hroot
      exact hdeep.containsStrongPolygonSet_of_cup_cap hCL hDU hC hD (by omega)
  · rintro ⟨hnoL, hnoU, hbound⟩ ⟨P, hPS, hPc, hP⟩
    by_cases hmeetL : (P ∩ lower).Nonempty
    · by_cases hmeetU : (P ∩ upper).Nonempty
      · obtain ⟨hcup, hcap⟩ :=
          (hdeep.isStrongPolygonSet_iff_inter_cup_cap hPS hmeetL hmeetU).mp hP
        have hsize := hbound (P ∩ lower) (P ∩ upper)
          Finset.inter_subset_right Finset.inter_subset_right hcup hcap
        have hunion : (P ∩ lower) ∪ (P ∩ upper) = P := by
          ext q
          simp only [Finset.mem_union, Finset.mem_inter]
          constructor
          · rintro (⟨hq, _⟩ | ⟨hq, _⟩) <;> exact hq
          · intro hq
            rcases Finset.mem_union.mp (hPS hq) with hL | hU
            · exact Or.inl ⟨hq, hL⟩
            · exact Or.inr ⟨hq, hU⟩
        have hcard := Finset.card_union_of_disjoint
          (hdeep.disjoint.mono Finset.inter_subset_right Finset.inter_subset_right :
            Disjoint (P ∩ lower) (P ∩ upper))
        rw [hunion, hPc] at hcard
        omega
      · have hPL : P ⊆ lower := by
          intro q hq
          rcases Finset.mem_union.mp (hPS hq) with hL | hU
          · exact hL
          · exact False.elim (hmeetU ⟨q, Finset.mem_inter.mpr ⟨hq, hU⟩⟩)
        exact hnoL ⟨P, hPL, hPc, hP⟩
    · have hPU : P ⊆ upper := by
        intro q hq
        rcases Finset.mem_union.mp (hPS hq) with hL | hU
        · exact False.elim (hmeetL ⟨q, Finset.mem_inter.mpr ⟨hq, hL⟩⟩)
        · exact hU
      exact hnoU ⟨P, hPU, hPc, hP⟩


end ErdosSzekeres
