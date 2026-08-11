module

public import ErdosSzekeres.DiagonalCupBlocksK9Normalized

@[expose] public section

/-! Transport the normalized fifteen-vertex k=9 certificates to arbitrary blocks. -/

namespace ErdosSzekeres

set_option maxHeartbeats 2000000 in
theorem diagonalCupBlocksK9_78_of_finFifteen
    {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)}
    (hdisjoint : Disjoint left right)
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hleftCard : left.card = 7)
    (hrightCard : right.card = 8)
    (hleft : IsCupSet χ left) (hright : IsCupSet χ right)
    (hone : OneChangeOn χ (left ∪ right)) :
    ContainsCapSet χ (left ∪ right) 4 ∨
      ContainsCupSet χ (left ∪ right) 9 ∨
        ContainsStrongPolygonSet χ (left ∪ right) 9 := by
  let le : Fin 7 ↪o Fin n := left.orderEmbOfFin hleftCard
  let re : Fin 8 ↪o Fin n := right.orderEmbOfFin hrightCard
  let f : Fin 15 ↪o Fin n := OrderEmbedding.ofStrictMono
    ![le 0, le 1, le 2, le 3, le 4, le 5, le 6, re 0,
      re 1, re 2, re 3, re 4, re 5, re 6, re 7] (by
      intro i j hij
      fin_cases i <;> fin_cases j
      all_goals (try norm_num at hij)
      all_goals first
        | exact le.strictMono (by decide)
        | exact re.strictMono (by decide)
        | exact horder _ (left.orderEmbOfFin_mem hleftCard _)
            _ (right.orderEmbOfFin_mem hrightCard _))
  let ψ : TripleColoring 15 := χ.restrict f
  have hfmem : ∀ i : Fin 15, f i ∈ left ∪ right := by
    intro i
    fin_cases i <;>
      simp [f, le, re, left.orderEmbOfFin_mem hleftCard,
        right.orderEmbOfFin_mem hrightCard]
  have hfirst : ∀ i : Fin 15, i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 15)) → f i ∈ left := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact left.orderEmbOfFin_mem hleftCard _
  have hlast : ∀ i : Fin 15, i ∈ ({7, 8, 9, 10, 11, 12, 13, 14} : Finset (Fin 15)) → f i ∈ right := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact right.orderEmbOfFin_mem hrightCard _
  have hψLeft : IsCupSet ψ {0, 1, 2, 3, 4, 5, 6} := by
    intro t hi hj hk
    exact hleft (t.map f) (hfirst t.i hi) (hfirst t.j hj) (hfirst t.k hk)
  have hψRight : IsCupSet ψ {7, 8, 9, 10, 11, 12, 13, 14} := by
    intro t hi hj hk
    exact hright (t.map f) (hlast t.i hi) (hlast t.j hj) (hlast t.k hk)
  have hψOne : OneChangeOn ψ Finset.univ := by
    intro i j k l hij hjk hkl _ _ _ _
    exact hone (f.strictMono hij) (f.strictMono hjk) (f.strictMono hkl)
      (hfmem i) (hfmem j) (hfmem k) (hfmem l)
  have hout := diagonalCupBlocksK9FinFifteen78 ψ hψLeft hψRight hψOne
  have himage : Finset.univ.image f = left ∪ right := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      exact hfmem i
    · have himageCard : (Finset.univ.image f).card = 15 := by
        simpa using Finset.card_image_of_injective Finset.univ f.injective
      rw [Finset.card_union_of_disjoint hdisjoint, hleftCard, hrightCard, himageCard]
  rcases hout with hcap | hcup | hstrong
  · exact Or.inl (by simpa [himage] using containsCapSet_map_restrict f hcap)
  · exact Or.inr (Or.inl (by simpa [himage] using containsCupSet_map_restrict f hcup))
  · exact Or.inr (Or.inr (by
      simpa [himage] using containsStrongPolygonSet_map_restrict f hstrong))

set_option maxHeartbeats 2000000 in
theorem diagonalCupBlocksK9_87_of_finFifteen
    {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)}
    (hdisjoint : Disjoint left right)
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hleftCard : left.card = 8)
    (hrightCard : right.card = 7)
    (hleft : IsCupSet χ left) (hright : IsCupSet χ right)
    (hone : OneChangeOn χ (left ∪ right)) :
    ContainsCapSet χ (left ∪ right) 4 ∨
      ContainsCupSet χ (left ∪ right) 9 ∨
        ContainsStrongPolygonSet χ (left ∪ right) 9 := by
  let le : Fin 8 ↪o Fin n := left.orderEmbOfFin hleftCard
  let re : Fin 7 ↪o Fin n := right.orderEmbOfFin hrightCard
  let f : Fin 15 ↪o Fin n := OrderEmbedding.ofStrictMono
    ![le 0, le 1, le 2, le 3, le 4, le 5, le 6, le 7,
      re 0, re 1, re 2, re 3, re 4, re 5, re 6] (by
      intro i j hij
      fin_cases i <;> fin_cases j
      all_goals (try norm_num at hij)
      all_goals first
        | exact le.strictMono (by decide)
        | exact re.strictMono (by decide)
        | exact horder _ (left.orderEmbOfFin_mem hleftCard _)
            _ (right.orderEmbOfFin_mem hrightCard _))
  let ψ : TripleColoring 15 := χ.restrict f
  have hfmem : ∀ i : Fin 15, f i ∈ left ∪ right := by
    intro i
    fin_cases i <;>
      simp [f, le, re, left.orderEmbOfFin_mem hleftCard,
        right.orderEmbOfFin_mem hrightCard]
  have hfirst : ∀ i : Fin 15, i ∈ ({0, 1, 2, 3, 4, 5, 6, 7} : Finset (Fin 15)) → f i ∈ left := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact left.orderEmbOfFin_mem hleftCard _
  have hlast : ∀ i : Fin 15, i ∈ ({8, 9, 10, 11, 12, 13, 14} : Finset (Fin 15)) → f i ∈ right := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact right.orderEmbOfFin_mem hrightCard _
  have hψLeft : IsCupSet ψ {0, 1, 2, 3, 4, 5, 6, 7} := by
    intro t hi hj hk
    exact hleft (t.map f) (hfirst t.i hi) (hfirst t.j hj) (hfirst t.k hk)
  have hψRight : IsCupSet ψ {8, 9, 10, 11, 12, 13, 14} := by
    intro t hi hj hk
    exact hright (t.map f) (hlast t.i hi) (hlast t.j hj) (hlast t.k hk)
  have hψOne : OneChangeOn ψ Finset.univ := by
    intro i j k l hij hjk hkl _ _ _ _
    exact hone (f.strictMono hij) (f.strictMono hjk) (f.strictMono hkl)
      (hfmem i) (hfmem j) (hfmem k) (hfmem l)
  have hout := diagonalCupBlocksK9FinFifteen87 ψ hψLeft hψRight hψOne
  have himage : Finset.univ.image f = left ∪ right := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      exact hfmem i
    · have himageCard : (Finset.univ.image f).card = 15 := by
        simpa using Finset.card_image_of_injective Finset.univ f.injective
      rw [Finset.card_union_of_disjoint hdisjoint, hleftCard, hrightCard, himageCard]
  rcases hout with hcap | hcup | hstrong
  · exact Or.inl (by simpa [himage] using containsCapSet_map_restrict f hcap)
  · exact Or.inr (Or.inl (by simpa [himage] using containsCupSet_map_restrict f hcup))
  · exact Or.inr (Or.inr (by
      simpa [himage] using containsStrongPolygonSet_map_restrict f hstrong))

/-- The exact k=9 diagonal cup-block contract. -/
theorem diagonalCupBlocksForce4kk_nine : DiagonalCupBlocksForce4kk 9 := by
  intro n χ left right hdisjoint horder hcards hleft hright hone
  norm_num at hcards
  rcases hcards with ⟨hleftCard, hrightCard⟩ | ⟨hleftCard, hrightCard⟩
  · exact diagonalCupBlocksK9_78_of_finFifteen hdisjoint horder
      hleftCard hrightCard hleft hright hone
  · exact diagonalCupBlocksK9_87_of_finFifteen hdisjoint horder
      hleftCard hrightCard hleft hright hone

end ErdosSzekeres

end
