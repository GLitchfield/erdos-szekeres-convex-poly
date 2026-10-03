import ESBlueprint.B.MonochromaticSetInsertMaxOfOneChange
import ESBlueprint.B.MonochromaticSetInsertMinOfOneChange

namespace ErdosSzekeres

/-- Two ordered cups avoiding four-caps and u-cups have at most 2u-3 points. Their boundary extrema admit a cup extension on at least one side, and a full block of size u-1 forces the extension on the other side.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.singletonLowerPascalTailGate_five_pred_of_six_le -/
theorem twoCupBlocks_card_and_extensions_of_oneChange_no_capFour_no_cup {n u : ℕ} {χ : TripleColoring n} {P Q : Finset (Fin n)} (hu : 2 ≤ u) (hone : OneChangeOn χ (P ∪ Q)) (hsep : ∀ x ∈ P, ∀ y ∈ Q, x < y) (hPcup : IsCupSet χ P) (hQcup : IsCupSet χ Q) (hnoCap : ¬ContainsCapSet χ (P ∪ Q) 4) (hnoCup : ¬ContainsCupSet χ (P ∪ Q) u) : P.card + Q.card ≤ 2 * u - 3 ∧ ∀ p q : Fin n, p ∈ P → q ∈ Q → (∀ x ∈ P, x ≤ p) → (∀ y ∈ Q, q ≤ y) → (IsCupSet χ (insert q P) ∨ IsCupSet χ (insert p Q)) ∧ (P.card = u - 1 → IsCupSet χ (insert p Q)) ∧ (Q.card = u - 1 → IsCupSet χ (insert q P)) := by
  classical
  have hsmall : ∀ (A : Finset (Fin n)), A.card ≤ 2 → IsCupSet χ A := by
    intro A hA t hi hj hk
    exfalso
    have hsub : ({t.i, t.j, t.k} : Finset (Fin n)) ⊆ A := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hi, hj, hk⟩
    have hcard : ({t.i, t.j, t.k} : Finset (Fin n)).card = 3 := by
      simp [ne_of_lt t.hij, ne_of_lt t.hjk, ne_of_lt (t.hij.trans t.hjk)]
    have := Finset.card_le_card hsub
    omega
  have hbound : ∀ (A : Finset (Fin n)), A ⊆ P ∪ Q → IsCupSet χ A → A.card < u := by
    intro A hAs hAcup
    by_contra h
    obtain ⟨D, hDA, hDcard⟩ := Finset.exists_subset_card_eq (show u ≤ A.card by omega)
    exact hnoCup ⟨D, hDA.trans hAs, hDcard, FinsetPolygon.IsCupSet.mono hAcup hDA⟩
  have hext : ∀ p q : Fin n, p ∈ P → q ∈ Q →
      (∀ x ∈ P, x ≤ p) → (∀ y ∈ Q, q ≤ y) →
      IsCupSet χ (insert q P) ∨ IsCupSet χ (insert p Q) := by
    intro p q hp hq hPmax hQmin
    have hpq : p < q := hsep p hp q hq
    by_cases hPsmall : P.card ≤ 1
    · exact Or.inl (hsmall _ (by have := Finset.card_insert_le q P; omega))
    by_cases hQsmall : Q.card ≤ 1
    · exact Or.inr (hsmall _ (by have := Finset.card_insert_le p Q; omega))
    have hPrest : (P.erase p).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hp]
      omega
    let a := (P.erase p).max' hPrest
    have haErase : a ∈ P.erase p := Finset.max'_mem _ _
    have haP : a ∈ P := (Finset.mem_erase.mp haErase).2
    have hap : a < p := by
      have := hPmax a haP
      have := (Finset.mem_erase.mp haErase).1
      omega
    have hPprev : ∀ x ∈ P, x < p → x ≤ a := by
      intro x hx hxp
      exact Finset.le_max' _ x (Finset.mem_erase.mpr ⟨ne_of_lt hxp, hx⟩)
    have hQrest : (Q.erase q).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hq]
      omega
    let b := (Q.erase q).min' hQrest
    have hbErase : b ∈ Q.erase q := Finset.min'_mem _ _
    have hbQ : b ∈ Q := (Finset.mem_erase.mp hbErase).2
    have hqb : q < b := by
      have := hQmin b hbQ
      have := (Finset.mem_erase.mp hbErase).1
      omega
    have hQnext : ∀ y ∈ Q, q < y → b ≤ y := by
      intro y hy hqy
      exact Finset.min'_le _ y (Finset.mem_erase.mpr ⟨ne_of_gt hqy, hy⟩)
    have hsubP : insert q P ⊆ P ∪ Q := Finset.insert_subset_iff.mpr
      ⟨Finset.mem_union_right _ hq, Finset.subset_union_left⟩
    have hsubQ : insert p Q ⊆ P ∪ Q := Finset.insert_subset_iff.mpr
      ⟨Finset.mem_union_left _ hp, Finset.subset_union_right⟩
    cases hfirst : χ ⟨a, p, q, hap, hpq⟩ with
    | left =>
      exact Or.inl (monochromaticSet_insert_max_of_oneChange haP hp hap hpq hPmax
        hPprev hPcup (hone.mono hsubP) hfirst)
    | right =>
      cases hlast : χ ⟨p, q, b, hpq, hqb⟩ with
      | left =>
        exact Or.inr (monochromaticSet_insert_min_of_oneChange hq hbQ hqb hpq hQmin
          hQnext hQcup (hone.mono hsubQ) hlast)
      | right =>
        exfalso
        apply hnoCap
        let f : Fin 4 ↪o Fin n := OrderEmbedding.ofStrictMono ![a, p, q, b] (by
          apply Fin.strictMono_iff_lt_succ.mpr
          intro i
          fin_cases i
          · simpa using hap
          · simpa using hpq
          · simpa using hqb)
        have hsub : Finset.univ.image f ⊆ P ∪ Q := by
          intro z hz
          simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz
          obtain ⟨i, rfl⟩ := hz
          fin_cases i
          · simpa [f] using Finset.mem_union_left Q haP
          · simpa [f] using Finset.mem_union_left Q hp
          · simpa [f] using Finset.mem_union_right P hq
          · simpa [f] using Finset.mem_union_right P hbQ
        refine ⟨Finset.univ.image f, hsub, ?_, ?_⟩
        · simpa using Finset.card_image_of_injective Finset.univ f.injective
        · exact FinsetPolygon.IsCap.image (isMonochromaticChain_finFour_of_outer_eq f
            (hone.mono hsub) (by simpa [f] using hfirst) (by simpa [f] using hlast))
  have hPbound := hbound P Finset.subset_union_left hPcup
  have hQbound := hbound Q Finset.subset_union_right hQcup
  refine ⟨?_, ?_⟩
  · rcases P.eq_empty_or_nonempty with hPempty | hPne
    · simp only [hPempty, Finset.card_empty, zero_add]
      omega
    rcases Q.eq_empty_or_nonempty with hQempty | hQne
    · simp only [hQempty, Finset.card_empty, add_zero]
      omega
    let p := P.max' hPne
    let q := Q.min' hQne
    have hp : p ∈ P := Finset.max'_mem _ _
    have hq : q ∈ Q := Finset.min'_mem _ _
    have hPmax : ∀ x ∈ P, x ≤ p := fun x hx ↦ Finset.le_max' _ x hx
    have hQmin : ∀ y ∈ Q, q ≤ y := fun y hy ↦ Finset.min'_le _ y hy
    have hqNotP : q ∉ P := fun hqP ↦ (lt_irrefl q) (hsep q hqP q hq)
    have hpNotQ : p ∉ Q := fun hpQ ↦ (lt_irrefl p) (hsep p hp p hpQ)
    rcases hext p q hp hq hPmax hQmin with hcup | hcup
    · have h := hbound (insert q P) (Finset.insert_subset_iff.mpr
        ⟨Finset.mem_union_right _ hq, Finset.subset_union_left⟩) hcup
      rw [Finset.card_insert_of_notMem hqNotP] at h
      omega
    · have h := hbound (insert p Q) (Finset.insert_subset_iff.mpr
        ⟨Finset.mem_union_left _ hp, Finset.subset_union_right⟩) hcup
      rw [Finset.card_insert_of_notMem hpNotQ] at h
      omega
  · intro p q hp hq hPmax hQmin
    have hqNotP : q ∉ P := fun hqP ↦ (lt_irrefl q) (hsep q hqP q hq)
    have hpNotQ : p ∉ Q := fun hpQ ↦ (lt_irrefl p) (hsep p hp p hpQ)
    have hsubP : insert q P ⊆ P ∪ Q := Finset.insert_subset_iff.mpr
      ⟨Finset.mem_union_right _ hq, Finset.subset_union_left⟩
    have hsubQ : insert p Q ⊆ P ∪ Q := Finset.insert_subset_iff.mpr
      ⟨Finset.mem_union_left _ hp, Finset.subset_union_right⟩
    have h := hext p q hp hq hPmax hQmin
    refine ⟨h, ?_, ?_⟩
    · intro hPfull
      rcases h with hcup | hcup
      · exfalso
        have hb := hbound (insert q P) hsubP hcup
        rw [Finset.card_insert_of_notMem hqNotP, hPfull] at hb
        omega
      · exact hcup
    · intro hQfull
      rcases h with hcup | hcup
      · exact hcup
      · exfalso
        have hb := hbound (insert p Q) hsubQ hcup
        rw [Finset.card_insert_of_notMem hpNotQ, hQfull] at hb
        omega

end ErdosSzekeres
