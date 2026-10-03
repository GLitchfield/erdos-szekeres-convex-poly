import ESBlueprint.B.IsMonochromaticSetOfOneChangeConsecutive

namespace ErdosSzekeres

/-- A point before a monochromatic set can be inserted when its turn with the first two points has the same colour; one-change propagates the sole new consecutive turn.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.singletonLowerPascalTailGate_five_pred_of_six_le -/
theorem monochromaticSet_insert_min_of_oneChange {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)} {c : Turn} {x a b : Fin n} (ha : a ∈ s) (hb : b ∈ s) (hab : a < b) (hxa : x < a) (hmin : ∀ y ∈ s, a ≤ y) (hnext : ∀ y ∈ s, a < y → b ≤ y) (hmono : ∀ t : OrderedTriple n, t.i ∈ s → t.j ∈ s → t.k ∈ s → χ t = c) (hone : OneChangeOn χ (insert x s)) (hturn : χ ⟨x, a, b, hxa, hab⟩ = c) : ∀ t : OrderedTriple n, t.i ∈ insert x s → t.j ∈ insert x s → t.k ∈ insert x s → χ t = c := by
  classical
  apply isMonochromaticSet_of_oneChange_consecutive hone
  intro t hi hj hk hgap₁ hgap₂
  have hxmin : ∀ y ∈ insert x s, x ≤ y := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact le_rfl
    · exact hxa.le.trans (hmin y hy)
  have hjx : t.j ≠ x := ne_of_gt ((hxmin t.i hi).trans_lt t.hij)
  have hkx : t.k ≠ x := ne_of_gt ((hxmin t.i hi).trans_lt (t.hij.trans t.hjk))
  have hjS : t.j ∈ s := (Finset.mem_insert.mp hj).resolve_left hjx
  have hkS : t.k ∈ s := (Finset.mem_insert.mp hk).resolve_left hkx
  rcases Finset.mem_insert.mp hi with hix | hiS
  · have hja : t.j = a := by
      apply le_antisymm
      · by_contra h
        have haj : a < t.j := lt_of_not_ge h
        exact hgap₁ a (Finset.mem_insert_of_mem ha) (by simpa [hix] using hxa) haj
      · exact hmin t.j hjS
    have hkb : t.k = b := by
      apply le_antisymm
      · by_contra h
        have hbk : b < t.k := lt_of_not_ge h
        exact hgap₂ b (Finset.mem_insert_of_mem hb) (by simpa [hja] using hab) hbk
      · exact hnext t.k hkS (by simpa [hja] using t.hjk)
    change χ ⟨t.i, t.j, t.k, t.hij, t.hjk⟩ = c
    simpa only [hix, hja, hkb] using hturn
  · exact hmono t hiS hjS hkS

end ErdosSzekeres
