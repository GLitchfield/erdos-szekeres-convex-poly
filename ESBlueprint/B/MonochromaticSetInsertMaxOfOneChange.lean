import ESBlueprint.B.IsMonochromaticSetOfOneChangeConsecutive

namespace ErdosSzekeres

/-- A point after a monochromatic set can be inserted when its turn with the last two points has the same colour; one-change propagates the sole new consecutive turn.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.singletonLowerPascalTailGate_five_pred_of_six_le -/
theorem monochromaticSet_insert_max_of_oneChange {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)} {c : Turn} {x a b : Fin n} (ha : a ∈ s) (hb : b ∈ s) (hab : a < b) (hbx : b < x) (hmax : ∀ y ∈ s, y ≤ b) (hprev : ∀ y ∈ s, y < b → y ≤ a) (hmono : ∀ t : OrderedTriple n, t.i ∈ s → t.j ∈ s → t.k ∈ s → χ t = c) (hone : OneChangeOn χ (insert x s)) (hturn : χ ⟨a, b, x, hab, hbx⟩ = c) : ∀ t : OrderedTriple n, t.i ∈ insert x s → t.j ∈ insert x s → t.k ∈ insert x s → χ t = c := by
  classical
  apply isMonochromaticSet_of_oneChange_consecutive hone
  intro t hi hj hk hgap₁ hgap₂
  have hxmax : ∀ y ∈ insert x s, y ≤ x := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact le_rfl
    · exact (hmax y hy).trans hbx.le
  have hix : t.i ≠ x := ne_of_lt (t.hij.trans_le (hxmax t.j hj))
  have hjx : t.j ≠ x := ne_of_lt (t.hjk.trans_le (hxmax t.k hk))
  have hiS : t.i ∈ s := (Finset.mem_insert.mp hi).resolve_left hix
  have hjS : t.j ∈ s := (Finset.mem_insert.mp hj).resolve_left hjx
  rcases Finset.mem_insert.mp hk with hkx | hkS
  · have hjb : t.j = b := by
      apply le_antisymm (hmax t.j hjS)
      by_contra h
      have hjb' : t.j < b := lt_of_not_ge h
      exact hgap₂ b (Finset.mem_insert_of_mem hb) hjb' (by simpa [hkx] using hbx)
    have hia : t.i = a := by
      apply le_antisymm
      · exact hprev t.i hiS (by simpa [hjb] using t.hij)
      · by_contra h
        have hia' : t.i < a := lt_of_not_ge h
        exact hgap₁ a (Finset.mem_insert_of_mem ha) hia' (by simpa [hjb] using hab)
    change χ ⟨t.i, t.j, t.k, t.hij, t.hjk⟩ = c
    simpa only [hia, hjb, hkx] using hturn
  · exact hmono t hiS hjS hkS

end ErdosSzekeres
