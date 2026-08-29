module

public import ErdosSzekeres.SynchronizedFiveFanFin11PredecessorConsumer

@[expose] public section

/-!
# Transport of the Fin11 synchronized fan to an arbitrary window

This file transports strong-polygon witnesses exactly through an increasing
embedding and applies the unconditional Fin11 fan theorem inside any eleven-point
window satisfying the same local hypotheses.
-/

namespace ErdosSzekeres

/-- The strong-polygon law on a support is preserved and reflected by an
increasing relabeling. -/
private theorem isStrongPolygonSet_image_restrict_iff
    {m n : Nat} (chi : TripleColoring n) (f : Fin m ↪o Fin n)
    (s : Finset (Fin m)) :
    IsStrongPolygonSet (chi.restrict f) s ↔
      IsStrongPolygonSet chi (s.image f) := by
  constructor
  · intro hstrong i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_image] at hi hj hk hl
    obtain ⟨i', hi', rfl⟩ := hi
    obtain ⟨j', hj', rfl⟩ := hj
    obtain ⟨k', hk', rfl⟩ := hk
    obtain ⟨l', hl', rfl⟩ := hl
    simpa [TripleColoring.restrict, OrderedTriple.map] using
      hstrong (f.lt_iff_lt.mp hij) (f.lt_iff_lt.mp hjk)
        (f.lt_iff_lt.mp hkl) hi' hj' hk' hl'
  · intro hstrong i j k l hij hjk hkl hi hj hk hl
    simpa [TripleColoring.restrict, OrderedTriple.map] using
      hstrong (f.strictMono hij) (f.strictMono hjk) (f.strictMono hkl)
        (by exact Finset.mem_image.mpr ⟨i, hi, rfl⟩)
        (by exact Finset.mem_image.mpr ⟨j, hj, rfl⟩)
        (by exact Finset.mem_image.mpr ⟨k, hk, rfl⟩)
        (by exact Finset.mem_image.mpr ⟨l, hl, rfl⟩)

/-- A strong polygon of prescribed size exists on a restricted support exactly
when its image is a strong polygon of that size in the ambient coloring. -/
theorem containsStrongPolygonSet_image_restrict_iff
    {m n k : Nat} (chi : TripleColoring n) (f : Fin m ↪o Fin n)
    (s : Finset (Fin m)) :
    ContainsStrongPolygonSet (chi.restrict f) s k ↔
      ContainsStrongPolygonSet chi (s.image f) k := by
  constructor
  · rintro ⟨polygon, hpolygon, hcard, hstrong⟩
    refine ⟨polygon.image f, Finset.image_mono f hpolygon, ?_, ?_⟩
    · exact (Finset.card_image_of_injective polygon f.injective).trans hcard
    · exact (isStrongPolygonSet_image_restrict_iff chi f polygon).mp hstrong
  · rintro ⟨polygon, hpolygon, hcard, hstrong⟩
    obtain ⟨preimage, hpreimage, himage⟩ := Finset.subset_image_iff.mp hpolygon
    refine ⟨preimage, hpreimage, ?_, ?_⟩
    · rw [← himage] at hcard
      exact (Finset.card_image_of_injective preimage f.injective).symm.trans hcard
    · apply (isStrongPolygonSet_image_restrict_iff chi f preimage).mpr
      simpa [himage] using hstrong

/-- Every one-change eleven-point window without a strong hexagon contains an
exact six-point support without a strong pentagon. -/
theorem predecessorFreeSixSubsetAtSixFinElevenWindow_of_oneChange
    {n : Nat} (chi : TripleColoring n) (f : Fin 11 ↪o Fin n)
    (hone : OneChangeOn chi (Finset.univ.image f))
    (hnoStrong :
      ¬ ContainsStrongPolygonSet chi (Finset.univ.image f) 6) :
    ∃ side : Finset (Fin n),
      side ⊆ Finset.univ.image f ∧
      side.card = 6 ∧
      ¬ ContainsStrongPolygonSet chi side 5 := by
  have honeRestrict : OneChangeOn (chi.restrict f) Finset.univ := by
    intro i j k l hij hjk hkl _ _ _ _
    simpa [TripleColoring.restrict, OrderedTriple.map] using
      hone (f.strictMono hij) (f.strictMono hjk) (f.strictMono hkl)
        (by simp) (by simp) (by simp) (by simp)
  have hnoStrongRestrict :
      ¬ ContainsStrongPolygonSet (chi.restrict f) Finset.univ 6 := by
    intro hstrong
    exact hnoStrong
      ((containsStrongPolygonSet_image_restrict_iff chi f Finset.univ).mp hstrong)
  obtain ⟨side, pivot, _hpivot, hcard, hbranch⟩ :=
    synchronizedFiveFanSideAtSixFinEleven (chi.restrict f)
      honeRestrict hnoStrongRestrict
  have hfree :
      ¬ ContainsStrongPolygonSet (chi.restrict f) side 5 := by
    rcases hbranch with hlower | hupper
    · exact hlower.1.predecessorFree_lower_of_cupPure
        (by omega) (by simp) hnoStrongRestrict hlower.2
    · exact hupper.1.predecessorFree_upper_of_capPure
        (by omega) (by simp) hnoStrongRestrict hupper.2
  refine ⟨side.image f, Finset.image_mono f (Finset.subset_univ side), ?_, ?_⟩
  · exact (Finset.card_image_of_injective side f.injective).trans hcard
  · intro hstrong
    exact hfree
      ((containsStrongPolygonSet_image_restrict_iff chi f side).mpr hstrong)

end ErdosSzekeres

end
