module

public import ErdosSzekeres.Fin15AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 031. -/

theorem fin15Anchored_strongSet_iff_mask09738 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {1, 3, 9, 10, 13} ↔
      Fin15AnchoredStrongQuad chi 1 3 9 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 3 9 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 3 10 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 9 10 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 9 10 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 9) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 10) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 9) (k := 10) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 9) (k := 10) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask17930 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {1, 3, 9, 10, 14} ↔
      Fin15AnchoredStrongQuad chi 1 3 9 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 3 9 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 3 10 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 9 10 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 9 10 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 9) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 10) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 9) (k := 10) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 9) (k := 10) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask06666 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {1, 3, 9, 11, 12} ↔
      Fin15AnchoredStrongQuad chi 1 3 9 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 3 9 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 3 11 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 9 11 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 9 11 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 9) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 9) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask10762 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {1, 3, 9, 11, 13} ↔
      Fin15AnchoredStrongQuad chi 1 3 9 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 3 9 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 3 11 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 9 11 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 9 11 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 9) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 11) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 9) (k := 11) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 9) (k := 11) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask18954 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {1, 3, 9, 11, 14} ↔
      Fin15AnchoredStrongQuad chi 1 3 9 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 3 9 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 3 11 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 9 11 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 9 11 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 9) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 11) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 9) (k := 11) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 9) (k := 11) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask12810 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {1, 3, 9, 12, 13} ↔
      Fin15AnchoredStrongQuad chi 1 3 9 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 3 9 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 3 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 9 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 9 12 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 9) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 9) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 9) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask21002 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {1, 3, 9, 12, 14} ↔
      Fin15AnchoredStrongQuad chi 1 3 9 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 3 9 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 3 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 9 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 9 12 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 9) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 9) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 9) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask25098 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {1, 3, 9, 13, 14} ↔
      Fin15AnchoredStrongQuad chi 1 3 9 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 3 9 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 3 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 9 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 9 13 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 9) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 9) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 9) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 9) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask07178 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {1, 3, 10, 11, 12} ↔
      Fin15AnchoredStrongQuad chi 1 3 10 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 3 10 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 3 11 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 10 11 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 10 11 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 10) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 10) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask11274 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {1, 3, 10, 11, 13} ↔
      Fin15AnchoredStrongQuad chi 1 3 10 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 3 10 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 3 11 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 10 11 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 10 11 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 10) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 11) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 10) (k := 11) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 10) (k := 11) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask19466 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {1, 3, 10, 11, 14} ↔
      Fin15AnchoredStrongQuad chi 1 3 10 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 3 10 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 3 11 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 10 11 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 10 11 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 10) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 11) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 10) (k := 11) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 10) (k := 11) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask13322 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {1, 3, 10, 12, 13} ↔
      Fin15AnchoredStrongQuad chi 1 3 10 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 3 10 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 3 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 10 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 10 12 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 10) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 10) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 10) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask21514 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {1, 3, 10, 12, 14} ↔
      Fin15AnchoredStrongQuad chi 1 3 10 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 3 10 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 3 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 10 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 10 12 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 10) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 10) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 10) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask25610 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {1, 3, 10, 13, 14} ↔
      Fin15AnchoredStrongQuad chi 1 3 10 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 3 10 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 3 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 10 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 10 13 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 10) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 10) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 10) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 10) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask14346 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {1, 3, 11, 12, 13} ↔
      Fin15AnchoredStrongQuad chi 1 3 11 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 3 11 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 3 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 11 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 11 12 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 11) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 11) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 11) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask22538 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {1, 3, 11, 12, 14} ↔
      Fin15AnchoredStrongQuad chi 1 3 11 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 3 11 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 3 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 11 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 11 12 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 11) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 11) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 11) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask28682 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {1, 3, 12, 13, 14} ↔
      Fin15AnchoredStrongQuad chi 1 3 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 3 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 3 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 12 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 12 13 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 3) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 12) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 12) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask00242 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {1, 4, 5, 6, 7} ↔
      Fin15AnchoredStrongQuad chi 1 4 5 6 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 5 7 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 6 7 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 5 6 7 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 4 5 6 7 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 6) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 5) (k := 6) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 4) (j := 5) (k := 6) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask00370 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {1, 4, 5, 6, 8} ↔
      Fin15AnchoredStrongQuad chi 1 4 5 6 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 5 8 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 6 8 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 5 6 8 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 4 5 6 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 6) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 5) (k := 6) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 4) (j := 5) (k := 6) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask00626 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {1, 4, 5, 6, 9} ↔
      Fin15AnchoredStrongQuad chi 1 4 5 6 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 5 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 6 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 5 6 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 4 5 6 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 6) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 5) (k := 6) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 4) (j := 5) (k := 6) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask01138 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {1, 4, 5, 6, 10} ↔
      Fin15AnchoredStrongQuad chi 1 4 5 6 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 5 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 6 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 5 6 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 4 5 6 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 6) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 5) (k := 6) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 4) (j := 5) (k := 6) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask02162 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {1, 4, 5, 6, 11} ↔
      Fin15AnchoredStrongQuad chi 1 4 5 6 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 5 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 6 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 5 6 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 4 5 6 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 6) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 5) (k := 6) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 4) (j := 5) (k := 6) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask04210 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {1, 4, 5, 6, 12} ↔
      Fin15AnchoredStrongQuad chi 1 4 5 6 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 5 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 6 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 5 6 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 4 5 6 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 6) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 5) (k := 6) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 4) (j := 5) (k := 6) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask08306 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {1, 4, 5, 6, 13} ↔
      Fin15AnchoredStrongQuad chi 1 4 5 6 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 5 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 6 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 5 6 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 4 5 6 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 6) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 5) (k := 6) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 4) (j := 5) (k := 6) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask16498 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {1, 4, 5, 6, 14} ↔
      Fin15AnchoredStrongQuad chi 1 4 5 6 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 5 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 6 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 5 6 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 4 5 6 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 6) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 5) (k := 6) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 4) (j := 5) (k := 6) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask00434 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {1, 4, 5, 7, 8} ↔
      Fin15AnchoredStrongQuad chi 1 4 5 7 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 5 8 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 7 8 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 5 7 8 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 4 5 7 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 7) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 5) (k := 7) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 4) (j := 5) (k := 7) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask00690 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {1, 4, 5, 7, 9} ↔
      Fin15AnchoredStrongQuad chi 1 4 5 7 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 5 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 7 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 5 7 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 4 5 7 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 7) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 5) (k := 7) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 4) (j := 5) (k := 7) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask01202 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {1, 4, 5, 7, 10} ↔
      Fin15AnchoredStrongQuad chi 1 4 5 7 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 5 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 7 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 5 7 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 4 5 7 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 7) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 5) (k := 7) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 4) (j := 5) (k := 7) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask02226 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {1, 4, 5, 7, 11} ↔
      Fin15AnchoredStrongQuad chi 1 4 5 7 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 5 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 7 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 5 7 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 4 5 7 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 7) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 5) (k := 7) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 4) (j := 5) (k := 7) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask04274 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {1, 4, 5, 7, 12} ↔
      Fin15AnchoredStrongQuad chi 1 4 5 7 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 5 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 7 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 5 7 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 4 5 7 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 7) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 5) (k := 7) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 4) (j := 5) (k := 7) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask08370 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {1, 4, 5, 7, 13} ↔
      Fin15AnchoredStrongQuad chi 1 4 5 7 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 5 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 7 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 5 7 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 4 5 7 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 7) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 5) (k := 7) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 4) (j := 5) (k := 7) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask16562 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {1, 4, 5, 7, 14} ↔
      Fin15AnchoredStrongQuad chi 1 4 5 7 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 5 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 7 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 5 7 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 4 5 7 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 7) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 5) (k := 7) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 4) (j := 5) (k := 7) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask00818 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {1, 4, 5, 8, 9} ↔
      Fin15AnchoredStrongQuad chi 1 4 5 8 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 5 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 8 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 5 8 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 4 5 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 5) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 4) (j := 5) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask01330 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {1, 4, 5, 8, 10} ↔
      Fin15AnchoredStrongQuad chi 1 4 5 8 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 5 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 8 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 5 8 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 4 5 8 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 5) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 4) (j := 5) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask04402 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {1, 4, 5, 8, 12} ↔
      Fin15AnchoredStrongQuad chi 1 4 5 8 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 5 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 8 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 5 8 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 4 5 8 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 5) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 4) (j := 5) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask08498 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {1, 4, 5, 8, 13} ↔
      Fin15AnchoredStrongQuad chi 1 4 5 8 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 5 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 8 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 5 8 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 4 5 8 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 8) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 5) (k := 8) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 4) (j := 5) (k := 8) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask16690 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {1, 4, 5, 8, 14} ↔
      Fin15AnchoredStrongQuad chi 1 4 5 8 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 5 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 8 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 5 8 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 4 5 8 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 8) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 5) (k := 8) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 4) (j := 5) (k := 8) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask01586 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {1, 4, 5, 9, 10} ↔
      Fin15AnchoredStrongQuad chi 1 4 5 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 5 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 9 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 5 9 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 4 5 9 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 5) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 4) (j := 5) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask02610 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {1, 4, 5, 9, 11} ↔
      Fin15AnchoredStrongQuad chi 1 4 5 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 5 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 9 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 5 9 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 4 5 9 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 5) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 4) (j := 5) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask04658 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {1, 4, 5, 9, 12} ↔
      Fin15AnchoredStrongQuad chi 1 4 5 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 5 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 4 9 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 1 5 9 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 4 5 9 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 5) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 4) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 1) (j := 5) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 4) (j := 5) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
