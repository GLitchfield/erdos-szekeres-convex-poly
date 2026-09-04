module

public import ErdosSzekeres.Fin15AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 015. -/

theorem fin15Anchored_strongSet_iff_mask10377 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 7, 11, 13} ↔
      Fin15AnchoredStrongQuad chi 0 3 7 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 7 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 11 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 7 11 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 7 11 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 7) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 7) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 11) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 7) (k := 11) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 7) (k := 11) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask18569 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 7, 11, 14} ↔
      Fin15AnchoredStrongQuad chi 0 3 7 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 7 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 11 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 7 11 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 7 11 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 7) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 7) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 11) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 7) (k := 11) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 7) (k := 11) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask12425 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 7, 12, 13} ↔
      Fin15AnchoredStrongQuad chi 0 3 7 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 7 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 7 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 7 12 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 7) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 7) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 7) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 7) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask20617 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 7, 12, 14} ↔
      Fin15AnchoredStrongQuad chi 0 3 7 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 7 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 7 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 7 12 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 7) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 7) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 7) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 7) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask24713 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 7, 13, 14} ↔
      Fin15AnchoredStrongQuad chi 0 3 7 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 7 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 7 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 7 13 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 7) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 7) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 7) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 7) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask01801 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 8, 9, 10} ↔
      Fin15AnchoredStrongQuad chi 0 3 8 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 8 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 9 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 8 9 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 8 9 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 8) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 8) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask04873 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 8, 9, 12} ↔
      Fin15AnchoredStrongQuad chi 0 3 8 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 8 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 9 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 8 9 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 8 9 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 8) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 8) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask08969 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 8, 9, 13} ↔
      Fin15AnchoredStrongQuad chi 0 3 8 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 8 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 9 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 8 9 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 8 9 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 8) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 9) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 8) (k := 9) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 8) (k := 9) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask17161 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 8, 9, 14} ↔
      Fin15AnchoredStrongQuad chi 0 3 8 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 8 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 9 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 8 9 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 8 9 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 8) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 9) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 8) (k := 9) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 8) (k := 9) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask05385 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 8, 10, 12} ↔
      Fin15AnchoredStrongQuad chi 0 3 8 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 8 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 10 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 8 10 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 8 10 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 8) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 8) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask09481 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 8, 10, 13} ↔
      Fin15AnchoredStrongQuad chi 0 3 8 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 8 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 10 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 8 10 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 8 10 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 8) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 10) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 8) (k := 10) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 8) (k := 10) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask17673 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 8, 10, 14} ↔
      Fin15AnchoredStrongQuad chi 0 3 8 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 8 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 10 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 8 10 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 8 10 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 8) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 10) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 8) (k := 10) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 8) (k := 10) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask12553 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 8, 12, 13} ↔
      Fin15AnchoredStrongQuad chi 0 3 8 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 8 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 8 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 8 12 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 8) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 8) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 8) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask20745 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 8, 12, 14} ↔
      Fin15AnchoredStrongQuad chi 0 3 8 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 8 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 8 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 8 12 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 8) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 8) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 8) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask24841 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 8, 13, 14} ↔
      Fin15AnchoredStrongQuad chi 0 3 8 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 8 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 8 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 8 13 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 8) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 8) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 8) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 8) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask03593 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 9, 10, 11} ↔
      Fin15AnchoredStrongQuad chi 0 3 9 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 9 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 10 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 9 10 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 9 10 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 9) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 9) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask05641 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 9, 10, 12} ↔
      Fin15AnchoredStrongQuad chi 0 3 9 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 9 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 10 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 9 10 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 9 10 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 9) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 9) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask09737 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 9, 10, 13} ↔
      Fin15AnchoredStrongQuad chi 0 3 9 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 9 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 10 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 9 10 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 9 10 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 9) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 10) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 9) (k := 10) (l := 13)
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

theorem fin15Anchored_strongSet_iff_mask17929 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 9, 10, 14} ↔
      Fin15AnchoredStrongQuad chi 0 3 9 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 9 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 10 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 9 10 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 9 10 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 9) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 10) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 9) (k := 10) (l := 14)
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

theorem fin15Anchored_strongSet_iff_mask06665 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 9, 11, 12} ↔
      Fin15AnchoredStrongQuad chi 0 3 9 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 9 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 11 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 9 11 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 9 11 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 9) (k := 11) (l := 12)
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

theorem fin15Anchored_strongSet_iff_mask10761 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 9, 11, 13} ↔
      Fin15AnchoredStrongQuad chi 0 3 9 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 9 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 11 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 9 11 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 9 11 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 9) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 11) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 9) (k := 11) (l := 13)
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

theorem fin15Anchored_strongSet_iff_mask18953 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 9, 11, 14} ↔
      Fin15AnchoredStrongQuad chi 0 3 9 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 9 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 11 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 9 11 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 9 11 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 9) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 11) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 9) (k := 11) (l := 14)
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

theorem fin15Anchored_strongSet_iff_mask12809 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 9, 12, 13} ↔
      Fin15AnchoredStrongQuad chi 0 3 9 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 9 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 9 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 9 12 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 9) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 9) (k := 12) (l := 13)
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

theorem fin15Anchored_strongSet_iff_mask21001 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 9, 12, 14} ↔
      Fin15AnchoredStrongQuad chi 0 3 9 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 9 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 9 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 9 12 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 9) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 9) (k := 12) (l := 14)
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

theorem fin15Anchored_strongSet_iff_mask25097 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 9, 13, 14} ↔
      Fin15AnchoredStrongQuad chi 0 3 9 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 9 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 9 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 9 13 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 9) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 9) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 9) (k := 13) (l := 14)
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

theorem fin15Anchored_strongSet_iff_mask07177 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 10, 11, 12} ↔
      Fin15AnchoredStrongQuad chi 0 3 10 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 10 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 11 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 10 11 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 10 11 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 10) (k := 11) (l := 12)
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

theorem fin15Anchored_strongSet_iff_mask11273 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 10, 11, 13} ↔
      Fin15AnchoredStrongQuad chi 0 3 10 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 10 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 11 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 10 11 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 10 11 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 10) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 11) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 10) (k := 11) (l := 13)
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

theorem fin15Anchored_strongSet_iff_mask19465 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 10, 11, 14} ↔
      Fin15AnchoredStrongQuad chi 0 3 10 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 10 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 11 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 10 11 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 10 11 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 10) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 11) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 10) (k := 11) (l := 14)
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

theorem fin15Anchored_strongSet_iff_mask13321 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 10, 12, 13} ↔
      Fin15AnchoredStrongQuad chi 0 3 10 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 10 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 10 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 10 12 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 10) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 10) (k := 12) (l := 13)
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

theorem fin15Anchored_strongSet_iff_mask21513 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 10, 12, 14} ↔
      Fin15AnchoredStrongQuad chi 0 3 10 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 10 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 10 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 10 12 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 10) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 10) (k := 12) (l := 14)
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

theorem fin15Anchored_strongSet_iff_mask25609 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 10, 13, 14} ↔
      Fin15AnchoredStrongQuad chi 0 3 10 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 10 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 10 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 10 13 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 10) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 10) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 10) (k := 13) (l := 14)
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

theorem fin15Anchored_strongSet_iff_mask14345 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 11, 12, 13} ↔
      Fin15AnchoredStrongQuad chi 0 3 11 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 11 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 11 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 11 12 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 11) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 11) (k := 12) (l := 13)
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

theorem fin15Anchored_strongSet_iff_mask22537 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 11, 12, 14} ↔
      Fin15AnchoredStrongQuad chi 0 3 11 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 11 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 11 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 11 12 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 11) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 11) (k := 12) (l := 14)
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

theorem fin15Anchored_strongSet_iff_mask26633 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 11, 13, 14} ↔
      Fin15AnchoredStrongQuad chi 0 3 11 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 11 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 11 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 11 13 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 11) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 11) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 11) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 11) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask28681 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 12, 13, 14} ↔
      Fin15AnchoredStrongQuad chi 0 3 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 12 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 12 13 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 12) (k := 13) (l := 14)
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

theorem fin15Anchored_strongSet_iff_mask00241 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 4, 5, 6, 7} ↔
      Fin15AnchoredStrongQuad chi 0 4 5 6 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 5 7 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 6 7 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 5 6 7 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 4 5 6 7 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 5) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 5) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 6) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 5) (k := 6) (l := 7)
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

theorem fin15Anchored_strongSet_iff_mask00369 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 4, 5, 6, 8} ↔
      Fin15AnchoredStrongQuad chi 0 4 5 6 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 5 8 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 6 8 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 5 6 8 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 4 5 6 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 5) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 5) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 6) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 5) (k := 6) (l := 8)
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

theorem fin15Anchored_strongSet_iff_mask00625 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 4, 5, 6, 9} ↔
      Fin15AnchoredStrongQuad chi 0 4 5 6 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 5 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 6 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 5 6 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 4 5 6 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 5) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 5) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 6) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 5) (k := 6) (l := 9)
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

theorem fin15Anchored_strongSet_iff_mask01137 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 4, 5, 6, 10} ↔
      Fin15AnchoredStrongQuad chi 0 4 5 6 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 5 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 6 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 5 6 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 4 5 6 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 5) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 5) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 6) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 5) (k := 6) (l := 10)
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

theorem fin15Anchored_strongSet_iff_mask02161 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 4, 5, 6, 11} ↔
      Fin15AnchoredStrongQuad chi 0 4 5 6 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 5 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 6 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 5 6 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 4 5 6 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 5) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 5) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 6) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 5) (k := 6) (l := 11)
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

end ErdosSzekeres

end
