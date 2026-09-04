module

public import ErdosSzekeres.Fin15AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 061. -/

theorem fin15Anchored_strongSet_iff_mask21600 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {5, 6, 10, 12, 14} ↔
      Fin15AnchoredStrongQuad chi 5 6 10 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 6 10 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 6 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 10 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 6 10 12 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 6) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 6) (k := 10) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 6) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 10) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 6) (j := 10) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask25696 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {5, 6, 10, 13, 14} ↔
      Fin15AnchoredStrongQuad chi 5 6 10 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 6 10 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 6 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 10 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 6 10 13 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 6) (k := 10) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 6) (k := 10) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 6) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 10) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 6) (j := 10) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask14432 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {5, 6, 11, 12, 13} ↔
      Fin15AnchoredStrongQuad chi 5 6 11 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 6 11 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 6 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 11 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 6 11 12 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 6) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 6) (k := 11) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 6) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 11) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 6) (j := 11) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask22624 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {5, 6, 11, 12, 14} ↔
      Fin15AnchoredStrongQuad chi 5 6 11 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 6 11 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 6 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 11 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 6 11 12 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 6) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 6) (k := 11) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 6) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 11) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 6) (j := 11) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask28768 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {5, 6, 12, 13, 14} ↔
      Fin15AnchoredStrongQuad chi 5 6 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 6 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 6 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 12 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 6 12 13 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 6) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 6) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 6) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 12) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 6) (j := 12) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask01952 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {5, 7, 8, 9, 10} ↔
      Fin15AnchoredStrongQuad chi 5 7 8 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 8 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 9 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 8 9 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 8 9 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 8) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 8) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask05024 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {5, 7, 8, 9, 12} ↔
      Fin15AnchoredStrongQuad chi 5 7 8 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 8 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 9 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 8 9 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 8 9 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 8) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 8) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask09120 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {5, 7, 8, 9, 13} ↔
      Fin15AnchoredStrongQuad chi 5 7 8 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 8 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 9 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 8 9 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 8 9 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 8) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 9) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 8) (k := 9) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 8) (k := 9) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask17312 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {5, 7, 8, 9, 14} ↔
      Fin15AnchoredStrongQuad chi 5 7 8 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 8 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 9 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 8 9 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 8 9 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 8) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 9) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 8) (k := 9) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 8) (k := 9) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask05536 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {5, 7, 8, 10, 12} ↔
      Fin15AnchoredStrongQuad chi 5 7 8 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 8 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 10 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 8 10 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 8 10 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 8) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 8) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask09632 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {5, 7, 8, 10, 13} ↔
      Fin15AnchoredStrongQuad chi 5 7 8 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 8 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 10 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 8 10 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 8 10 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 8) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 10) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 8) (k := 10) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 8) (k := 10) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask17824 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {5, 7, 8, 10, 14} ↔
      Fin15AnchoredStrongQuad chi 5 7 8 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 8 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 10 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 8 10 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 8 10 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 8) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 10) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 8) (k := 10) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 8) (k := 10) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask12704 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {5, 7, 8, 12, 13} ↔
      Fin15AnchoredStrongQuad chi 5 7 8 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 8 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 8 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 8 12 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 8) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 8) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 8) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask20896 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {5, 7, 8, 12, 14} ↔
      Fin15AnchoredStrongQuad chi 5 7 8 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 8 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 8 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 8 12 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 8) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 8) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 8) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask24992 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {5, 7, 8, 13, 14} ↔
      Fin15AnchoredStrongQuad chi 5 7 8 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 8 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 8 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 8 13 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 8) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 8) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 8) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 8) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask03744 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {5, 7, 9, 10, 11} ↔
      Fin15AnchoredStrongQuad chi 5 7 9 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 9 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 10 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 9 10 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 9 10 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 9) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 9) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask05792 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {5, 7, 9, 10, 12} ↔
      Fin15AnchoredStrongQuad chi 5 7 9 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 9 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 10 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 9 10 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 9 10 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 9) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 9) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask09888 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {5, 7, 9, 10, 13} ↔
      Fin15AnchoredStrongQuad chi 5 7 9 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 9 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 10 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 9 10 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 9 10 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 9) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 10) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 9) (k := 10) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 9) (k := 10) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask18080 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {5, 7, 9, 10, 14} ↔
      Fin15AnchoredStrongQuad chi 5 7 9 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 9 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 10 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 9 10 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 9 10 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 9) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 10) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 9) (k := 10) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 9) (k := 10) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask06816 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {5, 7, 9, 11, 12} ↔
      Fin15AnchoredStrongQuad chi 5 7 9 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 9 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 11 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 9 11 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 9 11 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 9) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 9) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask10912 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {5, 7, 9, 11, 13} ↔
      Fin15AnchoredStrongQuad chi 5 7 9 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 9 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 11 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 9 11 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 9 11 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 9) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 11) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 9) (k := 11) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 9) (k := 11) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask19104 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {5, 7, 9, 11, 14} ↔
      Fin15AnchoredStrongQuad chi 5 7 9 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 9 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 11 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 9 11 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 9 11 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 9) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 11) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 9) (k := 11) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 9) (k := 11) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask12960 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {5, 7, 9, 12, 13} ↔
      Fin15AnchoredStrongQuad chi 5 7 9 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 9 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 9 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 9 12 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 9) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 9) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 9) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask21152 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {5, 7, 9, 12, 14} ↔
      Fin15AnchoredStrongQuad chi 5 7 9 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 9 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 9 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 9 12 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 9) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 9) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 9) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask25248 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {5, 7, 9, 13, 14} ↔
      Fin15AnchoredStrongQuad chi 5 7 9 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 9 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 9 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 9 13 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 9) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 9) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 9) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 9) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask07328 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {5, 7, 10, 11, 12} ↔
      Fin15AnchoredStrongQuad chi 5 7 10 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 10 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 11 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 10 11 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 10 11 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 10) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 10) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask11424 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {5, 7, 10, 11, 13} ↔
      Fin15AnchoredStrongQuad chi 5 7 10 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 10 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 11 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 10 11 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 10 11 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 10) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 11) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 10) (k := 11) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 10) (k := 11) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask19616 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {5, 7, 10, 11, 14} ↔
      Fin15AnchoredStrongQuad chi 5 7 10 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 10 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 11 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 10 11 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 10 11 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 10) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 11) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 10) (k := 11) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 10) (k := 11) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask13472 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {5, 7, 10, 12, 13} ↔
      Fin15AnchoredStrongQuad chi 5 7 10 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 10 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 10 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 10 12 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 10) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 10) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 10) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask21664 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {5, 7, 10, 12, 14} ↔
      Fin15AnchoredStrongQuad chi 5 7 10 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 10 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 10 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 10 12 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 10) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 10) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 10) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask25760 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {5, 7, 10, 13, 14} ↔
      Fin15AnchoredStrongQuad chi 5 7 10 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 10 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 10 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 10 13 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 10) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 10) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 10) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 10) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask14496 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {5, 7, 11, 12, 13} ↔
      Fin15AnchoredStrongQuad chi 5 7 11 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 11 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 11 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 11 12 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 11) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 11) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 11) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask22688 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {5, 7, 11, 12, 14} ↔
      Fin15AnchoredStrongQuad chi 5 7 11 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 11 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 11 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 11 12 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 11) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 11) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 11) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask26784 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {5, 7, 11, 13, 14} ↔
      Fin15AnchoredStrongQuad chi 5 7 11 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 11 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 11 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 11 13 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 11) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 11) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 11) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 11) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask28832 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {5, 7, 12, 13, 14} ↔
      Fin15AnchoredStrongQuad chi 5 7 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 7 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 12 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 12 13 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 7) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 12) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 12) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask05920 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {5, 8, 9, 10, 12} ↔
      Fin15AnchoredStrongQuad chi 5 8 9 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 8 9 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 8 10 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 9 10 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 8 9 10 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 8) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 8) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 8) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 9) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 8) (j := 9) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask10016 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {5, 8, 9, 10, 13} ↔
      Fin15AnchoredStrongQuad chi 5 8 9 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 8 9 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 8 10 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 9 10 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 8 9 10 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 8) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 8) (k := 9) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 8) (k := 10) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 9) (k := 10) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 8) (j := 9) (k := 10) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask18208 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {5, 8, 9, 10, 14} ↔
      Fin15AnchoredStrongQuad chi 5 8 9 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 8 9 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 8 10 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 9 10 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 8 9 10 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 8) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 8) (k := 9) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 8) (k := 10) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 9) (k := 10) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 8) (j := 9) (k := 10) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask13088 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {5, 8, 9, 12, 13} ↔
      Fin15AnchoredStrongQuad chi 5 8 9 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 8 9 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 8 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 9 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 8 9 12 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 8) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 8) (k := 9) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 8) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 9) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 8) (j := 9) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask21280 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {5, 8, 9, 12, 14} ↔
      Fin15AnchoredStrongQuad chi 5 8 9 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 8 9 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 8 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 5 9 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 8 9 12 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 8) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 8) (k := 9) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 8) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 5) (j := 9) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 8) (j := 9) (k := 12) (l := 14)
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
