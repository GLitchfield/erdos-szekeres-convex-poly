module

public import ErdosSzekeres.Fin15AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 007. -/

theorem fin15Anchored_strongSet_iff_mask02077 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 2, 3, 4, 11} ↔
      Fin15AnchoredStrongQuad chi 0 2 3 4 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 3 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 4 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 2 3 4 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 4)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 4) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask04125 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 2, 3, 4, 12} ↔
      Fin15AnchoredStrongQuad chi 0 2 3 4 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 3 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 4 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 2 3 4 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 4)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 4) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask08221 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 2, 3, 4, 13} ↔
      Fin15AnchoredStrongQuad chi 0 2 3 4 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 3 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 4 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 2 3 4 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 4)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 4) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask16413 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 2, 3, 4, 14} ↔
      Fin15AnchoredStrongQuad chi 0 2 3 4 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 3 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 4 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 2 3 4 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 4)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 4) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask00109 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 2, 3, 5, 6} ↔
      Fin15AnchoredStrongQuad chi 0 2 3 5 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 3 6 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 5 6 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 5 6 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 2 3 5 6 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 5)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 5) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 5) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask00173 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 2, 3, 5, 7} ↔
      Fin15AnchoredStrongQuad chi 0 2 3 5 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 3 7 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 5 7 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 5 7 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 2 3 5 7 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 5)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 5) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 5) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask00301 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 2, 3, 5, 8} ↔
      Fin15AnchoredStrongQuad chi 0 2 3 5 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 3 8 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 5 8 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 5 8 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 2 3 5 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 5)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 5) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 5) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask00557 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 2, 3, 5, 9} ↔
      Fin15AnchoredStrongQuad chi 0 2 3 5 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 3 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 5 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 5 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 2 3 5 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 5)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 5) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 5) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask01069 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 2, 3, 5, 10} ↔
      Fin15AnchoredStrongQuad chi 0 2 3 5 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 3 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 5 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 5 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 2 3 5 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 5)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 5) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 5) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask02093 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 2, 3, 5, 11} ↔
      Fin15AnchoredStrongQuad chi 0 2 3 5 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 3 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 5 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 5 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 2 3 5 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 5)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 5) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 5) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask04141 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 2, 3, 5, 12} ↔
      Fin15AnchoredStrongQuad chi 0 2 3 5 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 3 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 5 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 5 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 2 3 5 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 5)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 5) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 5) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask08237 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 2, 3, 5, 13} ↔
      Fin15AnchoredStrongQuad chi 0 2 3 5 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 3 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 5 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 5 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 2 3 5 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 5)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 5) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 5) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask16429 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 2, 3, 5, 14} ↔
      Fin15AnchoredStrongQuad chi 0 2 3 5 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 3 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 5 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 5 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 2 3 5 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 5)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 5) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 5) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask00205 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 2, 3, 6, 7} ↔
      Fin15AnchoredStrongQuad chi 0 2 3 6 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 3 7 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 6 7 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 6 7 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 2 3 6 7 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 6) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 6) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask00333 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 2, 3, 6, 8} ↔
      Fin15AnchoredStrongQuad chi 0 2 3 6 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 3 8 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 6 8 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 6 8 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 2 3 6 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 6) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 6) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask00589 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 2, 3, 6, 9} ↔
      Fin15AnchoredStrongQuad chi 0 2 3 6 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 3 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 6 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 6 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 2 3 6 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 6) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 6) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask01101 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 2, 3, 6, 10} ↔
      Fin15AnchoredStrongQuad chi 0 2 3 6 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 3 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 6 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 6 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 2 3 6 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 6) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 6) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask02125 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 2, 3, 6, 11} ↔
      Fin15AnchoredStrongQuad chi 0 2 3 6 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 3 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 6 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 6 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 2 3 6 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 6) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 6) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask04173 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 2, 3, 6, 12} ↔
      Fin15AnchoredStrongQuad chi 0 2 3 6 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 3 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 6 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 6 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 2 3 6 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 6) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 6) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask08269 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 2, 3, 6, 13} ↔
      Fin15AnchoredStrongQuad chi 0 2 3 6 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 3 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 6 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 6 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 2 3 6 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 6) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 6) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask16461 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 2, 3, 6, 14} ↔
      Fin15AnchoredStrongQuad chi 0 2 3 6 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 3 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 6 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 6 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 2 3 6 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 6) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 6) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask00397 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 2, 3, 7, 8} ↔
      Fin15AnchoredStrongQuad chi 0 2 3 7 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 3 8 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 7 8 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 7 8 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 2 3 7 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 7) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 7) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask00653 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 2, 3, 7, 9} ↔
      Fin15AnchoredStrongQuad chi 0 2 3 7 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 3 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 7 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 7 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 2 3 7 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 7) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 7) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask01165 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 2, 3, 7, 10} ↔
      Fin15AnchoredStrongQuad chi 0 2 3 7 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 3 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 7 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 7 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 2 3 7 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 7) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 7) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask02189 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 2, 3, 7, 11} ↔
      Fin15AnchoredStrongQuad chi 0 2 3 7 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 3 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 7 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 7 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 2 3 7 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 7) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 7) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask04237 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 2, 3, 7, 12} ↔
      Fin15AnchoredStrongQuad chi 0 2 3 7 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 3 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 7 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 7 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 2 3 7 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 7) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 7) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask08333 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 2, 3, 7, 13} ↔
      Fin15AnchoredStrongQuad chi 0 2 3 7 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 3 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 7 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 7 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 2 3 7 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 7) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 7) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask16525 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 2, 3, 7, 14} ↔
      Fin15AnchoredStrongQuad chi 0 2 3 7 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 3 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 7 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 7 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 2 3 7 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 7) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 7) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask00781 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 2, 3, 8, 9} ↔
      Fin15AnchoredStrongQuad chi 0 2 3 8 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 3 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 8 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 8 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 2 3 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 2) (j := 3) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask01293 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 2, 3, 8, 10} ↔
      Fin15AnchoredStrongQuad chi 0 2 3 8 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 3 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 8 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 8 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 2 3 8 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 2) (j := 3) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask04365 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 2, 3, 8, 12} ↔
      Fin15AnchoredStrongQuad chi 0 2 3 8 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 3 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 8 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 8 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 2 3 8 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 2) (j := 3) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask08461 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 2, 3, 8, 13} ↔
      Fin15AnchoredStrongQuad chi 0 2 3 8 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 3 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 8 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 8 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 2 3 8 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 8) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 8) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 2) (j := 3) (k := 8) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask16653 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 2, 3, 8, 14} ↔
      Fin15AnchoredStrongQuad chi 0 2 3 8 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 3 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 8 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 8 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 2 3 8 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 8) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 8) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 2) (j := 3) (k := 8) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask01549 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 2, 3, 9, 10} ↔
      Fin15AnchoredStrongQuad chi 0 2 3 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 3 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 9 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 9 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 2 3 9 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 2) (j := 3) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask02573 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 2, 3, 9, 11} ↔
      Fin15AnchoredStrongQuad chi 0 2 3 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 3 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 9 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 9 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 2 3 9 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 2) (j := 3) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask04621 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 2, 3, 9, 12} ↔
      Fin15AnchoredStrongQuad chi 0 2 3 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 3 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 9 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 9 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 2 3 9 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 2) (j := 3) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask08717 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 2, 3, 9, 13} ↔
      Fin15AnchoredStrongQuad chi 0 2 3 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 3 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 9 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 9 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 2 3 9 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 9) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 9) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 2) (j := 3) (k := 9) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask16909 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 2, 3, 9, 14} ↔
      Fin15AnchoredStrongQuad chi 0 2 3 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 3 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 9 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 9 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 2 3 9 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 9) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 9) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 2) (j := 3) (k := 9) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask03085 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 2, 3, 10, 11} ↔
      Fin15AnchoredStrongQuad chi 0 2 3 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 3 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 10 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 10 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 2 3 10 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 2) (j := 3) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask05133 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 2, 3, 10, 12} ↔
      Fin15AnchoredStrongQuad chi 0 2 3 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 3 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 2 10 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 10 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 2 3 10 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 2) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 2) (j := 3) (k := 10) (l := 12)
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
