module

public import ErdosSzekeres.Fin15AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 012. -/

theorem fin15Anchored_strongSet_iff_mask00121 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 4, 5, 6} ↔
      Fin15AnchoredStrongQuad chi 0 3 4 5 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 6 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 5 6 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 5 6 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 4 5 6 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 5)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 5) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 5) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask00185 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 4, 5, 7} ↔
      Fin15AnchoredStrongQuad chi 0 3 4 5 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 7 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 5 7 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 5 7 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 4 5 7 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 5)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 5) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 5) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask00313 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 4, 5, 8} ↔
      Fin15AnchoredStrongQuad chi 0 3 4 5 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 8 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 5 8 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 5 8 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 4 5 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 5)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 5) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 5) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask00569 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 4, 5, 9} ↔
      Fin15AnchoredStrongQuad chi 0 3 4 5 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 5 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 5 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 4 5 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 5)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 5) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 5) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask01081 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 4, 5, 10} ↔
      Fin15AnchoredStrongQuad chi 0 3 4 5 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 5 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 5 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 4 5 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 5)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 5) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 5) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask02105 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 4, 5, 11} ↔
      Fin15AnchoredStrongQuad chi 0 3 4 5 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 5 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 5 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 4 5 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 5)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 5) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 5) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask04153 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 4, 5, 12} ↔
      Fin15AnchoredStrongQuad chi 0 3 4 5 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 5 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 5 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 4 5 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 5)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 5) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 5) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask08249 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 4, 5, 13} ↔
      Fin15AnchoredStrongQuad chi 0 3 4 5 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 5 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 5 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 4 5 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 5)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 5) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 5) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask16441 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 4, 5, 14} ↔
      Fin15AnchoredStrongQuad chi 0 3 4 5 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 5 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 5 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 4 5 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 5)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 5) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 5) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask00217 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 4, 6, 7} ↔
      Fin15AnchoredStrongQuad chi 0 3 4 6 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 7 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 6 7 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 6 7 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 4 6 7 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 6) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 6) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask00345 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 4, 6, 8} ↔
      Fin15AnchoredStrongQuad chi 0 3 4 6 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 8 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 6 8 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 6 8 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 4 6 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 6) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 6) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask00601 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 4, 6, 9} ↔
      Fin15AnchoredStrongQuad chi 0 3 4 6 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 6 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 6 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 4 6 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 6) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 6) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask01113 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 4, 6, 10} ↔
      Fin15AnchoredStrongQuad chi 0 3 4 6 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 6 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 6 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 4 6 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 6) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 6) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask02137 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 4, 6, 11} ↔
      Fin15AnchoredStrongQuad chi 0 3 4 6 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 6 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 6 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 4 6 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 6) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 6) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask04185 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 4, 6, 12} ↔
      Fin15AnchoredStrongQuad chi 0 3 4 6 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 6 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 6 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 4 6 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 6) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 6) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask08281 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 4, 6, 13} ↔
      Fin15AnchoredStrongQuad chi 0 3 4 6 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 6 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 6 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 4 6 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 6) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 6) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask16473 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 4, 6, 14} ↔
      Fin15AnchoredStrongQuad chi 0 3 4 6 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 6 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 6 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 4 6 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 6) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 6) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask00409 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 4, 7, 8} ↔
      Fin15AnchoredStrongQuad chi 0 3 4 7 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 8 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 7 8 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 7 8 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 4 7 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 7) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 7) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask00665 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 4, 7, 9} ↔
      Fin15AnchoredStrongQuad chi 0 3 4 7 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 7 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 7 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 4 7 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 7) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 7) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask01177 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 4, 7, 10} ↔
      Fin15AnchoredStrongQuad chi 0 3 4 7 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 7 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 7 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 4 7 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 7) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 7) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask02201 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 4, 7, 11} ↔
      Fin15AnchoredStrongQuad chi 0 3 4 7 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 7 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 7 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 4 7 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 7) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 7) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask04249 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 4, 7, 12} ↔
      Fin15AnchoredStrongQuad chi 0 3 4 7 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 7 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 7 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 4 7 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 7) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 7) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask08345 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 4, 7, 13} ↔
      Fin15AnchoredStrongQuad chi 0 3 4 7 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 7 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 7 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 4 7 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 7) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 7) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask16537 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 4, 7, 14} ↔
      Fin15AnchoredStrongQuad chi 0 3 4 7 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 7 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 7 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 4 7 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 7) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 7) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask00793 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 4, 8, 9} ↔
      Fin15AnchoredStrongQuad chi 0 3 4 8 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 8 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 8 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 4 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 4) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask01305 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 4, 8, 10} ↔
      Fin15AnchoredStrongQuad chi 0 3 4 8 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 8 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 8 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 4 8 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 4) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask04377 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 4, 8, 12} ↔
      Fin15AnchoredStrongQuad chi 0 3 4 8 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 8 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 8 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 4 8 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 4) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask08473 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 4, 8, 13} ↔
      Fin15AnchoredStrongQuad chi 0 3 4 8 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 8 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 8 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 4 8 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 8) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 8) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 4) (k := 8) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask16665 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 4, 8, 14} ↔
      Fin15AnchoredStrongQuad chi 0 3 4 8 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 8 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 8 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 4 8 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 8) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 8) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 4) (k := 8) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask01561 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 4, 9, 10} ↔
      Fin15AnchoredStrongQuad chi 0 3 4 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 9 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 9 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 4 9 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 4) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask02585 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 4, 9, 11} ↔
      Fin15AnchoredStrongQuad chi 0 3 4 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 9 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 9 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 4 9 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 4) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask04633 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 4, 9, 12} ↔
      Fin15AnchoredStrongQuad chi 0 3 4 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 9 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 9 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 4 9 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 4) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask08729 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 4, 9, 13} ↔
      Fin15AnchoredStrongQuad chi 0 3 4 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 9 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 9 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 4 9 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 9) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 9) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 4) (k := 9) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask16921 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 4, 9, 14} ↔
      Fin15AnchoredStrongQuad chi 0 3 4 9 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 9 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 9 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 4 9 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 9) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 9) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 4) (k := 9) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask03097 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 4, 10, 11} ↔
      Fin15AnchoredStrongQuad chi 0 3 4 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 10 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 10 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 4 10 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 4) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask05145 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 4, 10, 12} ↔
      Fin15AnchoredStrongQuad chi 0 3 4 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 10 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 10 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 4 10 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 4) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask09241 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 4, 10, 13} ↔
      Fin15AnchoredStrongQuad chi 0 3 4 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 10 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 10 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 4 10 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 10) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 10) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 4) (k := 10) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask17433 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 4, 10, 14} ↔
      Fin15AnchoredStrongQuad chi 0 3 4 10 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 10 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 10 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 4 10 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 10) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 10) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 4) (k := 10) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask06169 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 4, 11, 12} ↔
      Fin15AnchoredStrongQuad chi 0 3 4 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 11 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 11 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 4 11 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 4) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask10265 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {0, 3, 4, 11, 13} ↔
      Fin15AnchoredStrongQuad chi 0 3 4 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 4 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 3 11 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 0 4 11 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 3 4 11 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 4) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 3) (k := 11) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 0) (j := 4) (k := 11) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 3) (j := 4) (k := 11) (l := 13)
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
