module

public import ErdosSzekeres.PredecessorHalfFin13Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 011. -/

theorem predecessorHalfFin13_strongSet_iff_mask6200 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 5, 11, 12} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 5 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 5 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 5 11 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 5) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask0472 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 6, 7, 8} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 6 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 6 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 7 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 6 7 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 6 7 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 6) (k := 7) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 6) (k := 7) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask0728 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 6, 7, 9} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 6 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 6 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 7 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 6 7 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 6 7 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 6) (k := 7) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 6) (k := 7) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask1240 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 6, 7, 10} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 6 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 6 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 7 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 6 7 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 6 7 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 6) (k := 7) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 6) (k := 7) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask2264 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 6, 7, 11} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 6 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 6 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 7 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 6 7 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 6 7 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 6) (k := 7) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 6) (k := 7) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask4312 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 6, 7, 12} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 6 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 6 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 7 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 6 7 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 6 7 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 6) (k := 7) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 6) (k := 7) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask0856 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 6, 8, 9} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 6 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 6 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 8 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 6 8 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 6 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 6) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 6) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask1368 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 6, 8, 10} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 6 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 6 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 8 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 6 8 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 6 8 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 6) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 6) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask2392 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 6, 8, 11} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 6 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 6 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 8 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 6 8 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 6 8 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 8) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 6) (k := 8) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 6) (k := 8) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask4440 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 6, 8, 12} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 6 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 6 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 8 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 6 8 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 6 8 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 6) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 6) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask1624 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 6, 9, 10} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 6 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 6 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 6 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 6 9 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 6) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 6) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask2648 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 6, 9, 11} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 6 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 6 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 9 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 6 9 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 6 9 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 6) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 6) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask4696 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 6, 9, 12} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 6 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 6 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 9 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 6 9 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 6 9 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 6) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 6) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask3160 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 6, 10, 11} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 6 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 6 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 10 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 6 10 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 6 10 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 6) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 6) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask5208 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 6, 10, 12} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 6 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 6 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 6 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 6 10 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 6) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 6) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask6232 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 6, 11, 12} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 6 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 6 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 6 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 6 11 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 6) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 6) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask0920 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 7, 8, 9} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 7 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 7 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 8 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 7 8 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 7 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 7) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 7) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask1432 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 7, 8, 10} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 7 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 7 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 8 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 7 8 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 7 8 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 7) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 7) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask2456 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 7, 8, 11} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 7 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 7 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 8 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 7 8 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 7 8 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 8) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 7) (k := 8) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 7) (k := 8) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask4504 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 7, 8, 12} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 7 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 7 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 8 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 7 8 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 7 8 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 7) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 7) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask1688 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 7, 9, 10} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 7 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 7 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 7 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 7 9 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 7) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 7) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask2712 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 7, 9, 11} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 7 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 7 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 9 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 7 9 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 7 9 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 7) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 7) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask4760 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 7, 9, 12} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 7 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 7 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 9 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 7 9 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 7 9 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 7) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 7) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask3224 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 7, 10, 11} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 7 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 7 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 10 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 7 10 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 7 10 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 7) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 7) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask5272 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 7, 10, 12} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 7 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 7 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 7 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 7 10 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 7) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 7) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask6296 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 7, 11, 12} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 7 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 7 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 7 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 7 11 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 7) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 7) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask1816 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 8, 9, 10} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 8 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 8 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 8 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 8 9 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 8) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 8) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask2840 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 8, 9, 11} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 8 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 8 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 9 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 8 9 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 8 9 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 8) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 8) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 8) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask4888 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 8, 9, 12} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 8 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 8 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 9 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 8 9 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 8 9 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 8) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 8) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask3352 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 8, 10, 11} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 8 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 8 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 10 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 8 10 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 8 10 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 8) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 8) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 8) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask5400 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 8, 10, 12} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 8 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 8 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 8 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 8 10 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 8) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 8) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask6424 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 8, 11, 12} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 8 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 8 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 8 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 8 11 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 8) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 8) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 8) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask3608 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 9, 10, 11} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 9 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 10 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 9 10 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 9 10 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 9) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 9) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask5656 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 9, 10, 12} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 9 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 9 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 9 10 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 9) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 9) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask6680 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 9, 11, 12} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 9 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 9 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 9 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 9 11 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 9) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 9) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask7192 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 10, 11, 12} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 10 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 10 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 10 11 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 10) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 10) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask0488 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 5, 6, 7, 8} ↔
      PredecessorHalfFin13StrongQuad chi 3 5 6 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 6 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 7 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 6 7 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 5 6 7 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 6) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 6) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 7) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 6) (k := 7) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 5) (j := 6) (k := 7) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask0744 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 5, 6, 7, 9} ↔
      PredecessorHalfFin13StrongQuad chi 3 5 6 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 6 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 7 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 6 7 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 5 6 7 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 6) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 6) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 7) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 6) (k := 7) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 5) (j := 6) (k := 7) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask1256 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 5, 6, 7, 10} ↔
      PredecessorHalfFin13StrongQuad chi 3 5 6 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 6 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 7 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 6 7 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 5 6 7 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 6) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 6) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 7) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 6) (k := 7) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 5) (j := 6) (k := 7) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask2280 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 5, 6, 7, 11} ↔
      PredecessorHalfFin13StrongQuad chi 3 5 6 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 6 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 7 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 6 7 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 5 6 7 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 6) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 6) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 7) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 6) (k := 7) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 5) (j := 6) (k := 7) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

end ErdosSzekeres

end
