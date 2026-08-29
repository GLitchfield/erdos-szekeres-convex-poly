module

public import ErdosSzekeres.PredecessorHalfFin13Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 008. -/

theorem predecessorHalfFin13_strongSet_iff_mask0852 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 4, 6, 8, 9} ↔
      PredecessorHalfFin13StrongQuad chi 2 4 6 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 6 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 8 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 8 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 6 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 6) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 6) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 8) (l := 9)
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

theorem predecessorHalfFin13_strongSet_iff_mask1364 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 4, 6, 8, 10} ↔
      PredecessorHalfFin13StrongQuad chi 2 4 6 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 6 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 8 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 8 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 6 8 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 6) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 6) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 8) (l := 10)
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

theorem predecessorHalfFin13_strongSet_iff_mask2388 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 4, 6, 8, 11} ↔
      PredecessorHalfFin13StrongQuad chi 2 4 6 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 6 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 8 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 8 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 6 8 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 6) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 6) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 8) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 8) (l := 11)
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

theorem predecessorHalfFin13_strongSet_iff_mask4436 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 4, 6, 8, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 4 6 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 6 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 8 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 8 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 6 8 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 6) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 6) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 8) (l := 12)
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

theorem predecessorHalfFin13_strongSet_iff_mask1620 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 4, 6, 9, 10} ↔
      PredecessorHalfFin13StrongQuad chi 2 4 6 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 6 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 6 9 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 6) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 6) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 9) (l := 10)
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

theorem predecessorHalfFin13_strongSet_iff_mask2644 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 4, 6, 9, 11} ↔
      PredecessorHalfFin13StrongQuad chi 2 4 6 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 6 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 9 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 9 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 6 9 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 6) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 6) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 9) (l := 11)
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

theorem predecessorHalfFin13_strongSet_iff_mask4692 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 4, 6, 9, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 4 6 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 6 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 9 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 9 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 6 9 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 6) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 6) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 9) (l := 12)
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

theorem predecessorHalfFin13_strongSet_iff_mask3156 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 4, 6, 10, 11} ↔
      PredecessorHalfFin13StrongQuad chi 2 4 6 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 6 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 10 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 10 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 6 10 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 6) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 6) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 10) (l := 11)
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

theorem predecessorHalfFin13_strongSet_iff_mask5204 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 4, 6, 10, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 4 6 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 6 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 6 10 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 6) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 6) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 10) (l := 12)
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

theorem predecessorHalfFin13_strongSet_iff_mask6228 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 4, 6, 11, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 4 6 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 6 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 6 11 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 6) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 6) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 11) (l := 12)
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

theorem predecessorHalfFin13_strongSet_iff_mask0916 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 4, 7, 8, 9} ↔
      PredecessorHalfFin13StrongQuad chi 2 4 7 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 7 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 8 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 7 8 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 7 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 7) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 7) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 8) (l := 9)
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

theorem predecessorHalfFin13_strongSet_iff_mask1428 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 4, 7, 8, 10} ↔
      PredecessorHalfFin13StrongQuad chi 2 4 7 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 7 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 8 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 7 8 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 7 8 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 7) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 7) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 8) (l := 10)
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

theorem predecessorHalfFin13_strongSet_iff_mask2452 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 4, 7, 8, 11} ↔
      PredecessorHalfFin13StrongQuad chi 2 4 7 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 7 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 8 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 7 8 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 7 8 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 7) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 7) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 8) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 8) (l := 11)
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

theorem predecessorHalfFin13_strongSet_iff_mask4500 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 4, 7, 8, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 4 7 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 7 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 8 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 7 8 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 7 8 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 7) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 7) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 8) (l := 12)
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

theorem predecessorHalfFin13_strongSet_iff_mask1684 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 4, 7, 9, 10} ↔
      PredecessorHalfFin13StrongQuad chi 2 4 7 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 7 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 7 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 7 9 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 7) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 7) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 9) (l := 10)
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

theorem predecessorHalfFin13_strongSet_iff_mask2708 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 4, 7, 9, 11} ↔
      PredecessorHalfFin13StrongQuad chi 2 4 7 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 7 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 9 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 7 9 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 7 9 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 7) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 7) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 9) (l := 11)
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

theorem predecessorHalfFin13_strongSet_iff_mask4756 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 4, 7, 9, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 4 7 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 7 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 9 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 7 9 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 7 9 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 7) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 7) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 9) (l := 12)
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

theorem predecessorHalfFin13_strongSet_iff_mask3220 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 4, 7, 10, 11} ↔
      PredecessorHalfFin13StrongQuad chi 2 4 7 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 7 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 10 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 7 10 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 7 10 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 7) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 7) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 10) (l := 11)
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

theorem predecessorHalfFin13_strongSet_iff_mask5268 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 4, 7, 10, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 4 7 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 7 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 7 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 7 10 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 7) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 7) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 10) (l := 12)
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

theorem predecessorHalfFin13_strongSet_iff_mask6292 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 4, 7, 11, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 4 7 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 7 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 7 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 7 11 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 7) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 7) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 11) (l := 12)
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

theorem predecessorHalfFin13_strongSet_iff_mask1812 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 4, 8, 9, 10} ↔
      PredecessorHalfFin13StrongQuad chi 2 4 8 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 8 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 8 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 8 9 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 8) (k := 9) (l := 10)
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

theorem predecessorHalfFin13_strongSet_iff_mask2836 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 4, 8, 9, 11} ↔
      PredecessorHalfFin13StrongQuad chi 2 4 8 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 8 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 9 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 8 9 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 8 9 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 8) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 8) (k := 9) (l := 11)
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

theorem predecessorHalfFin13_strongSet_iff_mask4884 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 4, 8, 9, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 4 8 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 8 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 9 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 8 9 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 8 9 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 8) (k := 9) (l := 12)
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

theorem predecessorHalfFin13_strongSet_iff_mask3348 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 4, 8, 10, 11} ↔
      PredecessorHalfFin13StrongQuad chi 2 4 8 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 8 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 10 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 8 10 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 8 10 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 8) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 8) (k := 10) (l := 11)
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

theorem predecessorHalfFin13_strongSet_iff_mask5396 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 4, 8, 10, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 4 8 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 8 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 8 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 8 10 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 8) (k := 10) (l := 12)
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

theorem predecessorHalfFin13_strongSet_iff_mask6420 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 4, 8, 11, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 4 8 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 8 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 8 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 8 11 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 8) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 8) (k := 11) (l := 12)
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

theorem predecessorHalfFin13_strongSet_iff_mask3604 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 4, 9, 10, 11} ↔
      PredecessorHalfFin13StrongQuad chi 2 4 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 9 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 10 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 9 10 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 9 10 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 9) (k := 10) (l := 11)
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

theorem predecessorHalfFin13_strongSet_iff_mask5652 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 4, 9, 10, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 4 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 9 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 9 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 9 10 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 9) (k := 10) (l := 12)
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

theorem predecessorHalfFin13_strongSet_iff_mask6676 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 4, 9, 11, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 4 9 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 9 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 9 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 9 11 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 9) (k := 11) (l := 12)
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

theorem predecessorHalfFin13_strongSet_iff_mask7188 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 4, 10, 11, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 4 10 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 10 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 10 11 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 10) (k := 11) (l := 12)
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

theorem predecessorHalfFin13_strongSet_iff_mask0484 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 5, 6, 7, 8} ↔
      PredecessorHalfFin13StrongQuad chi 2 5 6 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 5 6 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 5 7 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 7 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 5 6 7 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 6) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 6) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 7) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 7) (l := 8)
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

theorem predecessorHalfFin13_strongSet_iff_mask0740 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 5, 6, 7, 9} ↔
      PredecessorHalfFin13StrongQuad chi 2 5 6 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 5 6 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 5 7 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 7 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 5 6 7 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 6) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 6) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 7) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 7) (l := 9)
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

theorem predecessorHalfFin13_strongSet_iff_mask1252 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 5, 6, 7, 10} ↔
      PredecessorHalfFin13StrongQuad chi 2 5 6 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 5 6 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 5 7 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 7 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 5 6 7 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 6) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 6) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 7) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 7) (l := 10)
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

theorem predecessorHalfFin13_strongSet_iff_mask2276 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 5, 6, 7, 11} ↔
      PredecessorHalfFin13StrongQuad chi 2 5 6 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 5 6 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 5 7 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 7 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 5 6 7 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 6) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 6) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 7) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 7) (l := 11)
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

theorem predecessorHalfFin13_strongSet_iff_mask4324 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 5, 6, 7, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 5 6 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 5 6 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 5 7 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 7 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 5 6 7 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 6) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 6) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 7) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 7) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 5) (j := 6) (k := 7) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask0868 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 5, 6, 8, 9} ↔
      PredecessorHalfFin13StrongQuad chi 2 5 6 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 5 6 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 5 8 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 8 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 5 6 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 6) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 6) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 5) (j := 6) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask1380 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 5, 6, 8, 10} ↔
      PredecessorHalfFin13StrongQuad chi 2 5 6 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 5 6 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 5 8 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 8 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 5 6 8 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 6) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 6) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 5) (j := 6) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask2404 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 5, 6, 8, 11} ↔
      PredecessorHalfFin13StrongQuad chi 2 5 6 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 5 6 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 5 8 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 8 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 5 6 8 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 6) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 6) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 8) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 8) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 5) (j := 6) (k := 8) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask4452 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 5, 6, 8, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 5 6 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 5 6 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 5 8 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 8 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 5 6 8 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 6) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 6) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 5) (j := 6) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask1636 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 5, 6, 9, 10} ↔
      PredecessorHalfFin13StrongQuad chi 2 5 6 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 5 6 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 5 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 5 6 9 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 6) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 6) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 5) (j := 6) (k := 9) (l := 10)
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
