module

public import ErdosSzekeres.PredecessorHalfFin13Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 005. -/

theorem predecessorHalfFin13_strongSet_iff_mask5313 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {0, 6, 7, 10, 12} ↔
      PredecessorHalfFin13StrongQuad chi 0 6 7 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 0 6 7 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 0 6 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 0 7 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 6 7 10 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 0) (j := 6) (k := 7) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 0) (j := 6) (k := 7) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 0) (j := 6) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 0) (j := 7) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 6) (j := 7) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask1857 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {0, 6, 8, 9, 10} ↔
      PredecessorHalfFin13StrongQuad chi 0 6 8 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 0 6 8 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 0 6 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 0 8 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 6 8 9 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 0) (j := 6) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 0) (j := 6) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 0) (j := 6) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 0) (j := 8) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 6) (j := 8) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask4929 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {0, 6, 8, 9, 12} ↔
      PredecessorHalfFin13StrongQuad chi 0 6 8 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 0 6 8 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 0 6 9 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 0 8 9 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 6 8 9 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 0) (j := 6) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 0) (j := 6) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 0) (j := 6) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 0) (j := 8) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 6) (j := 8) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask5441 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {0, 6, 8, 10, 12} ↔
      PredecessorHalfFin13StrongQuad chi 0 6 8 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 0 6 8 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 0 6 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 0 8 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 6 8 10 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 0) (j := 6) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 0) (j := 6) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 0) (j := 6) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 0) (j := 8) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 6) (j := 8) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask5697 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {0, 6, 9, 10, 12} ↔
      PredecessorHalfFin13StrongQuad chi 0 6 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 0 6 9 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 0 6 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 0 9 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 6 9 10 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 0) (j := 6) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 0) (j := 6) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 0) (j := 6) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 0) (j := 9) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 6) (j := 9) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask1921 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {0, 7, 8, 9, 10} ↔
      PredecessorHalfFin13StrongQuad chi 0 7 8 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 0 7 8 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 0 7 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 0 8 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 7 8 9 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 0) (j := 7) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 0) (j := 7) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 0) (j := 7) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 0) (j := 8) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 7) (j := 8) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask4993 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {0, 7, 8, 9, 12} ↔
      PredecessorHalfFin13StrongQuad chi 0 7 8 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 0 7 8 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 0 7 9 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 0 8 9 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 7 8 9 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 0) (j := 7) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 0) (j := 7) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 0) (j := 7) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 0) (j := 8) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 7) (j := 8) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask5505 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {0, 7, 8, 10, 12} ↔
      PredecessorHalfFin13StrongQuad chi 0 7 8 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 0 7 8 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 0 7 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 0 8 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 7 8 10 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 0) (j := 7) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 0) (j := 7) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 0) (j := 7) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 0) (j := 8) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 7) (j := 8) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask5761 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {0, 7, 9, 10, 12} ↔
      PredecessorHalfFin13StrongQuad chi 0 7 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 0 7 9 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 0 7 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 0 9 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 7 9 10 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 0) (j := 7) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 0) (j := 7) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 0) (j := 7) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 0) (j := 9) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 7) (j := 9) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask5889 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {0, 8, 9, 10, 12} ↔
      PredecessorHalfFin13StrongQuad chi 0 8 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 0 8 9 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 0 8 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 0 9 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 8 9 10 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 0) (j := 8) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 0) (j := 8) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 0) (j := 8) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 0) (j := 9) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 8) (j := 9) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask0124 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 4, 5, 6} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 4 5 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 4 6 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 5 6 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 5 6 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 5 6 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 5)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 5) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask0188 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 4, 5, 7} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 4 5 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 4 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 5 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 5 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 5 7 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 5)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 5) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask0316 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 4, 5, 8} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 4 5 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 4 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 5 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 5 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 5 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 5)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 5) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask0572 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 4, 5, 9} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 4 5 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 4 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 5 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 5 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 5 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 5)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 5) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask1084 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 4, 5, 10} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 4 5 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 4 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 5 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 5 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 5 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 5)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 5) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask2108 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 4, 5, 11} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 4 5 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 4 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 5 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 5 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 5 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 5)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 5) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask4156 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 4, 5, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 4 5 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 4 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 5 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 5 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 5 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 5)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 5) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask0220 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 4, 6, 7} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 4 6 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 4 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 6 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 6 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 6 7 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 6) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask0348 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 4, 6, 8} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 4 6 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 4 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 6 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 6 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 6 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 6) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask0604 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 4, 6, 9} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 4 6 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 4 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 6 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 6 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 6 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 6) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask1116 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 4, 6, 10} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 4 6 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 4 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 6 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 6 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 6 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 6) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask2140 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 4, 6, 11} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 4 6 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 4 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 6 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 6 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 6 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 6) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask4188 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 4, 6, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 4 6 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 4 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 6 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 6 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 6 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 6) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask0412 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 4, 7, 8} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 4 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 4 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 7 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 7 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 7 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 7) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask0668 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 4, 7, 9} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 4 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 4 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 7 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 7 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 7 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 7) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask1180 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 4, 7, 10} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 4 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 4 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 7 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 7 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 7 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 7) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask2204 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 4, 7, 11} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 4 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 4 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 7 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 7 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 7 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 7) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask4252 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 4, 7, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 4 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 4 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 7 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 7 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 7 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 7) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask0796 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 4, 8, 9} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 4 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 4 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 8 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 8 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask1308 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 4, 8, 10} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 4 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 4 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 8 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 8 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 8 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask2332 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 4, 8, 11} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 4 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 4 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 8 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 8 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 8 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 8) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 8) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 8) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask4380 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 4, 8, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 4 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 4 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 8 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 8 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 8 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask1564 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 4, 9, 10} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 4 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 4 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 9 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask2588 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 4, 9, 11} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 4 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 4 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 9 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 9 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 9 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask4636 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 4, 9, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 4 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 4 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 9 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 9 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 9 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask3100 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 4, 10, 11} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 4 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 4 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 10 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 10 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 10 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask5148 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 4, 10, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 4 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 4 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 10 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask6172 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 4, 11, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 4 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 4 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 4 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 11 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 4) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask0236 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 5, 6, 7} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 5 6 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 5 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 6 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 5 6 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 6 7 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 6) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 6) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask0364 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 5, 6, 8} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 5 6 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 5 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 6 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 5 6 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 6 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 6) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 6) (l := 8)
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
