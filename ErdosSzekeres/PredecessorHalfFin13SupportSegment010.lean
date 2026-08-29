module

public import ErdosSzekeres.PredecessorHalfFin13Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 010. -/

theorem predecessorHalfFin13_strongSet_iff_mask6468 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 6, 8, 11, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 6 8 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 8 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 8 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 6 8 11 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 8) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 8) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 6) (j := 8) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask3652 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 6, 9, 10, 11} ↔
      PredecessorHalfFin13StrongQuad chi 2 6 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 9 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 10 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 9 10 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 6 9 10 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 9) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 6) (j := 9) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask5700 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 6, 9, 10, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 6 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 9 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 9 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 6 9 10 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 9) (k := 10) (l := 12)
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

theorem predecessorHalfFin13_strongSet_iff_mask6724 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 6, 9, 11, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 6 9 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 9 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 9 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 6 9 11 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 9) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 6) (j := 9) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask7236 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 6, 10, 11, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 6 10 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 10 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 6 10 11 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 10) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 6) (j := 10) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask1924 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 7, 8, 9, 10} ↔
      PredecessorHalfFin13StrongQuad chi 2 7 8 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 7 8 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 7 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 8 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 7 8 9 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 8) (k := 9) (l := 10)
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

theorem predecessorHalfFin13_strongSet_iff_mask2948 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 7, 8, 9, 11} ↔
      PredecessorHalfFin13StrongQuad chi 2 7 8 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 7 8 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 7 9 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 8 9 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 7 8 9 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 8) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 8) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 7) (j := 8) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask4996 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 7, 8, 9, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 7 8 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 7 8 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 7 9 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 8 9 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 7 8 9 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 8) (k := 9) (l := 12)
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

theorem predecessorHalfFin13_strongSet_iff_mask3460 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 7, 8, 10, 11} ↔
      PredecessorHalfFin13StrongQuad chi 2 7 8 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 7 8 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 7 10 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 8 10 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 7 8 10 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 8) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 8) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 7) (j := 8) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask5508 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 7, 8, 10, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 7 8 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 7 8 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 7 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 8 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 7 8 10 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 8) (k := 10) (l := 12)
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

theorem predecessorHalfFin13_strongSet_iff_mask6532 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 7, 8, 11, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 7 8 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 7 8 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 7 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 8 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 7 8 11 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 8) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 8) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 7) (j := 8) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask3716 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 7, 9, 10, 11} ↔
      PredecessorHalfFin13StrongQuad chi 2 7 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 7 9 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 7 10 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 9 10 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 7 9 10 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 9) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 7) (j := 9) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask5764 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 7, 9, 10, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 7 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 7 9 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 7 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 9 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 7 9 10 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 9) (k := 10) (l := 12)
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

theorem predecessorHalfFin13_strongSet_iff_mask6788 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 7, 9, 11, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 7 9 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 7 9 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 7 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 9 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 7 9 11 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 9) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 7) (j := 9) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask7300 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 7, 10, 11, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 7 10 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 7 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 7 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 10 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 7 10 11 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 10) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 7) (j := 10) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask3844 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 8, 9, 10, 11} ↔
      PredecessorHalfFin13StrongQuad chi 2 8 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 8 9 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 8 10 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 9 10 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 8 9 10 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 8) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 8) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 8) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 9) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 8) (j := 9) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask5892 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 8, 9, 10, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 8 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 8 9 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 8 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 9 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 8 9 10 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 8) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 8) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 8) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 9) (k := 10) (l := 12)
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

theorem predecessorHalfFin13_strongSet_iff_mask6916 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 8, 9, 11, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 8 9 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 8 9 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 8 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 9 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 8 9 11 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 8) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 8) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 8) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 9) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 8) (j := 9) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask7428 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 8, 10, 11, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 8 10 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 8 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 8 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 10 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 8 10 11 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 8) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 8) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 8) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 10) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 8) (j := 10) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask7684 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 9, 10, 11, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 9 10 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 9 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 9 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 10 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 9 10 11 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 9) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 9) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 9) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 10) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 9) (j := 10) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask0248 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 5, 6, 7} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 5 6 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 5 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 6 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 6 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 5 6 7 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 6) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 5) (k := 6) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask0376 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 5, 6, 8} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 5 6 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 5 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 6 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 6 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 5 6 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 6) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 5) (k := 6) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask0632 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 5, 6, 9} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 5 6 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 5 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 6 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 6 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 5 6 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 6) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 5) (k := 6) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask1144 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 5, 6, 10} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 5 6 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 5 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 6 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 6 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 5 6 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 6) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 5) (k := 6) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask2168 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 5, 6, 11} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 5 6 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 5 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 6 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 6 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 5 6 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 6) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 5) (k := 6) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask4216 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 5, 6, 12} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 5 6 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 5 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 6 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 6 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 5 6 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 6) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 5) (k := 6) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask0440 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 5, 7, 8} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 5 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 5 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 7 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 7 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 5 7 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 7) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 5) (k := 7) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask0696 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 5, 7, 9} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 5 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 5 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 7 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 7 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 5 7 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 7) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 5) (k := 7) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask1208 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 5, 7, 10} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 5 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 5 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 7 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 7 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 5 7 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 7) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 5) (k := 7) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask2232 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 5, 7, 11} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 5 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 5 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 7 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 7 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 5 7 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 7) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 5) (k := 7) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask4280 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 5, 7, 12} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 5 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 5 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 7 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 7 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 5 7 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 7) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 5) (k := 7) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask0824 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 5, 8, 9} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 5 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 5 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 8 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 8 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 5 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 5) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask1336 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 5, 8, 10} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 5 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 5 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 8 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 8 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 5 8 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 5) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask2360 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 5, 8, 11} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 5 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 5 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 8 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 8 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 5 8 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 8) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 8) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 5) (k := 8) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask4408 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 5, 8, 12} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 5 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 5 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 8 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 8 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 5 8 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 5) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask1592 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 5, 9, 10} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 5 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 5 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 5 9 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 5) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask2616 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 5, 9, 11} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 5 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 5 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 9 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 9 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 5 9 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 5) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask4664 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 5, 9, 12} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 5 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 5 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 9 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 9 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 5 9 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 5) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask3128 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 5, 10, 11} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 5 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 5 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 10 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 10 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 5 10 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 5) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask5176 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {3, 4, 5, 10, 12} ↔
      PredecessorHalfFin13StrongQuad chi 3 4 5 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 5 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 4 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 4 5 10 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 4) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 4) (j := 5) (k := 10) (l := 12)
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
