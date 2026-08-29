module

public import ErdosSzekeres.PredecessorHalfFin13Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 006. -/

theorem predecessorHalfFin13_strongSet_iff_mask0620 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 5, 6, 9} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 5 6 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 5 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 6 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 5 6 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 6 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 6) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 6) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask1132 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 5, 6, 10} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 5 6 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 5 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 6 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 5 6 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 6 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 6) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 6) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask2156 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 5, 6, 11} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 5 6 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 5 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 6 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 5 6 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 6 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 6) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 6) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask4204 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 5, 6, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 5 6 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 5 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 6 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 5 6 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 6 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 6)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 6) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 6) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask0428 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 5, 7, 8} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 5 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 5 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 7 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 5 7 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 7 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 7) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 7) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask0684 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 5, 7, 9} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 5 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 5 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 7 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 5 7 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 7 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 7) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 7) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask1196 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 5, 7, 10} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 5 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 5 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 7 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 5 7 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 7 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 7) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 7) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask2220 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 5, 7, 11} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 5 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 5 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 7 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 5 7 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 7 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 7) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 7) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask4268 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 5, 7, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 5 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 5 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 7 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 5 7 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 7 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 7) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 7) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask0812 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 5, 8, 9} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 5 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 5 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 8 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 5 8 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask1324 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 5, 8, 10} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 5 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 5 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 8 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 5 8 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 8 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask2348 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 5, 8, 11} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 5 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 5 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 8 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 5 8 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 8 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 8) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 8) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 8) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask4396 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 5, 8, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 5 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 5 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 8 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 5 8 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 8 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask1580 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 5, 9, 10} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 5 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 5 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 5 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 9 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask2604 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 5, 9, 11} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 5 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 5 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 9 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 5 9 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 9 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask4652 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 5, 9, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 5 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 5 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 9 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 5 9 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 9 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask3116 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 5, 10, 11} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 5 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 5 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 10 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 5 10 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 10 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask5164 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 5, 10, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 5 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 5 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 5 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 10 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask6188 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 5, 11, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 5 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 5 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 5 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 5 11 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 5) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 5) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask0460 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 6, 7, 8} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 6 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 6 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 7 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 7 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 6 7 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 7) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 6) (k := 7) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask0716 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 6, 7, 9} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 6 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 6 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 7 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 7 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 6 7 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 7) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 6) (k := 7) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask1228 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 6, 7, 10} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 6 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 6 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 7 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 7 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 6 7 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 7) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 6) (k := 7) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask2252 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 6, 7, 11} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 6 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 6 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 7 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 7 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 6 7 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 7) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 6) (k := 7) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask4300 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 6, 7, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 6 7 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 6 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 7 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 7 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 6 7 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 7)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 7) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 6) (k := 7) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask0844 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 6, 8, 9} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 6 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 6 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 8 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 8 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 6 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 6) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask1356 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 6, 8, 10} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 6 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 6 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 8 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 8 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 6 8 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 6) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask2380 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 6, 8, 11} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 6 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 6 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 8 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 8 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 6 8 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 8) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 8) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 6) (k := 8) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask4428 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 6, 8, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 6 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 6 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 8 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 8 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 6 8 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 6) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask1612 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 6, 9, 10} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 6 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 6 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 6 9 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 6) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask2636 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 6, 9, 11} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 6 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 6 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 9 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 9 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 6 9 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 6) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask4684 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 6, 9, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 6 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 6 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 9 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 9 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 6 9 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 6) (k := 9) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask3148 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 6, 10, 11} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 6 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 6 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 10 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 10 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 6 10 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 6) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask5196 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 6, 10, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 6 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 6 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 10 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 6 10 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 6) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask6220 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 6, 11, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 6 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 6 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 6 11 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 6 11 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 6) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 6) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask0908 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 7, 8, 9} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 7 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 7 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 8 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 7 8 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 7 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 7) (k := 8) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask1420 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 7, 8, 10} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 7 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 7 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 8 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 7 8 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 7 8 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 7) (k := 8) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask2444 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 7, 8, 11} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 7 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 7 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 8 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 7 8 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 7 8 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 8) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 8) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 7) (k := 8) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask4492 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 7, 8, 12} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 7 8 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 7 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 8 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 7 8 12 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 7 8 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 8)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 7) (k := 8) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask1676 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 7, 9, 10} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 7 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 7 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 7 9 10 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 7 9 10 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 7) (k := 9) (l := 10)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_strongSet_iff_mask2700 (chi : TripleColoring 13) :
    IsStrongPolygonSet chi {2, 3, 7, 9, 11} ↔
      PredecessorHalfFin13StrongQuad chi 2 3 7 9 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 7 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 3 9 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 2 7 9 11 (by decide) (by decide) (by decide) ∧
      PredecessorHalfFin13StrongQuad chi 3 7 9 11 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 9)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 3) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 2) (j := 7) (k := 9) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [PredecessorHalfFin13StrongQuad] using h
        (i := 3) (j := 7) (k := 9) (l := 11)
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
