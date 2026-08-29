module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSupportSegment002

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 003. -/

theorem synchronizedFiveFanFin11_strongSet_iff_mask0143 (chi : TripleColoring 11) :
    IsStrongPolygonSet chi {0, 1, 2, 3, 7} ↔
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 2 3
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 2 7
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 3 7
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 2 3 7
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 1 2 3 7
        (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 1) (k := 2) (l := 3)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 1) (k := 2) (l := 7)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 1) (k := 3) (l := 7)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 2) (k := 3) (l := 7)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 1) (j := 2) (k := 3) (l := 7)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp))⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11_strongSet_iff_mask0171 (chi : TripleColoring 11) :
    IsStrongPolygonSet chi {0, 1, 3, 5, 7} ↔
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 3 5
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 3 7
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 5 7
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 3 5 7
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 1 3 5 7
        (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 1) (k := 3) (l := 5)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 1) (k := 3) (l := 7)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 1) (k := 5) (l := 7)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 3) (k := 5) (l := 7)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 1) (j := 3) (k := 5) (l := 7)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp))⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11_strongSet_iff_mask0611 (chi : TripleColoring 11) :
    IsStrongPolygonSet chi {0, 1, 5, 6, 9} ↔
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 5 6
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 5 9
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 6 9
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 5 6 9
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 1 5 6 9
        (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 1) (k := 5) (l := 6)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 1) (k := 5) (l := 9)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 1) (k := 6) (l := 9)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 5) (k := 6) (l := 9)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 1) (j := 5) (k := 6) (l := 9)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp))⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11_strongSet_iff_mask0397 (chi : TripleColoring 11) :
    IsStrongPolygonSet chi {0, 2, 3, 7, 8} ↔
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 2 3 7
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 2 3 8
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 2 7 8
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 3 7 8
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 2 3 7 8
        (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 2) (k := 3) (l := 7)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 2) (k := 3) (l := 8)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 2) (k := 7) (l := 8)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 3) (k := 7) (l := 8)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 2) (j := 3) (k := 7) (l := 8)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp))⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11_strongSet_iff_mask0453 (chi : TripleColoring 11) :
    IsStrongPolygonSet chi {0, 2, 6, 7, 8} ↔
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 2 6 7
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 2 6 8
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 2 7 8
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 6 7 8
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 2 6 7 8
        (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 2) (k := 6) (l := 7)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 2) (k := 6) (l := 8)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 2) (k := 7) (l := 8)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 6) (k := 7) (l := 8)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 2) (j := 6) (k := 7) (l := 8)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp))⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11_strongSet_iff_mask1193 (chi : TripleColoring 11) :
    IsStrongPolygonSet chi {0, 3, 5, 7, 10} ↔
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 3 5 7
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 3 5 10
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 3 7 10
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 5 7 10
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 3 5 7 10
        (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 3) (k := 5) (l := 7)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 3) (k := 5) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 3) (k := 7) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 5) (k := 7) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 3) (j := 5) (k := 7) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp))⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11_strongSet_iff_mask0737 (chi : TripleColoring 11) :
    IsStrongPolygonSet chi {0, 5, 6, 7, 9} ↔
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 5 6 7
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 5 6 9
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 5 7 9
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 6 7 9
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 5 6 7 9
        (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 5) (k := 6) (l := 7)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 5) (k := 6) (l := 9)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 5) (k := 7) (l := 9)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 6) (k := 7) (l := 9)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 5) (j := 6) (k := 7) (l := 9)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp))⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11_strongSet_iff_mask0782 (chi : TripleColoring 11) :
    IsStrongPolygonSet chi {1, 2, 3, 8, 9} ↔
      SynchronizedFiveFanFin11SemanticStrongQuad chi 1 2 3 8
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 1 2 3 9
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 1 2 8 9
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 1 3 8 9
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 2 3 8 9
        (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 1) (j := 2) (k := 3) (l := 8)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 1) (j := 2) (k := 3) (l := 9)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 1) (j := 2) (k := 8) (l := 9)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 1) (j := 3) (k := 8) (l := 9)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 2) (j := 3) (k := 8) (l := 9)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp))⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11_strongSet_iff_mask0838 (chi : TripleColoring 11) :
    IsStrongPolygonSet chi {1, 2, 6, 8, 9} ↔
      SynchronizedFiveFanFin11SemanticStrongQuad chi 1 2 6 8
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 1 2 6 9
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 1 2 8 9
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 1 6 8 9
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 2 6 8 9
        (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 1) (j := 2) (k := 6) (l := 8)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 1) (j := 2) (k := 6) (l := 9)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 1) (j := 2) (k := 8) (l := 9)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 1) (j := 6) (k := 8) (l := 9)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 2) (j := 6) (k := 8) (l := 9)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp))⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11_strongSet_iff_mask0714 (chi : TripleColoring 11) :
    IsStrongPolygonSet chi {1, 3, 6, 7, 9} ↔
      SynchronizedFiveFanFin11SemanticStrongQuad chi 1 3 6 7
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 1 3 6 9
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 1 3 7 9
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 1 6 7 9
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 3 6 7 9
        (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 1) (j := 3) (k := 6) (l := 7)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 1) (j := 3) (k := 6) (l := 9)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 1) (j := 3) (k := 7) (l := 9)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 1) (j := 6) (k := 7) (l := 9)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 3) (j := 6) (k := 7) (l := 9)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp))⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11_strongSet_iff_mask1378 (chi : TripleColoring 11) :
    IsStrongPolygonSet chi {1, 5, 6, 8, 10} ↔
      SynchronizedFiveFanFin11SemanticStrongQuad chi 1 5 6 8
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 1 5 6 10
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 1 5 8 10
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 1 6 8 10
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 5 6 8 10
        (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 1) (j := 5) (k := 6) (l := 8)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 1) (j := 5) (k := 6) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 1) (j := 5) (k := 8) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 1) (j := 6) (k := 8) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 5) (j := 6) (k := 8) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp))⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11_strongSet_iff_mask1196 (chi : TripleColoring 11) :
    IsStrongPolygonSet chi {2, 3, 5, 7, 10} ↔
      SynchronizedFiveFanFin11SemanticStrongQuad chi 2 3 5 7
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 2 3 5 10
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 2 3 7 10
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 2 5 7 10
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 3 5 7 10
        (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 2) (j := 3) (k := 5) (l := 7)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 2) (j := 3) (k := 5) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 2) (j := 3) (k := 7) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 2) (j := 5) (k := 7) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 3) (j := 5) (k := 7) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp))⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11_strongSet_iff_mask0484 (chi : TripleColoring 11) :
    IsStrongPolygonSet chi {2, 5, 6, 7, 8} ↔
      SynchronizedFiveFanFin11SemanticStrongQuad chi 2 5 6 7
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 2 5 6 8
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 2 5 7 8
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 2 6 7 8
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 5 6 7 8
        (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 2) (j := 5) (k := 6) (l := 7)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 2) (j := 5) (k := 6) (l := 8)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 2) (j := 5) (k := 7) (l := 8)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 2) (j := 6) (k := 7) (l := 8)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 5) (j := 6) (k := 7) (l := 8)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp))⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11_strongSet_iff_mask0920 (chi : TripleColoring 11) :
    IsStrongPolygonSet chi {3, 4, 7, 8, 9} ↔
      SynchronizedFiveFanFin11SemanticStrongQuad chi 3 4 7 8
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 3 4 7 9
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 3 4 8 9
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 3 7 8 9
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 4 7 8 9
        (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 3) (j := 4) (k := 7) (l := 8)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 3) (j := 4) (k := 7) (l := 9)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 3) (j := 4) (k := 8) (l := 9)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 3) (j := 7) (k := 8) (l := 9)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 4) (j := 7) (k := 8) (l := 9)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp))⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11_strongSet_iff_mask1872 (chi : TripleColoring 11) :
    IsStrongPolygonSet chi {4, 6, 8, 9, 10} ↔
      SynchronizedFiveFanFin11SemanticStrongQuad chi 4 6 8 9
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 4 6 8 10
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 4 6 9 10
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 4 8 9 10
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 6 8 9 10
        (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 4) (j := 6) (k := 8) (l := 9)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 4) (j := 6) (k := 8) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 4) (j := 6) (k := 9) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 4) (j := 8) (k := 9) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 6) (j := 8) (k := 9) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp))⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11_cupSet_iff_mask1547 (chi : TripleColoring 11) :
    IsCupSet chi {0, 1, 3, 9, 10} ↔
      chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 3, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 3, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem synchronizedFiveFanFin11_cupSet_iff_mask0093 (chi : TripleColoring 11) :
    IsCupSet chi {0, 2, 3, 4, 6} ↔
      chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 3, 6, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left ∧
      chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem synchronizedFiveFanFin11_cupSet_iff_mask0789 (chi : TripleColoring 11) :
    IsCupSet chi {0, 2, 4, 8, 9} ↔
      chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem synchronizedFiveFanFin11_cupSet_iff_mask1113 (chi : TripleColoring 11) :
    IsCupSet chi {0, 3, 4, 6, 10} ↔
      chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 3, 6, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 3, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left ∧
      chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem synchronizedFiveFanFin11_cupSet_iff_mask1329 (chi : TripleColoring 11) :
    IsCupSet chi {0, 4, 5, 8, 10} ↔
      chi ⟨0, 4, 5, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem synchronizedFiveFanFin11_cupSet_iff_mask0302 (chi : TripleColoring 11) :
    IsCupSet chi {1, 2, 3, 5, 8} ↔
      chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 3, 5, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 3, 8, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left ∧
      chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem synchronizedFiveFanFin11_cupSet_iff_mask0678 (chi : TripleColoring 11) :
    IsCupSet chi {1, 2, 5, 7, 9} ↔
      chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem synchronizedFiveFanFin11_cupSet_iff_mask0426 (chi : TripleColoring 11) :
    IsCupSet chi {1, 3, 5, 7, 8} ↔
      chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left ∧
      chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left ∧
      chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left ∧
      chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem synchronizedFiveFanFin11_cupSet_iff_mask1426 (chi : TripleColoring 11) :
    IsCupSet chi {1, 4, 7, 8, 10} ↔
      chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem synchronizedFiveFanFin11_cupSet_iff_mask1132 (chi : TripleColoring 11) :
    IsCupSet chi {2, 3, 5, 6, 10} ↔
      chi ⟨2, 3, 5, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left ∧
      chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem synchronizedFiveFanFin11_cupSet_iff_mask1684 (chi : TripleColoring 11) :
    IsCupSet chi {2, 4, 7, 9, 10} ↔
      chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem synchronizedFiveFanFin11_cupSet_iff_mask0920 (chi : TripleColoring 11) :
    IsCupSet chi {3, 4, 7, 8, 9} ↔
      chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left ∧
      chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left ∧
      chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem synchronizedFiveFanFin11_cupSet_iff_mask1936 (chi : TripleColoring 11) :
    IsCupSet chi {4, 7, 8, 9, 10} ↔
      chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem synchronizedFiveFanFin11_capSet_iff_mask1543 (chi : TripleColoring 11) :
    IsCapSet chi {0, 1, 2, 9, 10} ↔
      chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem synchronizedFiveFanFin11_capSet_iff_mask0787 (chi : TripleColoring 11) :
    IsCapSet chi {0, 1, 4, 8, 9} ↔
      chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem synchronizedFiveFanFin11_capSet_iff_mask0557 (chi : TripleColoring 11) :
    IsCapSet chi {0, 2, 3, 5, 9} ↔
      chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 3, 5, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 3, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 3, 5, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem synchronizedFiveFanFin11_capSet_iff_mask0677 (chi : TripleColoring 11) :
    IsCapSet chi {0, 2, 5, 7, 9} ↔
      chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem synchronizedFiveFanFin11_capSet_iff_mask0617 (chi : TripleColoring 11) :
    IsCapSet chi {0, 3, 5, 6, 9} ↔
      chi ⟨0, 3, 5, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 3, 6, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 3, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.right ∧
      chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem synchronizedFiveFanFin11_capSet_iff_mask1425 (chi : TripleColoring 11) :
    IsCapSet chi {0, 4, 7, 8, 10} ↔
      chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem synchronizedFiveFanFin11_capSet_iff_mask1166 (chi : TripleColoring 11) :
    IsCapSet chi {1, 2, 3, 7, 10} ↔
      chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem synchronizedFiveFanFin11_capSet_iff_mask0838 (chi : TripleColoring 11) :
    IsCapSet chi {1, 2, 6, 8, 9} ↔
      chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem synchronizedFiveFanFin11_capSet_iff_mask1226 (chi : TripleColoring 11) :
    IsCapSet chi {1, 3, 6, 7, 10} ↔
      chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem synchronizedFiveFanFin11_capSet_iff_mask1634 (chi : TripleColoring 11) :
    IsCapSet chi {1, 5, 6, 9, 10} ↔
      chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem synchronizedFiveFanFin11_capSet_iff_mask1324 (chi : TripleColoring 11) :
    IsCapSet chi {2, 3, 5, 8, 10} ↔
      chi ⟨2, 3, 5, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 3, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem synchronizedFiveFanFin11_capSet_iff_mask1252 (chi : TripleColoring 11) :
    IsCapSet chi {2, 5, 6, 7, 10} ↔
      chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem synchronizedFiveFanFin11_capSet_iff_mask1640 (chi : TripleColoring 11) :
    IsCapSet chi {3, 5, 6, 9, 10} ↔
      chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.right ∧
      chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem synchronizedFiveFanFin11_fiveSubset_mask0335 :
    ∀ polygon : Finset (Fin 11), polygon ⊆ {0, 1, 2, 3, 6, 8} →
      polygon.card = 5 →
        polygon = {0, 1, 2, 3, 6} ∨
          polygon = {0, 1, 2, 3, 8} ∨
          polygon = {0, 1, 2, 6, 8} ∨
          polygon = {0, 1, 3, 6, 8} ∨
          polygon = {0, 2, 3, 6, 8} ∨
          polygon = {1, 2, 3, 6, 8} := by decide

theorem synchronizedFiveFanFin11_fiveSubset_mask0215 :
    ∀ polygon : Finset (Fin 11), polygon ⊆ {0, 1, 2, 4, 6, 7} →
      polygon.card = 5 →
        polygon = {0, 1, 2, 4, 6} ∨
          polygon = {0, 1, 2, 4, 7} ∨
          polygon = {0, 1, 2, 6, 7} ∨
          polygon = {0, 1, 4, 6, 7} ∨
          polygon = {0, 2, 4, 6, 7} ∨
          polygon = {1, 2, 4, 6, 7} := by decide

theorem synchronizedFiveFanFin11_fiveSubset_mask0347 :
    ∀ polygon : Finset (Fin 11), polygon ⊆ {0, 1, 3, 4, 6, 8} →
      polygon.card = 5 →
        polygon = {0, 1, 3, 4, 6} ∨
          polygon = {0, 1, 3, 4, 8} ∨
          polygon = {0, 1, 3, 6, 8} ∨
          polygon = {0, 1, 4, 6, 8} ∨
          polygon = {0, 3, 4, 6, 8} ∨
          polygon = {1, 3, 4, 6, 8} := by decide

theorem synchronizedFiveFanFin11_fiveSubset_mask1587 :
    ∀ polygon : Finset (Fin 11), polygon ⊆ {0, 1, 4, 5, 9, 10} →
      polygon.card = 5 →
        polygon = {0, 1, 4, 5, 9} ∨
          polygon = {0, 1, 4, 5, 10} ∨
          polygon = {0, 1, 4, 9, 10} ∨
          polygon = {0, 1, 5, 9, 10} ∨
          polygon = {0, 4, 5, 9, 10} ∨
          polygon = {1, 4, 5, 9, 10} := by decide

theorem synchronizedFiveFanFin11_fiveSubset_mask0797 :
    ∀ polygon : Finset (Fin 11), polygon ⊆ {0, 2, 3, 4, 8, 9} →
      polygon.card = 5 →
        polygon = {0, 2, 3, 4, 8} ∨
          polygon = {0, 2, 3, 4, 9} ∨
          polygon = {0, 2, 3, 8, 9} ∨
          polygon = {0, 2, 4, 8, 9} ∨
          polygon = {0, 3, 4, 8, 9} ∨
          polygon = {2, 3, 4, 8, 9} := by decide

theorem synchronizedFiveFanFin11_fiveSubset_mask0469 :
    ∀ polygon : Finset (Fin 11), polygon ⊆ {0, 2, 4, 6, 7, 8} →
      polygon.card = 5 →
        polygon = {0, 2, 4, 6, 7} ∨
          polygon = {0, 2, 4, 6, 8} ∨
          polygon = {0, 2, 4, 7, 8} ∨
          polygon = {0, 2, 6, 7, 8} ∨
          polygon = {0, 4, 6, 7, 8} ∨
          polygon = {2, 4, 6, 7, 8} := by decide

theorem synchronizedFiveFanFin11_fiveSubset_mask1241 :
    ∀ polygon : Finset (Fin 11), polygon ⊆ {0, 3, 4, 6, 7, 10} →
      polygon.card = 5 →
        polygon = {0, 3, 4, 6, 7} ∨
          polygon = {0, 3, 4, 6, 10} ∨
          polygon = {0, 3, 4, 7, 10} ∨
          polygon = {0, 3, 6, 7, 10} ∨
          polygon = {0, 4, 6, 7, 10} ∨
          polygon = {3, 4, 6, 7, 10} := by decide

theorem synchronizedFiveFanFin11_fiveSubset_mask0222 :
    ∀ polygon : Finset (Fin 11), polygon ⊆ {1, 2, 3, 4, 6, 7} →
      polygon.card = 5 →
        polygon = {1, 2, 3, 4, 6} ∨
          polygon = {1, 2, 3, 4, 7} ∨
          polygon = {1, 2, 3, 6, 7} ∨
          polygon = {1, 2, 4, 6, 7} ∨
          polygon = {1, 3, 4, 6, 7} ∨
          polygon = {2, 3, 4, 6, 7} := by decide

theorem synchronizedFiveFanFin11_fiveSubset_mask0822 :
    ∀ polygon : Finset (Fin 11), polygon ⊆ {1, 2, 4, 5, 8, 9} →
      polygon.card = 5 →
        polygon = {1, 2, 4, 5, 8} ∨
          polygon = {1, 2, 4, 5, 9} ∨
          polygon = {1, 2, 4, 8, 9} ∨
          polygon = {1, 2, 5, 8, 9} ∨
          polygon = {1, 4, 5, 8, 9} ∨
          polygon = {2, 4, 5, 8, 9} := by decide

theorem synchronizedFiveFanFin11_fiveSubset_mask0730 :
    ∀ polygon : Finset (Fin 11), polygon ⊆ {1, 3, 4, 6, 7, 9} →
      polygon.card = 5 →
        polygon = {1, 3, 4, 6, 7} ∨
          polygon = {1, 3, 4, 6, 9} ∨
          polygon = {1, 3, 4, 7, 9} ∨
          polygon = {1, 3, 6, 7, 9} ∨
          polygon = {1, 4, 6, 7, 9} ∨
          polygon = {3, 4, 6, 7, 9} := by decide

theorem synchronizedFiveFanFin11_fiveSubset_mask1874 :
    ∀ polygon : Finset (Fin 11), polygon ⊆ {1, 4, 6, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {1, 4, 6, 8, 9} ∨
          polygon = {1, 4, 6, 8, 10} ∨
          polygon = {1, 4, 6, 9, 10} ∨
          polygon = {1, 4, 8, 9, 10} ∨
          polygon = {1, 6, 8, 9, 10} ∨
          polygon = {4, 6, 8, 9, 10} := by decide

theorem synchronizedFiveFanFin11_fiveSubset_mask0756 :
    ∀ polygon : Finset (Fin 11), polygon ⊆ {2, 4, 5, 6, 7, 9} →
      polygon.card = 5 →
        polygon = {2, 4, 5, 6, 7} ∨
          polygon = {2, 4, 5, 6, 9} ∨
          polygon = {2, 4, 5, 7, 9} ∨
          polygon = {2, 4, 6, 7, 9} ∨
          polygon = {2, 5, 6, 7, 9} ∨
          polygon = {4, 5, 6, 7, 9} := by decide

theorem synchronizedFiveFanFin11_fiveSubset_mask2000 :
    ∀ polygon : Finset (Fin 11), polygon ⊆ {4, 6, 7, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 8, 9} ∨
          polygon = {4, 6, 7, 8, 10} ∨
          polygon = {4, 6, 7, 9, 10} ∨
          polygon = {4, 6, 8, 9, 10} ∨
          polygon = {4, 7, 8, 9, 10} ∨
          polygon = {6, 7, 8, 9, 10} := by decide

end ErdosSzekeres

end
