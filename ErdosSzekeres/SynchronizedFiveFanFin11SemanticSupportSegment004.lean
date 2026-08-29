module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSupportSegment003

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 004. -/

theorem synchronizedFiveFanFin11_strongSet_iff_mask0271 (chi : TripleColoring 11) :
    IsStrongPolygonSet chi {0, 1, 2, 3, 8} ↔
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 2 3
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 2 8
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 3 8
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 2 3 8
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 1 2 3 8
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
          (i := 0) (j := 1) (k := 2) (l := 8)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 1) (k := 3) (l := 8)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 2) (k := 3) (l := 8)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 1) (j := 2) (k := 3) (l := 8)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp))⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11_strongSet_iff_mask0299 (chi : TripleColoring 11) :
    IsStrongPolygonSet chi {0, 1, 3, 5, 8} ↔
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 3 5
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 3 8
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 5 8
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 3 5 8
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 1 3 5 8
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
          (i := 0) (j := 1) (k := 3) (l := 8)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 1) (k := 5) (l := 8)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 3) (k := 5) (l := 8)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 1) (j := 3) (k := 5) (l := 8)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp))⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11_strongSet_iff_mask1123 (chi : TripleColoring 11) :
    IsStrongPolygonSet chi {0, 1, 5, 6, 10} ↔
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 5 6
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 5 10
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 6 10
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 5 6 10
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 1 5 6 10
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
          (i := 0) (j := 1) (k := 5) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 1) (k := 6) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 5) (k := 6) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 1) (j := 5) (k := 6) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp))⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11_strongSet_iff_mask0181 (chi : TripleColoring 11) :
    IsStrongPolygonSet chi {0, 2, 4, 5, 7} ↔
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 2 4 5
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 2 4 7
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 2 5 7
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 4 5 7
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 2 4 5 7
        (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 2) (k := 4) (l := 5)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 2) (k := 4) (l := 7)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 2) (k := 5) (l := 7)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 4) (k := 5) (l := 7)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 2) (j := 4) (k := 5) (l := 7)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp))⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11_strongSet_iff_mask1605 (chi : TripleColoring 11) :
    IsStrongPolygonSet chi {0, 2, 6, 9, 10} ↔
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 2 6 9
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 2 6 10
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 2 9 10
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 6 9 10
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 2 6 9 10
        (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 2) (k := 6) (l := 9)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 2) (k := 6) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 2) (k := 9) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 6) (k := 9) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 2) (j := 6) (k := 9) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp))⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11_strongSet_iff_mask1137 (chi : TripleColoring 11) :
    IsStrongPolygonSet chi {0, 4, 5, 6, 10} ↔
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 4 5 6
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 4 5 10
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 4 6 10
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 0 5 6 10
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 4 5 6 10
        (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 4) (k := 5) (l := 6)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 4) (k := 5) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 4) (k := 6) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 0) (j := 5) (k := 6) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 4) (j := 5) (k := 6) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp))⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11_strongSet_iff_mask0110 (chi : TripleColoring 11) :
    IsStrongPolygonSet chi {1, 2, 3, 5, 6} ↔
      SynchronizedFiveFanFin11SemanticStrongQuad chi 1 2 3 5
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 1 2 3 6
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 1 2 5 6
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 1 3 5 6
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 2 3 5 6
        (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 1) (j := 2) (k := 3) (l := 5)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 1) (j := 2) (k := 3) (l := 6)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 1) (j := 2) (k := 5) (l := 6)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 1) (j := 3) (k := 5) (l := 6)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 2) (j := 3) (k := 5) (l := 6)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp))⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11_strongSet_iff_mask1174 (chi : TripleColoring 11) :
    IsStrongPolygonSet chi {1, 2, 4, 7, 10} ↔
      SynchronizedFiveFanFin11SemanticStrongQuad chi 1 2 4 7
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 1 2 4 10
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 1 2 7 10
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 1 4 7 10
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 2 4 7 10
        (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 1) (j := 2) (k := 4) (l := 7)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 1) (j := 2) (k := 4) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 1) (j := 2) (k := 7) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 1) (j := 4) (k := 7) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 2) (j := 4) (k := 7) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp))⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11_strongSet_iff_mask0234 (chi : TripleColoring 11) :
    IsStrongPolygonSet chi {1, 3, 5, 6, 7} ↔
      SynchronizedFiveFanFin11SemanticStrongQuad chi 1 3 5 6
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 1 3 5 7
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 1 3 6 7
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 1 5 6 7
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 3 5 6 7
        (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 1) (j := 3) (k := 5) (l := 6)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 1) (j := 3) (k := 5) (l := 7)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 1) (j := 3) (k := 6) (l := 7)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 1) (j := 5) (k := 6) (l := 7)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 3) (j := 5) (k := 6) (l := 7)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp))⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11_strongSet_iff_mask1330 (chi : TripleColoring 11) :
    IsStrongPolygonSet chi {1, 4, 5, 8, 10} ↔
      SynchronizedFiveFanFin11SemanticStrongQuad chi 1 4 5 8
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 1 4 5 10
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 1 4 8 10
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 1 5 8 10
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 4 5 8 10
        (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 1) (j := 4) (k := 5) (l := 8)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 1) (j := 4) (k := 5) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 1) (j := 4) (k := 8) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 1) (j := 5) (k := 8) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 4) (j := 5) (k := 8) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp))⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11_strongSet_iff_mask0412 (chi : TripleColoring 11) :
    IsStrongPolygonSet chi {2, 3, 4, 7, 8} ↔
      SynchronizedFiveFanFin11SemanticStrongQuad chi 2 3 4 7
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 2 3 4 8
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 2 3 7 8
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 2 4 7 8
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 3 4 7 8
        (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 2) (j := 3) (k := 4) (l := 7)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 2) (j := 3) (k := 4) (l := 8)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 2) (j := 3) (k := 7) (l := 8)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 2) (j := 4) (k := 7) (l := 8)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 3) (j := 4) (k := 7) (l := 8)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp))⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11_strongSet_iff_mask0692 (chi : TripleColoring 11) :
    IsStrongPolygonSet chi {2, 4, 5, 7, 9} ↔
      SynchronizedFiveFanFin11SemanticStrongQuad chi 2 4 5 7
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 2 4 5 9
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 2 4 7 9
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 2 5 7 9
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 4 5 7 9
        (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 2) (j := 4) (k := 5) (l := 7)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 2) (j := 4) (k := 5) (l := 9)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 2) (j := 4) (k := 7) (l := 9)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 2) (j := 5) (k := 7) (l := 9)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 4) (j := 5) (k := 7) (l := 9)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp))⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11_strongSet_iff_mask1476 (chi : TripleColoring 11) :
    IsStrongPolygonSet chi {2, 6, 7, 8, 10} ↔
      SynchronizedFiveFanFin11SemanticStrongQuad chi 2 6 7 8
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 2 6 7 10
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 2 6 8 10
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 2 7 8 10
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 6 7 8 10
        (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 2) (j := 6) (k := 7) (l := 8)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 2) (j := 6) (k := 7) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 2) (j := 6) (k := 8) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 2) (j := 7) (k := 8) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 6) (j := 7) (k := 8) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp))⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11_strongSet_iff_mask1736 (chi : TripleColoring 11) :
    IsStrongPolygonSet chi {3, 6, 7, 9, 10} ↔
      SynchronizedFiveFanFin11SemanticStrongQuad chi 3 6 7 9
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 3 6 7 10
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 3 6 9 10
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 3 7 9 10
        (by decide) (by decide) (by decide) ∧
      SynchronizedFiveFanFin11SemanticStrongQuad chi 6 7 9 10
        (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 3) (j := 6) (k := 7) (l := 9)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 3) (j := 6) (k := 7) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 3) (j := 6) (k := 9) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 3) (j := 7) (k := 9) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp)),
      (by
        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h
          (i := 6) (j := 7) (k := 9) (l := 10)
          (by decide) (by decide) (by decide)
          (by simp) (by simp) (by simp) (by simp))⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11_cupSet_iff_mask0535 (chi : TripleColoring 11) :
    IsCupSet chi {0, 1, 2, 4, 9} ↔
      chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left := by
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

theorem synchronizedFiveFanFin11_cupSet_iff_mask0171 (chi : TripleColoring 11) :
    IsCupSet chi {0, 1, 3, 5, 7} ↔
      chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 3, 5, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 3, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left := by
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

theorem synchronizedFiveFanFin11_cupSet_iff_mask1123 (chi : TripleColoring 11) :
    IsCupSet chi {0, 1, 5, 6, 10} ↔
      chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left ∧
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

theorem synchronizedFiveFanFin11_cupSet_iff_mask0117 (chi : TripleColoring 11) :
    IsCupSet chi {0, 2, 4, 5, 6} ↔
      chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 4, 5, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left := by
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

theorem synchronizedFiveFanFin11_cupSet_iff_mask1605 (chi : TripleColoring 11) :
    IsCupSet chi {0, 2, 6, 9, 10} ↔
      chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left := by
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

theorem synchronizedFiveFanFin11_cupSet_iff_mask1609 (chi : TripleColoring 11) :
    IsCupSet chi {0, 3, 6, 9, 10} ↔
      chi ⟨0, 3, 6, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 3, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 3, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left := by
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

theorem synchronizedFiveFanFin11_cupSet_iff_mask1729 (chi : TripleColoring 11) :
    IsCupSet chi {0, 6, 7, 9, 10} ↔
      chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left ∧
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

theorem synchronizedFiveFanFin11_cupSet_iff_mask1174 (chi : TripleColoring 11) :
    IsCupSet chi {1, 2, 4, 7, 10} ↔
      chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left := by
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

theorem synchronizedFiveFanFin11_cupSet_iff_mask1178 (chi : TripleColoring 11) :
    IsCupSet chi {1, 3, 4, 7, 10} ↔
      chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left := by
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

theorem synchronizedFiveFanFin11_cupSet_iff_mask0722 (chi : TripleColoring 11) :
    IsCupSet chi {1, 4, 6, 7, 9} ↔
      chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left := by
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

theorem synchronizedFiveFanFin11_cupSet_iff_mask1180 (chi : TripleColoring 11) :
    IsCupSet chi {2, 3, 4, 7, 10} ↔
      chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left := by
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

theorem synchronizedFiveFanFin11_cupSet_iff_mask1236 (chi : TripleColoring 11) :
    IsCupSet chi {2, 4, 6, 7, 10} ↔
      chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left := by
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

theorem synchronizedFiveFanFin11_cupSet_iff_mask0472 (chi : TripleColoring 11) :
    IsCupSet chi {3, 4, 6, 7, 8} ↔
      chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left ∧
      chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left ∧
      chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left ∧
      chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left ∧
      chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left := by
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

theorem synchronizedFiveFanFin11_cupSet_iff_mask1840 (chi : TripleColoring 11) :
    IsCupSet chi {4, 5, 8, 9, 10} ↔
      chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left ∧
      chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left ∧
      chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left ∧
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

theorem synchronizedFiveFanFin11_capSet_iff_mask0647 (chi : TripleColoring 11) :
    IsCapSet chi {0, 1, 2, 7, 9} ↔
      chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.right := by
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

theorem synchronizedFiveFanFin11_capSet_iff_mask0211 (chi : TripleColoring 11) :
    IsCapSet chi {0, 1, 4, 6, 7} ↔
      chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.right := by
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

theorem synchronizedFiveFanFin11_capSet_iff_mask0157 (chi : TripleColoring 11) :
    IsCapSet chi {0, 2, 3, 4, 7} ↔
      chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 3, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.right := by
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

theorem synchronizedFiveFanFin11_capSet_iff_mask1301 (chi : TripleColoring 11) :
    IsCapSet chi {0, 2, 4, 8, 10} ↔
      chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.right := by
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

theorem synchronizedFiveFanFin11_capSet_iff_mask1177 (chi : TripleColoring 11) :
    IsCapSet chi {0, 3, 4, 7, 10} ↔
      chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 3, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 3, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.right := by
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

theorem synchronizedFiveFanFin11_capSet_iff_mask0721 (chi : TripleColoring 11) :
    IsCapSet chi {0, 4, 6, 7, 9} ↔
      chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.right := by
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

theorem synchronizedFiveFanFin11_capSet_iff_mask0206 (chi : TripleColoring 11) :
    IsCapSet chi {1, 2, 3, 6, 7} ↔
      chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.right := by
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

theorem synchronizedFiveFanFin11_capSet_iff_mask1190 (chi : TripleColoring 11) :
    IsCapSet chi {1, 2, 5, 7, 10} ↔
      chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.right := by
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

theorem synchronizedFiveFanFin11_capSet_iff_mask1194 (chi : TripleColoring 11) :
    IsCapSet chi {1, 3, 5, 7, 10} ↔
      chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.right := by
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

theorem synchronizedFiveFanFin11_capSet_iff_mask0482 (chi : TripleColoring 11) :
    IsCapSet chi {1, 5, 6, 7, 8} ↔
      chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.right ∧
      chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.right := by
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

theorem synchronizedFiveFanFin11_capSet_iff_mask0364 (chi : TripleColoring 11) :
    IsCapSet chi {2, 3, 5, 6, 8} ↔
      chi ⟨2, 3, 5, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 3, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.right ∧
      chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.right := by
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

theorem synchronizedFiveFanFin11_capSet_iff_mask0852 (chi : TripleColoring 11) :
    IsCapSet chi {2, 4, 6, 8, 9} ↔
      chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.right ∧
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

theorem synchronizedFiveFanFin11_capSet_iff_mask1368 (chi : TripleColoring 11) :
    IsCapSet chi {3, 4, 6, 8, 10} ↔
      chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.right ∧
      chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.right := by
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

theorem synchronizedFiveFanFin11_capSet_iff_mask1888 (chi : TripleColoring 11) :
    IsCapSet chi {5, 6, 8, 9, 10} ↔
      chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.right ∧
      chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.right ∧
      chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.right ∧
      chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.right := by
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

theorem synchronizedFiveFanFin11_fiveSubset_mask0187 :
    ∀ polygon : Finset (Fin 11), polygon ⊆ {0, 1, 3, 4, 5, 7} →
      polygon.card = 5 →
        polygon = {0, 1, 3, 4, 5} ∨
          polygon = {0, 1, 3, 4, 7} ∨
          polygon = {0, 1, 3, 5, 7} ∨
          polygon = {0, 1, 4, 5, 7} ∨
          polygon = {0, 3, 4, 5, 7} ∨
          polygon = {1, 3, 4, 5, 7} := by decide

theorem synchronizedFiveFanFin11_fiveSubset_mask1139 :
    ∀ polygon : Finset (Fin 11), polygon ⊆ {0, 1, 4, 5, 6, 10} →
      polygon.card = 5 →
        polygon = {0, 1, 4, 5, 6} ∨
          polygon = {0, 1, 4, 5, 10} ∨
          polygon = {0, 1, 4, 6, 10} ∨
          polygon = {0, 1, 5, 6, 10} ∨
          polygon = {0, 4, 5, 6, 10} ∨
          polygon = {1, 4, 5, 6, 10} := by decide

theorem synchronizedFiveFanFin11_fiveSubset_mask0605 :
    ∀ polygon : Finset (Fin 11), polygon ⊆ {0, 2, 3, 4, 6, 9} →
      polygon.card = 5 →
        polygon = {0, 2, 3, 4, 6} ∨
          polygon = {0, 2, 3, 4, 9} ∨
          polygon = {0, 2, 3, 6, 9} ∨
          polygon = {0, 2, 4, 6, 9} ∨
          polygon = {0, 3, 4, 6, 9} ∨
          polygon = {2, 3, 4, 6, 9} := by decide

theorem synchronizedFiveFanFin11_fiveSubset_mask0693 :
    ∀ polygon : Finset (Fin 11), polygon ⊆ {0, 2, 4, 5, 7, 9} →
      polygon.card = 5 →
        polygon = {0, 2, 4, 5, 7} ∨
          polygon = {0, 2, 4, 5, 9} ∨
          polygon = {0, 2, 4, 7, 9} ∨
          polygon = {0, 2, 5, 7, 9} ∨
          polygon = {0, 4, 5, 7, 9} ∨
          polygon = {2, 4, 5, 7, 9} := by decide

theorem synchronizedFiveFanFin11_fiveSubset_mask1145 :
    ∀ polygon : Finset (Fin 11), polygon ⊆ {0, 3, 4, 5, 6, 10} →
      polygon.card = 5 →
        polygon = {0, 3, 4, 5, 6} ∨
          polygon = {0, 3, 4, 5, 10} ∨
          polygon = {0, 3, 4, 6, 10} ∨
          polygon = {0, 3, 5, 6, 10} ∨
          polygon = {0, 4, 5, 6, 10} ∨
          polygon = {3, 4, 5, 6, 10} := by decide

theorem synchronizedFiveFanFin11_fiveSubset_mask1761 :
    ∀ polygon : Finset (Fin 11), polygon ⊆ {0, 5, 6, 7, 9, 10} →
      polygon.card = 5 →
        polygon = {0, 5, 6, 7, 9} ∨
          polygon = {0, 5, 6, 7, 10} ∨
          polygon = {0, 5, 6, 9, 10} ∨
          polygon = {0, 5, 7, 9, 10} ∨
          polygon = {0, 6, 7, 9, 10} ∨
          polygon = {5, 6, 7, 9, 10} := by decide

theorem synchronizedFiveFanFin11_fiveSubset_mask0374 :
    ∀ polygon : Finset (Fin 11), polygon ⊆ {1, 2, 4, 5, 6, 8} →
      polygon.card = 5 →
        polygon = {1, 2, 4, 5, 6} ∨
          polygon = {1, 2, 4, 5, 8} ∨
          polygon = {1, 2, 4, 6, 8} ∨
          polygon = {1, 2, 5, 6, 8} ∨
          polygon = {1, 4, 5, 6, 8} ∨
          polygon = {2, 4, 5, 6, 8} := by decide

theorem synchronizedFiveFanFin11_fiveSubset_mask0698 :
    ∀ polygon : Finset (Fin 11), polygon ⊆ {1, 3, 4, 5, 7, 9} →
      polygon.card = 5 →
        polygon = {1, 3, 4, 5, 7} ∨
          polygon = {1, 3, 4, 5, 9} ∨
          polygon = {1, 3, 4, 7, 9} ∨
          polygon = {1, 3, 5, 7, 9} ∨
          polygon = {1, 4, 5, 7, 9} ∨
          polygon = {3, 4, 5, 7, 9} := by decide

theorem synchronizedFiveFanFin11_fiveSubset_mask1650 :
    ∀ polygon : Finset (Fin 11), polygon ⊆ {1, 4, 5, 6, 9, 10} →
      polygon.card = 5 →
        polygon = {1, 4, 5, 6, 9} ∨
          polygon = {1, 4, 5, 6, 10} ∨
          polygon = {1, 4, 5, 9, 10} ∨
          polygon = {1, 4, 6, 9, 10} ∨
          polygon = {1, 5, 6, 9, 10} ∨
          polygon = {4, 5, 6, 9, 10} := by decide

theorem synchronizedFiveFanFin11_fiveSubset_mask1388 :
    ∀ polygon : Finset (Fin 11), polygon ⊆ {2, 3, 5, 6, 8, 10} →
      polygon.card = 5 →
        polygon = {2, 3, 5, 6, 8} ∨
          polygon = {2, 3, 5, 6, 10} ∨
          polygon = {2, 3, 5, 8, 10} ∨
          polygon = {2, 3, 6, 8, 10} ∨
          polygon = {2, 5, 6, 8, 10} ∨
          polygon = {3, 5, 6, 8, 10} := by decide

theorem synchronizedFiveFanFin11_fiveSubset_mask1944 :
    ∀ polygon : Finset (Fin 11), polygon ⊆ {3, 4, 7, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {3, 4, 7, 8, 9} ∨
          polygon = {3, 4, 7, 8, 10} ∨
          polygon = {3, 4, 7, 9, 10} ∨
          polygon = {3, 4, 8, 9, 10} ∨
          polygon = {3, 7, 8, 9, 10} ∨
          polygon = {4, 7, 8, 9, 10} := by decide

end ErdosSzekeres

end
