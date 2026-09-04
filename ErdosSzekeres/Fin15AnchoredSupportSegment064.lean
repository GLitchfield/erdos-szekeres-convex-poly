module

public import ErdosSzekeres.Fin15AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 064. -/

theorem fin15Anchored_strongSet_iff_mask29056 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {7, 8, 12, 13, 14} ↔
      Fin15AnchoredStrongQuad chi 7 8 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 8 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 8 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 12 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 8 12 13 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 8) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 8) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 8) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 12) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 8) (j := 12) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask07808 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {7, 9, 10, 11, 12} ↔
      Fin15AnchoredStrongQuad chi 7 9 10 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 9 10 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 9 11 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 10 11 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 9 10 11 12 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 9) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 9) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 9) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 10) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 9) (j := 10) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask11904 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {7, 9, 10, 11, 13} ↔
      Fin15AnchoredStrongQuad chi 7 9 10 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 9 10 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 9 11 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 10 11 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 9 10 11 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 9) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 9) (k := 10) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 9) (k := 11) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 10) (k := 11) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 9) (j := 10) (k := 11) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask20096 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {7, 9, 10, 11, 14} ↔
      Fin15AnchoredStrongQuad chi 7 9 10 11 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 9 10 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 9 11 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 10 11 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 9 10 11 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 9) (k := 10) (l := 11)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 9) (k := 10) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 9) (k := 11) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 10) (k := 11) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 9) (j := 10) (k := 11) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask13952 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {7, 9, 10, 12, 13} ↔
      Fin15AnchoredStrongQuad chi 7 9 10 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 9 10 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 9 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 10 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 9 10 12 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 9) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 9) (k := 10) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 9) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 10) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 9) (j := 10) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask22144 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {7, 9, 10, 12, 14} ↔
      Fin15AnchoredStrongQuad chi 7 9 10 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 9 10 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 9 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 10 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 9 10 12 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 9) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 9) (k := 10) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 9) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 10) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 9) (j := 10) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask26240 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {7, 9, 10, 13, 14} ↔
      Fin15AnchoredStrongQuad chi 7 9 10 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 9 10 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 9 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 10 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 9 10 13 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 9) (k := 10) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 9) (k := 10) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 9) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 10) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 9) (j := 10) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask14976 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {7, 9, 11, 12, 13} ↔
      Fin15AnchoredStrongQuad chi 7 9 11 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 9 11 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 9 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 11 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 9 11 12 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 9) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 9) (k := 11) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 9) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 11) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 9) (j := 11) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask23168 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {7, 9, 11, 12, 14} ↔
      Fin15AnchoredStrongQuad chi 7 9 11 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 9 11 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 9 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 11 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 9 11 12 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 9) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 9) (k := 11) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 9) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 11) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 9) (j := 11) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask27264 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {7, 9, 11, 13, 14} ↔
      Fin15AnchoredStrongQuad chi 7 9 11 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 9 11 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 9 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 11 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 9 11 13 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 9) (k := 11) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 9) (k := 11) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 9) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 11) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 9) (j := 11) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask29312 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {7, 9, 12, 13, 14} ↔
      Fin15AnchoredStrongQuad chi 7 9 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 9 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 9 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 12 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 9 12 13 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 9) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 9) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 9) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 12) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 9) (j := 12) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask15488 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {7, 10, 11, 12, 13} ↔
      Fin15AnchoredStrongQuad chi 7 10 11 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 10 11 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 10 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 11 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 10 11 12 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 10) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 10) (k := 11) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 10) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 11) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 10) (j := 11) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask23680 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {7, 10, 11, 12, 14} ↔
      Fin15AnchoredStrongQuad chi 7 10 11 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 10 11 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 10 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 11 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 10 11 12 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 10) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 10) (k := 11) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 10) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 11) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 10) (j := 11) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask27776 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {7, 10, 11, 13, 14} ↔
      Fin15AnchoredStrongQuad chi 7 10 11 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 10 11 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 10 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 11 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 10 11 13 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 10) (k := 11) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 10) (k := 11) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 10) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 11) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 10) (j := 11) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask29824 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {7, 10, 12, 13, 14} ↔
      Fin15AnchoredStrongQuad chi 7 10 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 10 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 10 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 12 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 10 12 13 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 10) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 10) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 10) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 12) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 10) (j := 12) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask30848 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {7, 11, 12, 13, 14} ↔
      Fin15AnchoredStrongQuad chi 7 11 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 11 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 11 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 7 12 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 11 12 13 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 11) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 11) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 11) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 7) (j := 12) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 11) (j := 12) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask14080 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {8, 9, 10, 12, 13} ↔
      Fin15AnchoredStrongQuad chi 8 9 10 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 8 9 10 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 8 9 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 8 10 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 9 10 12 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 8) (j := 9) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 8) (j := 9) (k := 10) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 8) (j := 9) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 8) (j := 10) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 9) (j := 10) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask22272 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {8, 9, 10, 12, 14} ↔
      Fin15AnchoredStrongQuad chi 8 9 10 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 8 9 10 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 8 9 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 8 10 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 9 10 12 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 8) (j := 9) (k := 10) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 8) (j := 9) (k := 10) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 8) (j := 9) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 8) (j := 10) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 9) (j := 10) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask26368 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {8, 9, 10, 13, 14} ↔
      Fin15AnchoredStrongQuad chi 8 9 10 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 8 9 10 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 8 9 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 8 10 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 9 10 13 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 8) (j := 9) (k := 10) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 8) (j := 9) (k := 10) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 8) (j := 9) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 8) (j := 10) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 9) (j := 10) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask29440 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {8, 9, 12, 13, 14} ↔
      Fin15AnchoredStrongQuad chi 8 9 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 8 9 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 8 9 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 8 12 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 9 12 13 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 8) (j := 9) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 8) (j := 9) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 8) (j := 9) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 8) (j := 12) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 9) (j := 12) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask29952 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {8, 10, 12, 13, 14} ↔
      Fin15AnchoredStrongQuad chi 8 10 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 8 10 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 8 10 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 8 12 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 10 12 13 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 8) (j := 10) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 8) (j := 10) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 8) (j := 10) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 8) (j := 12) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 10) (j := 12) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask15872 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {9, 10, 11, 12, 13} ↔
      Fin15AnchoredStrongQuad chi 9 10 11 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 9 10 11 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 9 10 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 9 11 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 10 11 12 13 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 9) (j := 10) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 9) (j := 10) (k := 11) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 9) (j := 10) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 9) (j := 11) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 10) (j := 11) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask24064 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {9, 10, 11, 12, 14} ↔
      Fin15AnchoredStrongQuad chi 9 10 11 12 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 9 10 11 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 9 10 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 9 11 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 10 11 12 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 9) (j := 10) (k := 11) (l := 12)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 9) (j := 10) (k := 11) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 9) (j := 10) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 9) (j := 11) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 10) (j := 11) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask28160 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {9, 10, 11, 13, 14} ↔
      Fin15AnchoredStrongQuad chi 9 10 11 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 9 10 11 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 9 10 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 9 11 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 10 11 13 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 9) (j := 10) (k := 11) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 9) (j := 10) (k := 11) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 9) (j := 10) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 9) (j := 11) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 10) (j := 11) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask30208 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {9, 10, 12, 13, 14} ↔
      Fin15AnchoredStrongQuad chi 9 10 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 9 10 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 9 10 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 9 12 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 10 12 13 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 9) (j := 10) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 9) (j := 10) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 9) (j := 10) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 9) (j := 12) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 10) (j := 12) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask31232 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {9, 11, 12, 13, 14} ↔
      Fin15AnchoredStrongQuad chi 9 11 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 9 11 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 9 11 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 9 12 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 11 12 13 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 9) (j := 11) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 9) (j := 11) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 9) (j := 11) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 9) (j := 12) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 11) (j := 12) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_strongSet_iff_mask31744 (chi : TripleColoring 15) :
    IsStrongPolygonSet chi {10, 11, 12, 13, 14} ↔
      Fin15AnchoredStrongQuad chi 10 11 12 13 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 10 11 12 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 10 11 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 10 12 13 14 (by decide) (by decide) (by decide) ∧
      Fin15AnchoredStrongQuad chi 11 12 13 14 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 10) (j := 11) (k := 12) (l := 13)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 10) (j := 11) (k := 12) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 10) (j := 11) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 10) (j := 12) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
    · simpa [Fin15AnchoredStrongQuad] using h
        (i := 11) (j := 12) (k := 13) (l := 14)
        (by decide) (by decide) (by decide)
        (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_fiveFamily_mask00255 :
    (({0, 1, 2, 3, 4, 5, 6, 7} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 6, 7}, {2, 4, 5, 6, 7}, {2, 3, 5, 6, 7}, {2, 3, 4, 6, 7}, {2, 3, 4, 5, 7}, {2, 3, 4, 5, 6}, {1, 4, 5, 6, 7}, {1, 3, 5, 6, 7}, {1, 3, 4, 6, 7}, {1, 3, 4, 5, 7}, {1, 3, 4, 5, 6}, {1, 2, 5, 6, 7}, {1, 2, 4, 6, 7}, {1, 2, 4, 5, 7}, {1, 2, 4, 5, 6}, {1, 2, 3, 6, 7}, {1, 2, 3, 5, 7}, {1, 2, 3, 5, 6}, {1, 2, 3, 4, 7}, {1, 2, 3, 4, 6}, {1, 2, 3, 4, 5}, {0, 4, 5, 6, 7}, {0, 3, 5, 6, 7}, {0, 3, 4, 6, 7}, {0, 3, 4, 5, 7}, {0, 3, 4, 5, 6}, {0, 2, 5, 6, 7}, {0, 2, 4, 6, 7}, {0, 2, 4, 5, 7}, {0, 2, 4, 5, 6}, {0, 2, 3, 6, 7}, {0, 2, 3, 5, 7}, {0, 2, 3, 5, 6}, {0, 2, 3, 4, 7}, {0, 2, 3, 4, 6}, {0, 2, 3, 4, 5}, {0, 1, 5, 6, 7}, {0, 1, 4, 6, 7}, {0, 1, 4, 5, 7}, {0, 1, 4, 5, 6}, {0, 1, 3, 6, 7}, {0, 1, 3, 5, 7}, {0, 1, 3, 5, 6}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 6}, {0, 1, 3, 4, 5}, {0, 1, 2, 6, 7}, {0, 1, 2, 5, 7}, {0, 1, 2, 5, 6}, {0, 1, 2, 4, 7}, {0, 1, 2, 4, 6}, {0, 1, 2, 4, 5}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 6}, {0, 1, 2, 3, 5}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask00255 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 5, 6, 7} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 6, 7} ∨
        polygon = {2, 4, 5, 6, 7} ∨
        polygon = {2, 3, 5, 6, 7} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {1, 4, 5, 6, 7} ∨
        polygon = {1, 3, 5, 6, 7} ∨
        polygon = {1, 3, 4, 6, 7} ∨
        polygon = {1, 3, 4, 5, 7} ∨
        polygon = {1, 3, 4, 5, 6} ∨
        polygon = {1, 2, 5, 6, 7} ∨
        polygon = {1, 2, 4, 6, 7} ∨
        polygon = {1, 2, 4, 5, 7} ∨
        polygon = {1, 2, 4, 5, 6} ∨
        polygon = {1, 2, 3, 6, 7} ∨
        polygon = {1, 2, 3, 5, 7} ∨
        polygon = {1, 2, 3, 5, 6} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {1, 2, 3, 4, 6} ∨
        polygon = {1, 2, 3, 4, 5} ∨
        polygon = {0, 4, 5, 6, 7} ∨
        polygon = {0, 3, 5, 6, 7} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 3, 4, 5, 6} ∨
        polygon = {0, 2, 5, 6, 7} ∨
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 2, 3, 5, 6} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 2, 3, 4, 6} ∨
        polygon = {0, 2, 3, 4, 5} ∨
        polygon = {0, 1, 5, 6, 7} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 4, 5, 7} ∨
        polygon = {0, 1, 4, 5, 6} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 5, 6} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 6} ∨
        polygon = {0, 1, 3, 4, 5} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 5, 6} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 4, 6} ∨
        polygon = {0, 1, 2, 4, 5} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 6} ∨
        polygon = {0, 1, 2, 3, 5} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 5, 6, 7} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask00255] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask00639 :
    (({0, 1, 2, 3, 4, 5, 6, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 6, 9}, {2, 4, 5, 6, 9}, {2, 3, 5, 6, 9}, {2, 3, 4, 6, 9}, {2, 3, 4, 5, 9}, {2, 3, 4, 5, 6}, {1, 4, 5, 6, 9}, {1, 3, 5, 6, 9}, {1, 3, 4, 6, 9}, {1, 3, 4, 5, 9}, {1, 3, 4, 5, 6}, {1, 2, 5, 6, 9}, {1, 2, 4, 6, 9}, {1, 2, 4, 5, 9}, {1, 2, 4, 5, 6}, {1, 2, 3, 6, 9}, {1, 2, 3, 5, 9}, {1, 2, 3, 5, 6}, {1, 2, 3, 4, 9}, {1, 2, 3, 4, 6}, {1, 2, 3, 4, 5}, {0, 4, 5, 6, 9}, {0, 3, 5, 6, 9}, {0, 3, 4, 6, 9}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 6}, {0, 2, 5, 6, 9}, {0, 2, 4, 6, 9}, {0, 2, 4, 5, 9}, {0, 2, 4, 5, 6}, {0, 2, 3, 6, 9}, {0, 2, 3, 5, 9}, {0, 2, 3, 5, 6}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 6}, {0, 2, 3, 4, 5}, {0, 1, 5, 6, 9}, {0, 1, 4, 6, 9}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 6}, {0, 1, 3, 6, 9}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 6}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 6}, {0, 1, 3, 4, 5}, {0, 1, 2, 6, 9}, {0, 1, 2, 5, 9}, {0, 1, 2, 5, 6}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 6}, {0, 1, 2, 4, 5}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 6}, {0, 1, 2, 3, 5}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask00639 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 5, 6, 9} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {2, 4, 5, 6, 9} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {1, 4, 5, 6, 9} ∨
        polygon = {1, 3, 5, 6, 9} ∨
        polygon = {1, 3, 4, 6, 9} ∨
        polygon = {1, 3, 4, 5, 9} ∨
        polygon = {1, 3, 4, 5, 6} ∨
        polygon = {1, 2, 5, 6, 9} ∨
        polygon = {1, 2, 4, 6, 9} ∨
        polygon = {1, 2, 4, 5, 9} ∨
        polygon = {1, 2, 4, 5, 6} ∨
        polygon = {1, 2, 3, 6, 9} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {1, 2, 3, 5, 6} ∨
        polygon = {1, 2, 3, 4, 9} ∨
        polygon = {1, 2, 3, 4, 6} ∨
        polygon = {1, 2, 3, 4, 5} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 6} ∨
        polygon = {0, 2, 5, 6, 9} ∨
        polygon = {0, 2, 4, 6, 9} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 5, 6} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 6} ∨
        polygon = {0, 2, 3, 4, 5} ∨
        polygon = {0, 1, 5, 6, 9} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 4, 5, 6} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 6} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 6} ∨
        polygon = {0, 1, 3, 4, 5} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 5, 9} ∨
        polygon = {0, 1, 2, 5, 6} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 6} ∨
        polygon = {0, 1, 2, 4, 5} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 6} ∨
        polygon = {0, 1, 2, 3, 5} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 5, 6, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask00639] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01151 :
    (({0, 1, 2, 3, 4, 5, 6, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 6, 10}, {2, 4, 5, 6, 10}, {2, 3, 5, 6, 10}, {2, 3, 4, 6, 10}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 6}, {1, 4, 5, 6, 10}, {1, 3, 5, 6, 10}, {1, 3, 4, 6, 10}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 6}, {1, 2, 5, 6, 10}, {1, 2, 4, 6, 10}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 6}, {1, 2, 3, 6, 10}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 6}, {1, 2, 3, 4, 10}, {1, 2, 3, 4, 6}, {1, 2, 3, 4, 5}, {0, 4, 5, 6, 10}, {0, 3, 5, 6, 10}, {0, 3, 4, 6, 10}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 6}, {0, 2, 5, 6, 10}, {0, 2, 4, 6, 10}, {0, 2, 4, 5, 10}, {0, 2, 4, 5, 6}, {0, 2, 3, 6, 10}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 6}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 6}, {0, 2, 3, 4, 5}, {0, 1, 5, 6, 10}, {0, 1, 4, 6, 10}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 6}, {0, 1, 3, 6, 10}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 6}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 6}, {0, 1, 3, 4, 5}, {0, 1, 2, 6, 10}, {0, 1, 2, 5, 10}, {0, 1, 2, 5, 6}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 6}, {0, 1, 2, 4, 5}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 6}, {0, 1, 2, 3, 5}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01151 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 5, 6, 10} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {1, 4, 5, 6, 10} ∨
        polygon = {1, 3, 5, 6, 10} ∨
        polygon = {1, 3, 4, 6, 10} ∨
        polygon = {1, 3, 4, 5, 10} ∨
        polygon = {1, 3, 4, 5, 6} ∨
        polygon = {1, 2, 5, 6, 10} ∨
        polygon = {1, 2, 4, 6, 10} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {1, 2, 4, 5, 6} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 6} ∨
        polygon = {1, 2, 3, 4, 10} ∨
        polygon = {1, 2, 3, 4, 6} ∨
        polygon = {1, 2, 3, 4, 5} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 6} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 4, 6, 10} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 6} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 6} ∨
        polygon = {0, 2, 3, 4, 5} ∨
        polygon = {0, 1, 5, 6, 10} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 6} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 6} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 6} ∨
        polygon = {0, 1, 3, 4, 5} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 5, 6} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 6} ∨
        polygon = {0, 1, 2, 4, 5} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 6} ∨
        polygon = {0, 1, 2, 3, 5} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 5, 6, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01151] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask04223 :
    (({0, 1, 2, 3, 4, 5, 6, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 6, 12}, {2, 4, 5, 6, 12}, {2, 3, 5, 6, 12}, {2, 3, 4, 6, 12}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 6}, {1, 4, 5, 6, 12}, {1, 3, 5, 6, 12}, {1, 3, 4, 6, 12}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 6}, {1, 2, 5, 6, 12}, {1, 2, 4, 6, 12}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 6}, {1, 2, 3, 6, 12}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 6}, {1, 2, 3, 4, 12}, {1, 2, 3, 4, 6}, {1, 2, 3, 4, 5}, {0, 4, 5, 6, 12}, {0, 3, 5, 6, 12}, {0, 3, 4, 6, 12}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 6}, {0, 2, 5, 6, 12}, {0, 2, 4, 6, 12}, {0, 2, 4, 5, 12}, {0, 2, 4, 5, 6}, {0, 2, 3, 6, 12}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 6}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 6}, {0, 2, 3, 4, 5}, {0, 1, 5, 6, 12}, {0, 1, 4, 6, 12}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 6}, {0, 1, 3, 6, 12}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 6}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 6}, {0, 1, 3, 4, 5}, {0, 1, 2, 6, 12}, {0, 1, 2, 5, 12}, {0, 1, 2, 5, 6}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 6}, {0, 1, 2, 4, 5}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 6}, {0, 1, 2, 3, 5}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask04223 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 5, 6, 12} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {2, 4, 5, 6, 12} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {1, 4, 5, 6, 12} ∨
        polygon = {1, 3, 5, 6, 12} ∨
        polygon = {1, 3, 4, 6, 12} ∨
        polygon = {1, 3, 4, 5, 12} ∨
        polygon = {1, 3, 4, 5, 6} ∨
        polygon = {1, 2, 5, 6, 12} ∨
        polygon = {1, 2, 4, 6, 12} ∨
        polygon = {1, 2, 4, 5, 12} ∨
        polygon = {1, 2, 4, 5, 6} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 6} ∨
        polygon = {1, 2, 3, 4, 12} ∨
        polygon = {1, 2, 3, 4, 6} ∨
        polygon = {1, 2, 3, 4, 5} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 6} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 4, 6, 12} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 6} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 6} ∨
        polygon = {0, 2, 3, 4, 5} ∨
        polygon = {0, 1, 5, 6, 12} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 6} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 6} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 6} ∨
        polygon = {0, 1, 3, 4, 5} ∨
        polygon = {0, 1, 2, 6, 12} ∨
        polygon = {0, 1, 2, 5, 12} ∨
        polygon = {0, 1, 2, 5, 6} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 6} ∨
        polygon = {0, 1, 2, 4, 5} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 6} ∨
        polygon = {0, 1, 2, 3, 5} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 5, 6, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask04223] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask08319 :
    (({0, 1, 2, 3, 4, 5, 6, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 6, 13}, {2, 4, 5, 6, 13}, {2, 3, 5, 6, 13}, {2, 3, 4, 6, 13}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 6}, {1, 4, 5, 6, 13}, {1, 3, 5, 6, 13}, {1, 3, 4, 6, 13}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 6}, {1, 2, 5, 6, 13}, {1, 2, 4, 6, 13}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 6}, {1, 2, 3, 6, 13}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 6}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 6}, {1, 2, 3, 4, 5}, {0, 4, 5, 6, 13}, {0, 3, 5, 6, 13}, {0, 3, 4, 6, 13}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 6}, {0, 2, 5, 6, 13}, {0, 2, 4, 6, 13}, {0, 2, 4, 5, 13}, {0, 2, 4, 5, 6}, {0, 2, 3, 6, 13}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 6}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 6}, {0, 2, 3, 4, 5}, {0, 1, 5, 6, 13}, {0, 1, 4, 6, 13}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 6}, {0, 1, 3, 6, 13}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 6}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 6}, {0, 1, 3, 4, 5}, {0, 1, 2, 6, 13}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 6}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 6}, {0, 1, 2, 4, 5}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 6}, {0, 1, 2, 3, 5}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask08319 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 5, 6, 13} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 6, 13} ∨
        polygon = {2, 4, 5, 6, 13} ∨
        polygon = {2, 3, 5, 6, 13} ∨
        polygon = {2, 3, 4, 6, 13} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {1, 4, 5, 6, 13} ∨
        polygon = {1, 3, 5, 6, 13} ∨
        polygon = {1, 3, 4, 6, 13} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 3, 4, 5, 6} ∨
        polygon = {1, 2, 5, 6, 13} ∨
        polygon = {1, 2, 4, 6, 13} ∨
        polygon = {1, 2, 4, 5, 13} ∨
        polygon = {1, 2, 4, 5, 6} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 6} ∨
        polygon = {1, 2, 3, 4, 13} ∨
        polygon = {1, 2, 3, 4, 6} ∨
        polygon = {1, 2, 3, 4, 5} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 3, 5, 6, 13} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 6} ∨
        polygon = {0, 2, 5, 6, 13} ∨
        polygon = {0, 2, 4, 6, 13} ∨
        polygon = {0, 2, 4, 5, 13} ∨
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 6} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 6} ∨
        polygon = {0, 2, 3, 4, 5} ∨
        polygon = {0, 1, 5, 6, 13} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 6} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 6} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 6} ∨
        polygon = {0, 1, 3, 4, 5} ∨
        polygon = {0, 1, 2, 6, 13} ∨
        polygon = {0, 1, 2, 5, 13} ∨
        polygon = {0, 1, 2, 5, 6} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 6} ∨
        polygon = {0, 1, 2, 4, 5} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 6} ∨
        polygon = {0, 1, 2, 3, 5} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 5, 6, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask08319] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask16511 :
    (({0, 1, 2, 3, 4, 5, 6, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 6, 14}, {2, 4, 5, 6, 14}, {2, 3, 5, 6, 14}, {2, 3, 4, 6, 14}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 6}, {1, 4, 5, 6, 14}, {1, 3, 5, 6, 14}, {1, 3, 4, 6, 14}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 6}, {1, 2, 5, 6, 14}, {1, 2, 4, 6, 14}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 6}, {1, 2, 3, 6, 14}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 6}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 6}, {1, 2, 3, 4, 5}, {0, 4, 5, 6, 14}, {0, 3, 5, 6, 14}, {0, 3, 4, 6, 14}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 6}, {0, 2, 5, 6, 14}, {0, 2, 4, 6, 14}, {0, 2, 4, 5, 14}, {0, 2, 4, 5, 6}, {0, 2, 3, 6, 14}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 6}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 6}, {0, 2, 3, 4, 5}, {0, 1, 5, 6, 14}, {0, 1, 4, 6, 14}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 6}, {0, 1, 3, 6, 14}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 6}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 6}, {0, 1, 3, 4, 5}, {0, 1, 2, 6, 14}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 6}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 6}, {0, 1, 2, 4, 5}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 6}, {0, 1, 2, 3, 5}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask16511 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 5, 6, 14} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 6, 14} ∨
        polygon = {2, 4, 5, 6, 14} ∨
        polygon = {2, 3, 5, 6, 14} ∨
        polygon = {2, 3, 4, 6, 14} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {1, 4, 5, 6, 14} ∨
        polygon = {1, 3, 5, 6, 14} ∨
        polygon = {1, 3, 4, 6, 14} ∨
        polygon = {1, 3, 4, 5, 14} ∨
        polygon = {1, 3, 4, 5, 6} ∨
        polygon = {1, 2, 5, 6, 14} ∨
        polygon = {1, 2, 4, 6, 14} ∨
        polygon = {1, 2, 4, 5, 14} ∨
        polygon = {1, 2, 4, 5, 6} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 6} ∨
        polygon = {1, 2, 3, 4, 14} ∨
        polygon = {1, 2, 3, 4, 6} ∨
        polygon = {1, 2, 3, 4, 5} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 3, 5, 6, 14} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 6} ∨
        polygon = {0, 2, 5, 6, 14} ∨
        polygon = {0, 2, 4, 6, 14} ∨
        polygon = {0, 2, 4, 5, 14} ∨
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 6} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 6} ∨
        polygon = {0, 2, 3, 4, 5} ∨
        polygon = {0, 1, 5, 6, 14} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 6} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 6} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 6} ∨
        polygon = {0, 1, 3, 4, 5} ∨
        polygon = {0, 1, 2, 6, 14} ∨
        polygon = {0, 1, 2, 5, 14} ∨
        polygon = {0, 1, 2, 5, 6} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 6} ∨
        polygon = {0, 1, 2, 4, 5} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 6} ∨
        polygon = {0, 1, 2, 3, 5} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 5, 6, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask16511] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask00703 :
    (({0, 1, 2, 3, 4, 5, 7, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 7, 9}, {2, 4, 5, 7, 9}, {2, 3, 5, 7, 9}, {2, 3, 4, 7, 9}, {2, 3, 4, 5, 9}, {2, 3, 4, 5, 7}, {1, 4, 5, 7, 9}, {1, 3, 5, 7, 9}, {1, 3, 4, 7, 9}, {1, 3, 4, 5, 9}, {1, 3, 4, 5, 7}, {1, 2, 5, 7, 9}, {1, 2, 4, 7, 9}, {1, 2, 4, 5, 9}, {1, 2, 4, 5, 7}, {1, 2, 3, 7, 9}, {1, 2, 3, 5, 9}, {1, 2, 3, 5, 7}, {1, 2, 3, 4, 9}, {1, 2, 3, 4, 7}, {1, 2, 3, 4, 5}, {0, 4, 5, 7, 9}, {0, 3, 5, 7, 9}, {0, 3, 4, 7, 9}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 7}, {0, 2, 5, 7, 9}, {0, 2, 4, 7, 9}, {0, 2, 4, 5, 9}, {0, 2, 4, 5, 7}, {0, 2, 3, 7, 9}, {0, 2, 3, 5, 9}, {0, 2, 3, 5, 7}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 7}, {0, 2, 3, 4, 5}, {0, 1, 5, 7, 9}, {0, 1, 4, 7, 9}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 7}, {0, 1, 3, 7, 9}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 7}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 5}, {0, 1, 2, 7, 9}, {0, 1, 2, 5, 9}, {0, 1, 2, 5, 7}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 7}, {0, 1, 2, 4, 5}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 5}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask00703 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 5, 7, 9} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {2, 4, 5, 7, 9} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {1, 4, 5, 7, 9} ∨
        polygon = {1, 3, 5, 7, 9} ∨
        polygon = {1, 3, 4, 7, 9} ∨
        polygon = {1, 3, 4, 5, 9} ∨
        polygon = {1, 3, 4, 5, 7} ∨
        polygon = {1, 2, 5, 7, 9} ∨
        polygon = {1, 2, 4, 7, 9} ∨
        polygon = {1, 2, 4, 5, 9} ∨
        polygon = {1, 2, 4, 5, 7} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {1, 2, 3, 5, 7} ∨
        polygon = {1, 2, 3, 4, 9} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {1, 2, 3, 4, 5} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 4, 7, 9} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 2, 3, 4, 5} ∨
        polygon = {0, 1, 5, 7, 9} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 4, 5, 7} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 5} ∨
        polygon = {0, 1, 2, 7, 9} ∨
        polygon = {0, 1, 2, 5, 9} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 4, 5} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 5} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 5, 7, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask00703] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01215 :
    (({0, 1, 2, 3, 4, 5, 7, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 7, 10}, {2, 4, 5, 7, 10}, {2, 3, 5, 7, 10}, {2, 3, 4, 7, 10}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 7}, {1, 4, 5, 7, 10}, {1, 3, 5, 7, 10}, {1, 3, 4, 7, 10}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 7}, {1, 2, 5, 7, 10}, {1, 2, 4, 7, 10}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 7}, {1, 2, 3, 7, 10}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 7}, {1, 2, 3, 4, 10}, {1, 2, 3, 4, 7}, {1, 2, 3, 4, 5}, {0, 4, 5, 7, 10}, {0, 3, 5, 7, 10}, {0, 3, 4, 7, 10}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 7}, {0, 2, 5, 7, 10}, {0, 2, 4, 7, 10}, {0, 2, 4, 5, 10}, {0, 2, 4, 5, 7}, {0, 2, 3, 7, 10}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 7}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 7}, {0, 2, 3, 4, 5}, {0, 1, 5, 7, 10}, {0, 1, 4, 7, 10}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 7}, {0, 1, 3, 7, 10}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 7}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 5}, {0, 1, 2, 7, 10}, {0, 1, 2, 5, 10}, {0, 1, 2, 5, 7}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 7}, {0, 1, 2, 4, 5}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 5}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01215 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 5, 7, 10} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {1, 4, 5, 7, 10} ∨
        polygon = {1, 3, 5, 7, 10} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {1, 3, 4, 5, 10} ∨
        polygon = {1, 3, 4, 5, 7} ∨
        polygon = {1, 2, 5, 7, 10} ∨
        polygon = {1, 2, 4, 7, 10} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {1, 2, 4, 5, 7} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 7} ∨
        polygon = {1, 2, 3, 4, 10} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {1, 2, 3, 4, 5} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 4, 7, 10} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 2, 3, 4, 5} ∨
        polygon = {0, 1, 5, 7, 10} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 7} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 5} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 4, 5} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 5} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 5, 7, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01215] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask04287 :
    (({0, 1, 2, 3, 4, 5, 7, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 7, 12}, {2, 4, 5, 7, 12}, {2, 3, 5, 7, 12}, {2, 3, 4, 7, 12}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 7}, {1, 4, 5, 7, 12}, {1, 3, 5, 7, 12}, {1, 3, 4, 7, 12}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 7}, {1, 2, 5, 7, 12}, {1, 2, 4, 7, 12}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 7}, {1, 2, 3, 7, 12}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 7}, {1, 2, 3, 4, 12}, {1, 2, 3, 4, 7}, {1, 2, 3, 4, 5}, {0, 4, 5, 7, 12}, {0, 3, 5, 7, 12}, {0, 3, 4, 7, 12}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 7}, {0, 2, 5, 7, 12}, {0, 2, 4, 7, 12}, {0, 2, 4, 5, 12}, {0, 2, 4, 5, 7}, {0, 2, 3, 7, 12}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 7}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 7}, {0, 2, 3, 4, 5}, {0, 1, 5, 7, 12}, {0, 1, 4, 7, 12}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 7}, {0, 1, 3, 7, 12}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 7}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 5}, {0, 1, 2, 7, 12}, {0, 1, 2, 5, 12}, {0, 1, 2, 5, 7}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 7}, {0, 1, 2, 4, 5}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 5}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask04287 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 5, 7, 12} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {1, 4, 5, 7, 12} ∨
        polygon = {1, 3, 5, 7, 12} ∨
        polygon = {1, 3, 4, 7, 12} ∨
        polygon = {1, 3, 4, 5, 12} ∨
        polygon = {1, 3, 4, 5, 7} ∨
        polygon = {1, 2, 5, 7, 12} ∨
        polygon = {1, 2, 4, 7, 12} ∨
        polygon = {1, 2, 4, 5, 12} ∨
        polygon = {1, 2, 4, 5, 7} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 7} ∨
        polygon = {1, 2, 3, 4, 12} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {1, 2, 3, 4, 5} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 4, 7, 12} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 2, 3, 4, 5} ∨
        polygon = {0, 1, 5, 7, 12} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 7} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 5} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 5, 12} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 4, 5} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 5} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 5, 7, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask04287] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask08383 :
    (({0, 1, 2, 3, 4, 5, 7, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 7, 13}, {2, 4, 5, 7, 13}, {2, 3, 5, 7, 13}, {2, 3, 4, 7, 13}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 7}, {1, 4, 5, 7, 13}, {1, 3, 5, 7, 13}, {1, 3, 4, 7, 13}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 7}, {1, 2, 5, 7, 13}, {1, 2, 4, 7, 13}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 7}, {1, 2, 3, 7, 13}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 7}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 7}, {1, 2, 3, 4, 5}, {0, 4, 5, 7, 13}, {0, 3, 5, 7, 13}, {0, 3, 4, 7, 13}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 7}, {0, 2, 5, 7, 13}, {0, 2, 4, 7, 13}, {0, 2, 4, 5, 13}, {0, 2, 4, 5, 7}, {0, 2, 3, 7, 13}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 7}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 7}, {0, 2, 3, 4, 5}, {0, 1, 5, 7, 13}, {0, 1, 4, 7, 13}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 7}, {0, 1, 3, 7, 13}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 7}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 5}, {0, 1, 2, 7, 13}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 7}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 7}, {0, 1, 2, 4, 5}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 5}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask08383 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 5, 7, 13} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 7, 13} ∨
        polygon = {2, 4, 5, 7, 13} ∨
        polygon = {2, 3, 5, 7, 13} ∨
        polygon = {2, 3, 4, 7, 13} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {1, 4, 5, 7, 13} ∨
        polygon = {1, 3, 5, 7, 13} ∨
        polygon = {1, 3, 4, 7, 13} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 3, 4, 5, 7} ∨
        polygon = {1, 2, 5, 7, 13} ∨
        polygon = {1, 2, 4, 7, 13} ∨
        polygon = {1, 2, 4, 5, 13} ∨
        polygon = {1, 2, 4, 5, 7} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 7} ∨
        polygon = {1, 2, 3, 4, 13} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {1, 2, 3, 4, 5} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 2, 5, 7, 13} ∨
        polygon = {0, 2, 4, 7, 13} ∨
        polygon = {0, 2, 4, 5, 13} ∨
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 2, 3, 4, 5} ∨
        polygon = {0, 1, 5, 7, 13} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 7} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 5} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 5, 13} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 4, 5} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 5} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 5, 7, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask08383] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask16575 :
    (({0, 1, 2, 3, 4, 5, 7, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 7, 14}, {2, 4, 5, 7, 14}, {2, 3, 5, 7, 14}, {2, 3, 4, 7, 14}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 7}, {1, 4, 5, 7, 14}, {1, 3, 5, 7, 14}, {1, 3, 4, 7, 14}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 7}, {1, 2, 5, 7, 14}, {1, 2, 4, 7, 14}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 7}, {1, 2, 3, 7, 14}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 7}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 7}, {1, 2, 3, 4, 5}, {0, 4, 5, 7, 14}, {0, 3, 5, 7, 14}, {0, 3, 4, 7, 14}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 7}, {0, 2, 5, 7, 14}, {0, 2, 4, 7, 14}, {0, 2, 4, 5, 14}, {0, 2, 4, 5, 7}, {0, 2, 3, 7, 14}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 7}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 7}, {0, 2, 3, 4, 5}, {0, 1, 5, 7, 14}, {0, 1, 4, 7, 14}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 7}, {0, 1, 3, 7, 14}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 7}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 5}, {0, 1, 2, 7, 14}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 7}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 7}, {0, 1, 2, 4, 5}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 5}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask16575 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 5, 7, 14} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 7, 14} ∨
        polygon = {2, 4, 5, 7, 14} ∨
        polygon = {2, 3, 5, 7, 14} ∨
        polygon = {2, 3, 4, 7, 14} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {1, 4, 5, 7, 14} ∨
        polygon = {1, 3, 5, 7, 14} ∨
        polygon = {1, 3, 4, 7, 14} ∨
        polygon = {1, 3, 4, 5, 14} ∨
        polygon = {1, 3, 4, 5, 7} ∨
        polygon = {1, 2, 5, 7, 14} ∨
        polygon = {1, 2, 4, 7, 14} ∨
        polygon = {1, 2, 4, 5, 14} ∨
        polygon = {1, 2, 4, 5, 7} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 7} ∨
        polygon = {1, 2, 3, 4, 14} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {1, 2, 3, 4, 5} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 2, 5, 7, 14} ∨
        polygon = {0, 2, 4, 7, 14} ∨
        polygon = {0, 2, 4, 5, 14} ∨
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 2, 3, 4, 5} ∨
        polygon = {0, 1, 5, 7, 14} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 7} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 5} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 5, 14} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 4, 5} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 5} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 5, 7, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask16575] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01599 :
    (({0, 1, 2, 3, 4, 5, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 9, 10}, {2, 4, 5, 9, 10}, {2, 3, 5, 9, 10}, {2, 3, 4, 9, 10}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 9}, {1, 4, 5, 9, 10}, {1, 3, 5, 9, 10}, {1, 3, 4, 9, 10}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 9}, {1, 2, 5, 9, 10}, {1, 2, 4, 9, 10}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 9}, {1, 2, 3, 9, 10}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 9}, {1, 2, 3, 4, 10}, {1, 2, 3, 4, 9}, {1, 2, 3, 4, 5}, {0, 4, 5, 9, 10}, {0, 3, 5, 9, 10}, {0, 3, 4, 9, 10}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 9}, {0, 2, 5, 9, 10}, {0, 2, 4, 9, 10}, {0, 2, 4, 5, 10}, {0, 2, 4, 5, 9}, {0, 2, 3, 9, 10}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 9}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 5}, {0, 1, 5, 9, 10}, {0, 1, 4, 9, 10}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 9}, {0, 1, 3, 9, 10}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 9}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 5}, {0, 1, 2, 9, 10}, {0, 1, 2, 5, 10}, {0, 1, 2, 5, 9}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 5}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 5}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01599 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 5, 9, 10} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {1, 4, 5, 9, 10} ∨
        polygon = {1, 3, 5, 9, 10} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {1, 3, 4, 5, 10} ∨
        polygon = {1, 3, 4, 5, 9} ∨
        polygon = {1, 2, 5, 9, 10} ∨
        polygon = {1, 2, 4, 9, 10} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {1, 2, 4, 5, 9} ∨
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {1, 2, 3, 4, 10} ∨
        polygon = {1, 2, 3, 4, 9} ∨
        polygon = {1, 2, 3, 4, 5} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 4, 9, 10} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 5} ∨
        polygon = {0, 1, 5, 9, 10} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 5} ∨
        polygon = {0, 1, 2, 9, 10} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 5, 9} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 5} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 5} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 5, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01599] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask04671 :
    (({0, 1, 2, 3, 4, 5, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 9, 12}, {2, 4, 5, 9, 12}, {2, 3, 5, 9, 12}, {2, 3, 4, 9, 12}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 9}, {1, 4, 5, 9, 12}, {1, 3, 5, 9, 12}, {1, 3, 4, 9, 12}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 9}, {1, 2, 5, 9, 12}, {1, 2, 4, 9, 12}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 9}, {1, 2, 3, 9, 12}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 9}, {1, 2, 3, 4, 12}, {1, 2, 3, 4, 9}, {1, 2, 3, 4, 5}, {0, 4, 5, 9, 12}, {0, 3, 5, 9, 12}, {0, 3, 4, 9, 12}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 9}, {0, 2, 5, 9, 12}, {0, 2, 4, 9, 12}, {0, 2, 4, 5, 12}, {0, 2, 4, 5, 9}, {0, 2, 3, 9, 12}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 9}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 5}, {0, 1, 5, 9, 12}, {0, 1, 4, 9, 12}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 9}, {0, 1, 3, 9, 12}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 9}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 5}, {0, 1, 2, 9, 12}, {0, 1, 2, 5, 12}, {0, 1, 2, 5, 9}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 5}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 5}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask04671 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 5, 9, 12} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {1, 4, 5, 9, 12} ∨
        polygon = {1, 3, 5, 9, 12} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {1, 3, 4, 5, 12} ∨
        polygon = {1, 3, 4, 5, 9} ∨
        polygon = {1, 2, 5, 9, 12} ∨
        polygon = {1, 2, 4, 9, 12} ∨
        polygon = {1, 2, 4, 5, 12} ∨
        polygon = {1, 2, 4, 5, 9} ∨
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {1, 2, 3, 4, 12} ∨
        polygon = {1, 2, 3, 4, 9} ∨
        polygon = {1, 2, 3, 4, 5} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 4, 9, 12} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 5} ∨
        polygon = {0, 1, 5, 9, 12} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 5} ∨
        polygon = {0, 1, 2, 9, 12} ∨
        polygon = {0, 1, 2, 5, 12} ∨
        polygon = {0, 1, 2, 5, 9} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 5} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 5} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 5, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask04671] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

end ErdosSzekeres

end
