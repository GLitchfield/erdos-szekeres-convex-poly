module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 092. -/

theorem predecessorHalfFin13_clause25633 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0454 chi ∧
      PredecessorHalfFin13Atom0456 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0501 chi ∧
      PredecessorHalfFin13Atom0938 chi ∧
      PredecessorHalfFin13Atom0940 chi ∧
      PredecessorHalfFin13Atom0945 chi ∧
      PredecessorHalfFin13Atom0961 chi ∧
      PredecessorHalfFin13Atom0981 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 5, 6, 8, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 5, 6, 8, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0452 PredecessorHalfFin13Atom0454 PredecessorHalfFin13Atom0456
    PredecessorHalfFin13Atom0463 PredecessorHalfFin13Atom0465 PredecessorHalfFin13Atom0470
    PredecessorHalfFin13Atom0478 PredecessorHalfFin13Atom0480 PredecessorHalfFin13Atom0485
    PredecessorHalfFin13Atom0501 PredecessorHalfFin13Atom0938 PredecessorHalfFin13Atom0940
    PredecessorHalfFin13Atom0945 PredecessorHalfFin13Atom0961 PredecessorHalfFin13Atom0981 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25636 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0454 chi ∧
      PredecessorHalfFin13Atom0456 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0504 chi ∧
      PredecessorHalfFin13Atom0941 chi ∧
      PredecessorHalfFin13Atom0943 chi ∧
      PredecessorHalfFin13Atom0945 chi ∧
      PredecessorHalfFin13Atom0964 chi ∧
      PredecessorHalfFin13Atom0984 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 5, 6, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 5, 6, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0453 PredecessorHalfFin13Atom0454 PredecessorHalfFin13Atom0456
    PredecessorHalfFin13Atom0466 PredecessorHalfFin13Atom0468 PredecessorHalfFin13Atom0470
    PredecessorHalfFin13Atom0481 PredecessorHalfFin13Atom0483 PredecessorHalfFin13Atom0485
    PredecessorHalfFin13Atom0504 PredecessorHalfFin13Atom0941 PredecessorHalfFin13Atom0943
    PredecessorHalfFin13Atom0945 PredecessorHalfFin13Atom0964 PredecessorHalfFin13Atom0984 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25639 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0459 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0497 chi ∧
      PredecessorHalfFin13Atom0947 chi ∧
      PredecessorHalfFin13Atom0948 chi ∧
      PredecessorHalfFin13Atom0951 chi ∧
      PredecessorHalfFin13Atom0957 chi ∧
      PredecessorHalfFin13Atom0987 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 5, 7, 8, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 5, 7, 8, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0457 PredecessorHalfFin13Atom0458 PredecessorHalfFin13Atom0459
    PredecessorHalfFin13Atom0462 PredecessorHalfFin13Atom0463 PredecessorHalfFin13Atom0466
    PredecessorHalfFin13Atom0487 PredecessorHalfFin13Atom0488 PredecessorHalfFin13Atom0491
    PredecessorHalfFin13Atom0497 PredecessorHalfFin13Atom0947 PredecessorHalfFin13Atom0948
    PredecessorHalfFin13Atom0951 PredecessorHalfFin13Atom0957 PredecessorHalfFin13Atom0987 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25641 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0461 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0499 chi ∧
      PredecessorHalfFin13Atom0947 chi ∧
      PredecessorHalfFin13Atom0950 chi ∧
      PredecessorHalfFin13Atom0953 chi ∧
      PredecessorHalfFin13Atom0959 chi ∧
      PredecessorHalfFin13Atom0989 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 5, 7, 8, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 5, 7, 8, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0457 PredecessorHalfFin13Atom0458 PredecessorHalfFin13Atom0461
    PredecessorHalfFin13Atom0462 PredecessorHalfFin13Atom0465 PredecessorHalfFin13Atom0468
    PredecessorHalfFin13Atom0487 PredecessorHalfFin13Atom0490 PredecessorHalfFin13Atom0493
    PredecessorHalfFin13Atom0499 PredecessorHalfFin13Atom0947 PredecessorHalfFin13Atom0950
    PredecessorHalfFin13Atom0953 PredecessorHalfFin13Atom0959 PredecessorHalfFin13Atom0989 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25643 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0459 chi ∧
      PredecessorHalfFin13Atom0461 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0501 chi ∧
      PredecessorHalfFin13Atom0948 chi ∧
      PredecessorHalfFin13Atom0950 chi ∧
      PredecessorHalfFin13Atom0955 chi ∧
      PredecessorHalfFin13Atom0961 chi ∧
      PredecessorHalfFin13Atom0991 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 5, 7, 8, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 5, 7, 8, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0457 PredecessorHalfFin13Atom0459 PredecessorHalfFin13Atom0461
    PredecessorHalfFin13Atom0463 PredecessorHalfFin13Atom0465 PredecessorHalfFin13Atom0470
    PredecessorHalfFin13Atom0488 PredecessorHalfFin13Atom0490 PredecessorHalfFin13Atom0495
    PredecessorHalfFin13Atom0501 PredecessorHalfFin13Atom0948 PredecessorHalfFin13Atom0950
    PredecessorHalfFin13Atom0955 PredecessorHalfFin13Atom0961 PredecessorHalfFin13Atom0991 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25646 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0459 chi ∧
      PredecessorHalfFin13Atom0461 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0504 chi ∧
      PredecessorHalfFin13Atom0951 chi ∧
      PredecessorHalfFin13Atom0953 chi ∧
      PredecessorHalfFin13Atom0955 chi ∧
      PredecessorHalfFin13Atom0964 chi ∧
      PredecessorHalfFin13Atom0994 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 5, 7, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 5, 7, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0458 PredecessorHalfFin13Atom0459 PredecessorHalfFin13Atom0461
    PredecessorHalfFin13Atom0466 PredecessorHalfFin13Atom0468 PredecessorHalfFin13Atom0470
    PredecessorHalfFin13Atom0491 PredecessorHalfFin13Atom0493 PredecessorHalfFin13Atom0495
    PredecessorHalfFin13Atom0504 PredecessorHalfFin13Atom0951 PredecessorHalfFin13Atom0953
    PredecessorHalfFin13Atom0955 PredecessorHalfFin13Atom0964 PredecessorHalfFin13Atom0994 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25654 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0473 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0497 chi ∧
      PredecessorHalfFin13Atom0967 chi ∧
      PredecessorHalfFin13Atom0968 chi ∧
      PredecessorHalfFin13Atom0971 chi ∧
      PredecessorHalfFin13Atom0977 chi ∧
      PredecessorHalfFin13Atom0987 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 6, 7, 8, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 6, 7, 8, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0472 PredecessorHalfFin13Atom0473 PredecessorHalfFin13Atom0474
    PredecessorHalfFin13Atom0477 PredecessorHalfFin13Atom0478 PredecessorHalfFin13Atom0481
    PredecessorHalfFin13Atom0487 PredecessorHalfFin13Atom0488 PredecessorHalfFin13Atom0491
    PredecessorHalfFin13Atom0497 PredecessorHalfFin13Atom0967 PredecessorHalfFin13Atom0968
    PredecessorHalfFin13Atom0971 PredecessorHalfFin13Atom0977 PredecessorHalfFin13Atom0987 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25656 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0473 chi ∧
      PredecessorHalfFin13Atom0476 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0499 chi ∧
      PredecessorHalfFin13Atom0967 chi ∧
      PredecessorHalfFin13Atom0970 chi ∧
      PredecessorHalfFin13Atom0973 chi ∧
      PredecessorHalfFin13Atom0979 chi ∧
      PredecessorHalfFin13Atom0989 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 6, 7, 8, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 6, 7, 8, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0472 PredecessorHalfFin13Atom0473 PredecessorHalfFin13Atom0476
    PredecessorHalfFin13Atom0477 PredecessorHalfFin13Atom0480 PredecessorHalfFin13Atom0483
    PredecessorHalfFin13Atom0487 PredecessorHalfFin13Atom0490 PredecessorHalfFin13Atom0493
    PredecessorHalfFin13Atom0499 PredecessorHalfFin13Atom0967 PredecessorHalfFin13Atom0970
    PredecessorHalfFin13Atom0973 PredecessorHalfFin13Atom0979 PredecessorHalfFin13Atom0989 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25658 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0476 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0501 chi ∧
      PredecessorHalfFin13Atom0968 chi ∧
      PredecessorHalfFin13Atom0970 chi ∧
      PredecessorHalfFin13Atom0975 chi ∧
      PredecessorHalfFin13Atom0981 chi ∧
      PredecessorHalfFin13Atom0991 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 6, 7, 8, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 6, 7, 8, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0472 PredecessorHalfFin13Atom0474 PredecessorHalfFin13Atom0476
    PredecessorHalfFin13Atom0478 PredecessorHalfFin13Atom0480 PredecessorHalfFin13Atom0485
    PredecessorHalfFin13Atom0488 PredecessorHalfFin13Atom0490 PredecessorHalfFin13Atom0495
    PredecessorHalfFin13Atom0501 PredecessorHalfFin13Atom0968 PredecessorHalfFin13Atom0970
    PredecessorHalfFin13Atom0975 PredecessorHalfFin13Atom0981 PredecessorHalfFin13Atom0991 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25661 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0473 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0476 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0504 chi ∧
      PredecessorHalfFin13Atom0971 chi ∧
      PredecessorHalfFin13Atom0973 chi ∧
      PredecessorHalfFin13Atom0975 chi ∧
      PredecessorHalfFin13Atom0984 chi ∧
      PredecessorHalfFin13Atom0994 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 6, 7, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 6, 7, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0473 PredecessorHalfFin13Atom0474 PredecessorHalfFin13Atom0476
    PredecessorHalfFin13Atom0481 PredecessorHalfFin13Atom0483 PredecessorHalfFin13Atom0485
    PredecessorHalfFin13Atom0491 PredecessorHalfFin13Atom0493 PredecessorHalfFin13Atom0495
    PredecessorHalfFin13Atom0504 PredecessorHalfFin13Atom0971 PredecessorHalfFin13Atom0973
    PredecessorHalfFin13Atom0975 PredecessorHalfFin13Atom0984 PredecessorHalfFin13Atom0994 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26137 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0680 chi ∧
      PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0687 chi ∧
      PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0799 chi ∧
      PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0876 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 5, 6, 7} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 5, 6, 7}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0672 PredecessorHalfFin13Atom0673 PredecessorHalfFin13Atom0674
    PredecessorHalfFin13Atom0680 PredecessorHalfFin13Atom0681 PredecessorHalfFin13Atom0687
    PredecessorHalfFin13Atom0708 PredecessorHalfFin13Atom0709 PredecessorHalfFin13Atom0715
    PredecessorHalfFin13Atom0736 PredecessorHalfFin13Atom0792 PredecessorHalfFin13Atom0793
    PredecessorHalfFin13Atom0799 PredecessorHalfFin13Atom0820 PredecessorHalfFin13Atom0876 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26138 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0675 chi ∧
      PredecessorHalfFin13Atom0680 chi ∧
      PredecessorHalfFin13Atom0682 chi ∧
      PredecessorHalfFin13Atom0688 chi ∧
      PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0821 chi ∧
      PredecessorHalfFin13Atom0877 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 5, 6, 8} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 5, 6, 8}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0672 PredecessorHalfFin13Atom0673 PredecessorHalfFin13Atom0675
    PredecessorHalfFin13Atom0680 PredecessorHalfFin13Atom0682 PredecessorHalfFin13Atom0688
    PredecessorHalfFin13Atom0708 PredecessorHalfFin13Atom0710 PredecessorHalfFin13Atom0716
    PredecessorHalfFin13Atom0737 PredecessorHalfFin13Atom0792 PredecessorHalfFin13Atom0794
    PredecessorHalfFin13Atom0800 PredecessorHalfFin13Atom0821 PredecessorHalfFin13Atom0877 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26139 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0676 chi ∧
      PredecessorHalfFin13Atom0680 chi ∧
      PredecessorHalfFin13Atom0683 chi ∧
      PredecessorHalfFin13Atom0689 chi ∧
      PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0878 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 5, 6, 9} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 5, 6, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0672 PredecessorHalfFin13Atom0673 PredecessorHalfFin13Atom0676
    PredecessorHalfFin13Atom0680 PredecessorHalfFin13Atom0683 PredecessorHalfFin13Atom0689
    PredecessorHalfFin13Atom0708 PredecessorHalfFin13Atom0711 PredecessorHalfFin13Atom0717
    PredecessorHalfFin13Atom0738 PredecessorHalfFin13Atom0792 PredecessorHalfFin13Atom0795
    PredecessorHalfFin13Atom0801 PredecessorHalfFin13Atom0822 PredecessorHalfFin13Atom0878 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26140 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0677 chi ∧
      PredecessorHalfFin13Atom0680 chi ∧
      PredecessorHalfFin13Atom0684 chi ∧
      PredecessorHalfFin13Atom0690 chi ∧
      PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0879 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 5, 6, 10} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 5, 6, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0672 PredecessorHalfFin13Atom0673 PredecessorHalfFin13Atom0677
    PredecessorHalfFin13Atom0680 PredecessorHalfFin13Atom0684 PredecessorHalfFin13Atom0690
    PredecessorHalfFin13Atom0708 PredecessorHalfFin13Atom0712 PredecessorHalfFin13Atom0718
    PredecessorHalfFin13Atom0739 PredecessorHalfFin13Atom0792 PredecessorHalfFin13Atom0796
    PredecessorHalfFin13Atom0802 PredecessorHalfFin13Atom0823 PredecessorHalfFin13Atom0879 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26141 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0678 chi ∧
      PredecessorHalfFin13Atom0680 chi ∧
      PredecessorHalfFin13Atom0685 chi ∧
      PredecessorHalfFin13Atom0691 chi ∧
      PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0713 chi ∧
      PredecessorHalfFin13Atom0719 chi ∧
      PredecessorHalfFin13Atom0740 chi ∧
      PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0797 chi ∧
      PredecessorHalfFin13Atom0803 chi ∧
      PredecessorHalfFin13Atom0824 chi ∧
      PredecessorHalfFin13Atom0880 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 5, 6, 11} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 5, 6, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0672 PredecessorHalfFin13Atom0673 PredecessorHalfFin13Atom0678
    PredecessorHalfFin13Atom0680 PredecessorHalfFin13Atom0685 PredecessorHalfFin13Atom0691
    PredecessorHalfFin13Atom0708 PredecessorHalfFin13Atom0713 PredecessorHalfFin13Atom0719
    PredecessorHalfFin13Atom0740 PredecessorHalfFin13Atom0792 PredecessorHalfFin13Atom0797
    PredecessorHalfFin13Atom0803 PredecessorHalfFin13Atom0824 PredecessorHalfFin13Atom0880 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26142 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0679 chi ∧
      PredecessorHalfFin13Atom0680 chi ∧
      PredecessorHalfFin13Atom0686 chi ∧
      PredecessorHalfFin13Atom0692 chi ∧
      PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0804 chi ∧
      PredecessorHalfFin13Atom0825 chi ∧
      PredecessorHalfFin13Atom0881 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 5, 6, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 5, 6, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0672 PredecessorHalfFin13Atom0673 PredecessorHalfFin13Atom0679
    PredecessorHalfFin13Atom0680 PredecessorHalfFin13Atom0686 PredecessorHalfFin13Atom0692
    PredecessorHalfFin13Atom0708 PredecessorHalfFin13Atom0714 PredecessorHalfFin13Atom0720
    PredecessorHalfFin13Atom0741 PredecessorHalfFin13Atom0792 PredecessorHalfFin13Atom0798
    PredecessorHalfFin13Atom0804 PredecessorHalfFin13Atom0825 PredecessorHalfFin13Atom0881 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26143 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0675 chi ∧
      PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0682 chi ∧
      PredecessorHalfFin13Atom0693 chi ∧
      PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0882 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 5, 7, 8} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 5, 7, 8}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0672 PredecessorHalfFin13Atom0674 PredecessorHalfFin13Atom0675
    PredecessorHalfFin13Atom0681 PredecessorHalfFin13Atom0682 PredecessorHalfFin13Atom0693
    PredecessorHalfFin13Atom0709 PredecessorHalfFin13Atom0710 PredecessorHalfFin13Atom0721
    PredecessorHalfFin13Atom0742 PredecessorHalfFin13Atom0793 PredecessorHalfFin13Atom0794
    PredecessorHalfFin13Atom0805 PredecessorHalfFin13Atom0826 PredecessorHalfFin13Atom0882 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26144 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0676 chi ∧
      PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0683 chi ∧
      PredecessorHalfFin13Atom0694 chi ∧
      PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0883 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 5, 7, 9} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 5, 7, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0672 PredecessorHalfFin13Atom0674 PredecessorHalfFin13Atom0676
    PredecessorHalfFin13Atom0681 PredecessorHalfFin13Atom0683 PredecessorHalfFin13Atom0694
    PredecessorHalfFin13Atom0709 PredecessorHalfFin13Atom0711 PredecessorHalfFin13Atom0722
    PredecessorHalfFin13Atom0743 PredecessorHalfFin13Atom0793 PredecessorHalfFin13Atom0795
    PredecessorHalfFin13Atom0806 PredecessorHalfFin13Atom0827 PredecessorHalfFin13Atom0883 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26145 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0677 chi ∧
      PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0684 chi ∧
      PredecessorHalfFin13Atom0695 chi ∧
      PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0884 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 5, 7, 10} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 5, 7, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0672 PredecessorHalfFin13Atom0674 PredecessorHalfFin13Atom0677
    PredecessorHalfFin13Atom0681 PredecessorHalfFin13Atom0684 PredecessorHalfFin13Atom0695
    PredecessorHalfFin13Atom0709 PredecessorHalfFin13Atom0712 PredecessorHalfFin13Atom0723
    PredecessorHalfFin13Atom0744 PredecessorHalfFin13Atom0793 PredecessorHalfFin13Atom0796
    PredecessorHalfFin13Atom0807 PredecessorHalfFin13Atom0828 PredecessorHalfFin13Atom0884 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26146 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0678 chi ∧
      PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0685 chi ∧
      PredecessorHalfFin13Atom0696 chi ∧
      PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0713 chi ∧
      PredecessorHalfFin13Atom0724 chi ∧
      PredecessorHalfFin13Atom0745 chi ∧
      PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0797 chi ∧
      PredecessorHalfFin13Atom0808 chi ∧
      PredecessorHalfFin13Atom0829 chi ∧
      PredecessorHalfFin13Atom0885 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 5, 7, 11} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 5, 7, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0672 PredecessorHalfFin13Atom0674 PredecessorHalfFin13Atom0678
    PredecessorHalfFin13Atom0681 PredecessorHalfFin13Atom0685 PredecessorHalfFin13Atom0696
    PredecessorHalfFin13Atom0709 PredecessorHalfFin13Atom0713 PredecessorHalfFin13Atom0724
    PredecessorHalfFin13Atom0745 PredecessorHalfFin13Atom0793 PredecessorHalfFin13Atom0797
    PredecessorHalfFin13Atom0808 PredecessorHalfFin13Atom0829 PredecessorHalfFin13Atom0885 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26147 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0679 chi ∧
      PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0686 chi ∧
      PredecessorHalfFin13Atom0697 chi ∧
      PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0886 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 5, 7, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 5, 7, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0672 PredecessorHalfFin13Atom0674 PredecessorHalfFin13Atom0679
    PredecessorHalfFin13Atom0681 PredecessorHalfFin13Atom0686 PredecessorHalfFin13Atom0697
    PredecessorHalfFin13Atom0709 PredecessorHalfFin13Atom0714 PredecessorHalfFin13Atom0725
    PredecessorHalfFin13Atom0746 PredecessorHalfFin13Atom0793 PredecessorHalfFin13Atom0798
    PredecessorHalfFin13Atom0809 PredecessorHalfFin13Atom0830 PredecessorHalfFin13Atom0886 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26148 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0675 chi ∧
      PredecessorHalfFin13Atom0676 chi ∧
      PredecessorHalfFin13Atom0682 chi ∧
      PredecessorHalfFin13Atom0683 chi ∧
      PredecessorHalfFin13Atom0698 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0887 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 5, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 5, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0672 PredecessorHalfFin13Atom0675 PredecessorHalfFin13Atom0676
    PredecessorHalfFin13Atom0682 PredecessorHalfFin13Atom0683 PredecessorHalfFin13Atom0698
    PredecessorHalfFin13Atom0710 PredecessorHalfFin13Atom0711 PredecessorHalfFin13Atom0726
    PredecessorHalfFin13Atom0747 PredecessorHalfFin13Atom0794 PredecessorHalfFin13Atom0795
    PredecessorHalfFin13Atom0810 PredecessorHalfFin13Atom0831 PredecessorHalfFin13Atom0887 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26149 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0675 chi ∧
      PredecessorHalfFin13Atom0677 chi ∧
      PredecessorHalfFin13Atom0682 chi ∧
      PredecessorHalfFin13Atom0684 chi ∧
      PredecessorHalfFin13Atom0699 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0888 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 5, 8, 10} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 5, 8, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0672 PredecessorHalfFin13Atom0675 PredecessorHalfFin13Atom0677
    PredecessorHalfFin13Atom0682 PredecessorHalfFin13Atom0684 PredecessorHalfFin13Atom0699
    PredecessorHalfFin13Atom0710 PredecessorHalfFin13Atom0712 PredecessorHalfFin13Atom0727
    PredecessorHalfFin13Atom0748 PredecessorHalfFin13Atom0794 PredecessorHalfFin13Atom0796
    PredecessorHalfFin13Atom0811 PredecessorHalfFin13Atom0832 PredecessorHalfFin13Atom0888 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26150 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0675 chi ∧
      PredecessorHalfFin13Atom0678 chi ∧
      PredecessorHalfFin13Atom0682 chi ∧
      PredecessorHalfFin13Atom0685 chi ∧
      PredecessorHalfFin13Atom0700 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0713 chi ∧
      PredecessorHalfFin13Atom0728 chi ∧
      PredecessorHalfFin13Atom0749 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0797 chi ∧
      PredecessorHalfFin13Atom0812 chi ∧
      PredecessorHalfFin13Atom0833 chi ∧
      PredecessorHalfFin13Atom0889 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 5, 8, 11} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 5, 8, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0672 PredecessorHalfFin13Atom0675 PredecessorHalfFin13Atom0678
    PredecessorHalfFin13Atom0682 PredecessorHalfFin13Atom0685 PredecessorHalfFin13Atom0700
    PredecessorHalfFin13Atom0710 PredecessorHalfFin13Atom0713 PredecessorHalfFin13Atom0728
    PredecessorHalfFin13Atom0749 PredecessorHalfFin13Atom0794 PredecessorHalfFin13Atom0797
    PredecessorHalfFin13Atom0812 PredecessorHalfFin13Atom0833 PredecessorHalfFin13Atom0889 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26151 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0675 chi ∧
      PredecessorHalfFin13Atom0679 chi ∧
      PredecessorHalfFin13Atom0682 chi ∧
      PredecessorHalfFin13Atom0686 chi ∧
      PredecessorHalfFin13Atom0701 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0813 chi ∧
      PredecessorHalfFin13Atom0834 chi ∧
      PredecessorHalfFin13Atom0890 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 5, 8, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 5, 8, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0672 PredecessorHalfFin13Atom0675 PredecessorHalfFin13Atom0679
    PredecessorHalfFin13Atom0682 PredecessorHalfFin13Atom0686 PredecessorHalfFin13Atom0701
    PredecessorHalfFin13Atom0710 PredecessorHalfFin13Atom0714 PredecessorHalfFin13Atom0729
    PredecessorHalfFin13Atom0750 PredecessorHalfFin13Atom0794 PredecessorHalfFin13Atom0798
    PredecessorHalfFin13Atom0813 PredecessorHalfFin13Atom0834 PredecessorHalfFin13Atom0890 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26152 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0676 chi ∧
      PredecessorHalfFin13Atom0677 chi ∧
      PredecessorHalfFin13Atom0683 chi ∧
      PredecessorHalfFin13Atom0684 chi ∧
      PredecessorHalfFin13Atom0702 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0891 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 5, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 5, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0672 PredecessorHalfFin13Atom0676 PredecessorHalfFin13Atom0677
    PredecessorHalfFin13Atom0683 PredecessorHalfFin13Atom0684 PredecessorHalfFin13Atom0702
    PredecessorHalfFin13Atom0711 PredecessorHalfFin13Atom0712 PredecessorHalfFin13Atom0730
    PredecessorHalfFin13Atom0751 PredecessorHalfFin13Atom0795 PredecessorHalfFin13Atom0796
    PredecessorHalfFin13Atom0814 PredecessorHalfFin13Atom0835 PredecessorHalfFin13Atom0891 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26154 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0676 chi ∧
      PredecessorHalfFin13Atom0679 chi ∧
      PredecessorHalfFin13Atom0683 chi ∧
      PredecessorHalfFin13Atom0686 chi ∧
      PredecessorHalfFin13Atom0704 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0816 chi ∧
      PredecessorHalfFin13Atom0837 chi ∧
      PredecessorHalfFin13Atom0893 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 5, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 5, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0672 PredecessorHalfFin13Atom0676 PredecessorHalfFin13Atom0679
    PredecessorHalfFin13Atom0683 PredecessorHalfFin13Atom0686 PredecessorHalfFin13Atom0704
    PredecessorHalfFin13Atom0711 PredecessorHalfFin13Atom0714 PredecessorHalfFin13Atom0732
    PredecessorHalfFin13Atom0753 PredecessorHalfFin13Atom0795 PredecessorHalfFin13Atom0798
    PredecessorHalfFin13Atom0816 PredecessorHalfFin13Atom0837 PredecessorHalfFin13Atom0893 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26155 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0677 chi ∧
      PredecessorHalfFin13Atom0678 chi ∧
      PredecessorHalfFin13Atom0684 chi ∧
      PredecessorHalfFin13Atom0685 chi ∧
      PredecessorHalfFin13Atom0705 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0713 chi ∧
      PredecessorHalfFin13Atom0733 chi ∧
      PredecessorHalfFin13Atom0754 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0797 chi ∧
      PredecessorHalfFin13Atom0817 chi ∧
      PredecessorHalfFin13Atom0838 chi ∧
      PredecessorHalfFin13Atom0894 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 5, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 5, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0672 PredecessorHalfFin13Atom0677 PredecessorHalfFin13Atom0678
    PredecessorHalfFin13Atom0684 PredecessorHalfFin13Atom0685 PredecessorHalfFin13Atom0705
    PredecessorHalfFin13Atom0712 PredecessorHalfFin13Atom0713 PredecessorHalfFin13Atom0733
    PredecessorHalfFin13Atom0754 PredecessorHalfFin13Atom0796 PredecessorHalfFin13Atom0797
    PredecessorHalfFin13Atom0817 PredecessorHalfFin13Atom0838 PredecessorHalfFin13Atom0894 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26156 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0677 chi ∧
      PredecessorHalfFin13Atom0679 chi ∧
      PredecessorHalfFin13Atom0684 chi ∧
      PredecessorHalfFin13Atom0686 chi ∧
      PredecessorHalfFin13Atom0706 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0818 chi ∧
      PredecessorHalfFin13Atom0839 chi ∧
      PredecessorHalfFin13Atom0895 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 5, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 5, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0672 PredecessorHalfFin13Atom0677 PredecessorHalfFin13Atom0679
    PredecessorHalfFin13Atom0684 PredecessorHalfFin13Atom0686 PredecessorHalfFin13Atom0706
    PredecessorHalfFin13Atom0712 PredecessorHalfFin13Atom0714 PredecessorHalfFin13Atom0734
    PredecessorHalfFin13Atom0755 PredecessorHalfFin13Atom0796 PredecessorHalfFin13Atom0798
    PredecessorHalfFin13Atom0818 PredecessorHalfFin13Atom0839 PredecessorHalfFin13Atom0895 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26158 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0675 chi ∧
      PredecessorHalfFin13Atom0687 chi ∧
      PredecessorHalfFin13Atom0688 chi ∧
      PredecessorHalfFin13Atom0693 chi ∧
      PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0799 chi ∧
      PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0841 chi ∧
      PredecessorHalfFin13Atom0897 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 6, 7, 8} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 6, 7, 8}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0673 PredecessorHalfFin13Atom0674 PredecessorHalfFin13Atom0675
    PredecessorHalfFin13Atom0687 PredecessorHalfFin13Atom0688 PredecessorHalfFin13Atom0693
    PredecessorHalfFin13Atom0715 PredecessorHalfFin13Atom0716 PredecessorHalfFin13Atom0721
    PredecessorHalfFin13Atom0757 PredecessorHalfFin13Atom0799 PredecessorHalfFin13Atom0800
    PredecessorHalfFin13Atom0805 PredecessorHalfFin13Atom0841 PredecessorHalfFin13Atom0897 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26159 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0676 chi ∧
      PredecessorHalfFin13Atom0687 chi ∧
      PredecessorHalfFin13Atom0689 chi ∧
      PredecessorHalfFin13Atom0694 chi ∧
      PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0799 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0842 chi ∧
      PredecessorHalfFin13Atom0898 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 6, 7, 9} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 6, 7, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0673 PredecessorHalfFin13Atom0674 PredecessorHalfFin13Atom0676
    PredecessorHalfFin13Atom0687 PredecessorHalfFin13Atom0689 PredecessorHalfFin13Atom0694
    PredecessorHalfFin13Atom0715 PredecessorHalfFin13Atom0717 PredecessorHalfFin13Atom0722
    PredecessorHalfFin13Atom0758 PredecessorHalfFin13Atom0799 PredecessorHalfFin13Atom0801
    PredecessorHalfFin13Atom0806 PredecessorHalfFin13Atom0842 PredecessorHalfFin13Atom0898 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26160 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0677 chi ∧
      PredecessorHalfFin13Atom0687 chi ∧
      PredecessorHalfFin13Atom0690 chi ∧
      PredecessorHalfFin13Atom0695 chi ∧
      PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0799 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0843 chi ∧
      PredecessorHalfFin13Atom0899 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 6, 7, 10} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 6, 7, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0673 PredecessorHalfFin13Atom0674 PredecessorHalfFin13Atom0677
    PredecessorHalfFin13Atom0687 PredecessorHalfFin13Atom0690 PredecessorHalfFin13Atom0695
    PredecessorHalfFin13Atom0715 PredecessorHalfFin13Atom0718 PredecessorHalfFin13Atom0723
    PredecessorHalfFin13Atom0759 PredecessorHalfFin13Atom0799 PredecessorHalfFin13Atom0802
    PredecessorHalfFin13Atom0807 PredecessorHalfFin13Atom0843 PredecessorHalfFin13Atom0899 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26161 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0678 chi ∧
      PredecessorHalfFin13Atom0687 chi ∧
      PredecessorHalfFin13Atom0691 chi ∧
      PredecessorHalfFin13Atom0696 chi ∧
      PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0719 chi ∧
      PredecessorHalfFin13Atom0724 chi ∧
      PredecessorHalfFin13Atom0760 chi ∧
      PredecessorHalfFin13Atom0799 chi ∧
      PredecessorHalfFin13Atom0803 chi ∧
      PredecessorHalfFin13Atom0808 chi ∧
      PredecessorHalfFin13Atom0844 chi ∧
      PredecessorHalfFin13Atom0900 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 6, 7, 11} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 6, 7, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0673 PredecessorHalfFin13Atom0674 PredecessorHalfFin13Atom0678
    PredecessorHalfFin13Atom0687 PredecessorHalfFin13Atom0691 PredecessorHalfFin13Atom0696
    PredecessorHalfFin13Atom0715 PredecessorHalfFin13Atom0719 PredecessorHalfFin13Atom0724
    PredecessorHalfFin13Atom0760 PredecessorHalfFin13Atom0799 PredecessorHalfFin13Atom0803
    PredecessorHalfFin13Atom0808 PredecessorHalfFin13Atom0844 PredecessorHalfFin13Atom0900 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26162 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0679 chi ∧
      PredecessorHalfFin13Atom0687 chi ∧
      PredecessorHalfFin13Atom0692 chi ∧
      PredecessorHalfFin13Atom0697 chi ∧
      PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0799 chi ∧
      PredecessorHalfFin13Atom0804 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0845 chi ∧
      PredecessorHalfFin13Atom0901 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 6, 7, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 6, 7, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0673 PredecessorHalfFin13Atom0674 PredecessorHalfFin13Atom0679
    PredecessorHalfFin13Atom0687 PredecessorHalfFin13Atom0692 PredecessorHalfFin13Atom0697
    PredecessorHalfFin13Atom0715 PredecessorHalfFin13Atom0720 PredecessorHalfFin13Atom0725
    PredecessorHalfFin13Atom0761 PredecessorHalfFin13Atom0799 PredecessorHalfFin13Atom0804
    PredecessorHalfFin13Atom0809 PredecessorHalfFin13Atom0845 PredecessorHalfFin13Atom0901 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26163 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0675 chi ∧
      PredecessorHalfFin13Atom0676 chi ∧
      PredecessorHalfFin13Atom0688 chi ∧
      PredecessorHalfFin13Atom0689 chi ∧
      PredecessorHalfFin13Atom0698 chi ∧
      PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0846 chi ∧
      PredecessorHalfFin13Atom0902 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 6, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 6, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0673 PredecessorHalfFin13Atom0675 PredecessorHalfFin13Atom0676
    PredecessorHalfFin13Atom0688 PredecessorHalfFin13Atom0689 PredecessorHalfFin13Atom0698
    PredecessorHalfFin13Atom0716 PredecessorHalfFin13Atom0717 PredecessorHalfFin13Atom0726
    PredecessorHalfFin13Atom0762 PredecessorHalfFin13Atom0800 PredecessorHalfFin13Atom0801
    PredecessorHalfFin13Atom0810 PredecessorHalfFin13Atom0846 PredecessorHalfFin13Atom0902 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26164 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0675 chi ∧
      PredecessorHalfFin13Atom0677 chi ∧
      PredecessorHalfFin13Atom0688 chi ∧
      PredecessorHalfFin13Atom0690 chi ∧
      PredecessorHalfFin13Atom0699 chi ∧
      PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0847 chi ∧
      PredecessorHalfFin13Atom0903 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 6, 8, 10} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 6, 8, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0673 PredecessorHalfFin13Atom0675 PredecessorHalfFin13Atom0677
    PredecessorHalfFin13Atom0688 PredecessorHalfFin13Atom0690 PredecessorHalfFin13Atom0699
    PredecessorHalfFin13Atom0716 PredecessorHalfFin13Atom0718 PredecessorHalfFin13Atom0727
    PredecessorHalfFin13Atom0763 PredecessorHalfFin13Atom0800 PredecessorHalfFin13Atom0802
    PredecessorHalfFin13Atom0811 PredecessorHalfFin13Atom0847 PredecessorHalfFin13Atom0903 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26165 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0675 chi ∧
      PredecessorHalfFin13Atom0678 chi ∧
      PredecessorHalfFin13Atom0688 chi ∧
      PredecessorHalfFin13Atom0691 chi ∧
      PredecessorHalfFin13Atom0700 chi ∧
      PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0719 chi ∧
      PredecessorHalfFin13Atom0728 chi ∧
      PredecessorHalfFin13Atom0764 chi ∧
      PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0803 chi ∧
      PredecessorHalfFin13Atom0812 chi ∧
      PredecessorHalfFin13Atom0848 chi ∧
      PredecessorHalfFin13Atom0904 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 6, 8, 11} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 6, 8, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0673 PredecessorHalfFin13Atom0675 PredecessorHalfFin13Atom0678
    PredecessorHalfFin13Atom0688 PredecessorHalfFin13Atom0691 PredecessorHalfFin13Atom0700
    PredecessorHalfFin13Atom0716 PredecessorHalfFin13Atom0719 PredecessorHalfFin13Atom0728
    PredecessorHalfFin13Atom0764 PredecessorHalfFin13Atom0800 PredecessorHalfFin13Atom0803
    PredecessorHalfFin13Atom0812 PredecessorHalfFin13Atom0848 PredecessorHalfFin13Atom0904 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26166 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0675 chi ∧
      PredecessorHalfFin13Atom0679 chi ∧
      PredecessorHalfFin13Atom0688 chi ∧
      PredecessorHalfFin13Atom0692 chi ∧
      PredecessorHalfFin13Atom0701 chi ∧
      PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0804 chi ∧
      PredecessorHalfFin13Atom0813 chi ∧
      PredecessorHalfFin13Atom0849 chi ∧
      PredecessorHalfFin13Atom0905 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 6, 8, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 6, 8, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0673 PredecessorHalfFin13Atom0675 PredecessorHalfFin13Atom0679
    PredecessorHalfFin13Atom0688 PredecessorHalfFin13Atom0692 PredecessorHalfFin13Atom0701
    PredecessorHalfFin13Atom0716 PredecessorHalfFin13Atom0720 PredecessorHalfFin13Atom0729
    PredecessorHalfFin13Atom0765 PredecessorHalfFin13Atom0800 PredecessorHalfFin13Atom0804
    PredecessorHalfFin13Atom0813 PredecessorHalfFin13Atom0849 PredecessorHalfFin13Atom0905 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26167 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0676 chi ∧
      PredecessorHalfFin13Atom0677 chi ∧
      PredecessorHalfFin13Atom0689 chi ∧
      PredecessorHalfFin13Atom0690 chi ∧
      PredecessorHalfFin13Atom0702 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0850 chi ∧
      PredecessorHalfFin13Atom0906 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 6, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 6, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0673 PredecessorHalfFin13Atom0676 PredecessorHalfFin13Atom0677
    PredecessorHalfFin13Atom0689 PredecessorHalfFin13Atom0690 PredecessorHalfFin13Atom0702
    PredecessorHalfFin13Atom0717 PredecessorHalfFin13Atom0718 PredecessorHalfFin13Atom0730
    PredecessorHalfFin13Atom0766 PredecessorHalfFin13Atom0801 PredecessorHalfFin13Atom0802
    PredecessorHalfFin13Atom0814 PredecessorHalfFin13Atom0850 PredecessorHalfFin13Atom0906 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26169 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0676 chi ∧
      PredecessorHalfFin13Atom0679 chi ∧
      PredecessorHalfFin13Atom0689 chi ∧
      PredecessorHalfFin13Atom0692 chi ∧
      PredecessorHalfFin13Atom0704 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0804 chi ∧
      PredecessorHalfFin13Atom0816 chi ∧
      PredecessorHalfFin13Atom0852 chi ∧
      PredecessorHalfFin13Atom0908 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 6, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 6, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0673 PredecessorHalfFin13Atom0676 PredecessorHalfFin13Atom0679
    PredecessorHalfFin13Atom0689 PredecessorHalfFin13Atom0692 PredecessorHalfFin13Atom0704
    PredecessorHalfFin13Atom0717 PredecessorHalfFin13Atom0720 PredecessorHalfFin13Atom0732
    PredecessorHalfFin13Atom0768 PredecessorHalfFin13Atom0801 PredecessorHalfFin13Atom0804
    PredecessorHalfFin13Atom0816 PredecessorHalfFin13Atom0852 PredecessorHalfFin13Atom0908 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26170 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0677 chi ∧
      PredecessorHalfFin13Atom0678 chi ∧
      PredecessorHalfFin13Atom0690 chi ∧
      PredecessorHalfFin13Atom0691 chi ∧
      PredecessorHalfFin13Atom0705 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0719 chi ∧
      PredecessorHalfFin13Atom0733 chi ∧
      PredecessorHalfFin13Atom0769 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0803 chi ∧
      PredecessorHalfFin13Atom0817 chi ∧
      PredecessorHalfFin13Atom0853 chi ∧
      PredecessorHalfFin13Atom0909 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 6, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 6, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0673 PredecessorHalfFin13Atom0677 PredecessorHalfFin13Atom0678
    PredecessorHalfFin13Atom0690 PredecessorHalfFin13Atom0691 PredecessorHalfFin13Atom0705
    PredecessorHalfFin13Atom0718 PredecessorHalfFin13Atom0719 PredecessorHalfFin13Atom0733
    PredecessorHalfFin13Atom0769 PredecessorHalfFin13Atom0802 PredecessorHalfFin13Atom0803
    PredecessorHalfFin13Atom0817 PredecessorHalfFin13Atom0853 PredecessorHalfFin13Atom0909 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26171 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0677 chi ∧
      PredecessorHalfFin13Atom0679 chi ∧
      PredecessorHalfFin13Atom0690 chi ∧
      PredecessorHalfFin13Atom0692 chi ∧
      PredecessorHalfFin13Atom0706 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0804 chi ∧
      PredecessorHalfFin13Atom0818 chi ∧
      PredecessorHalfFin13Atom0854 chi ∧
      PredecessorHalfFin13Atom0910 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 6, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 6, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0673 PredecessorHalfFin13Atom0677 PredecessorHalfFin13Atom0679
    PredecessorHalfFin13Atom0690 PredecessorHalfFin13Atom0692 PredecessorHalfFin13Atom0706
    PredecessorHalfFin13Atom0718 PredecessorHalfFin13Atom0720 PredecessorHalfFin13Atom0734
    PredecessorHalfFin13Atom0770 PredecessorHalfFin13Atom0802 PredecessorHalfFin13Atom0804
    PredecessorHalfFin13Atom0818 PredecessorHalfFin13Atom0854 PredecessorHalfFin13Atom0910 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26173 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0675 chi ∧
      PredecessorHalfFin13Atom0676 chi ∧
      PredecessorHalfFin13Atom0693 chi ∧
      PredecessorHalfFin13Atom0694 chi ∧
      PredecessorHalfFin13Atom0698 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0856 chi ∧
      PredecessorHalfFin13Atom0912 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 7, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 7, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0674 PredecessorHalfFin13Atom0675 PredecessorHalfFin13Atom0676
    PredecessorHalfFin13Atom0693 PredecessorHalfFin13Atom0694 PredecessorHalfFin13Atom0698
    PredecessorHalfFin13Atom0721 PredecessorHalfFin13Atom0722 PredecessorHalfFin13Atom0726
    PredecessorHalfFin13Atom0772 PredecessorHalfFin13Atom0805 PredecessorHalfFin13Atom0806
    PredecessorHalfFin13Atom0810 PredecessorHalfFin13Atom0856 PredecessorHalfFin13Atom0912 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26174 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0675 chi ∧
      PredecessorHalfFin13Atom0677 chi ∧
      PredecessorHalfFin13Atom0693 chi ∧
      PredecessorHalfFin13Atom0695 chi ∧
      PredecessorHalfFin13Atom0699 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0857 chi ∧
      PredecessorHalfFin13Atom0913 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 7, 8, 10} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 7, 8, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0674 PredecessorHalfFin13Atom0675 PredecessorHalfFin13Atom0677
    PredecessorHalfFin13Atom0693 PredecessorHalfFin13Atom0695 PredecessorHalfFin13Atom0699
    PredecessorHalfFin13Atom0721 PredecessorHalfFin13Atom0723 PredecessorHalfFin13Atom0727
    PredecessorHalfFin13Atom0773 PredecessorHalfFin13Atom0805 PredecessorHalfFin13Atom0807
    PredecessorHalfFin13Atom0811 PredecessorHalfFin13Atom0857 PredecessorHalfFin13Atom0913 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26175 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0675 chi ∧
      PredecessorHalfFin13Atom0678 chi ∧
      PredecessorHalfFin13Atom0693 chi ∧
      PredecessorHalfFin13Atom0696 chi ∧
      PredecessorHalfFin13Atom0700 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0724 chi ∧
      PredecessorHalfFin13Atom0728 chi ∧
      PredecessorHalfFin13Atom0774 chi ∧
      PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0808 chi ∧
      PredecessorHalfFin13Atom0812 chi ∧
      PredecessorHalfFin13Atom0858 chi ∧
      PredecessorHalfFin13Atom0914 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 7, 8, 11} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 7, 8, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0674 PredecessorHalfFin13Atom0675 PredecessorHalfFin13Atom0678
    PredecessorHalfFin13Atom0693 PredecessorHalfFin13Atom0696 PredecessorHalfFin13Atom0700
    PredecessorHalfFin13Atom0721 PredecessorHalfFin13Atom0724 PredecessorHalfFin13Atom0728
    PredecessorHalfFin13Atom0774 PredecessorHalfFin13Atom0805 PredecessorHalfFin13Atom0808
    PredecessorHalfFin13Atom0812 PredecessorHalfFin13Atom0858 PredecessorHalfFin13Atom0914 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26176 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0675 chi ∧
      PredecessorHalfFin13Atom0679 chi ∧
      PredecessorHalfFin13Atom0693 chi ∧
      PredecessorHalfFin13Atom0697 chi ∧
      PredecessorHalfFin13Atom0701 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0813 chi ∧
      PredecessorHalfFin13Atom0859 chi ∧
      PredecessorHalfFin13Atom0915 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 7, 8, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 7, 8, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0674 PredecessorHalfFin13Atom0675 PredecessorHalfFin13Atom0679
    PredecessorHalfFin13Atom0693 PredecessorHalfFin13Atom0697 PredecessorHalfFin13Atom0701
    PredecessorHalfFin13Atom0721 PredecessorHalfFin13Atom0725 PredecessorHalfFin13Atom0729
    PredecessorHalfFin13Atom0775 PredecessorHalfFin13Atom0805 PredecessorHalfFin13Atom0809
    PredecessorHalfFin13Atom0813 PredecessorHalfFin13Atom0859 PredecessorHalfFin13Atom0915 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26177 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0676 chi ∧
      PredecessorHalfFin13Atom0677 chi ∧
      PredecessorHalfFin13Atom0694 chi ∧
      PredecessorHalfFin13Atom0695 chi ∧
      PredecessorHalfFin13Atom0702 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0860 chi ∧
      PredecessorHalfFin13Atom0916 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 7, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 7, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0674 PredecessorHalfFin13Atom0676 PredecessorHalfFin13Atom0677
    PredecessorHalfFin13Atom0694 PredecessorHalfFin13Atom0695 PredecessorHalfFin13Atom0702
    PredecessorHalfFin13Atom0722 PredecessorHalfFin13Atom0723 PredecessorHalfFin13Atom0730
    PredecessorHalfFin13Atom0776 PredecessorHalfFin13Atom0806 PredecessorHalfFin13Atom0807
    PredecessorHalfFin13Atom0814 PredecessorHalfFin13Atom0860 PredecessorHalfFin13Atom0916 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26178 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0676 chi ∧
      PredecessorHalfFin13Atom0678 chi ∧
      PredecessorHalfFin13Atom0694 chi ∧
      PredecessorHalfFin13Atom0696 chi ∧
      PredecessorHalfFin13Atom0703 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0724 chi ∧
      PredecessorHalfFin13Atom0731 chi ∧
      PredecessorHalfFin13Atom0777 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0808 chi ∧
      PredecessorHalfFin13Atom0815 chi ∧
      PredecessorHalfFin13Atom0861 chi ∧
      PredecessorHalfFin13Atom0917 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 7, 9, 11} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 7, 9, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0674 PredecessorHalfFin13Atom0676 PredecessorHalfFin13Atom0678
    PredecessorHalfFin13Atom0694 PredecessorHalfFin13Atom0696 PredecessorHalfFin13Atom0703
    PredecessorHalfFin13Atom0722 PredecessorHalfFin13Atom0724 PredecessorHalfFin13Atom0731
    PredecessorHalfFin13Atom0777 PredecessorHalfFin13Atom0806 PredecessorHalfFin13Atom0808
    PredecessorHalfFin13Atom0815 PredecessorHalfFin13Atom0861 PredecessorHalfFin13Atom0917 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26179 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0676 chi ∧
      PredecessorHalfFin13Atom0679 chi ∧
      PredecessorHalfFin13Atom0694 chi ∧
      PredecessorHalfFin13Atom0697 chi ∧
      PredecessorHalfFin13Atom0704 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0816 chi ∧
      PredecessorHalfFin13Atom0862 chi ∧
      PredecessorHalfFin13Atom0918 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 7, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 7, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0674 PredecessorHalfFin13Atom0676 PredecessorHalfFin13Atom0679
    PredecessorHalfFin13Atom0694 PredecessorHalfFin13Atom0697 PredecessorHalfFin13Atom0704
    PredecessorHalfFin13Atom0722 PredecessorHalfFin13Atom0725 PredecessorHalfFin13Atom0732
    PredecessorHalfFin13Atom0778 PredecessorHalfFin13Atom0806 PredecessorHalfFin13Atom0809
    PredecessorHalfFin13Atom0816 PredecessorHalfFin13Atom0862 PredecessorHalfFin13Atom0918 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26180 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0677 chi ∧
      PredecessorHalfFin13Atom0678 chi ∧
      PredecessorHalfFin13Atom0695 chi ∧
      PredecessorHalfFin13Atom0696 chi ∧
      PredecessorHalfFin13Atom0705 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0724 chi ∧
      PredecessorHalfFin13Atom0733 chi ∧
      PredecessorHalfFin13Atom0779 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0808 chi ∧
      PredecessorHalfFin13Atom0817 chi ∧
      PredecessorHalfFin13Atom0863 chi ∧
      PredecessorHalfFin13Atom0919 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 7, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 7, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0674 PredecessorHalfFin13Atom0677 PredecessorHalfFin13Atom0678
    PredecessorHalfFin13Atom0695 PredecessorHalfFin13Atom0696 PredecessorHalfFin13Atom0705
    PredecessorHalfFin13Atom0723 PredecessorHalfFin13Atom0724 PredecessorHalfFin13Atom0733
    PredecessorHalfFin13Atom0779 PredecessorHalfFin13Atom0807 PredecessorHalfFin13Atom0808
    PredecessorHalfFin13Atom0817 PredecessorHalfFin13Atom0863 PredecessorHalfFin13Atom0919 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26181 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0677 chi ∧
      PredecessorHalfFin13Atom0679 chi ∧
      PredecessorHalfFin13Atom0695 chi ∧
      PredecessorHalfFin13Atom0697 chi ∧
      PredecessorHalfFin13Atom0706 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0818 chi ∧
      PredecessorHalfFin13Atom0864 chi ∧
      PredecessorHalfFin13Atom0920 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 7, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 7, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0674 PredecessorHalfFin13Atom0677 PredecessorHalfFin13Atom0679
    PredecessorHalfFin13Atom0695 PredecessorHalfFin13Atom0697 PredecessorHalfFin13Atom0706
    PredecessorHalfFin13Atom0723 PredecessorHalfFin13Atom0725 PredecessorHalfFin13Atom0734
    PredecessorHalfFin13Atom0780 PredecessorHalfFin13Atom0807 PredecessorHalfFin13Atom0809
    PredecessorHalfFin13Atom0818 PredecessorHalfFin13Atom0864 PredecessorHalfFin13Atom0920 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26182 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0678 chi ∧
      PredecessorHalfFin13Atom0679 chi ∧
      PredecessorHalfFin13Atom0696 chi ∧
      PredecessorHalfFin13Atom0697 chi ∧
      PredecessorHalfFin13Atom0707 chi ∧
      PredecessorHalfFin13Atom0724 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0735 chi ∧
      PredecessorHalfFin13Atom0781 chi ∧
      PredecessorHalfFin13Atom0808 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0819 chi ∧
      PredecessorHalfFin13Atom0865 chi ∧
      PredecessorHalfFin13Atom0921 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 7, 11, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 7, 11, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0674 PredecessorHalfFin13Atom0678 PredecessorHalfFin13Atom0679
    PredecessorHalfFin13Atom0696 PredecessorHalfFin13Atom0697 PredecessorHalfFin13Atom0707
    PredecessorHalfFin13Atom0724 PredecessorHalfFin13Atom0725 PredecessorHalfFin13Atom0735
    PredecessorHalfFin13Atom0781 PredecessorHalfFin13Atom0808 PredecessorHalfFin13Atom0809
    PredecessorHalfFin13Atom0819 PredecessorHalfFin13Atom0865 PredecessorHalfFin13Atom0921 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26183 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0675 chi ∧
      PredecessorHalfFin13Atom0676 chi ∧
      PredecessorHalfFin13Atom0677 chi ∧
      PredecessorHalfFin13Atom0698 chi ∧
      PredecessorHalfFin13Atom0699 chi ∧
      PredecessorHalfFin13Atom0702 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0866 chi ∧
      PredecessorHalfFin13Atom0922 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 8, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 8, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0675 PredecessorHalfFin13Atom0676 PredecessorHalfFin13Atom0677
    PredecessorHalfFin13Atom0698 PredecessorHalfFin13Atom0699 PredecessorHalfFin13Atom0702
    PredecessorHalfFin13Atom0726 PredecessorHalfFin13Atom0727 PredecessorHalfFin13Atom0730
    PredecessorHalfFin13Atom0782 PredecessorHalfFin13Atom0810 PredecessorHalfFin13Atom0811
    PredecessorHalfFin13Atom0814 PredecessorHalfFin13Atom0866 PredecessorHalfFin13Atom0922 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26184 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0675 chi ∧
      PredecessorHalfFin13Atom0676 chi ∧
      PredecessorHalfFin13Atom0678 chi ∧
      PredecessorHalfFin13Atom0698 chi ∧
      PredecessorHalfFin13Atom0700 chi ∧
      PredecessorHalfFin13Atom0703 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0728 chi ∧
      PredecessorHalfFin13Atom0731 chi ∧
      PredecessorHalfFin13Atom0783 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0812 chi ∧
      PredecessorHalfFin13Atom0815 chi ∧
      PredecessorHalfFin13Atom0867 chi ∧
      PredecessorHalfFin13Atom0923 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 8, 9, 11} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 8, 9, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0675 PredecessorHalfFin13Atom0676 PredecessorHalfFin13Atom0678
    PredecessorHalfFin13Atom0698 PredecessorHalfFin13Atom0700 PredecessorHalfFin13Atom0703
    PredecessorHalfFin13Atom0726 PredecessorHalfFin13Atom0728 PredecessorHalfFin13Atom0731
    PredecessorHalfFin13Atom0783 PredecessorHalfFin13Atom0810 PredecessorHalfFin13Atom0812
    PredecessorHalfFin13Atom0815 PredecessorHalfFin13Atom0867 PredecessorHalfFin13Atom0923 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26185 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0675 chi ∧
      PredecessorHalfFin13Atom0676 chi ∧
      PredecessorHalfFin13Atom0679 chi ∧
      PredecessorHalfFin13Atom0698 chi ∧
      PredecessorHalfFin13Atom0701 chi ∧
      PredecessorHalfFin13Atom0704 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0813 chi ∧
      PredecessorHalfFin13Atom0816 chi ∧
      PredecessorHalfFin13Atom0868 chi ∧
      PredecessorHalfFin13Atom0924 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 8, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 8, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0675 PredecessorHalfFin13Atom0676 PredecessorHalfFin13Atom0679
    PredecessorHalfFin13Atom0698 PredecessorHalfFin13Atom0701 PredecessorHalfFin13Atom0704
    PredecessorHalfFin13Atom0726 PredecessorHalfFin13Atom0729 PredecessorHalfFin13Atom0732
    PredecessorHalfFin13Atom0784 PredecessorHalfFin13Atom0810 PredecessorHalfFin13Atom0813
    PredecessorHalfFin13Atom0816 PredecessorHalfFin13Atom0868 PredecessorHalfFin13Atom0924 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26187 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0675 chi ∧
      PredecessorHalfFin13Atom0677 chi ∧
      PredecessorHalfFin13Atom0679 chi ∧
      PredecessorHalfFin13Atom0699 chi ∧
      PredecessorHalfFin13Atom0701 chi ∧
      PredecessorHalfFin13Atom0706 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0813 chi ∧
      PredecessorHalfFin13Atom0818 chi ∧
      PredecessorHalfFin13Atom0870 chi ∧
      PredecessorHalfFin13Atom0926 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 8, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 8, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0675 PredecessorHalfFin13Atom0677 PredecessorHalfFin13Atom0679
    PredecessorHalfFin13Atom0699 PredecessorHalfFin13Atom0701 PredecessorHalfFin13Atom0706
    PredecessorHalfFin13Atom0727 PredecessorHalfFin13Atom0729 PredecessorHalfFin13Atom0734
    PredecessorHalfFin13Atom0786 PredecessorHalfFin13Atom0811 PredecessorHalfFin13Atom0813
    PredecessorHalfFin13Atom0818 PredecessorHalfFin13Atom0870 PredecessorHalfFin13Atom0926 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26189 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0676 chi ∧
      PredecessorHalfFin13Atom0677 chi ∧
      PredecessorHalfFin13Atom0678 chi ∧
      PredecessorHalfFin13Atom0702 chi ∧
      PredecessorHalfFin13Atom0703 chi ∧
      PredecessorHalfFin13Atom0705 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0731 chi ∧
      PredecessorHalfFin13Atom0733 chi ∧
      PredecessorHalfFin13Atom0788 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0815 chi ∧
      PredecessorHalfFin13Atom0817 chi ∧
      PredecessorHalfFin13Atom0872 chi ∧
      PredecessorHalfFin13Atom0928 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 9, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 9, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0676 PredecessorHalfFin13Atom0677 PredecessorHalfFin13Atom0678
    PredecessorHalfFin13Atom0702 PredecessorHalfFin13Atom0703 PredecessorHalfFin13Atom0705
    PredecessorHalfFin13Atom0730 PredecessorHalfFin13Atom0731 PredecessorHalfFin13Atom0733
    PredecessorHalfFin13Atom0788 PredecessorHalfFin13Atom0814 PredecessorHalfFin13Atom0815
    PredecessorHalfFin13Atom0817 PredecessorHalfFin13Atom0872 PredecessorHalfFin13Atom0928 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26190 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0676 chi ∧
      PredecessorHalfFin13Atom0677 chi ∧
      PredecessorHalfFin13Atom0679 chi ∧
      PredecessorHalfFin13Atom0702 chi ∧
      PredecessorHalfFin13Atom0704 chi ∧
      PredecessorHalfFin13Atom0706 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0816 chi ∧
      PredecessorHalfFin13Atom0818 chi ∧
      PredecessorHalfFin13Atom0873 chi ∧
      PredecessorHalfFin13Atom0929 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 4, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0676 PredecessorHalfFin13Atom0677 PredecessorHalfFin13Atom0679
    PredecessorHalfFin13Atom0702 PredecessorHalfFin13Atom0704 PredecessorHalfFin13Atom0706
    PredecessorHalfFin13Atom0730 PredecessorHalfFin13Atom0732 PredecessorHalfFin13Atom0734
    PredecessorHalfFin13Atom0789 PredecessorHalfFin13Atom0814 PredecessorHalfFin13Atom0816
    PredecessorHalfFin13Atom0818 PredecessorHalfFin13Atom0873 PredecessorHalfFin13Atom0929 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26193 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0680 chi ∧
      PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0682 chi ∧
      PredecessorHalfFin13Atom0687 chi ∧
      PredecessorHalfFin13Atom0688 chi ∧
      PredecessorHalfFin13Atom0693 chi ∧
      PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0821 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0841 chi ∧
      PredecessorHalfFin13Atom0932 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 5, 6, 7, 8} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 5, 6, 7, 8}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0680 PredecessorHalfFin13Atom0681 PredecessorHalfFin13Atom0682
    PredecessorHalfFin13Atom0687 PredecessorHalfFin13Atom0688 PredecessorHalfFin13Atom0693
    PredecessorHalfFin13Atom0736 PredecessorHalfFin13Atom0737 PredecessorHalfFin13Atom0742
    PredecessorHalfFin13Atom0757 PredecessorHalfFin13Atom0820 PredecessorHalfFin13Atom0821
    PredecessorHalfFin13Atom0826 PredecessorHalfFin13Atom0841 PredecessorHalfFin13Atom0932 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26194 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0680 chi ∧
      PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0683 chi ∧
      PredecessorHalfFin13Atom0687 chi ∧
      PredecessorHalfFin13Atom0689 chi ∧
      PredecessorHalfFin13Atom0694 chi ∧
      PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0842 chi ∧
      PredecessorHalfFin13Atom0933 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 5, 6, 7, 9} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 5, 6, 7, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0680 PredecessorHalfFin13Atom0681 PredecessorHalfFin13Atom0683
    PredecessorHalfFin13Atom0687 PredecessorHalfFin13Atom0689 PredecessorHalfFin13Atom0694
    PredecessorHalfFin13Atom0736 PredecessorHalfFin13Atom0738 PredecessorHalfFin13Atom0743
    PredecessorHalfFin13Atom0758 PredecessorHalfFin13Atom0820 PredecessorHalfFin13Atom0822
    PredecessorHalfFin13Atom0827 PredecessorHalfFin13Atom0842 PredecessorHalfFin13Atom0933 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26195 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0680 chi ∧
      PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0684 chi ∧
      PredecessorHalfFin13Atom0687 chi ∧
      PredecessorHalfFin13Atom0690 chi ∧
      PredecessorHalfFin13Atom0695 chi ∧
      PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0843 chi ∧
      PredecessorHalfFin13Atom0934 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 5, 6, 7, 10} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 5, 6, 7, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0680 PredecessorHalfFin13Atom0681 PredecessorHalfFin13Atom0684
    PredecessorHalfFin13Atom0687 PredecessorHalfFin13Atom0690 PredecessorHalfFin13Atom0695
    PredecessorHalfFin13Atom0736 PredecessorHalfFin13Atom0739 PredecessorHalfFin13Atom0744
    PredecessorHalfFin13Atom0759 PredecessorHalfFin13Atom0820 PredecessorHalfFin13Atom0823
    PredecessorHalfFin13Atom0828 PredecessorHalfFin13Atom0843 PredecessorHalfFin13Atom0934 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26196 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0680 chi ∧
      PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0685 chi ∧
      PredecessorHalfFin13Atom0687 chi ∧
      PredecessorHalfFin13Atom0691 chi ∧
      PredecessorHalfFin13Atom0696 chi ∧
      PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0740 chi ∧
      PredecessorHalfFin13Atom0745 chi ∧
      PredecessorHalfFin13Atom0760 chi ∧
      PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0824 chi ∧
      PredecessorHalfFin13Atom0829 chi ∧
      PredecessorHalfFin13Atom0844 chi ∧
      PredecessorHalfFin13Atom0935 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 5, 6, 7, 11} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 5, 6, 7, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0680 PredecessorHalfFin13Atom0681 PredecessorHalfFin13Atom0685
    PredecessorHalfFin13Atom0687 PredecessorHalfFin13Atom0691 PredecessorHalfFin13Atom0696
    PredecessorHalfFin13Atom0736 PredecessorHalfFin13Atom0740 PredecessorHalfFin13Atom0745
    PredecessorHalfFin13Atom0760 PredecessorHalfFin13Atom0820 PredecessorHalfFin13Atom0824
    PredecessorHalfFin13Atom0829 PredecessorHalfFin13Atom0844 PredecessorHalfFin13Atom0935 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26197 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0680 chi ∧
      PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0686 chi ∧
      PredecessorHalfFin13Atom0687 chi ∧
      PredecessorHalfFin13Atom0692 chi ∧
      PredecessorHalfFin13Atom0697 chi ∧
      PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0825 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0845 chi ∧
      PredecessorHalfFin13Atom0936 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 5, 6, 7, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 5, 6, 7, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0680 PredecessorHalfFin13Atom0681 PredecessorHalfFin13Atom0686
    PredecessorHalfFin13Atom0687 PredecessorHalfFin13Atom0692 PredecessorHalfFin13Atom0697
    PredecessorHalfFin13Atom0736 PredecessorHalfFin13Atom0741 PredecessorHalfFin13Atom0746
    PredecessorHalfFin13Atom0761 PredecessorHalfFin13Atom0820 PredecessorHalfFin13Atom0825
    PredecessorHalfFin13Atom0830 PredecessorHalfFin13Atom0845 PredecessorHalfFin13Atom0936 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26198 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0680 chi ∧
      PredecessorHalfFin13Atom0682 chi ∧
      PredecessorHalfFin13Atom0683 chi ∧
      PredecessorHalfFin13Atom0688 chi ∧
      PredecessorHalfFin13Atom0689 chi ∧
      PredecessorHalfFin13Atom0698 chi ∧
      PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0821 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0846 chi ∧
      PredecessorHalfFin13Atom0937 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 5, 6, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 5, 6, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0680 PredecessorHalfFin13Atom0682 PredecessorHalfFin13Atom0683
    PredecessorHalfFin13Atom0688 PredecessorHalfFin13Atom0689 PredecessorHalfFin13Atom0698
    PredecessorHalfFin13Atom0737 PredecessorHalfFin13Atom0738 PredecessorHalfFin13Atom0747
    PredecessorHalfFin13Atom0762 PredecessorHalfFin13Atom0821 PredecessorHalfFin13Atom0822
    PredecessorHalfFin13Atom0831 PredecessorHalfFin13Atom0846 PredecessorHalfFin13Atom0937 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26199 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0680 chi ∧
      PredecessorHalfFin13Atom0682 chi ∧
      PredecessorHalfFin13Atom0684 chi ∧
      PredecessorHalfFin13Atom0688 chi ∧
      PredecessorHalfFin13Atom0690 chi ∧
      PredecessorHalfFin13Atom0699 chi ∧
      PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0821 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0847 chi ∧
      PredecessorHalfFin13Atom0938 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 5, 6, 8, 10} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 5, 6, 8, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0680 PredecessorHalfFin13Atom0682 PredecessorHalfFin13Atom0684
    PredecessorHalfFin13Atom0688 PredecessorHalfFin13Atom0690 PredecessorHalfFin13Atom0699
    PredecessorHalfFin13Atom0737 PredecessorHalfFin13Atom0739 PredecessorHalfFin13Atom0748
    PredecessorHalfFin13Atom0763 PredecessorHalfFin13Atom0821 PredecessorHalfFin13Atom0823
    PredecessorHalfFin13Atom0832 PredecessorHalfFin13Atom0847 PredecessorHalfFin13Atom0938 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26201 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0680 chi ∧
      PredecessorHalfFin13Atom0682 chi ∧
      PredecessorHalfFin13Atom0686 chi ∧
      PredecessorHalfFin13Atom0688 chi ∧
      PredecessorHalfFin13Atom0692 chi ∧
      PredecessorHalfFin13Atom0701 chi ∧
      PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0821 chi ∧
      PredecessorHalfFin13Atom0825 chi ∧
      PredecessorHalfFin13Atom0834 chi ∧
      PredecessorHalfFin13Atom0849 chi ∧
      PredecessorHalfFin13Atom0940 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 5, 6, 8, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 5, 6, 8, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0680 PredecessorHalfFin13Atom0682 PredecessorHalfFin13Atom0686
    PredecessorHalfFin13Atom0688 PredecessorHalfFin13Atom0692 PredecessorHalfFin13Atom0701
    PredecessorHalfFin13Atom0737 PredecessorHalfFin13Atom0741 PredecessorHalfFin13Atom0750
    PredecessorHalfFin13Atom0765 PredecessorHalfFin13Atom0821 PredecessorHalfFin13Atom0825
    PredecessorHalfFin13Atom0834 PredecessorHalfFin13Atom0849 PredecessorHalfFin13Atom0940 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26202 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0680 chi ∧
      PredecessorHalfFin13Atom0683 chi ∧
      PredecessorHalfFin13Atom0684 chi ∧
      PredecessorHalfFin13Atom0689 chi ∧
      PredecessorHalfFin13Atom0690 chi ∧
      PredecessorHalfFin13Atom0702 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0850 chi ∧
      PredecessorHalfFin13Atom0941 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 5, 6, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 5, 6, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0680 PredecessorHalfFin13Atom0683 PredecessorHalfFin13Atom0684
    PredecessorHalfFin13Atom0689 PredecessorHalfFin13Atom0690 PredecessorHalfFin13Atom0702
    PredecessorHalfFin13Atom0738 PredecessorHalfFin13Atom0739 PredecessorHalfFin13Atom0751
    PredecessorHalfFin13Atom0766 PredecessorHalfFin13Atom0822 PredecessorHalfFin13Atom0823
    PredecessorHalfFin13Atom0835 PredecessorHalfFin13Atom0850 PredecessorHalfFin13Atom0941 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26204 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0680 chi ∧
      PredecessorHalfFin13Atom0683 chi ∧
      PredecessorHalfFin13Atom0686 chi ∧
      PredecessorHalfFin13Atom0689 chi ∧
      PredecessorHalfFin13Atom0692 chi ∧
      PredecessorHalfFin13Atom0704 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0825 chi ∧
      PredecessorHalfFin13Atom0837 chi ∧
      PredecessorHalfFin13Atom0852 chi ∧
      PredecessorHalfFin13Atom0943 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 5, 6, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 5, 6, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0680 PredecessorHalfFin13Atom0683 PredecessorHalfFin13Atom0686
    PredecessorHalfFin13Atom0689 PredecessorHalfFin13Atom0692 PredecessorHalfFin13Atom0704
    PredecessorHalfFin13Atom0738 PredecessorHalfFin13Atom0741 PredecessorHalfFin13Atom0753
    PredecessorHalfFin13Atom0768 PredecessorHalfFin13Atom0822 PredecessorHalfFin13Atom0825
    PredecessorHalfFin13Atom0837 PredecessorHalfFin13Atom0852 PredecessorHalfFin13Atom0943 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26206 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0680 chi ∧
      PredecessorHalfFin13Atom0684 chi ∧
      PredecessorHalfFin13Atom0686 chi ∧
      PredecessorHalfFin13Atom0690 chi ∧
      PredecessorHalfFin13Atom0692 chi ∧
      PredecessorHalfFin13Atom0706 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0825 chi ∧
      PredecessorHalfFin13Atom0839 chi ∧
      PredecessorHalfFin13Atom0854 chi ∧
      PredecessorHalfFin13Atom0945 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 5, 6, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 5, 6, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0680 PredecessorHalfFin13Atom0684 PredecessorHalfFin13Atom0686
    PredecessorHalfFin13Atom0690 PredecessorHalfFin13Atom0692 PredecessorHalfFin13Atom0706
    PredecessorHalfFin13Atom0739 PredecessorHalfFin13Atom0741 PredecessorHalfFin13Atom0755
    PredecessorHalfFin13Atom0770 PredecessorHalfFin13Atom0823 PredecessorHalfFin13Atom0825
    PredecessorHalfFin13Atom0839 PredecessorHalfFin13Atom0854 PredecessorHalfFin13Atom0945 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26208 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0682 chi ∧
      PredecessorHalfFin13Atom0683 chi ∧
      PredecessorHalfFin13Atom0693 chi ∧
      PredecessorHalfFin13Atom0694 chi ∧
      PredecessorHalfFin13Atom0698 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0856 chi ∧
      PredecessorHalfFin13Atom0947 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 5, 7, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 5, 7, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0681 PredecessorHalfFin13Atom0682 PredecessorHalfFin13Atom0683
    PredecessorHalfFin13Atom0693 PredecessorHalfFin13Atom0694 PredecessorHalfFin13Atom0698
    PredecessorHalfFin13Atom0742 PredecessorHalfFin13Atom0743 PredecessorHalfFin13Atom0747
    PredecessorHalfFin13Atom0772 PredecessorHalfFin13Atom0826 PredecessorHalfFin13Atom0827
    PredecessorHalfFin13Atom0831 PredecessorHalfFin13Atom0856 PredecessorHalfFin13Atom0947 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26209 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0682 chi ∧
      PredecessorHalfFin13Atom0684 chi ∧
      PredecessorHalfFin13Atom0693 chi ∧
      PredecessorHalfFin13Atom0695 chi ∧
      PredecessorHalfFin13Atom0699 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0857 chi ∧
      PredecessorHalfFin13Atom0948 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 5, 7, 8, 10} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 5, 7, 8, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0681 PredecessorHalfFin13Atom0682 PredecessorHalfFin13Atom0684
    PredecessorHalfFin13Atom0693 PredecessorHalfFin13Atom0695 PredecessorHalfFin13Atom0699
    PredecessorHalfFin13Atom0742 PredecessorHalfFin13Atom0744 PredecessorHalfFin13Atom0748
    PredecessorHalfFin13Atom0773 PredecessorHalfFin13Atom0826 PredecessorHalfFin13Atom0828
    PredecessorHalfFin13Atom0832 PredecessorHalfFin13Atom0857 PredecessorHalfFin13Atom0948 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26210 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0682 chi ∧
      PredecessorHalfFin13Atom0685 chi ∧
      PredecessorHalfFin13Atom0693 chi ∧
      PredecessorHalfFin13Atom0696 chi ∧
      PredecessorHalfFin13Atom0700 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0745 chi ∧
      PredecessorHalfFin13Atom0749 chi ∧
      PredecessorHalfFin13Atom0774 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0829 chi ∧
      PredecessorHalfFin13Atom0833 chi ∧
      PredecessorHalfFin13Atom0858 chi ∧
      PredecessorHalfFin13Atom0949 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 5, 7, 8, 11} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 5, 7, 8, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0681 PredecessorHalfFin13Atom0682 PredecessorHalfFin13Atom0685
    PredecessorHalfFin13Atom0693 PredecessorHalfFin13Atom0696 PredecessorHalfFin13Atom0700
    PredecessorHalfFin13Atom0742 PredecessorHalfFin13Atom0745 PredecessorHalfFin13Atom0749
    PredecessorHalfFin13Atom0774 PredecessorHalfFin13Atom0826 PredecessorHalfFin13Atom0829
    PredecessorHalfFin13Atom0833 PredecessorHalfFin13Atom0858 PredecessorHalfFin13Atom0949 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26211 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0682 chi ∧
      PredecessorHalfFin13Atom0686 chi ∧
      PredecessorHalfFin13Atom0693 chi ∧
      PredecessorHalfFin13Atom0697 chi ∧
      PredecessorHalfFin13Atom0701 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0834 chi ∧
      PredecessorHalfFin13Atom0859 chi ∧
      PredecessorHalfFin13Atom0950 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 5, 7, 8, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 5, 7, 8, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0681 PredecessorHalfFin13Atom0682 PredecessorHalfFin13Atom0686
    PredecessorHalfFin13Atom0693 PredecessorHalfFin13Atom0697 PredecessorHalfFin13Atom0701
    PredecessorHalfFin13Atom0742 PredecessorHalfFin13Atom0746 PredecessorHalfFin13Atom0750
    PredecessorHalfFin13Atom0775 PredecessorHalfFin13Atom0826 PredecessorHalfFin13Atom0830
    PredecessorHalfFin13Atom0834 PredecessorHalfFin13Atom0859 PredecessorHalfFin13Atom0950 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26212 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0683 chi ∧
      PredecessorHalfFin13Atom0684 chi ∧
      PredecessorHalfFin13Atom0694 chi ∧
      PredecessorHalfFin13Atom0695 chi ∧
      PredecessorHalfFin13Atom0702 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0860 chi ∧
      PredecessorHalfFin13Atom0951 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 5, 7, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 5, 7, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0681 PredecessorHalfFin13Atom0683 PredecessorHalfFin13Atom0684
    PredecessorHalfFin13Atom0694 PredecessorHalfFin13Atom0695 PredecessorHalfFin13Atom0702
    PredecessorHalfFin13Atom0743 PredecessorHalfFin13Atom0744 PredecessorHalfFin13Atom0751
    PredecessorHalfFin13Atom0776 PredecessorHalfFin13Atom0827 PredecessorHalfFin13Atom0828
    PredecessorHalfFin13Atom0835 PredecessorHalfFin13Atom0860 PredecessorHalfFin13Atom0951 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26213 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0683 chi ∧
      PredecessorHalfFin13Atom0685 chi ∧
      PredecessorHalfFin13Atom0694 chi ∧
      PredecessorHalfFin13Atom0696 chi ∧
      PredecessorHalfFin13Atom0703 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0745 chi ∧
      PredecessorHalfFin13Atom0752 chi ∧
      PredecessorHalfFin13Atom0777 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0829 chi ∧
      PredecessorHalfFin13Atom0836 chi ∧
      PredecessorHalfFin13Atom0861 chi ∧
      PredecessorHalfFin13Atom0952 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 5, 7, 9, 11} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 5, 7, 9, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0681 PredecessorHalfFin13Atom0683 PredecessorHalfFin13Atom0685
    PredecessorHalfFin13Atom0694 PredecessorHalfFin13Atom0696 PredecessorHalfFin13Atom0703
    PredecessorHalfFin13Atom0743 PredecessorHalfFin13Atom0745 PredecessorHalfFin13Atom0752
    PredecessorHalfFin13Atom0777 PredecessorHalfFin13Atom0827 PredecessorHalfFin13Atom0829
    PredecessorHalfFin13Atom0836 PredecessorHalfFin13Atom0861 PredecessorHalfFin13Atom0952 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26214 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0683 chi ∧
      PredecessorHalfFin13Atom0686 chi ∧
      PredecessorHalfFin13Atom0694 chi ∧
      PredecessorHalfFin13Atom0697 chi ∧
      PredecessorHalfFin13Atom0704 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0837 chi ∧
      PredecessorHalfFin13Atom0862 chi ∧
      PredecessorHalfFin13Atom0953 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 5, 7, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 5, 7, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0681 PredecessorHalfFin13Atom0683 PredecessorHalfFin13Atom0686
    PredecessorHalfFin13Atom0694 PredecessorHalfFin13Atom0697 PredecessorHalfFin13Atom0704
    PredecessorHalfFin13Atom0743 PredecessorHalfFin13Atom0746 PredecessorHalfFin13Atom0753
    PredecessorHalfFin13Atom0778 PredecessorHalfFin13Atom0827 PredecessorHalfFin13Atom0830
    PredecessorHalfFin13Atom0837 PredecessorHalfFin13Atom0862 PredecessorHalfFin13Atom0953 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26215 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0684 chi ∧
      PredecessorHalfFin13Atom0685 chi ∧
      PredecessorHalfFin13Atom0695 chi ∧
      PredecessorHalfFin13Atom0696 chi ∧
      PredecessorHalfFin13Atom0705 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0745 chi ∧
      PredecessorHalfFin13Atom0754 chi ∧
      PredecessorHalfFin13Atom0779 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0829 chi ∧
      PredecessorHalfFin13Atom0838 chi ∧
      PredecessorHalfFin13Atom0863 chi ∧
      PredecessorHalfFin13Atom0954 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 5, 7, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 5, 7, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0681 PredecessorHalfFin13Atom0684 PredecessorHalfFin13Atom0685
    PredecessorHalfFin13Atom0695 PredecessorHalfFin13Atom0696 PredecessorHalfFin13Atom0705
    PredecessorHalfFin13Atom0744 PredecessorHalfFin13Atom0745 PredecessorHalfFin13Atom0754
    PredecessorHalfFin13Atom0779 PredecessorHalfFin13Atom0828 PredecessorHalfFin13Atom0829
    PredecessorHalfFin13Atom0838 PredecessorHalfFin13Atom0863 PredecessorHalfFin13Atom0954 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26216 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0684 chi ∧
      PredecessorHalfFin13Atom0686 chi ∧
      PredecessorHalfFin13Atom0695 chi ∧
      PredecessorHalfFin13Atom0697 chi ∧
      PredecessorHalfFin13Atom0706 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0839 chi ∧
      PredecessorHalfFin13Atom0864 chi ∧
      PredecessorHalfFin13Atom0955 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 5, 7, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 5, 7, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0681 PredecessorHalfFin13Atom0684 PredecessorHalfFin13Atom0686
    PredecessorHalfFin13Atom0695 PredecessorHalfFin13Atom0697 PredecessorHalfFin13Atom0706
    PredecessorHalfFin13Atom0744 PredecessorHalfFin13Atom0746 PredecessorHalfFin13Atom0755
    PredecessorHalfFin13Atom0780 PredecessorHalfFin13Atom0828 PredecessorHalfFin13Atom0830
    PredecessorHalfFin13Atom0839 PredecessorHalfFin13Atom0864 PredecessorHalfFin13Atom0955 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26217 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0685 chi ∧
      PredecessorHalfFin13Atom0686 chi ∧
      PredecessorHalfFin13Atom0696 chi ∧
      PredecessorHalfFin13Atom0697 chi ∧
      PredecessorHalfFin13Atom0707 chi ∧
      PredecessorHalfFin13Atom0745 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0756 chi ∧
      PredecessorHalfFin13Atom0781 chi ∧
      PredecessorHalfFin13Atom0829 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0840 chi ∧
      PredecessorHalfFin13Atom0865 chi ∧
      PredecessorHalfFin13Atom0956 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 5, 7, 11, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 5, 7, 11, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0681 PredecessorHalfFin13Atom0685 PredecessorHalfFin13Atom0686
    PredecessorHalfFin13Atom0696 PredecessorHalfFin13Atom0697 PredecessorHalfFin13Atom0707
    PredecessorHalfFin13Atom0745 PredecessorHalfFin13Atom0746 PredecessorHalfFin13Atom0756
    PredecessorHalfFin13Atom0781 PredecessorHalfFin13Atom0829 PredecessorHalfFin13Atom0830
    PredecessorHalfFin13Atom0840 PredecessorHalfFin13Atom0865 PredecessorHalfFin13Atom0956 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26218 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0682 chi ∧
      PredecessorHalfFin13Atom0683 chi ∧
      PredecessorHalfFin13Atom0684 chi ∧
      PredecessorHalfFin13Atom0698 chi ∧
      PredecessorHalfFin13Atom0699 chi ∧
      PredecessorHalfFin13Atom0702 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0866 chi ∧
      PredecessorHalfFin13Atom0957 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 5, 8, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 5, 8, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0682 PredecessorHalfFin13Atom0683 PredecessorHalfFin13Atom0684
    PredecessorHalfFin13Atom0698 PredecessorHalfFin13Atom0699 PredecessorHalfFin13Atom0702
    PredecessorHalfFin13Atom0747 PredecessorHalfFin13Atom0748 PredecessorHalfFin13Atom0751
    PredecessorHalfFin13Atom0782 PredecessorHalfFin13Atom0831 PredecessorHalfFin13Atom0832
    PredecessorHalfFin13Atom0835 PredecessorHalfFin13Atom0866 PredecessorHalfFin13Atom0957 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26219 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0682 chi ∧
      PredecessorHalfFin13Atom0683 chi ∧
      PredecessorHalfFin13Atom0685 chi ∧
      PredecessorHalfFin13Atom0698 chi ∧
      PredecessorHalfFin13Atom0700 chi ∧
      PredecessorHalfFin13Atom0703 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0749 chi ∧
      PredecessorHalfFin13Atom0752 chi ∧
      PredecessorHalfFin13Atom0783 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0833 chi ∧
      PredecessorHalfFin13Atom0836 chi ∧
      PredecessorHalfFin13Atom0867 chi ∧
      PredecessorHalfFin13Atom0958 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 5, 8, 9, 11} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 5, 8, 9, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0682 PredecessorHalfFin13Atom0683 PredecessorHalfFin13Atom0685
    PredecessorHalfFin13Atom0698 PredecessorHalfFin13Atom0700 PredecessorHalfFin13Atom0703
    PredecessorHalfFin13Atom0747 PredecessorHalfFin13Atom0749 PredecessorHalfFin13Atom0752
    PredecessorHalfFin13Atom0783 PredecessorHalfFin13Atom0831 PredecessorHalfFin13Atom0833
    PredecessorHalfFin13Atom0836 PredecessorHalfFin13Atom0867 PredecessorHalfFin13Atom0958 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26220 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0682 chi ∧
      PredecessorHalfFin13Atom0683 chi ∧
      PredecessorHalfFin13Atom0686 chi ∧
      PredecessorHalfFin13Atom0698 chi ∧
      PredecessorHalfFin13Atom0701 chi ∧
      PredecessorHalfFin13Atom0704 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0834 chi ∧
      PredecessorHalfFin13Atom0837 chi ∧
      PredecessorHalfFin13Atom0868 chi ∧
      PredecessorHalfFin13Atom0959 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 5, 8, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 5, 8, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0682 PredecessorHalfFin13Atom0683 PredecessorHalfFin13Atom0686
    PredecessorHalfFin13Atom0698 PredecessorHalfFin13Atom0701 PredecessorHalfFin13Atom0704
    PredecessorHalfFin13Atom0747 PredecessorHalfFin13Atom0750 PredecessorHalfFin13Atom0753
    PredecessorHalfFin13Atom0784 PredecessorHalfFin13Atom0831 PredecessorHalfFin13Atom0834
    PredecessorHalfFin13Atom0837 PredecessorHalfFin13Atom0868 PredecessorHalfFin13Atom0959 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26221 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0682 chi ∧
      PredecessorHalfFin13Atom0684 chi ∧
      PredecessorHalfFin13Atom0685 chi ∧
      PredecessorHalfFin13Atom0699 chi ∧
      PredecessorHalfFin13Atom0700 chi ∧
      PredecessorHalfFin13Atom0705 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0749 chi ∧
      PredecessorHalfFin13Atom0754 chi ∧
      PredecessorHalfFin13Atom0785 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0833 chi ∧
      PredecessorHalfFin13Atom0838 chi ∧
      PredecessorHalfFin13Atom0869 chi ∧
      PredecessorHalfFin13Atom0960 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 5, 8, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 5, 8, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0682 PredecessorHalfFin13Atom0684 PredecessorHalfFin13Atom0685
    PredecessorHalfFin13Atom0699 PredecessorHalfFin13Atom0700 PredecessorHalfFin13Atom0705
    PredecessorHalfFin13Atom0748 PredecessorHalfFin13Atom0749 PredecessorHalfFin13Atom0754
    PredecessorHalfFin13Atom0785 PredecessorHalfFin13Atom0832 PredecessorHalfFin13Atom0833
    PredecessorHalfFin13Atom0838 PredecessorHalfFin13Atom0869 PredecessorHalfFin13Atom0960 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26222 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0682 chi ∧
      PredecessorHalfFin13Atom0684 chi ∧
      PredecessorHalfFin13Atom0686 chi ∧
      PredecessorHalfFin13Atom0699 chi ∧
      PredecessorHalfFin13Atom0701 chi ∧
      PredecessorHalfFin13Atom0706 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0834 chi ∧
      PredecessorHalfFin13Atom0839 chi ∧
      PredecessorHalfFin13Atom0870 chi ∧
      PredecessorHalfFin13Atom0961 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 5, 8, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 5, 8, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0682 PredecessorHalfFin13Atom0684 PredecessorHalfFin13Atom0686
    PredecessorHalfFin13Atom0699 PredecessorHalfFin13Atom0701 PredecessorHalfFin13Atom0706
    PredecessorHalfFin13Atom0748 PredecessorHalfFin13Atom0750 PredecessorHalfFin13Atom0755
    PredecessorHalfFin13Atom0786 PredecessorHalfFin13Atom0832 PredecessorHalfFin13Atom0834
    PredecessorHalfFin13Atom0839 PredecessorHalfFin13Atom0870 PredecessorHalfFin13Atom0961 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26224 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0683 chi ∧
      PredecessorHalfFin13Atom0684 chi ∧
      PredecessorHalfFin13Atom0685 chi ∧
      PredecessorHalfFin13Atom0702 chi ∧
      PredecessorHalfFin13Atom0703 chi ∧
      PredecessorHalfFin13Atom0705 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0752 chi ∧
      PredecessorHalfFin13Atom0754 chi ∧
      PredecessorHalfFin13Atom0788 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0836 chi ∧
      PredecessorHalfFin13Atom0838 chi ∧
      PredecessorHalfFin13Atom0872 chi ∧
      PredecessorHalfFin13Atom0963 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 5, 9, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 5, 9, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0683 PredecessorHalfFin13Atom0684 PredecessorHalfFin13Atom0685
    PredecessorHalfFin13Atom0702 PredecessorHalfFin13Atom0703 PredecessorHalfFin13Atom0705
    PredecessorHalfFin13Atom0751 PredecessorHalfFin13Atom0752 PredecessorHalfFin13Atom0754
    PredecessorHalfFin13Atom0788 PredecessorHalfFin13Atom0835 PredecessorHalfFin13Atom0836
    PredecessorHalfFin13Atom0838 PredecessorHalfFin13Atom0872 PredecessorHalfFin13Atom0963 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26225 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0683 chi ∧
      PredecessorHalfFin13Atom0684 chi ∧
      PredecessorHalfFin13Atom0686 chi ∧
      PredecessorHalfFin13Atom0702 chi ∧
      PredecessorHalfFin13Atom0704 chi ∧
      PredecessorHalfFin13Atom0706 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0837 chi ∧
      PredecessorHalfFin13Atom0839 chi ∧
      PredecessorHalfFin13Atom0873 chi ∧
      PredecessorHalfFin13Atom0964 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 5, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 5, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0683 PredecessorHalfFin13Atom0684 PredecessorHalfFin13Atom0686
    PredecessorHalfFin13Atom0702 PredecessorHalfFin13Atom0704 PredecessorHalfFin13Atom0706
    PredecessorHalfFin13Atom0751 PredecessorHalfFin13Atom0753 PredecessorHalfFin13Atom0755
    PredecessorHalfFin13Atom0789 PredecessorHalfFin13Atom0835 PredecessorHalfFin13Atom0837
    PredecessorHalfFin13Atom0839 PredecessorHalfFin13Atom0873 PredecessorHalfFin13Atom0964 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26228 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0687 chi ∧
      PredecessorHalfFin13Atom0688 chi ∧
      PredecessorHalfFin13Atom0689 chi ∧
      PredecessorHalfFin13Atom0693 chi ∧
      PredecessorHalfFin13Atom0694 chi ∧
      PredecessorHalfFin13Atom0698 chi ∧
      PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0841 chi ∧
      PredecessorHalfFin13Atom0842 chi ∧
      PredecessorHalfFin13Atom0846 chi ∧
      PredecessorHalfFin13Atom0856 chi ∧
      PredecessorHalfFin13Atom0967 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 6, 7, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 6, 7, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0687 PredecessorHalfFin13Atom0688 PredecessorHalfFin13Atom0689
    PredecessorHalfFin13Atom0693 PredecessorHalfFin13Atom0694 PredecessorHalfFin13Atom0698
    PredecessorHalfFin13Atom0757 PredecessorHalfFin13Atom0758 PredecessorHalfFin13Atom0762
    PredecessorHalfFin13Atom0772 PredecessorHalfFin13Atom0841 PredecessorHalfFin13Atom0842
    PredecessorHalfFin13Atom0846 PredecessorHalfFin13Atom0856 PredecessorHalfFin13Atom0967 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26229 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0687 chi ∧
      PredecessorHalfFin13Atom0688 chi ∧
      PredecessorHalfFin13Atom0690 chi ∧
      PredecessorHalfFin13Atom0693 chi ∧
      PredecessorHalfFin13Atom0695 chi ∧
      PredecessorHalfFin13Atom0699 chi ∧
      PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0841 chi ∧
      PredecessorHalfFin13Atom0843 chi ∧
      PredecessorHalfFin13Atom0847 chi ∧
      PredecessorHalfFin13Atom0857 chi ∧
      PredecessorHalfFin13Atom0968 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 6, 7, 8, 10} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 6, 7, 8, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0687 PredecessorHalfFin13Atom0688 PredecessorHalfFin13Atom0690
    PredecessorHalfFin13Atom0693 PredecessorHalfFin13Atom0695 PredecessorHalfFin13Atom0699
    PredecessorHalfFin13Atom0757 PredecessorHalfFin13Atom0759 PredecessorHalfFin13Atom0763
    PredecessorHalfFin13Atom0773 PredecessorHalfFin13Atom0841 PredecessorHalfFin13Atom0843
    PredecessorHalfFin13Atom0847 PredecessorHalfFin13Atom0857 PredecessorHalfFin13Atom0968 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26231 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0687 chi ∧
      PredecessorHalfFin13Atom0688 chi ∧
      PredecessorHalfFin13Atom0692 chi ∧
      PredecessorHalfFin13Atom0693 chi ∧
      PredecessorHalfFin13Atom0697 chi ∧
      PredecessorHalfFin13Atom0701 chi ∧
      PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0841 chi ∧
      PredecessorHalfFin13Atom0845 chi ∧
      PredecessorHalfFin13Atom0849 chi ∧
      PredecessorHalfFin13Atom0859 chi ∧
      PredecessorHalfFin13Atom0970 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 6, 7, 8, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 6, 7, 8, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0687 PredecessorHalfFin13Atom0688 PredecessorHalfFin13Atom0692
    PredecessorHalfFin13Atom0693 PredecessorHalfFin13Atom0697 PredecessorHalfFin13Atom0701
    PredecessorHalfFin13Atom0757 PredecessorHalfFin13Atom0761 PredecessorHalfFin13Atom0765
    PredecessorHalfFin13Atom0775 PredecessorHalfFin13Atom0841 PredecessorHalfFin13Atom0845
    PredecessorHalfFin13Atom0849 PredecessorHalfFin13Atom0859 PredecessorHalfFin13Atom0970 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26232 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0687 chi ∧
      PredecessorHalfFin13Atom0689 chi ∧
      PredecessorHalfFin13Atom0690 chi ∧
      PredecessorHalfFin13Atom0694 chi ∧
      PredecessorHalfFin13Atom0695 chi ∧
      PredecessorHalfFin13Atom0702 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0842 chi ∧
      PredecessorHalfFin13Atom0843 chi ∧
      PredecessorHalfFin13Atom0850 chi ∧
      PredecessorHalfFin13Atom0860 chi ∧
      PredecessorHalfFin13Atom0971 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 6, 7, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 6, 7, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0687 PredecessorHalfFin13Atom0689 PredecessorHalfFin13Atom0690
    PredecessorHalfFin13Atom0694 PredecessorHalfFin13Atom0695 PredecessorHalfFin13Atom0702
    PredecessorHalfFin13Atom0758 PredecessorHalfFin13Atom0759 PredecessorHalfFin13Atom0766
    PredecessorHalfFin13Atom0776 PredecessorHalfFin13Atom0842 PredecessorHalfFin13Atom0843
    PredecessorHalfFin13Atom0850 PredecessorHalfFin13Atom0860 PredecessorHalfFin13Atom0971 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26233 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0687 chi ∧
      PredecessorHalfFin13Atom0689 chi ∧
      PredecessorHalfFin13Atom0691 chi ∧
      PredecessorHalfFin13Atom0694 chi ∧
      PredecessorHalfFin13Atom0696 chi ∧
      PredecessorHalfFin13Atom0703 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0760 chi ∧
      PredecessorHalfFin13Atom0767 chi ∧
      PredecessorHalfFin13Atom0777 chi ∧
      PredecessorHalfFin13Atom0842 chi ∧
      PredecessorHalfFin13Atom0844 chi ∧
      PredecessorHalfFin13Atom0851 chi ∧
      PredecessorHalfFin13Atom0861 chi ∧
      PredecessorHalfFin13Atom0972 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 6, 7, 9, 11} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 6, 7, 9, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0687 PredecessorHalfFin13Atom0689 PredecessorHalfFin13Atom0691
    PredecessorHalfFin13Atom0694 PredecessorHalfFin13Atom0696 PredecessorHalfFin13Atom0703
    PredecessorHalfFin13Atom0758 PredecessorHalfFin13Atom0760 PredecessorHalfFin13Atom0767
    PredecessorHalfFin13Atom0777 PredecessorHalfFin13Atom0842 PredecessorHalfFin13Atom0844
    PredecessorHalfFin13Atom0851 PredecessorHalfFin13Atom0861 PredecessorHalfFin13Atom0972 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26234 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0687 chi ∧
      PredecessorHalfFin13Atom0689 chi ∧
      PredecessorHalfFin13Atom0692 chi ∧
      PredecessorHalfFin13Atom0694 chi ∧
      PredecessorHalfFin13Atom0697 chi ∧
      PredecessorHalfFin13Atom0704 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0842 chi ∧
      PredecessorHalfFin13Atom0845 chi ∧
      PredecessorHalfFin13Atom0852 chi ∧
      PredecessorHalfFin13Atom0862 chi ∧
      PredecessorHalfFin13Atom0973 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 6, 7, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 6, 7, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0687 PredecessorHalfFin13Atom0689 PredecessorHalfFin13Atom0692
    PredecessorHalfFin13Atom0694 PredecessorHalfFin13Atom0697 PredecessorHalfFin13Atom0704
    PredecessorHalfFin13Atom0758 PredecessorHalfFin13Atom0761 PredecessorHalfFin13Atom0768
    PredecessorHalfFin13Atom0778 PredecessorHalfFin13Atom0842 PredecessorHalfFin13Atom0845
    PredecessorHalfFin13Atom0852 PredecessorHalfFin13Atom0862 PredecessorHalfFin13Atom0973 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26236 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0687 chi ∧
      PredecessorHalfFin13Atom0690 chi ∧
      PredecessorHalfFin13Atom0692 chi ∧
      PredecessorHalfFin13Atom0695 chi ∧
      PredecessorHalfFin13Atom0697 chi ∧
      PredecessorHalfFin13Atom0706 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0843 chi ∧
      PredecessorHalfFin13Atom0845 chi ∧
      PredecessorHalfFin13Atom0854 chi ∧
      PredecessorHalfFin13Atom0864 chi ∧
      PredecessorHalfFin13Atom0975 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 6, 7, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 6, 7, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0687 PredecessorHalfFin13Atom0690 PredecessorHalfFin13Atom0692
    PredecessorHalfFin13Atom0695 PredecessorHalfFin13Atom0697 PredecessorHalfFin13Atom0706
    PredecessorHalfFin13Atom0759 PredecessorHalfFin13Atom0761 PredecessorHalfFin13Atom0770
    PredecessorHalfFin13Atom0780 PredecessorHalfFin13Atom0843 PredecessorHalfFin13Atom0845
    PredecessorHalfFin13Atom0854 PredecessorHalfFin13Atom0864 PredecessorHalfFin13Atom0975 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26238 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0688 chi ∧
      PredecessorHalfFin13Atom0689 chi ∧
      PredecessorHalfFin13Atom0690 chi ∧
      PredecessorHalfFin13Atom0698 chi ∧
      PredecessorHalfFin13Atom0699 chi ∧
      PredecessorHalfFin13Atom0702 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0846 chi ∧
      PredecessorHalfFin13Atom0847 chi ∧
      PredecessorHalfFin13Atom0850 chi ∧
      PredecessorHalfFin13Atom0866 chi ∧
      PredecessorHalfFin13Atom0977 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 6, 8, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 6, 8, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0688 PredecessorHalfFin13Atom0689 PredecessorHalfFin13Atom0690
    PredecessorHalfFin13Atom0698 PredecessorHalfFin13Atom0699 PredecessorHalfFin13Atom0702
    PredecessorHalfFin13Atom0762 PredecessorHalfFin13Atom0763 PredecessorHalfFin13Atom0766
    PredecessorHalfFin13Atom0782 PredecessorHalfFin13Atom0846 PredecessorHalfFin13Atom0847
    PredecessorHalfFin13Atom0850 PredecessorHalfFin13Atom0866 PredecessorHalfFin13Atom0977 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26240 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0688 chi ∧
      PredecessorHalfFin13Atom0689 chi ∧
      PredecessorHalfFin13Atom0692 chi ∧
      PredecessorHalfFin13Atom0698 chi ∧
      PredecessorHalfFin13Atom0701 chi ∧
      PredecessorHalfFin13Atom0704 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0846 chi ∧
      PredecessorHalfFin13Atom0849 chi ∧
      PredecessorHalfFin13Atom0852 chi ∧
      PredecessorHalfFin13Atom0868 chi ∧
      PredecessorHalfFin13Atom0979 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 6, 8, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 6, 8, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0688 PredecessorHalfFin13Atom0689 PredecessorHalfFin13Atom0692
    PredecessorHalfFin13Atom0698 PredecessorHalfFin13Atom0701 PredecessorHalfFin13Atom0704
    PredecessorHalfFin13Atom0762 PredecessorHalfFin13Atom0765 PredecessorHalfFin13Atom0768
    PredecessorHalfFin13Atom0784 PredecessorHalfFin13Atom0846 PredecessorHalfFin13Atom0849
    PredecessorHalfFin13Atom0852 PredecessorHalfFin13Atom0868 PredecessorHalfFin13Atom0979 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26241 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0688 chi ∧
      PredecessorHalfFin13Atom0690 chi ∧
      PredecessorHalfFin13Atom0691 chi ∧
      PredecessorHalfFin13Atom0699 chi ∧
      PredecessorHalfFin13Atom0700 chi ∧
      PredecessorHalfFin13Atom0705 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0764 chi ∧
      PredecessorHalfFin13Atom0769 chi ∧
      PredecessorHalfFin13Atom0785 chi ∧
      PredecessorHalfFin13Atom0847 chi ∧
      PredecessorHalfFin13Atom0848 chi ∧
      PredecessorHalfFin13Atom0853 chi ∧
      PredecessorHalfFin13Atom0869 chi ∧
      PredecessorHalfFin13Atom0980 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 6, 8, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 6, 8, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0688 PredecessorHalfFin13Atom0690 PredecessorHalfFin13Atom0691
    PredecessorHalfFin13Atom0699 PredecessorHalfFin13Atom0700 PredecessorHalfFin13Atom0705
    PredecessorHalfFin13Atom0763 PredecessorHalfFin13Atom0764 PredecessorHalfFin13Atom0769
    PredecessorHalfFin13Atom0785 PredecessorHalfFin13Atom0847 PredecessorHalfFin13Atom0848
    PredecessorHalfFin13Atom0853 PredecessorHalfFin13Atom0869 PredecessorHalfFin13Atom0980 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26242 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0688 chi ∧
      PredecessorHalfFin13Atom0690 chi ∧
      PredecessorHalfFin13Atom0692 chi ∧
      PredecessorHalfFin13Atom0699 chi ∧
      PredecessorHalfFin13Atom0701 chi ∧
      PredecessorHalfFin13Atom0706 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0847 chi ∧
      PredecessorHalfFin13Atom0849 chi ∧
      PredecessorHalfFin13Atom0854 chi ∧
      PredecessorHalfFin13Atom0870 chi ∧
      PredecessorHalfFin13Atom0981 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 6, 8, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 6, 8, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0688 PredecessorHalfFin13Atom0690 PredecessorHalfFin13Atom0692
    PredecessorHalfFin13Atom0699 PredecessorHalfFin13Atom0701 PredecessorHalfFin13Atom0706
    PredecessorHalfFin13Atom0763 PredecessorHalfFin13Atom0765 PredecessorHalfFin13Atom0770
    PredecessorHalfFin13Atom0786 PredecessorHalfFin13Atom0847 PredecessorHalfFin13Atom0849
    PredecessorHalfFin13Atom0854 PredecessorHalfFin13Atom0870 PredecessorHalfFin13Atom0981 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26244 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0689 chi ∧
      PredecessorHalfFin13Atom0690 chi ∧
      PredecessorHalfFin13Atom0691 chi ∧
      PredecessorHalfFin13Atom0702 chi ∧
      PredecessorHalfFin13Atom0703 chi ∧
      PredecessorHalfFin13Atom0705 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0767 chi ∧
      PredecessorHalfFin13Atom0769 chi ∧
      PredecessorHalfFin13Atom0788 chi ∧
      PredecessorHalfFin13Atom0850 chi ∧
      PredecessorHalfFin13Atom0851 chi ∧
      PredecessorHalfFin13Atom0853 chi ∧
      PredecessorHalfFin13Atom0872 chi ∧
      PredecessorHalfFin13Atom0983 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 6, 9, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 6, 9, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0689 PredecessorHalfFin13Atom0690 PredecessorHalfFin13Atom0691
    PredecessorHalfFin13Atom0702 PredecessorHalfFin13Atom0703 PredecessorHalfFin13Atom0705
    PredecessorHalfFin13Atom0766 PredecessorHalfFin13Atom0767 PredecessorHalfFin13Atom0769
    PredecessorHalfFin13Atom0788 PredecessorHalfFin13Atom0850 PredecessorHalfFin13Atom0851
    PredecessorHalfFin13Atom0853 PredecessorHalfFin13Atom0872 PredecessorHalfFin13Atom0983 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26245 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0689 chi ∧
      PredecessorHalfFin13Atom0690 chi ∧
      PredecessorHalfFin13Atom0692 chi ∧
      PredecessorHalfFin13Atom0702 chi ∧
      PredecessorHalfFin13Atom0704 chi ∧
      PredecessorHalfFin13Atom0706 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0850 chi ∧
      PredecessorHalfFin13Atom0852 chi ∧
      PredecessorHalfFin13Atom0854 chi ∧
      PredecessorHalfFin13Atom0873 chi ∧
      PredecessorHalfFin13Atom0984 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 6, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 6, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0689 PredecessorHalfFin13Atom0690 PredecessorHalfFin13Atom0692
    PredecessorHalfFin13Atom0702 PredecessorHalfFin13Atom0704 PredecessorHalfFin13Atom0706
    PredecessorHalfFin13Atom0766 PredecessorHalfFin13Atom0768 PredecessorHalfFin13Atom0770
    PredecessorHalfFin13Atom0789 PredecessorHalfFin13Atom0850 PredecessorHalfFin13Atom0852
    PredecessorHalfFin13Atom0854 PredecessorHalfFin13Atom0873 PredecessorHalfFin13Atom0984 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26247 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0690 chi ∧
      PredecessorHalfFin13Atom0691 chi ∧
      PredecessorHalfFin13Atom0692 chi ∧
      PredecessorHalfFin13Atom0705 chi ∧
      PredecessorHalfFin13Atom0706 chi ∧
      PredecessorHalfFin13Atom0707 chi ∧
      PredecessorHalfFin13Atom0769 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0771 chi ∧
      PredecessorHalfFin13Atom0791 chi ∧
      PredecessorHalfFin13Atom0853 chi ∧
      PredecessorHalfFin13Atom0854 chi ∧
      PredecessorHalfFin13Atom0855 chi ∧
      PredecessorHalfFin13Atom0875 chi ∧
      PredecessorHalfFin13Atom0986 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 6, 10, 11, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 6, 10, 11, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0690 PredecessorHalfFin13Atom0691 PredecessorHalfFin13Atom0692
    PredecessorHalfFin13Atom0705 PredecessorHalfFin13Atom0706 PredecessorHalfFin13Atom0707
    PredecessorHalfFin13Atom0769 PredecessorHalfFin13Atom0770 PredecessorHalfFin13Atom0771
    PredecessorHalfFin13Atom0791 PredecessorHalfFin13Atom0853 PredecessorHalfFin13Atom0854
    PredecessorHalfFin13Atom0855 PredecessorHalfFin13Atom0875 PredecessorHalfFin13Atom0986 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26248 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0693 chi ∧
      PredecessorHalfFin13Atom0694 chi ∧
      PredecessorHalfFin13Atom0695 chi ∧
      PredecessorHalfFin13Atom0698 chi ∧
      PredecessorHalfFin13Atom0699 chi ∧
      PredecessorHalfFin13Atom0702 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0856 chi ∧
      PredecessorHalfFin13Atom0857 chi ∧
      PredecessorHalfFin13Atom0860 chi ∧
      PredecessorHalfFin13Atom0866 chi ∧
      PredecessorHalfFin13Atom0987 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 7, 8, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 7, 8, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0693 PredecessorHalfFin13Atom0694 PredecessorHalfFin13Atom0695
    PredecessorHalfFin13Atom0698 PredecessorHalfFin13Atom0699 PredecessorHalfFin13Atom0702
    PredecessorHalfFin13Atom0772 PredecessorHalfFin13Atom0773 PredecessorHalfFin13Atom0776
    PredecessorHalfFin13Atom0782 PredecessorHalfFin13Atom0856 PredecessorHalfFin13Atom0857
    PredecessorHalfFin13Atom0860 PredecessorHalfFin13Atom0866 PredecessorHalfFin13Atom0987 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26249 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0693 chi ∧
      PredecessorHalfFin13Atom0694 chi ∧
      PredecessorHalfFin13Atom0696 chi ∧
      PredecessorHalfFin13Atom0698 chi ∧
      PredecessorHalfFin13Atom0700 chi ∧
      PredecessorHalfFin13Atom0703 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0774 chi ∧
      PredecessorHalfFin13Atom0777 chi ∧
      PredecessorHalfFin13Atom0783 chi ∧
      PredecessorHalfFin13Atom0856 chi ∧
      PredecessorHalfFin13Atom0858 chi ∧
      PredecessorHalfFin13Atom0861 chi ∧
      PredecessorHalfFin13Atom0867 chi ∧
      PredecessorHalfFin13Atom0988 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 7, 8, 9, 11} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 7, 8, 9, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0693 PredecessorHalfFin13Atom0694 PredecessorHalfFin13Atom0696
    PredecessorHalfFin13Atom0698 PredecessorHalfFin13Atom0700 PredecessorHalfFin13Atom0703
    PredecessorHalfFin13Atom0772 PredecessorHalfFin13Atom0774 PredecessorHalfFin13Atom0777
    PredecessorHalfFin13Atom0783 PredecessorHalfFin13Atom0856 PredecessorHalfFin13Atom0858
    PredecessorHalfFin13Atom0861 PredecessorHalfFin13Atom0867 PredecessorHalfFin13Atom0988 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26250 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0693 chi ∧
      PredecessorHalfFin13Atom0694 chi ∧
      PredecessorHalfFin13Atom0697 chi ∧
      PredecessorHalfFin13Atom0698 chi ∧
      PredecessorHalfFin13Atom0701 chi ∧
      PredecessorHalfFin13Atom0704 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0856 chi ∧
      PredecessorHalfFin13Atom0859 chi ∧
      PredecessorHalfFin13Atom0862 chi ∧
      PredecessorHalfFin13Atom0868 chi ∧
      PredecessorHalfFin13Atom0989 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 7, 8, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 7, 8, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0693 PredecessorHalfFin13Atom0694 PredecessorHalfFin13Atom0697
    PredecessorHalfFin13Atom0698 PredecessorHalfFin13Atom0701 PredecessorHalfFin13Atom0704
    PredecessorHalfFin13Atom0772 PredecessorHalfFin13Atom0775 PredecessorHalfFin13Atom0778
    PredecessorHalfFin13Atom0784 PredecessorHalfFin13Atom0856 PredecessorHalfFin13Atom0859
    PredecessorHalfFin13Atom0862 PredecessorHalfFin13Atom0868 PredecessorHalfFin13Atom0989 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26251 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0693 chi ∧
      PredecessorHalfFin13Atom0695 chi ∧
      PredecessorHalfFin13Atom0696 chi ∧
      PredecessorHalfFin13Atom0699 chi ∧
      PredecessorHalfFin13Atom0700 chi ∧
      PredecessorHalfFin13Atom0705 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0774 chi ∧
      PredecessorHalfFin13Atom0779 chi ∧
      PredecessorHalfFin13Atom0785 chi ∧
      PredecessorHalfFin13Atom0857 chi ∧
      PredecessorHalfFin13Atom0858 chi ∧
      PredecessorHalfFin13Atom0863 chi ∧
      PredecessorHalfFin13Atom0869 chi ∧
      PredecessorHalfFin13Atom0990 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 7, 8, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 7, 8, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0693 PredecessorHalfFin13Atom0695 PredecessorHalfFin13Atom0696
    PredecessorHalfFin13Atom0699 PredecessorHalfFin13Atom0700 PredecessorHalfFin13Atom0705
    PredecessorHalfFin13Atom0773 PredecessorHalfFin13Atom0774 PredecessorHalfFin13Atom0779
    PredecessorHalfFin13Atom0785 PredecessorHalfFin13Atom0857 PredecessorHalfFin13Atom0858
    PredecessorHalfFin13Atom0863 PredecessorHalfFin13Atom0869 PredecessorHalfFin13Atom0990 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26252 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0693 chi ∧
      PredecessorHalfFin13Atom0695 chi ∧
      PredecessorHalfFin13Atom0697 chi ∧
      PredecessorHalfFin13Atom0699 chi ∧
      PredecessorHalfFin13Atom0701 chi ∧
      PredecessorHalfFin13Atom0706 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0857 chi ∧
      PredecessorHalfFin13Atom0859 chi ∧
      PredecessorHalfFin13Atom0864 chi ∧
      PredecessorHalfFin13Atom0870 chi ∧
      PredecessorHalfFin13Atom0991 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 7, 8, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 7, 8, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0693 PredecessorHalfFin13Atom0695 PredecessorHalfFin13Atom0697
    PredecessorHalfFin13Atom0699 PredecessorHalfFin13Atom0701 PredecessorHalfFin13Atom0706
    PredecessorHalfFin13Atom0773 PredecessorHalfFin13Atom0775 PredecessorHalfFin13Atom0780
    PredecessorHalfFin13Atom0786 PredecessorHalfFin13Atom0857 PredecessorHalfFin13Atom0859
    PredecessorHalfFin13Atom0864 PredecessorHalfFin13Atom0870 PredecessorHalfFin13Atom0991 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26255 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0694 chi ∧
      PredecessorHalfFin13Atom0695 chi ∧
      PredecessorHalfFin13Atom0697 chi ∧
      PredecessorHalfFin13Atom0702 chi ∧
      PredecessorHalfFin13Atom0704 chi ∧
      PredecessorHalfFin13Atom0706 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0860 chi ∧
      PredecessorHalfFin13Atom0862 chi ∧
      PredecessorHalfFin13Atom0864 chi ∧
      PredecessorHalfFin13Atom0873 chi ∧
      PredecessorHalfFin13Atom0994 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 7, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 7, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0694 PredecessorHalfFin13Atom0695 PredecessorHalfFin13Atom0697
    PredecessorHalfFin13Atom0702 PredecessorHalfFin13Atom0704 PredecessorHalfFin13Atom0706
    PredecessorHalfFin13Atom0776 PredecessorHalfFin13Atom0778 PredecessorHalfFin13Atom0780
    PredecessorHalfFin13Atom0789 PredecessorHalfFin13Atom0860 PredecessorHalfFin13Atom0862
    PredecessorHalfFin13Atom0864 PredecessorHalfFin13Atom0873 PredecessorHalfFin13Atom0994 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26258 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0698 chi ∧
      PredecessorHalfFin13Atom0699 chi ∧
      PredecessorHalfFin13Atom0700 chi ∧
      PredecessorHalfFin13Atom0702 chi ∧
      PredecessorHalfFin13Atom0703 chi ∧
      PredecessorHalfFin13Atom0705 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0783 chi ∧
      PredecessorHalfFin13Atom0785 chi ∧
      PredecessorHalfFin13Atom0788 chi ∧
      PredecessorHalfFin13Atom0866 chi ∧
      PredecessorHalfFin13Atom0867 chi ∧
      PredecessorHalfFin13Atom0869 chi ∧
      PredecessorHalfFin13Atom0872 chi ∧
      PredecessorHalfFin13Atom0997 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 8, 9, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 8, 9, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0698 PredecessorHalfFin13Atom0699 PredecessorHalfFin13Atom0700
    PredecessorHalfFin13Atom0702 PredecessorHalfFin13Atom0703 PredecessorHalfFin13Atom0705
    PredecessorHalfFin13Atom0782 PredecessorHalfFin13Atom0783 PredecessorHalfFin13Atom0785
    PredecessorHalfFin13Atom0788 PredecessorHalfFin13Atom0866 PredecessorHalfFin13Atom0867
    PredecessorHalfFin13Atom0869 PredecessorHalfFin13Atom0872 PredecessorHalfFin13Atom0997 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26259 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0698 chi ∧
      PredecessorHalfFin13Atom0699 chi ∧
      PredecessorHalfFin13Atom0701 chi ∧
      PredecessorHalfFin13Atom0702 chi ∧
      PredecessorHalfFin13Atom0704 chi ∧
      PredecessorHalfFin13Atom0706 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0866 chi ∧
      PredecessorHalfFin13Atom0868 chi ∧
      PredecessorHalfFin13Atom0870 chi ∧
      PredecessorHalfFin13Atom0873 chi ∧
      PredecessorHalfFin13Atom0998 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 3, 8, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 8, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0698 PredecessorHalfFin13Atom0699 PredecessorHalfFin13Atom0701
    PredecessorHalfFin13Atom0702 PredecessorHalfFin13Atom0704 PredecessorHalfFin13Atom0706
    PredecessorHalfFin13Atom0782 PredecessorHalfFin13Atom0784 PredecessorHalfFin13Atom0786
    PredecessorHalfFin13Atom0789 PredecessorHalfFin13Atom0866 PredecessorHalfFin13Atom0868
    PredecessorHalfFin13Atom0870 PredecessorHalfFin13Atom0873 PredecessorHalfFin13Atom0998 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26263 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0876 chi ∧
      PredecessorHalfFin13Atom0877 chi ∧
      PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0897 chi ∧
      PredecessorHalfFin13Atom0932 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 5, 6, 7, 8} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 5, 6, 7, 8}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0708 PredecessorHalfFin13Atom0709 PredecessorHalfFin13Atom0710
    PredecessorHalfFin13Atom0715 PredecessorHalfFin13Atom0716 PredecessorHalfFin13Atom0721
    PredecessorHalfFin13Atom0736 PredecessorHalfFin13Atom0737 PredecessorHalfFin13Atom0742
    PredecessorHalfFin13Atom0757 PredecessorHalfFin13Atom0876 PredecessorHalfFin13Atom0877
    PredecessorHalfFin13Atom0882 PredecessorHalfFin13Atom0897 PredecessorHalfFin13Atom0932 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26264 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0876 chi ∧
      PredecessorHalfFin13Atom0878 chi ∧
      PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0898 chi ∧
      PredecessorHalfFin13Atom0933 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 5, 6, 7, 9} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 5, 6, 7, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0708 PredecessorHalfFin13Atom0709 PredecessorHalfFin13Atom0711
    PredecessorHalfFin13Atom0715 PredecessorHalfFin13Atom0717 PredecessorHalfFin13Atom0722
    PredecessorHalfFin13Atom0736 PredecessorHalfFin13Atom0738 PredecessorHalfFin13Atom0743
    PredecessorHalfFin13Atom0758 PredecessorHalfFin13Atom0876 PredecessorHalfFin13Atom0878
    PredecessorHalfFin13Atom0883 PredecessorHalfFin13Atom0898 PredecessorHalfFin13Atom0933 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26265 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0876 chi ∧
      PredecessorHalfFin13Atom0879 chi ∧
      PredecessorHalfFin13Atom0884 chi ∧
      PredecessorHalfFin13Atom0899 chi ∧
      PredecessorHalfFin13Atom0934 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 5, 6, 7, 10} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 5, 6, 7, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0708 PredecessorHalfFin13Atom0709 PredecessorHalfFin13Atom0712
    PredecessorHalfFin13Atom0715 PredecessorHalfFin13Atom0718 PredecessorHalfFin13Atom0723
    PredecessorHalfFin13Atom0736 PredecessorHalfFin13Atom0739 PredecessorHalfFin13Atom0744
    PredecessorHalfFin13Atom0759 PredecessorHalfFin13Atom0876 PredecessorHalfFin13Atom0879
    PredecessorHalfFin13Atom0884 PredecessorHalfFin13Atom0899 PredecessorHalfFin13Atom0934 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26267 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0876 chi ∧
      PredecessorHalfFin13Atom0881 chi ∧
      PredecessorHalfFin13Atom0886 chi ∧
      PredecessorHalfFin13Atom0901 chi ∧
      PredecessorHalfFin13Atom0936 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 5, 6, 7, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 5, 6, 7, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0708 PredecessorHalfFin13Atom0709 PredecessorHalfFin13Atom0714
    PredecessorHalfFin13Atom0715 PredecessorHalfFin13Atom0720 PredecessorHalfFin13Atom0725
    PredecessorHalfFin13Atom0736 PredecessorHalfFin13Atom0741 PredecessorHalfFin13Atom0746
    PredecessorHalfFin13Atom0761 PredecessorHalfFin13Atom0876 PredecessorHalfFin13Atom0881
    PredecessorHalfFin13Atom0886 PredecessorHalfFin13Atom0901 PredecessorHalfFin13Atom0936 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26268 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0877 chi ∧
      PredecessorHalfFin13Atom0878 chi ∧
      PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0902 chi ∧
      PredecessorHalfFin13Atom0937 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 5, 6, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 5, 6, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0708 PredecessorHalfFin13Atom0710 PredecessorHalfFin13Atom0711
    PredecessorHalfFin13Atom0716 PredecessorHalfFin13Atom0717 PredecessorHalfFin13Atom0726
    PredecessorHalfFin13Atom0737 PredecessorHalfFin13Atom0738 PredecessorHalfFin13Atom0747
    PredecessorHalfFin13Atom0762 PredecessorHalfFin13Atom0877 PredecessorHalfFin13Atom0878
    PredecessorHalfFin13Atom0887 PredecessorHalfFin13Atom0902 PredecessorHalfFin13Atom0937 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26269 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0877 chi ∧
      PredecessorHalfFin13Atom0879 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0938 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 5, 6, 8, 10} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 5, 6, 8, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0708 PredecessorHalfFin13Atom0710 PredecessorHalfFin13Atom0712
    PredecessorHalfFin13Atom0716 PredecessorHalfFin13Atom0718 PredecessorHalfFin13Atom0727
    PredecessorHalfFin13Atom0737 PredecessorHalfFin13Atom0739 PredecessorHalfFin13Atom0748
    PredecessorHalfFin13Atom0763 PredecessorHalfFin13Atom0877 PredecessorHalfFin13Atom0879
    PredecessorHalfFin13Atom0888 PredecessorHalfFin13Atom0903 PredecessorHalfFin13Atom0938 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26271 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0877 chi ∧
      PredecessorHalfFin13Atom0881 chi ∧
      PredecessorHalfFin13Atom0890 chi ∧
      PredecessorHalfFin13Atom0905 chi ∧
      PredecessorHalfFin13Atom0940 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 5, 6, 8, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 5, 6, 8, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0708 PredecessorHalfFin13Atom0710 PredecessorHalfFin13Atom0714
    PredecessorHalfFin13Atom0716 PredecessorHalfFin13Atom0720 PredecessorHalfFin13Atom0729
    PredecessorHalfFin13Atom0737 PredecessorHalfFin13Atom0741 PredecessorHalfFin13Atom0750
    PredecessorHalfFin13Atom0765 PredecessorHalfFin13Atom0877 PredecessorHalfFin13Atom0881
    PredecessorHalfFin13Atom0890 PredecessorHalfFin13Atom0905 PredecessorHalfFin13Atom0940 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26272 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0878 chi ∧
      PredecessorHalfFin13Atom0879 chi ∧
      PredecessorHalfFin13Atom0891 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0941 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 5, 6, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 5, 6, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0708 PredecessorHalfFin13Atom0711 PredecessorHalfFin13Atom0712
    PredecessorHalfFin13Atom0717 PredecessorHalfFin13Atom0718 PredecessorHalfFin13Atom0730
    PredecessorHalfFin13Atom0738 PredecessorHalfFin13Atom0739 PredecessorHalfFin13Atom0751
    PredecessorHalfFin13Atom0766 PredecessorHalfFin13Atom0878 PredecessorHalfFin13Atom0879
    PredecessorHalfFin13Atom0891 PredecessorHalfFin13Atom0906 PredecessorHalfFin13Atom0941 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26274 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0878 chi ∧
      PredecessorHalfFin13Atom0881 chi ∧
      PredecessorHalfFin13Atom0893 chi ∧
      PredecessorHalfFin13Atom0908 chi ∧
      PredecessorHalfFin13Atom0943 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 5, 6, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 5, 6, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0708 PredecessorHalfFin13Atom0711 PredecessorHalfFin13Atom0714
    PredecessorHalfFin13Atom0717 PredecessorHalfFin13Atom0720 PredecessorHalfFin13Atom0732
    PredecessorHalfFin13Atom0738 PredecessorHalfFin13Atom0741 PredecessorHalfFin13Atom0753
    PredecessorHalfFin13Atom0768 PredecessorHalfFin13Atom0878 PredecessorHalfFin13Atom0881
    PredecessorHalfFin13Atom0893 PredecessorHalfFin13Atom0908 PredecessorHalfFin13Atom0943 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26275 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0713 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0719 chi ∧
      PredecessorHalfFin13Atom0733 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0740 chi ∧
      PredecessorHalfFin13Atom0754 chi ∧
      PredecessorHalfFin13Atom0769 chi ∧
      PredecessorHalfFin13Atom0879 chi ∧
      PredecessorHalfFin13Atom0880 chi ∧
      PredecessorHalfFin13Atom0894 chi ∧
      PredecessorHalfFin13Atom0909 chi ∧
      PredecessorHalfFin13Atom0944 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 5, 6, 10, 11} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 5, 6, 10, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0708 PredecessorHalfFin13Atom0712 PredecessorHalfFin13Atom0713
    PredecessorHalfFin13Atom0718 PredecessorHalfFin13Atom0719 PredecessorHalfFin13Atom0733
    PredecessorHalfFin13Atom0739 PredecessorHalfFin13Atom0740 PredecessorHalfFin13Atom0754
    PredecessorHalfFin13Atom0769 PredecessorHalfFin13Atom0879 PredecessorHalfFin13Atom0880
    PredecessorHalfFin13Atom0894 PredecessorHalfFin13Atom0909 PredecessorHalfFin13Atom0944 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26276 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0879 chi ∧
      PredecessorHalfFin13Atom0881 chi ∧
      PredecessorHalfFin13Atom0895 chi ∧
      PredecessorHalfFin13Atom0910 chi ∧
      PredecessorHalfFin13Atom0945 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 5, 6, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 5, 6, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0708 PredecessorHalfFin13Atom0712 PredecessorHalfFin13Atom0714
    PredecessorHalfFin13Atom0718 PredecessorHalfFin13Atom0720 PredecessorHalfFin13Atom0734
    PredecessorHalfFin13Atom0739 PredecessorHalfFin13Atom0741 PredecessorHalfFin13Atom0755
    PredecessorHalfFin13Atom0770 PredecessorHalfFin13Atom0879 PredecessorHalfFin13Atom0881
    PredecessorHalfFin13Atom0895 PredecessorHalfFin13Atom0910 PredecessorHalfFin13Atom0945 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26277 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0713 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0719 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0735 chi ∧
      PredecessorHalfFin13Atom0740 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0756 chi ∧
      PredecessorHalfFin13Atom0771 chi ∧
      PredecessorHalfFin13Atom0880 chi ∧
      PredecessorHalfFin13Atom0881 chi ∧
      PredecessorHalfFin13Atom0896 chi ∧
      PredecessorHalfFin13Atom0911 chi ∧
      PredecessorHalfFin13Atom0946 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 5, 6, 11, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 5, 6, 11, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0708 PredecessorHalfFin13Atom0713 PredecessorHalfFin13Atom0714
    PredecessorHalfFin13Atom0719 PredecessorHalfFin13Atom0720 PredecessorHalfFin13Atom0735
    PredecessorHalfFin13Atom0740 PredecessorHalfFin13Atom0741 PredecessorHalfFin13Atom0756
    PredecessorHalfFin13Atom0771 PredecessorHalfFin13Atom0880 PredecessorHalfFin13Atom0881
    PredecessorHalfFin13Atom0896 PredecessorHalfFin13Atom0911 PredecessorHalfFin13Atom0946 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26278 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0947 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 5, 7, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 5, 7, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0709 PredecessorHalfFin13Atom0710 PredecessorHalfFin13Atom0711
    PredecessorHalfFin13Atom0721 PredecessorHalfFin13Atom0722 PredecessorHalfFin13Atom0726
    PredecessorHalfFin13Atom0742 PredecessorHalfFin13Atom0743 PredecessorHalfFin13Atom0747
    PredecessorHalfFin13Atom0772 PredecessorHalfFin13Atom0882 PredecessorHalfFin13Atom0883
    PredecessorHalfFin13Atom0887 PredecessorHalfFin13Atom0912 PredecessorHalfFin13Atom0947 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26279 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0884 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0913 chi ∧
      PredecessorHalfFin13Atom0948 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 5, 7, 8, 10} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 5, 7, 8, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0709 PredecessorHalfFin13Atom0710 PredecessorHalfFin13Atom0712
    PredecessorHalfFin13Atom0721 PredecessorHalfFin13Atom0723 PredecessorHalfFin13Atom0727
    PredecessorHalfFin13Atom0742 PredecessorHalfFin13Atom0744 PredecessorHalfFin13Atom0748
    PredecessorHalfFin13Atom0773 PredecessorHalfFin13Atom0882 PredecessorHalfFin13Atom0884
    PredecessorHalfFin13Atom0888 PredecessorHalfFin13Atom0913 PredecessorHalfFin13Atom0948 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26280 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0713 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0724 chi ∧
      PredecessorHalfFin13Atom0728 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0745 chi ∧
      PredecessorHalfFin13Atom0749 chi ∧
      PredecessorHalfFin13Atom0774 chi ∧
      PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0885 chi ∧
      PredecessorHalfFin13Atom0889 chi ∧
      PredecessorHalfFin13Atom0914 chi ∧
      PredecessorHalfFin13Atom0949 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 5, 7, 8, 11} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 5, 7, 8, 11}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0709 PredecessorHalfFin13Atom0710 PredecessorHalfFin13Atom0713
    PredecessorHalfFin13Atom0721 PredecessorHalfFin13Atom0724 PredecessorHalfFin13Atom0728
    PredecessorHalfFin13Atom0742 PredecessorHalfFin13Atom0745 PredecessorHalfFin13Atom0749
    PredecessorHalfFin13Atom0774 PredecessorHalfFin13Atom0882 PredecessorHalfFin13Atom0885
    PredecessorHalfFin13Atom0889 PredecessorHalfFin13Atom0914 PredecessorHalfFin13Atom0949 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26281 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0886 chi ∧
      PredecessorHalfFin13Atom0890 chi ∧
      PredecessorHalfFin13Atom0915 chi ∧
      PredecessorHalfFin13Atom0950 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 5, 7, 8, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 5, 7, 8, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0709 PredecessorHalfFin13Atom0710 PredecessorHalfFin13Atom0714
    PredecessorHalfFin13Atom0721 PredecessorHalfFin13Atom0725 PredecessorHalfFin13Atom0729
    PredecessorHalfFin13Atom0742 PredecessorHalfFin13Atom0746 PredecessorHalfFin13Atom0750
    PredecessorHalfFin13Atom0775 PredecessorHalfFin13Atom0882 PredecessorHalfFin13Atom0886
    PredecessorHalfFin13Atom0890 PredecessorHalfFin13Atom0915 PredecessorHalfFin13Atom0950 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26282 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0884 chi ∧
      PredecessorHalfFin13Atom0891 chi ∧
      PredecessorHalfFin13Atom0916 chi ∧
      PredecessorHalfFin13Atom0951 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 5, 7, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 5, 7, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0709 PredecessorHalfFin13Atom0711 PredecessorHalfFin13Atom0712
    PredecessorHalfFin13Atom0722 PredecessorHalfFin13Atom0723 PredecessorHalfFin13Atom0730
    PredecessorHalfFin13Atom0743 PredecessorHalfFin13Atom0744 PredecessorHalfFin13Atom0751
    PredecessorHalfFin13Atom0776 PredecessorHalfFin13Atom0883 PredecessorHalfFin13Atom0884
    PredecessorHalfFin13Atom0891 PredecessorHalfFin13Atom0916 PredecessorHalfFin13Atom0951 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26284 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0886 chi ∧
      PredecessorHalfFin13Atom0893 chi ∧
      PredecessorHalfFin13Atom0918 chi ∧
      PredecessorHalfFin13Atom0953 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 5, 7, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 5, 7, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0709 PredecessorHalfFin13Atom0711 PredecessorHalfFin13Atom0714
    PredecessorHalfFin13Atom0722 PredecessorHalfFin13Atom0725 PredecessorHalfFin13Atom0732
    PredecessorHalfFin13Atom0743 PredecessorHalfFin13Atom0746 PredecessorHalfFin13Atom0753
    PredecessorHalfFin13Atom0778 PredecessorHalfFin13Atom0883 PredecessorHalfFin13Atom0886
    PredecessorHalfFin13Atom0893 PredecessorHalfFin13Atom0918 PredecessorHalfFin13Atom0953 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26286 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0884 chi ∧
      PredecessorHalfFin13Atom0886 chi ∧
      PredecessorHalfFin13Atom0895 chi ∧
      PredecessorHalfFin13Atom0920 chi ∧
      PredecessorHalfFin13Atom0955 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 5, 7, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 5, 7, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0709 PredecessorHalfFin13Atom0712 PredecessorHalfFin13Atom0714
    PredecessorHalfFin13Atom0723 PredecessorHalfFin13Atom0725 PredecessorHalfFin13Atom0734
    PredecessorHalfFin13Atom0744 PredecessorHalfFin13Atom0746 PredecessorHalfFin13Atom0755
    PredecessorHalfFin13Atom0780 PredecessorHalfFin13Atom0884 PredecessorHalfFin13Atom0886
    PredecessorHalfFin13Atom0895 PredecessorHalfFin13Atom0920 PredecessorHalfFin13Atom0955 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause26288 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0891 chi ∧
      PredecessorHalfFin13Atom0922 chi ∧
      PredecessorHalfFin13Atom0957 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {2, 4, 5, 8, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 5, 8, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0710 PredecessorHalfFin13Atom0711 PredecessorHalfFin13Atom0712
    PredecessorHalfFin13Atom0726 PredecessorHalfFin13Atom0727 PredecessorHalfFin13Atom0730
    PredecessorHalfFin13Atom0747 PredecessorHalfFin13Atom0748 PredecessorHalfFin13Atom0751
    PredecessorHalfFin13Atom0782 PredecessorHalfFin13Atom0887 PredecessorHalfFin13Atom0888
    PredecessorHalfFin13Atom0891 PredecessorHalfFin13Atom0922 PredecessorHalfFin13Atom0957 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

end ErdosSzekeres

end
