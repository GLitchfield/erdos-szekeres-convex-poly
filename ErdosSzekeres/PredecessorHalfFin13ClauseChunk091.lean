module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 091. -/

theorem predecessorHalfFin13_clause25354 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0359 chi ∧
      PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0362 chi ∧
      PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0451 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0473 chi ∧
      PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0933 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 5, 6, 7, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 5, 6, 7, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0359 PredecessorHalfFin13Atom0360 PredecessorHalfFin13Atom0362
    PredecessorHalfFin13Atom0366 PredecessorHalfFin13Atom0368 PredecessorHalfFin13Atom0373
    PredecessorHalfFin13Atom0451 PredecessorHalfFin13Atom0453 PredecessorHalfFin13Atom0458
    PredecessorHalfFin13Atom0473 PredecessorHalfFin13Atom0736 PredecessorHalfFin13Atom0738
    PredecessorHalfFin13Atom0743 PredecessorHalfFin13Atom0758 PredecessorHalfFin13Atom0933 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25355 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0359 chi ∧
      PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0451 chi ∧
      PredecessorHalfFin13Atom0454 chi ∧
      PredecessorHalfFin13Atom0459 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0934 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 5, 6, 7, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 5, 6, 7, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0359 PredecessorHalfFin13Atom0360 PredecessorHalfFin13Atom0363
    PredecessorHalfFin13Atom0366 PredecessorHalfFin13Atom0369 PredecessorHalfFin13Atom0374
    PredecessorHalfFin13Atom0451 PredecessorHalfFin13Atom0454 PredecessorHalfFin13Atom0459
    PredecessorHalfFin13Atom0474 PredecessorHalfFin13Atom0736 PredecessorHalfFin13Atom0739
    PredecessorHalfFin13Atom0744 PredecessorHalfFin13Atom0759 PredecessorHalfFin13Atom0934 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25358 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0359 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0362 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0937 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 5, 6, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 5, 6, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0359 PredecessorHalfFin13Atom0361 PredecessorHalfFin13Atom0362
    PredecessorHalfFin13Atom0367 PredecessorHalfFin13Atom0368 PredecessorHalfFin13Atom0377
    PredecessorHalfFin13Atom0452 PredecessorHalfFin13Atom0453 PredecessorHalfFin13Atom0462
    PredecessorHalfFin13Atom0477 PredecessorHalfFin13Atom0737 PredecessorHalfFin13Atom0738
    PredecessorHalfFin13Atom0747 PredecessorHalfFin13Atom0762 PredecessorHalfFin13Atom0937 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25359 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0359 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0454 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0938 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 5, 6, 8, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 5, 6, 8, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0359 PredecessorHalfFin13Atom0361 PredecessorHalfFin13Atom0363
    PredecessorHalfFin13Atom0367 PredecessorHalfFin13Atom0369 PredecessorHalfFin13Atom0378
    PredecessorHalfFin13Atom0452 PredecessorHalfFin13Atom0454 PredecessorHalfFin13Atom0463
    PredecessorHalfFin13Atom0478 PredecessorHalfFin13Atom0737 PredecessorHalfFin13Atom0739
    PredecessorHalfFin13Atom0748 PredecessorHalfFin13Atom0763 PredecessorHalfFin13Atom0938 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25361 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0359 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0456 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0940 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 5, 6, 8, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 5, 6, 8, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0359 PredecessorHalfFin13Atom0361 PredecessorHalfFin13Atom0365
    PredecessorHalfFin13Atom0367 PredecessorHalfFin13Atom0371 PredecessorHalfFin13Atom0380
    PredecessorHalfFin13Atom0452 PredecessorHalfFin13Atom0456 PredecessorHalfFin13Atom0465
    PredecessorHalfFin13Atom0480 PredecessorHalfFin13Atom0737 PredecessorHalfFin13Atom0741
    PredecessorHalfFin13Atom0750 PredecessorHalfFin13Atom0765 PredecessorHalfFin13Atom0940 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25362 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0359 chi ∧
      PredecessorHalfFin13Atom0362 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0454 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0941 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 5, 6, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 5, 6, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0359 PredecessorHalfFin13Atom0362 PredecessorHalfFin13Atom0363
    PredecessorHalfFin13Atom0368 PredecessorHalfFin13Atom0369 PredecessorHalfFin13Atom0381
    PredecessorHalfFin13Atom0453 PredecessorHalfFin13Atom0454 PredecessorHalfFin13Atom0466
    PredecessorHalfFin13Atom0481 PredecessorHalfFin13Atom0738 PredecessorHalfFin13Atom0739
    PredecessorHalfFin13Atom0751 PredecessorHalfFin13Atom0766 PredecessorHalfFin13Atom0941 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25364 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0359 chi ∧
      PredecessorHalfFin13Atom0362 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0456 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0943 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 5, 6, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 5, 6, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0359 PredecessorHalfFin13Atom0362 PredecessorHalfFin13Atom0365
    PredecessorHalfFin13Atom0368 PredecessorHalfFin13Atom0371 PredecessorHalfFin13Atom0383
    PredecessorHalfFin13Atom0453 PredecessorHalfFin13Atom0456 PredecessorHalfFin13Atom0468
    PredecessorHalfFin13Atom0483 PredecessorHalfFin13Atom0738 PredecessorHalfFin13Atom0741
    PredecessorHalfFin13Atom0753 PredecessorHalfFin13Atom0768 PredecessorHalfFin13Atom0943 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25366 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0359 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0454 chi ∧
      PredecessorHalfFin13Atom0456 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0945 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 5, 6, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 5, 6, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0359 PredecessorHalfFin13Atom0363 PredecessorHalfFin13Atom0365
    PredecessorHalfFin13Atom0369 PredecessorHalfFin13Atom0371 PredecessorHalfFin13Atom0385
    PredecessorHalfFin13Atom0454 PredecessorHalfFin13Atom0456 PredecessorHalfFin13Atom0470
    PredecessorHalfFin13Atom0485 PredecessorHalfFin13Atom0739 PredecessorHalfFin13Atom0741
    PredecessorHalfFin13Atom0755 PredecessorHalfFin13Atom0770 PredecessorHalfFin13Atom0945 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25368 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0362 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0947 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 5, 7, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 5, 7, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0360 PredecessorHalfFin13Atom0361 PredecessorHalfFin13Atom0362
    PredecessorHalfFin13Atom0372 PredecessorHalfFin13Atom0373 PredecessorHalfFin13Atom0377
    PredecessorHalfFin13Atom0457 PredecessorHalfFin13Atom0458 PredecessorHalfFin13Atom0462
    PredecessorHalfFin13Atom0487 PredecessorHalfFin13Atom0742 PredecessorHalfFin13Atom0743
    PredecessorHalfFin13Atom0747 PredecessorHalfFin13Atom0772 PredecessorHalfFin13Atom0947 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25369 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0459 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0948 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 5, 7, 8, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 5, 7, 8, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0360 PredecessorHalfFin13Atom0361 PredecessorHalfFin13Atom0363
    PredecessorHalfFin13Atom0372 PredecessorHalfFin13Atom0374 PredecessorHalfFin13Atom0378
    PredecessorHalfFin13Atom0457 PredecessorHalfFin13Atom0459 PredecessorHalfFin13Atom0463
    PredecessorHalfFin13Atom0488 PredecessorHalfFin13Atom0742 PredecessorHalfFin13Atom0744
    PredecessorHalfFin13Atom0748 PredecessorHalfFin13Atom0773 PredecessorHalfFin13Atom0948 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25371 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0461 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0950 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 5, 7, 8, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 5, 7, 8, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0360 PredecessorHalfFin13Atom0361 PredecessorHalfFin13Atom0365
    PredecessorHalfFin13Atom0372 PredecessorHalfFin13Atom0376 PredecessorHalfFin13Atom0380
    PredecessorHalfFin13Atom0457 PredecessorHalfFin13Atom0461 PredecessorHalfFin13Atom0465
    PredecessorHalfFin13Atom0490 PredecessorHalfFin13Atom0742 PredecessorHalfFin13Atom0746
    PredecessorHalfFin13Atom0750 PredecessorHalfFin13Atom0775 PredecessorHalfFin13Atom0950 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25372 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0362 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0459 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0951 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 5, 7, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 5, 7, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0360 PredecessorHalfFin13Atom0362 PredecessorHalfFin13Atom0363
    PredecessorHalfFin13Atom0373 PredecessorHalfFin13Atom0374 PredecessorHalfFin13Atom0381
    PredecessorHalfFin13Atom0458 PredecessorHalfFin13Atom0459 PredecessorHalfFin13Atom0466
    PredecessorHalfFin13Atom0491 PredecessorHalfFin13Atom0743 PredecessorHalfFin13Atom0744
    PredecessorHalfFin13Atom0751 PredecessorHalfFin13Atom0776 PredecessorHalfFin13Atom0951 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25374 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0362 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0461 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0953 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 5, 7, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 5, 7, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0360 PredecessorHalfFin13Atom0362 PredecessorHalfFin13Atom0365
    PredecessorHalfFin13Atom0373 PredecessorHalfFin13Atom0376 PredecessorHalfFin13Atom0383
    PredecessorHalfFin13Atom0458 PredecessorHalfFin13Atom0461 PredecessorHalfFin13Atom0468
    PredecessorHalfFin13Atom0493 PredecessorHalfFin13Atom0743 PredecessorHalfFin13Atom0746
    PredecessorHalfFin13Atom0753 PredecessorHalfFin13Atom0778 PredecessorHalfFin13Atom0953 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25376 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0459 chi ∧
      PredecessorHalfFin13Atom0461 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0955 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 5, 7, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 5, 7, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0360 PredecessorHalfFin13Atom0363 PredecessorHalfFin13Atom0365
    PredecessorHalfFin13Atom0374 PredecessorHalfFin13Atom0376 PredecessorHalfFin13Atom0385
    PredecessorHalfFin13Atom0459 PredecessorHalfFin13Atom0461 PredecessorHalfFin13Atom0470
    PredecessorHalfFin13Atom0495 PredecessorHalfFin13Atom0744 PredecessorHalfFin13Atom0746
    PredecessorHalfFin13Atom0755 PredecessorHalfFin13Atom0780 PredecessorHalfFin13Atom0955 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25378 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0362 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0497 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0957 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 5, 8, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 5, 8, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0361 PredecessorHalfFin13Atom0362 PredecessorHalfFin13Atom0363
    PredecessorHalfFin13Atom0377 PredecessorHalfFin13Atom0378 PredecessorHalfFin13Atom0381
    PredecessorHalfFin13Atom0462 PredecessorHalfFin13Atom0463 PredecessorHalfFin13Atom0466
    PredecessorHalfFin13Atom0497 PredecessorHalfFin13Atom0747 PredecessorHalfFin13Atom0748
    PredecessorHalfFin13Atom0751 PredecessorHalfFin13Atom0782 PredecessorHalfFin13Atom0957 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25380 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0362 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0499 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0959 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 5, 8, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 5, 8, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0361 PredecessorHalfFin13Atom0362 PredecessorHalfFin13Atom0365
    PredecessorHalfFin13Atom0377 PredecessorHalfFin13Atom0380 PredecessorHalfFin13Atom0383
    PredecessorHalfFin13Atom0462 PredecessorHalfFin13Atom0465 PredecessorHalfFin13Atom0468
    PredecessorHalfFin13Atom0499 PredecessorHalfFin13Atom0747 PredecessorHalfFin13Atom0750
    PredecessorHalfFin13Atom0753 PredecessorHalfFin13Atom0784 PredecessorHalfFin13Atom0959 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25382 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0501 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0961 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 5, 8, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 5, 8, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0361 PredecessorHalfFin13Atom0363 PredecessorHalfFin13Atom0365
    PredecessorHalfFin13Atom0378 PredecessorHalfFin13Atom0380 PredecessorHalfFin13Atom0385
    PredecessorHalfFin13Atom0463 PredecessorHalfFin13Atom0465 PredecessorHalfFin13Atom0470
    PredecessorHalfFin13Atom0501 PredecessorHalfFin13Atom0748 PredecessorHalfFin13Atom0750
    PredecessorHalfFin13Atom0755 PredecessorHalfFin13Atom0786 PredecessorHalfFin13Atom0961 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25385 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0362 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0504 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0964 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 5, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 5, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0362 PredecessorHalfFin13Atom0363 PredecessorHalfFin13Atom0365
    PredecessorHalfFin13Atom0381 PredecessorHalfFin13Atom0383 PredecessorHalfFin13Atom0385
    PredecessorHalfFin13Atom0466 PredecessorHalfFin13Atom0468 PredecessorHalfFin13Atom0470
    PredecessorHalfFin13Atom0504 PredecessorHalfFin13Atom0751 PredecessorHalfFin13Atom0753
    PredecessorHalfFin13Atom0755 PredecessorHalfFin13Atom0789 PredecessorHalfFin13Atom0964 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25388 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0473 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0967 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 6, 7, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 6, 7, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0366 PredecessorHalfFin13Atom0367 PredecessorHalfFin13Atom0368
    PredecessorHalfFin13Atom0372 PredecessorHalfFin13Atom0373 PredecessorHalfFin13Atom0377
    PredecessorHalfFin13Atom0472 PredecessorHalfFin13Atom0473 PredecessorHalfFin13Atom0477
    PredecessorHalfFin13Atom0487 PredecessorHalfFin13Atom0757 PredecessorHalfFin13Atom0758
    PredecessorHalfFin13Atom0762 PredecessorHalfFin13Atom0772 PredecessorHalfFin13Atom0967 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25389 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0968 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 6, 7, 8, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 6, 7, 8, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0366 PredecessorHalfFin13Atom0367 PredecessorHalfFin13Atom0369
    PredecessorHalfFin13Atom0372 PredecessorHalfFin13Atom0374 PredecessorHalfFin13Atom0378
    PredecessorHalfFin13Atom0472 PredecessorHalfFin13Atom0474 PredecessorHalfFin13Atom0478
    PredecessorHalfFin13Atom0488 PredecessorHalfFin13Atom0757 PredecessorHalfFin13Atom0759
    PredecessorHalfFin13Atom0763 PredecessorHalfFin13Atom0773 PredecessorHalfFin13Atom0968 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25391 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0476 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0970 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 6, 7, 8, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 6, 7, 8, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0366 PredecessorHalfFin13Atom0367 PredecessorHalfFin13Atom0371
    PredecessorHalfFin13Atom0372 PredecessorHalfFin13Atom0376 PredecessorHalfFin13Atom0380
    PredecessorHalfFin13Atom0472 PredecessorHalfFin13Atom0476 PredecessorHalfFin13Atom0480
    PredecessorHalfFin13Atom0490 PredecessorHalfFin13Atom0757 PredecessorHalfFin13Atom0761
    PredecessorHalfFin13Atom0765 PredecessorHalfFin13Atom0775 PredecessorHalfFin13Atom0970 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25392 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0473 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0971 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 6, 7, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 6, 7, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0366 PredecessorHalfFin13Atom0368 PredecessorHalfFin13Atom0369
    PredecessorHalfFin13Atom0373 PredecessorHalfFin13Atom0374 PredecessorHalfFin13Atom0381
    PredecessorHalfFin13Atom0473 PredecessorHalfFin13Atom0474 PredecessorHalfFin13Atom0481
    PredecessorHalfFin13Atom0491 PredecessorHalfFin13Atom0758 PredecessorHalfFin13Atom0759
    PredecessorHalfFin13Atom0766 PredecessorHalfFin13Atom0776 PredecessorHalfFin13Atom0971 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25394 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0473 chi ∧
      PredecessorHalfFin13Atom0476 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0973 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 6, 7, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 6, 7, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0366 PredecessorHalfFin13Atom0368 PredecessorHalfFin13Atom0371
    PredecessorHalfFin13Atom0373 PredecessorHalfFin13Atom0376 PredecessorHalfFin13Atom0383
    PredecessorHalfFin13Atom0473 PredecessorHalfFin13Atom0476 PredecessorHalfFin13Atom0483
    PredecessorHalfFin13Atom0493 PredecessorHalfFin13Atom0758 PredecessorHalfFin13Atom0761
    PredecessorHalfFin13Atom0768 PredecessorHalfFin13Atom0778 PredecessorHalfFin13Atom0973 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25396 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0476 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0975 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 6, 7, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 6, 7, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0366 PredecessorHalfFin13Atom0369 PredecessorHalfFin13Atom0371
    PredecessorHalfFin13Atom0374 PredecessorHalfFin13Atom0376 PredecessorHalfFin13Atom0385
    PredecessorHalfFin13Atom0474 PredecessorHalfFin13Atom0476 PredecessorHalfFin13Atom0485
    PredecessorHalfFin13Atom0495 PredecessorHalfFin13Atom0759 PredecessorHalfFin13Atom0761
    PredecessorHalfFin13Atom0770 PredecessorHalfFin13Atom0780 PredecessorHalfFin13Atom0975 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25398 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0497 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0977 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 6, 8, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 6, 8, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0367 PredecessorHalfFin13Atom0368 PredecessorHalfFin13Atom0369
    PredecessorHalfFin13Atom0377 PredecessorHalfFin13Atom0378 PredecessorHalfFin13Atom0381
    PredecessorHalfFin13Atom0477 PredecessorHalfFin13Atom0478 PredecessorHalfFin13Atom0481
    PredecessorHalfFin13Atom0497 PredecessorHalfFin13Atom0762 PredecessorHalfFin13Atom0763
    PredecessorHalfFin13Atom0766 PredecessorHalfFin13Atom0782 PredecessorHalfFin13Atom0977 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25400 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0499 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0979 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 6, 8, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 6, 8, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0367 PredecessorHalfFin13Atom0368 PredecessorHalfFin13Atom0371
    PredecessorHalfFin13Atom0377 PredecessorHalfFin13Atom0380 PredecessorHalfFin13Atom0383
    PredecessorHalfFin13Atom0477 PredecessorHalfFin13Atom0480 PredecessorHalfFin13Atom0483
    PredecessorHalfFin13Atom0499 PredecessorHalfFin13Atom0762 PredecessorHalfFin13Atom0765
    PredecessorHalfFin13Atom0768 PredecessorHalfFin13Atom0784 PredecessorHalfFin13Atom0979 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25402 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0501 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0981 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 6, 8, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 6, 8, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0367 PredecessorHalfFin13Atom0369 PredecessorHalfFin13Atom0371
    PredecessorHalfFin13Atom0378 PredecessorHalfFin13Atom0380 PredecessorHalfFin13Atom0385
    PredecessorHalfFin13Atom0478 PredecessorHalfFin13Atom0480 PredecessorHalfFin13Atom0485
    PredecessorHalfFin13Atom0501 PredecessorHalfFin13Atom0763 PredecessorHalfFin13Atom0765
    PredecessorHalfFin13Atom0770 PredecessorHalfFin13Atom0786 PredecessorHalfFin13Atom0981 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25405 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0504 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0984 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 6, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 6, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0368 PredecessorHalfFin13Atom0369 PredecessorHalfFin13Atom0371
    PredecessorHalfFin13Atom0381 PredecessorHalfFin13Atom0383 PredecessorHalfFin13Atom0385
    PredecessorHalfFin13Atom0481 PredecessorHalfFin13Atom0483 PredecessorHalfFin13Atom0485
    PredecessorHalfFin13Atom0504 PredecessorHalfFin13Atom0766 PredecessorHalfFin13Atom0768
    PredecessorHalfFin13Atom0770 PredecessorHalfFin13Atom0789 PredecessorHalfFin13Atom0984 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25408 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0497 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0987 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 7, 8, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 7, 8, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0372 PredecessorHalfFin13Atom0373 PredecessorHalfFin13Atom0374
    PredecessorHalfFin13Atom0377 PredecessorHalfFin13Atom0378 PredecessorHalfFin13Atom0381
    PredecessorHalfFin13Atom0487 PredecessorHalfFin13Atom0488 PredecessorHalfFin13Atom0491
    PredecessorHalfFin13Atom0497 PredecessorHalfFin13Atom0772 PredecessorHalfFin13Atom0773
    PredecessorHalfFin13Atom0776 PredecessorHalfFin13Atom0782 PredecessorHalfFin13Atom0987 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25412 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0501 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0991 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 7, 8, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 7, 8, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0372 PredecessorHalfFin13Atom0374 PredecessorHalfFin13Atom0376
    PredecessorHalfFin13Atom0378 PredecessorHalfFin13Atom0380 PredecessorHalfFin13Atom0385
    PredecessorHalfFin13Atom0488 PredecessorHalfFin13Atom0490 PredecessorHalfFin13Atom0495
    PredecessorHalfFin13Atom0501 PredecessorHalfFin13Atom0773 PredecessorHalfFin13Atom0775
    PredecessorHalfFin13Atom0780 PredecessorHalfFin13Atom0786 PredecessorHalfFin13Atom0991 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25415 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0504 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0994 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 2, 7, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 7, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0373 PredecessorHalfFin13Atom0374 PredecessorHalfFin13Atom0376
    PredecessorHalfFin13Atom0381 PredecessorHalfFin13Atom0383 PredecessorHalfFin13Atom0385
    PredecessorHalfFin13Atom0491 PredecessorHalfFin13Atom0493 PredecessorHalfFin13Atom0495
    PredecessorHalfFin13Atom0504 PredecessorHalfFin13Atom0776 PredecessorHalfFin13Atom0778
    PredecessorHalfFin13Atom0780 PredecessorHalfFin13Atom0789 PredecessorHalfFin13Atom0994 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25423 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0451 chi ∧
      PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0799 chi ∧
      PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0876 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 4, 5, 6, 7} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 4, 5, 6, 7}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0387 PredecessorHalfFin13Atom0388 PredecessorHalfFin13Atom0389
    PredecessorHalfFin13Atom0395 PredecessorHalfFin13Atom0396 PredecessorHalfFin13Atom0402
    PredecessorHalfFin13Atom0423 PredecessorHalfFin13Atom0424 PredecessorHalfFin13Atom0430
    PredecessorHalfFin13Atom0451 PredecessorHalfFin13Atom0792 PredecessorHalfFin13Atom0793
    PredecessorHalfFin13Atom0799 PredecessorHalfFin13Atom0820 PredecessorHalfFin13Atom0876 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25424 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0821 chi ∧
      PredecessorHalfFin13Atom0877 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 4, 5, 6, 8} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 4, 5, 6, 8}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0387 PredecessorHalfFin13Atom0388 PredecessorHalfFin13Atom0390
    PredecessorHalfFin13Atom0395 PredecessorHalfFin13Atom0397 PredecessorHalfFin13Atom0403
    PredecessorHalfFin13Atom0423 PredecessorHalfFin13Atom0425 PredecessorHalfFin13Atom0431
    PredecessorHalfFin13Atom0452 PredecessorHalfFin13Atom0792 PredecessorHalfFin13Atom0794
    PredecessorHalfFin13Atom0800 PredecessorHalfFin13Atom0821 PredecessorHalfFin13Atom0877 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25425 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0878 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 4, 5, 6, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 4, 5, 6, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0387 PredecessorHalfFin13Atom0388 PredecessorHalfFin13Atom0391
    PredecessorHalfFin13Atom0395 PredecessorHalfFin13Atom0398 PredecessorHalfFin13Atom0404
    PredecessorHalfFin13Atom0423 PredecessorHalfFin13Atom0426 PredecessorHalfFin13Atom0432
    PredecessorHalfFin13Atom0453 PredecessorHalfFin13Atom0792 PredecessorHalfFin13Atom0795
    PredecessorHalfFin13Atom0801 PredecessorHalfFin13Atom0822 PredecessorHalfFin13Atom0878 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25426 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0454 chi ∧
      PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0879 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 4, 5, 6, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 4, 5, 6, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0387 PredecessorHalfFin13Atom0388 PredecessorHalfFin13Atom0392
    PredecessorHalfFin13Atom0395 PredecessorHalfFin13Atom0399 PredecessorHalfFin13Atom0405
    PredecessorHalfFin13Atom0423 PredecessorHalfFin13Atom0427 PredecessorHalfFin13Atom0433
    PredecessorHalfFin13Atom0454 PredecessorHalfFin13Atom0792 PredecessorHalfFin13Atom0796
    PredecessorHalfFin13Atom0802 PredecessorHalfFin13Atom0823 PredecessorHalfFin13Atom0879 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25428 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0401 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0456 chi ∧
      PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0804 chi ∧
      PredecessorHalfFin13Atom0825 chi ∧
      PredecessorHalfFin13Atom0881 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 4, 5, 6, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 4, 5, 6, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0387 PredecessorHalfFin13Atom0388 PredecessorHalfFin13Atom0394
    PredecessorHalfFin13Atom0395 PredecessorHalfFin13Atom0401 PredecessorHalfFin13Atom0407
    PredecessorHalfFin13Atom0423 PredecessorHalfFin13Atom0429 PredecessorHalfFin13Atom0435
    PredecessorHalfFin13Atom0456 PredecessorHalfFin13Atom0792 PredecessorHalfFin13Atom0798
    PredecessorHalfFin13Atom0804 PredecessorHalfFin13Atom0825 PredecessorHalfFin13Atom0881 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25429 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0882 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 4, 5, 7, 8} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 4, 5, 7, 8}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0387 PredecessorHalfFin13Atom0389 PredecessorHalfFin13Atom0390
    PredecessorHalfFin13Atom0396 PredecessorHalfFin13Atom0397 PredecessorHalfFin13Atom0408
    PredecessorHalfFin13Atom0424 PredecessorHalfFin13Atom0425 PredecessorHalfFin13Atom0436
    PredecessorHalfFin13Atom0457 PredecessorHalfFin13Atom0793 PredecessorHalfFin13Atom0794
    PredecessorHalfFin13Atom0805 PredecessorHalfFin13Atom0826 PredecessorHalfFin13Atom0882 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25430 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0883 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 4, 5, 7, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 4, 5, 7, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0387 PredecessorHalfFin13Atom0389 PredecessorHalfFin13Atom0391
    PredecessorHalfFin13Atom0396 PredecessorHalfFin13Atom0398 PredecessorHalfFin13Atom0409
    PredecessorHalfFin13Atom0424 PredecessorHalfFin13Atom0426 PredecessorHalfFin13Atom0437
    PredecessorHalfFin13Atom0458 PredecessorHalfFin13Atom0793 PredecessorHalfFin13Atom0795
    PredecessorHalfFin13Atom0806 PredecessorHalfFin13Atom0827 PredecessorHalfFin13Atom0883 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25431 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0459 chi ∧
      PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0884 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 4, 5, 7, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 4, 5, 7, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0387 PredecessorHalfFin13Atom0389 PredecessorHalfFin13Atom0392
    PredecessorHalfFin13Atom0396 PredecessorHalfFin13Atom0399 PredecessorHalfFin13Atom0410
    PredecessorHalfFin13Atom0424 PredecessorHalfFin13Atom0427 PredecessorHalfFin13Atom0438
    PredecessorHalfFin13Atom0459 PredecessorHalfFin13Atom0793 PredecessorHalfFin13Atom0796
    PredecessorHalfFin13Atom0807 PredecessorHalfFin13Atom0828 PredecessorHalfFin13Atom0884 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25433 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0401 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0461 chi ∧
      PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0886 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 4, 5, 7, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 4, 5, 7, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0387 PredecessorHalfFin13Atom0389 PredecessorHalfFin13Atom0394
    PredecessorHalfFin13Atom0396 PredecessorHalfFin13Atom0401 PredecessorHalfFin13Atom0412
    PredecessorHalfFin13Atom0424 PredecessorHalfFin13Atom0429 PredecessorHalfFin13Atom0440
    PredecessorHalfFin13Atom0461 PredecessorHalfFin13Atom0793 PredecessorHalfFin13Atom0798
    PredecessorHalfFin13Atom0809 PredecessorHalfFin13Atom0830 PredecessorHalfFin13Atom0886 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25434 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0887 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 4, 5, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 4, 5, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0387 PredecessorHalfFin13Atom0390 PredecessorHalfFin13Atom0391
    PredecessorHalfFin13Atom0397 PredecessorHalfFin13Atom0398 PredecessorHalfFin13Atom0413
    PredecessorHalfFin13Atom0425 PredecessorHalfFin13Atom0426 PredecessorHalfFin13Atom0441
    PredecessorHalfFin13Atom0462 PredecessorHalfFin13Atom0794 PredecessorHalfFin13Atom0795
    PredecessorHalfFin13Atom0810 PredecessorHalfFin13Atom0831 PredecessorHalfFin13Atom0887 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25435 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0888 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 4, 5, 8, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 4, 5, 8, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0387 PredecessorHalfFin13Atom0390 PredecessorHalfFin13Atom0392
    PredecessorHalfFin13Atom0397 PredecessorHalfFin13Atom0399 PredecessorHalfFin13Atom0414
    PredecessorHalfFin13Atom0425 PredecessorHalfFin13Atom0427 PredecessorHalfFin13Atom0442
    PredecessorHalfFin13Atom0463 PredecessorHalfFin13Atom0794 PredecessorHalfFin13Atom0796
    PredecessorHalfFin13Atom0811 PredecessorHalfFin13Atom0832 PredecessorHalfFin13Atom0888 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25437 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0401 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0813 chi ∧
      PredecessorHalfFin13Atom0834 chi ∧
      PredecessorHalfFin13Atom0890 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 4, 5, 8, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 4, 5, 8, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0387 PredecessorHalfFin13Atom0390 PredecessorHalfFin13Atom0394
    PredecessorHalfFin13Atom0397 PredecessorHalfFin13Atom0401 PredecessorHalfFin13Atom0416
    PredecessorHalfFin13Atom0425 PredecessorHalfFin13Atom0429 PredecessorHalfFin13Atom0444
    PredecessorHalfFin13Atom0465 PredecessorHalfFin13Atom0794 PredecessorHalfFin13Atom0798
    PredecessorHalfFin13Atom0813 PredecessorHalfFin13Atom0834 PredecessorHalfFin13Atom0890 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25438 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0891 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 4, 5, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 4, 5, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0387 PredecessorHalfFin13Atom0391 PredecessorHalfFin13Atom0392
    PredecessorHalfFin13Atom0398 PredecessorHalfFin13Atom0399 PredecessorHalfFin13Atom0417
    PredecessorHalfFin13Atom0426 PredecessorHalfFin13Atom0427 PredecessorHalfFin13Atom0445
    PredecessorHalfFin13Atom0466 PredecessorHalfFin13Atom0795 PredecessorHalfFin13Atom0796
    PredecessorHalfFin13Atom0814 PredecessorHalfFin13Atom0835 PredecessorHalfFin13Atom0891 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25440 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0401 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0816 chi ∧
      PredecessorHalfFin13Atom0837 chi ∧
      PredecessorHalfFin13Atom0893 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 4, 5, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 4, 5, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0387 PredecessorHalfFin13Atom0391 PredecessorHalfFin13Atom0394
    PredecessorHalfFin13Atom0398 PredecessorHalfFin13Atom0401 PredecessorHalfFin13Atom0419
    PredecessorHalfFin13Atom0426 PredecessorHalfFin13Atom0429 PredecessorHalfFin13Atom0447
    PredecessorHalfFin13Atom0468 PredecessorHalfFin13Atom0795 PredecessorHalfFin13Atom0798
    PredecessorHalfFin13Atom0816 PredecessorHalfFin13Atom0837 PredecessorHalfFin13Atom0893 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25442 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0401 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0818 chi ∧
      PredecessorHalfFin13Atom0839 chi ∧
      PredecessorHalfFin13Atom0895 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 4, 5, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 4, 5, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0387 PredecessorHalfFin13Atom0392 PredecessorHalfFin13Atom0394
    PredecessorHalfFin13Atom0399 PredecessorHalfFin13Atom0401 PredecessorHalfFin13Atom0421
    PredecessorHalfFin13Atom0427 PredecessorHalfFin13Atom0429 PredecessorHalfFin13Atom0449
    PredecessorHalfFin13Atom0470 PredecessorHalfFin13Atom0796 PredecessorHalfFin13Atom0798
    PredecessorHalfFin13Atom0818 PredecessorHalfFin13Atom0839 PredecessorHalfFin13Atom0895 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25444 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0799 chi ∧
      PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0841 chi ∧
      PredecessorHalfFin13Atom0897 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 4, 6, 7, 8} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 4, 6, 7, 8}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0388 PredecessorHalfFin13Atom0389 PredecessorHalfFin13Atom0390
    PredecessorHalfFin13Atom0402 PredecessorHalfFin13Atom0403 PredecessorHalfFin13Atom0408
    PredecessorHalfFin13Atom0430 PredecessorHalfFin13Atom0431 PredecessorHalfFin13Atom0436
    PredecessorHalfFin13Atom0472 PredecessorHalfFin13Atom0799 PredecessorHalfFin13Atom0800
    PredecessorHalfFin13Atom0805 PredecessorHalfFin13Atom0841 PredecessorHalfFin13Atom0897 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25446 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0799 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0843 chi ∧
      PredecessorHalfFin13Atom0899 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 4, 6, 7, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 4, 6, 7, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0388 PredecessorHalfFin13Atom0389 PredecessorHalfFin13Atom0392
    PredecessorHalfFin13Atom0402 PredecessorHalfFin13Atom0405 PredecessorHalfFin13Atom0410
    PredecessorHalfFin13Atom0430 PredecessorHalfFin13Atom0433 PredecessorHalfFin13Atom0438
    PredecessorHalfFin13Atom0474 PredecessorHalfFin13Atom0799 PredecessorHalfFin13Atom0802
    PredecessorHalfFin13Atom0807 PredecessorHalfFin13Atom0843 PredecessorHalfFin13Atom0899 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25448 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0476 chi ∧
      PredecessorHalfFin13Atom0799 chi ∧
      PredecessorHalfFin13Atom0804 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0845 chi ∧
      PredecessorHalfFin13Atom0901 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 4, 6, 7, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 4, 6, 7, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0388 PredecessorHalfFin13Atom0389 PredecessorHalfFin13Atom0394
    PredecessorHalfFin13Atom0402 PredecessorHalfFin13Atom0407 PredecessorHalfFin13Atom0412
    PredecessorHalfFin13Atom0430 PredecessorHalfFin13Atom0435 PredecessorHalfFin13Atom0440
    PredecessorHalfFin13Atom0476 PredecessorHalfFin13Atom0799 PredecessorHalfFin13Atom0804
    PredecessorHalfFin13Atom0809 PredecessorHalfFin13Atom0845 PredecessorHalfFin13Atom0901 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25449 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0846 chi ∧
      PredecessorHalfFin13Atom0902 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 4, 6, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 4, 6, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0388 PredecessorHalfFin13Atom0390 PredecessorHalfFin13Atom0391
    PredecessorHalfFin13Atom0403 PredecessorHalfFin13Atom0404 PredecessorHalfFin13Atom0413
    PredecessorHalfFin13Atom0431 PredecessorHalfFin13Atom0432 PredecessorHalfFin13Atom0441
    PredecessorHalfFin13Atom0477 PredecessorHalfFin13Atom0800 PredecessorHalfFin13Atom0801
    PredecessorHalfFin13Atom0810 PredecessorHalfFin13Atom0846 PredecessorHalfFin13Atom0902 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25450 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0847 chi ∧
      PredecessorHalfFin13Atom0903 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 4, 6, 8, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 4, 6, 8, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0388 PredecessorHalfFin13Atom0390 PredecessorHalfFin13Atom0392
    PredecessorHalfFin13Atom0403 PredecessorHalfFin13Atom0405 PredecessorHalfFin13Atom0414
    PredecessorHalfFin13Atom0431 PredecessorHalfFin13Atom0433 PredecessorHalfFin13Atom0442
    PredecessorHalfFin13Atom0478 PredecessorHalfFin13Atom0800 PredecessorHalfFin13Atom0802
    PredecessorHalfFin13Atom0811 PredecessorHalfFin13Atom0847 PredecessorHalfFin13Atom0903 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25452 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0804 chi ∧
      PredecessorHalfFin13Atom0813 chi ∧
      PredecessorHalfFin13Atom0849 chi ∧
      PredecessorHalfFin13Atom0905 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 4, 6, 8, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 4, 6, 8, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0388 PredecessorHalfFin13Atom0390 PredecessorHalfFin13Atom0394
    PredecessorHalfFin13Atom0403 PredecessorHalfFin13Atom0407 PredecessorHalfFin13Atom0416
    PredecessorHalfFin13Atom0431 PredecessorHalfFin13Atom0435 PredecessorHalfFin13Atom0444
    PredecessorHalfFin13Atom0480 PredecessorHalfFin13Atom0800 PredecessorHalfFin13Atom0804
    PredecessorHalfFin13Atom0813 PredecessorHalfFin13Atom0849 PredecessorHalfFin13Atom0905 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25453 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0850 chi ∧
      PredecessorHalfFin13Atom0906 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 4, 6, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 4, 6, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0388 PredecessorHalfFin13Atom0391 PredecessorHalfFin13Atom0392
    PredecessorHalfFin13Atom0404 PredecessorHalfFin13Atom0405 PredecessorHalfFin13Atom0417
    PredecessorHalfFin13Atom0432 PredecessorHalfFin13Atom0433 PredecessorHalfFin13Atom0445
    PredecessorHalfFin13Atom0481 PredecessorHalfFin13Atom0801 PredecessorHalfFin13Atom0802
    PredecessorHalfFin13Atom0814 PredecessorHalfFin13Atom0850 PredecessorHalfFin13Atom0906 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25455 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0804 chi ∧
      PredecessorHalfFin13Atom0816 chi ∧
      PredecessorHalfFin13Atom0852 chi ∧
      PredecessorHalfFin13Atom0908 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 4, 6, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 4, 6, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0388 PredecessorHalfFin13Atom0391 PredecessorHalfFin13Atom0394
    PredecessorHalfFin13Atom0404 PredecessorHalfFin13Atom0407 PredecessorHalfFin13Atom0419
    PredecessorHalfFin13Atom0432 PredecessorHalfFin13Atom0435 PredecessorHalfFin13Atom0447
    PredecessorHalfFin13Atom0483 PredecessorHalfFin13Atom0801 PredecessorHalfFin13Atom0804
    PredecessorHalfFin13Atom0816 PredecessorHalfFin13Atom0852 PredecessorHalfFin13Atom0908 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25457 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0804 chi ∧
      PredecessorHalfFin13Atom0818 chi ∧
      PredecessorHalfFin13Atom0854 chi ∧
      PredecessorHalfFin13Atom0910 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 4, 6, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 4, 6, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0388 PredecessorHalfFin13Atom0392 PredecessorHalfFin13Atom0394
    PredecessorHalfFin13Atom0405 PredecessorHalfFin13Atom0407 PredecessorHalfFin13Atom0421
    PredecessorHalfFin13Atom0433 PredecessorHalfFin13Atom0435 PredecessorHalfFin13Atom0449
    PredecessorHalfFin13Atom0485 PredecessorHalfFin13Atom0802 PredecessorHalfFin13Atom0804
    PredecessorHalfFin13Atom0818 PredecessorHalfFin13Atom0854 PredecessorHalfFin13Atom0910 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25459 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0856 chi ∧
      PredecessorHalfFin13Atom0912 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 4, 7, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 4, 7, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0389 PredecessorHalfFin13Atom0390 PredecessorHalfFin13Atom0391
    PredecessorHalfFin13Atom0408 PredecessorHalfFin13Atom0409 PredecessorHalfFin13Atom0413
    PredecessorHalfFin13Atom0436 PredecessorHalfFin13Atom0437 PredecessorHalfFin13Atom0441
    PredecessorHalfFin13Atom0487 PredecessorHalfFin13Atom0805 PredecessorHalfFin13Atom0806
    PredecessorHalfFin13Atom0810 PredecessorHalfFin13Atom0856 PredecessorHalfFin13Atom0912 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25460 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0857 chi ∧
      PredecessorHalfFin13Atom0913 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 4, 7, 8, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 4, 7, 8, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0389 PredecessorHalfFin13Atom0390 PredecessorHalfFin13Atom0392
    PredecessorHalfFin13Atom0408 PredecessorHalfFin13Atom0410 PredecessorHalfFin13Atom0414
    PredecessorHalfFin13Atom0436 PredecessorHalfFin13Atom0438 PredecessorHalfFin13Atom0442
    PredecessorHalfFin13Atom0488 PredecessorHalfFin13Atom0805 PredecessorHalfFin13Atom0807
    PredecessorHalfFin13Atom0811 PredecessorHalfFin13Atom0857 PredecessorHalfFin13Atom0913 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25462 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0813 chi ∧
      PredecessorHalfFin13Atom0859 chi ∧
      PredecessorHalfFin13Atom0915 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 4, 7, 8, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 4, 7, 8, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0389 PredecessorHalfFin13Atom0390 PredecessorHalfFin13Atom0394
    PredecessorHalfFin13Atom0408 PredecessorHalfFin13Atom0412 PredecessorHalfFin13Atom0416
    PredecessorHalfFin13Atom0436 PredecessorHalfFin13Atom0440 PredecessorHalfFin13Atom0444
    PredecessorHalfFin13Atom0490 PredecessorHalfFin13Atom0805 PredecessorHalfFin13Atom0809
    PredecessorHalfFin13Atom0813 PredecessorHalfFin13Atom0859 PredecessorHalfFin13Atom0915 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25463 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0860 chi ∧
      PredecessorHalfFin13Atom0916 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 4, 7, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 4, 7, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0389 PredecessorHalfFin13Atom0391 PredecessorHalfFin13Atom0392
    PredecessorHalfFin13Atom0409 PredecessorHalfFin13Atom0410 PredecessorHalfFin13Atom0417
    PredecessorHalfFin13Atom0437 PredecessorHalfFin13Atom0438 PredecessorHalfFin13Atom0445
    PredecessorHalfFin13Atom0491 PredecessorHalfFin13Atom0806 PredecessorHalfFin13Atom0807
    PredecessorHalfFin13Atom0814 PredecessorHalfFin13Atom0860 PredecessorHalfFin13Atom0916 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25465 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0816 chi ∧
      PredecessorHalfFin13Atom0862 chi ∧
      PredecessorHalfFin13Atom0918 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 4, 7, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 4, 7, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0389 PredecessorHalfFin13Atom0391 PredecessorHalfFin13Atom0394
    PredecessorHalfFin13Atom0409 PredecessorHalfFin13Atom0412 PredecessorHalfFin13Atom0419
    PredecessorHalfFin13Atom0437 PredecessorHalfFin13Atom0440 PredecessorHalfFin13Atom0447
    PredecessorHalfFin13Atom0493 PredecessorHalfFin13Atom0806 PredecessorHalfFin13Atom0809
    PredecessorHalfFin13Atom0816 PredecessorHalfFin13Atom0862 PredecessorHalfFin13Atom0918 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25467 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0818 chi ∧
      PredecessorHalfFin13Atom0864 chi ∧
      PredecessorHalfFin13Atom0920 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 4, 7, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 4, 7, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0389 PredecessorHalfFin13Atom0392 PredecessorHalfFin13Atom0394
    PredecessorHalfFin13Atom0410 PredecessorHalfFin13Atom0412 PredecessorHalfFin13Atom0421
    PredecessorHalfFin13Atom0438 PredecessorHalfFin13Atom0440 PredecessorHalfFin13Atom0449
    PredecessorHalfFin13Atom0495 PredecessorHalfFin13Atom0807 PredecessorHalfFin13Atom0809
    PredecessorHalfFin13Atom0818 PredecessorHalfFin13Atom0864 PredecessorHalfFin13Atom0920 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25469 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0497 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0866 chi ∧
      PredecessorHalfFin13Atom0922 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 4, 8, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 4, 8, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0390 PredecessorHalfFin13Atom0391 PredecessorHalfFin13Atom0392
    PredecessorHalfFin13Atom0413 PredecessorHalfFin13Atom0414 PredecessorHalfFin13Atom0417
    PredecessorHalfFin13Atom0441 PredecessorHalfFin13Atom0442 PredecessorHalfFin13Atom0445
    PredecessorHalfFin13Atom0497 PredecessorHalfFin13Atom0810 PredecessorHalfFin13Atom0811
    PredecessorHalfFin13Atom0814 PredecessorHalfFin13Atom0866 PredecessorHalfFin13Atom0922 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25471 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0499 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0813 chi ∧
      PredecessorHalfFin13Atom0816 chi ∧
      PredecessorHalfFin13Atom0868 chi ∧
      PredecessorHalfFin13Atom0924 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 4, 8, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 4, 8, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0390 PredecessorHalfFin13Atom0391 PredecessorHalfFin13Atom0394
    PredecessorHalfFin13Atom0413 PredecessorHalfFin13Atom0416 PredecessorHalfFin13Atom0419
    PredecessorHalfFin13Atom0441 PredecessorHalfFin13Atom0444 PredecessorHalfFin13Atom0447
    PredecessorHalfFin13Atom0499 PredecessorHalfFin13Atom0810 PredecessorHalfFin13Atom0813
    PredecessorHalfFin13Atom0816 PredecessorHalfFin13Atom0868 PredecessorHalfFin13Atom0924 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25473 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0501 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0813 chi ∧
      PredecessorHalfFin13Atom0818 chi ∧
      PredecessorHalfFin13Atom0870 chi ∧
      PredecessorHalfFin13Atom0926 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 4, 8, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 4, 8, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0390 PredecessorHalfFin13Atom0392 PredecessorHalfFin13Atom0394
    PredecessorHalfFin13Atom0414 PredecessorHalfFin13Atom0416 PredecessorHalfFin13Atom0421
    PredecessorHalfFin13Atom0442 PredecessorHalfFin13Atom0444 PredecessorHalfFin13Atom0449
    PredecessorHalfFin13Atom0501 PredecessorHalfFin13Atom0811 PredecessorHalfFin13Atom0813
    PredecessorHalfFin13Atom0818 PredecessorHalfFin13Atom0870 PredecessorHalfFin13Atom0926 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25476 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0504 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0816 chi ∧
      PredecessorHalfFin13Atom0818 chi ∧
      PredecessorHalfFin13Atom0873 chi ∧
      PredecessorHalfFin13Atom0929 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 4, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 4, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0391 PredecessorHalfFin13Atom0392 PredecessorHalfFin13Atom0394
    PredecessorHalfFin13Atom0417 PredecessorHalfFin13Atom0419 PredecessorHalfFin13Atom0421
    PredecessorHalfFin13Atom0445 PredecessorHalfFin13Atom0447 PredecessorHalfFin13Atom0449
    PredecessorHalfFin13Atom0504 PredecessorHalfFin13Atom0814 PredecessorHalfFin13Atom0816
    PredecessorHalfFin13Atom0818 PredecessorHalfFin13Atom0873 PredecessorHalfFin13Atom0929 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25479 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0451 chi ∧
      PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0821 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0841 chi ∧
      PredecessorHalfFin13Atom0932 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 5, 6, 7, 8} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 5, 6, 7, 8}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0395 PredecessorHalfFin13Atom0396 PredecessorHalfFin13Atom0397
    PredecessorHalfFin13Atom0402 PredecessorHalfFin13Atom0403 PredecessorHalfFin13Atom0408
    PredecessorHalfFin13Atom0451 PredecessorHalfFin13Atom0452 PredecessorHalfFin13Atom0457
    PredecessorHalfFin13Atom0472 PredecessorHalfFin13Atom0820 PredecessorHalfFin13Atom0821
    PredecessorHalfFin13Atom0826 PredecessorHalfFin13Atom0841 PredecessorHalfFin13Atom0932 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25480 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0451 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0473 chi ∧
      PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0842 chi ∧
      PredecessorHalfFin13Atom0933 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 5, 6, 7, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 5, 6, 7, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0395 PredecessorHalfFin13Atom0396 PredecessorHalfFin13Atom0398
    PredecessorHalfFin13Atom0402 PredecessorHalfFin13Atom0404 PredecessorHalfFin13Atom0409
    PredecessorHalfFin13Atom0451 PredecessorHalfFin13Atom0453 PredecessorHalfFin13Atom0458
    PredecessorHalfFin13Atom0473 PredecessorHalfFin13Atom0820 PredecessorHalfFin13Atom0822
    PredecessorHalfFin13Atom0827 PredecessorHalfFin13Atom0842 PredecessorHalfFin13Atom0933 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25481 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0451 chi ∧
      PredecessorHalfFin13Atom0454 chi ∧
      PredecessorHalfFin13Atom0459 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0843 chi ∧
      PredecessorHalfFin13Atom0934 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 5, 6, 7, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 5, 6, 7, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0395 PredecessorHalfFin13Atom0396 PredecessorHalfFin13Atom0399
    PredecessorHalfFin13Atom0402 PredecessorHalfFin13Atom0405 PredecessorHalfFin13Atom0410
    PredecessorHalfFin13Atom0451 PredecessorHalfFin13Atom0454 PredecessorHalfFin13Atom0459
    PredecessorHalfFin13Atom0474 PredecessorHalfFin13Atom0820 PredecessorHalfFin13Atom0823
    PredecessorHalfFin13Atom0828 PredecessorHalfFin13Atom0843 PredecessorHalfFin13Atom0934 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25483 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0401 chi ∧
      PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0451 chi ∧
      PredecessorHalfFin13Atom0456 chi ∧
      PredecessorHalfFin13Atom0461 chi ∧
      PredecessorHalfFin13Atom0476 chi ∧
      PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0825 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0845 chi ∧
      PredecessorHalfFin13Atom0936 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 5, 6, 7, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 5, 6, 7, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0395 PredecessorHalfFin13Atom0396 PredecessorHalfFin13Atom0401
    PredecessorHalfFin13Atom0402 PredecessorHalfFin13Atom0407 PredecessorHalfFin13Atom0412
    PredecessorHalfFin13Atom0451 PredecessorHalfFin13Atom0456 PredecessorHalfFin13Atom0461
    PredecessorHalfFin13Atom0476 PredecessorHalfFin13Atom0820 PredecessorHalfFin13Atom0825
    PredecessorHalfFin13Atom0830 PredecessorHalfFin13Atom0845 PredecessorHalfFin13Atom0936 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25484 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0821 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0846 chi ∧
      PredecessorHalfFin13Atom0937 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 5, 6, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 5, 6, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0395 PredecessorHalfFin13Atom0397 PredecessorHalfFin13Atom0398
    PredecessorHalfFin13Atom0403 PredecessorHalfFin13Atom0404 PredecessorHalfFin13Atom0413
    PredecessorHalfFin13Atom0452 PredecessorHalfFin13Atom0453 PredecessorHalfFin13Atom0462
    PredecessorHalfFin13Atom0477 PredecessorHalfFin13Atom0821 PredecessorHalfFin13Atom0822
    PredecessorHalfFin13Atom0831 PredecessorHalfFin13Atom0846 PredecessorHalfFin13Atom0937 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25485 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0454 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0821 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0847 chi ∧
      PredecessorHalfFin13Atom0938 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 5, 6, 8, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 5, 6, 8, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0395 PredecessorHalfFin13Atom0397 PredecessorHalfFin13Atom0399
    PredecessorHalfFin13Atom0403 PredecessorHalfFin13Atom0405 PredecessorHalfFin13Atom0414
    PredecessorHalfFin13Atom0452 PredecessorHalfFin13Atom0454 PredecessorHalfFin13Atom0463
    PredecessorHalfFin13Atom0478 PredecessorHalfFin13Atom0821 PredecessorHalfFin13Atom0823
    PredecessorHalfFin13Atom0832 PredecessorHalfFin13Atom0847 PredecessorHalfFin13Atom0938 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25487 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0401 chi ∧
      PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0456 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0821 chi ∧
      PredecessorHalfFin13Atom0825 chi ∧
      PredecessorHalfFin13Atom0834 chi ∧
      PredecessorHalfFin13Atom0849 chi ∧
      PredecessorHalfFin13Atom0940 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 5, 6, 8, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 5, 6, 8, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0395 PredecessorHalfFin13Atom0397 PredecessorHalfFin13Atom0401
    PredecessorHalfFin13Atom0403 PredecessorHalfFin13Atom0407 PredecessorHalfFin13Atom0416
    PredecessorHalfFin13Atom0452 PredecessorHalfFin13Atom0456 PredecessorHalfFin13Atom0465
    PredecessorHalfFin13Atom0480 PredecessorHalfFin13Atom0821 PredecessorHalfFin13Atom0825
    PredecessorHalfFin13Atom0834 PredecessorHalfFin13Atom0849 PredecessorHalfFin13Atom0940 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25488 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0454 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0850 chi ∧
      PredecessorHalfFin13Atom0941 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 5, 6, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 5, 6, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0395 PredecessorHalfFin13Atom0398 PredecessorHalfFin13Atom0399
    PredecessorHalfFin13Atom0404 PredecessorHalfFin13Atom0405 PredecessorHalfFin13Atom0417
    PredecessorHalfFin13Atom0453 PredecessorHalfFin13Atom0454 PredecessorHalfFin13Atom0466
    PredecessorHalfFin13Atom0481 PredecessorHalfFin13Atom0822 PredecessorHalfFin13Atom0823
    PredecessorHalfFin13Atom0835 PredecessorHalfFin13Atom0850 PredecessorHalfFin13Atom0941 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25490 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0401 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0456 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0825 chi ∧
      PredecessorHalfFin13Atom0837 chi ∧
      PredecessorHalfFin13Atom0852 chi ∧
      PredecessorHalfFin13Atom0943 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 5, 6, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 5, 6, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0395 PredecessorHalfFin13Atom0398 PredecessorHalfFin13Atom0401
    PredecessorHalfFin13Atom0404 PredecessorHalfFin13Atom0407 PredecessorHalfFin13Atom0419
    PredecessorHalfFin13Atom0453 PredecessorHalfFin13Atom0456 PredecessorHalfFin13Atom0468
    PredecessorHalfFin13Atom0483 PredecessorHalfFin13Atom0822 PredecessorHalfFin13Atom0825
    PredecessorHalfFin13Atom0837 PredecessorHalfFin13Atom0852 PredecessorHalfFin13Atom0943 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25492 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0401 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0454 chi ∧
      PredecessorHalfFin13Atom0456 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0825 chi ∧
      PredecessorHalfFin13Atom0839 chi ∧
      PredecessorHalfFin13Atom0854 chi ∧
      PredecessorHalfFin13Atom0945 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 5, 6, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 5, 6, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0395 PredecessorHalfFin13Atom0399 PredecessorHalfFin13Atom0401
    PredecessorHalfFin13Atom0405 PredecessorHalfFin13Atom0407 PredecessorHalfFin13Atom0421
    PredecessorHalfFin13Atom0454 PredecessorHalfFin13Atom0456 PredecessorHalfFin13Atom0470
    PredecessorHalfFin13Atom0485 PredecessorHalfFin13Atom0823 PredecessorHalfFin13Atom0825
    PredecessorHalfFin13Atom0839 PredecessorHalfFin13Atom0854 PredecessorHalfFin13Atom0945 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25494 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0856 chi ∧
      PredecessorHalfFin13Atom0947 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 5, 7, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 5, 7, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0396 PredecessorHalfFin13Atom0397 PredecessorHalfFin13Atom0398
    PredecessorHalfFin13Atom0408 PredecessorHalfFin13Atom0409 PredecessorHalfFin13Atom0413
    PredecessorHalfFin13Atom0457 PredecessorHalfFin13Atom0458 PredecessorHalfFin13Atom0462
    PredecessorHalfFin13Atom0487 PredecessorHalfFin13Atom0826 PredecessorHalfFin13Atom0827
    PredecessorHalfFin13Atom0831 PredecessorHalfFin13Atom0856 PredecessorHalfFin13Atom0947 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25495 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0459 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0857 chi ∧
      PredecessorHalfFin13Atom0948 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 5, 7, 8, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 5, 7, 8, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0396 PredecessorHalfFin13Atom0397 PredecessorHalfFin13Atom0399
    PredecessorHalfFin13Atom0408 PredecessorHalfFin13Atom0410 PredecessorHalfFin13Atom0414
    PredecessorHalfFin13Atom0457 PredecessorHalfFin13Atom0459 PredecessorHalfFin13Atom0463
    PredecessorHalfFin13Atom0488 PredecessorHalfFin13Atom0826 PredecessorHalfFin13Atom0828
    PredecessorHalfFin13Atom0832 PredecessorHalfFin13Atom0857 PredecessorHalfFin13Atom0948 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25497 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0401 chi ∧
      PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0461 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0834 chi ∧
      PredecessorHalfFin13Atom0859 chi ∧
      PredecessorHalfFin13Atom0950 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 5, 7, 8, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 5, 7, 8, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0396 PredecessorHalfFin13Atom0397 PredecessorHalfFin13Atom0401
    PredecessorHalfFin13Atom0408 PredecessorHalfFin13Atom0412 PredecessorHalfFin13Atom0416
    PredecessorHalfFin13Atom0457 PredecessorHalfFin13Atom0461 PredecessorHalfFin13Atom0465
    PredecessorHalfFin13Atom0490 PredecessorHalfFin13Atom0826 PredecessorHalfFin13Atom0830
    PredecessorHalfFin13Atom0834 PredecessorHalfFin13Atom0859 PredecessorHalfFin13Atom0950 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25498 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0459 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0860 chi ∧
      PredecessorHalfFin13Atom0951 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 5, 7, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 5, 7, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0396 PredecessorHalfFin13Atom0398 PredecessorHalfFin13Atom0399
    PredecessorHalfFin13Atom0409 PredecessorHalfFin13Atom0410 PredecessorHalfFin13Atom0417
    PredecessorHalfFin13Atom0458 PredecessorHalfFin13Atom0459 PredecessorHalfFin13Atom0466
    PredecessorHalfFin13Atom0491 PredecessorHalfFin13Atom0827 PredecessorHalfFin13Atom0828
    PredecessorHalfFin13Atom0835 PredecessorHalfFin13Atom0860 PredecessorHalfFin13Atom0951 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25500 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0401 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0461 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0837 chi ∧
      PredecessorHalfFin13Atom0862 chi ∧
      PredecessorHalfFin13Atom0953 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 5, 7, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 5, 7, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0396 PredecessorHalfFin13Atom0398 PredecessorHalfFin13Atom0401
    PredecessorHalfFin13Atom0409 PredecessorHalfFin13Atom0412 PredecessorHalfFin13Atom0419
    PredecessorHalfFin13Atom0458 PredecessorHalfFin13Atom0461 PredecessorHalfFin13Atom0468
    PredecessorHalfFin13Atom0493 PredecessorHalfFin13Atom0827 PredecessorHalfFin13Atom0830
    PredecessorHalfFin13Atom0837 PredecessorHalfFin13Atom0862 PredecessorHalfFin13Atom0953 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25502 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0401 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0459 chi ∧
      PredecessorHalfFin13Atom0461 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0839 chi ∧
      PredecessorHalfFin13Atom0864 chi ∧
      PredecessorHalfFin13Atom0955 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 5, 7, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 5, 7, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0396 PredecessorHalfFin13Atom0399 PredecessorHalfFin13Atom0401
    PredecessorHalfFin13Atom0410 PredecessorHalfFin13Atom0412 PredecessorHalfFin13Atom0421
    PredecessorHalfFin13Atom0459 PredecessorHalfFin13Atom0461 PredecessorHalfFin13Atom0470
    PredecessorHalfFin13Atom0495 PredecessorHalfFin13Atom0828 PredecessorHalfFin13Atom0830
    PredecessorHalfFin13Atom0839 PredecessorHalfFin13Atom0864 PredecessorHalfFin13Atom0955 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25504 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0497 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0866 chi ∧
      PredecessorHalfFin13Atom0957 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 5, 8, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 5, 8, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0397 PredecessorHalfFin13Atom0398 PredecessorHalfFin13Atom0399
    PredecessorHalfFin13Atom0413 PredecessorHalfFin13Atom0414 PredecessorHalfFin13Atom0417
    PredecessorHalfFin13Atom0462 PredecessorHalfFin13Atom0463 PredecessorHalfFin13Atom0466
    PredecessorHalfFin13Atom0497 PredecessorHalfFin13Atom0831 PredecessorHalfFin13Atom0832
    PredecessorHalfFin13Atom0835 PredecessorHalfFin13Atom0866 PredecessorHalfFin13Atom0957 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25506 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0401 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0499 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0834 chi ∧
      PredecessorHalfFin13Atom0837 chi ∧
      PredecessorHalfFin13Atom0868 chi ∧
      PredecessorHalfFin13Atom0959 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 5, 8, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 5, 8, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0397 PredecessorHalfFin13Atom0398 PredecessorHalfFin13Atom0401
    PredecessorHalfFin13Atom0413 PredecessorHalfFin13Atom0416 PredecessorHalfFin13Atom0419
    PredecessorHalfFin13Atom0462 PredecessorHalfFin13Atom0465 PredecessorHalfFin13Atom0468
    PredecessorHalfFin13Atom0499 PredecessorHalfFin13Atom0831 PredecessorHalfFin13Atom0834
    PredecessorHalfFin13Atom0837 PredecessorHalfFin13Atom0868 PredecessorHalfFin13Atom0959 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25508 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0401 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0501 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0834 chi ∧
      PredecessorHalfFin13Atom0839 chi ∧
      PredecessorHalfFin13Atom0870 chi ∧
      PredecessorHalfFin13Atom0961 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 5, 8, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 5, 8, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0397 PredecessorHalfFin13Atom0399 PredecessorHalfFin13Atom0401
    PredecessorHalfFin13Atom0414 PredecessorHalfFin13Atom0416 PredecessorHalfFin13Atom0421
    PredecessorHalfFin13Atom0463 PredecessorHalfFin13Atom0465 PredecessorHalfFin13Atom0470
    PredecessorHalfFin13Atom0501 PredecessorHalfFin13Atom0832 PredecessorHalfFin13Atom0834
    PredecessorHalfFin13Atom0839 PredecessorHalfFin13Atom0870 PredecessorHalfFin13Atom0961 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25511 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0401 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0504 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0837 chi ∧
      PredecessorHalfFin13Atom0839 chi ∧
      PredecessorHalfFin13Atom0873 chi ∧
      PredecessorHalfFin13Atom0964 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 5, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 5, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0398 PredecessorHalfFin13Atom0399 PredecessorHalfFin13Atom0401
    PredecessorHalfFin13Atom0417 PredecessorHalfFin13Atom0419 PredecessorHalfFin13Atom0421
    PredecessorHalfFin13Atom0466 PredecessorHalfFin13Atom0468 PredecessorHalfFin13Atom0470
    PredecessorHalfFin13Atom0504 PredecessorHalfFin13Atom0835 PredecessorHalfFin13Atom0837
    PredecessorHalfFin13Atom0839 PredecessorHalfFin13Atom0873 PredecessorHalfFin13Atom0964 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25515 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0841 chi ∧
      PredecessorHalfFin13Atom0843 chi ∧
      PredecessorHalfFin13Atom0847 chi ∧
      PredecessorHalfFin13Atom0857 chi ∧
      PredecessorHalfFin13Atom0968 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 6, 7, 8, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 6, 7, 8, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0402 PredecessorHalfFin13Atom0403 PredecessorHalfFin13Atom0405
    PredecessorHalfFin13Atom0408 PredecessorHalfFin13Atom0410 PredecessorHalfFin13Atom0414
    PredecessorHalfFin13Atom0472 PredecessorHalfFin13Atom0474 PredecessorHalfFin13Atom0478
    PredecessorHalfFin13Atom0488 PredecessorHalfFin13Atom0841 PredecessorHalfFin13Atom0843
    PredecessorHalfFin13Atom0847 PredecessorHalfFin13Atom0857 PredecessorHalfFin13Atom0968 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25518 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0473 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0842 chi ∧
      PredecessorHalfFin13Atom0843 chi ∧
      PredecessorHalfFin13Atom0850 chi ∧
      PredecessorHalfFin13Atom0860 chi ∧
      PredecessorHalfFin13Atom0971 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 6, 7, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 6, 7, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0402 PredecessorHalfFin13Atom0404 PredecessorHalfFin13Atom0405
    PredecessorHalfFin13Atom0409 PredecessorHalfFin13Atom0410 PredecessorHalfFin13Atom0417
    PredecessorHalfFin13Atom0473 PredecessorHalfFin13Atom0474 PredecessorHalfFin13Atom0481
    PredecessorHalfFin13Atom0491 PredecessorHalfFin13Atom0842 PredecessorHalfFin13Atom0843
    PredecessorHalfFin13Atom0850 PredecessorHalfFin13Atom0860 PredecessorHalfFin13Atom0971 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25520 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0473 chi ∧
      PredecessorHalfFin13Atom0476 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0842 chi ∧
      PredecessorHalfFin13Atom0845 chi ∧
      PredecessorHalfFin13Atom0852 chi ∧
      PredecessorHalfFin13Atom0862 chi ∧
      PredecessorHalfFin13Atom0973 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 6, 7, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 6, 7, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0402 PredecessorHalfFin13Atom0404 PredecessorHalfFin13Atom0407
    PredecessorHalfFin13Atom0409 PredecessorHalfFin13Atom0412 PredecessorHalfFin13Atom0419
    PredecessorHalfFin13Atom0473 PredecessorHalfFin13Atom0476 PredecessorHalfFin13Atom0483
    PredecessorHalfFin13Atom0493 PredecessorHalfFin13Atom0842 PredecessorHalfFin13Atom0845
    PredecessorHalfFin13Atom0852 PredecessorHalfFin13Atom0862 PredecessorHalfFin13Atom0973 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25522 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0476 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0843 chi ∧
      PredecessorHalfFin13Atom0845 chi ∧
      PredecessorHalfFin13Atom0854 chi ∧
      PredecessorHalfFin13Atom0864 chi ∧
      PredecessorHalfFin13Atom0975 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 6, 7, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 6, 7, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0402 PredecessorHalfFin13Atom0405 PredecessorHalfFin13Atom0407
    PredecessorHalfFin13Atom0410 PredecessorHalfFin13Atom0412 PredecessorHalfFin13Atom0421
    PredecessorHalfFin13Atom0474 PredecessorHalfFin13Atom0476 PredecessorHalfFin13Atom0485
    PredecessorHalfFin13Atom0495 PredecessorHalfFin13Atom0843 PredecessorHalfFin13Atom0845
    PredecessorHalfFin13Atom0854 PredecessorHalfFin13Atom0864 PredecessorHalfFin13Atom0975 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25524 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0497 chi ∧
      PredecessorHalfFin13Atom0846 chi ∧
      PredecessorHalfFin13Atom0847 chi ∧
      PredecessorHalfFin13Atom0850 chi ∧
      PredecessorHalfFin13Atom0866 chi ∧
      PredecessorHalfFin13Atom0977 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 6, 8, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 6, 8, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0403 PredecessorHalfFin13Atom0404 PredecessorHalfFin13Atom0405
    PredecessorHalfFin13Atom0413 PredecessorHalfFin13Atom0414 PredecessorHalfFin13Atom0417
    PredecessorHalfFin13Atom0477 PredecessorHalfFin13Atom0478 PredecessorHalfFin13Atom0481
    PredecessorHalfFin13Atom0497 PredecessorHalfFin13Atom0846 PredecessorHalfFin13Atom0847
    PredecessorHalfFin13Atom0850 PredecessorHalfFin13Atom0866 PredecessorHalfFin13Atom0977 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25528 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0501 chi ∧
      PredecessorHalfFin13Atom0847 chi ∧
      PredecessorHalfFin13Atom0849 chi ∧
      PredecessorHalfFin13Atom0854 chi ∧
      PredecessorHalfFin13Atom0870 chi ∧
      PredecessorHalfFin13Atom0981 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 6, 8, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 6, 8, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0403 PredecessorHalfFin13Atom0405 PredecessorHalfFin13Atom0407
    PredecessorHalfFin13Atom0414 PredecessorHalfFin13Atom0416 PredecessorHalfFin13Atom0421
    PredecessorHalfFin13Atom0478 PredecessorHalfFin13Atom0480 PredecessorHalfFin13Atom0485
    PredecessorHalfFin13Atom0501 PredecessorHalfFin13Atom0847 PredecessorHalfFin13Atom0849
    PredecessorHalfFin13Atom0854 PredecessorHalfFin13Atom0870 PredecessorHalfFin13Atom0981 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25531 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0504 chi ∧
      PredecessorHalfFin13Atom0850 chi ∧
      PredecessorHalfFin13Atom0852 chi ∧
      PredecessorHalfFin13Atom0854 chi ∧
      PredecessorHalfFin13Atom0873 chi ∧
      PredecessorHalfFin13Atom0984 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 6, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 6, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0404 PredecessorHalfFin13Atom0405 PredecessorHalfFin13Atom0407
    PredecessorHalfFin13Atom0417 PredecessorHalfFin13Atom0419 PredecessorHalfFin13Atom0421
    PredecessorHalfFin13Atom0481 PredecessorHalfFin13Atom0483 PredecessorHalfFin13Atom0485
    PredecessorHalfFin13Atom0504 PredecessorHalfFin13Atom0850 PredecessorHalfFin13Atom0852
    PredecessorHalfFin13Atom0854 PredecessorHalfFin13Atom0873 PredecessorHalfFin13Atom0984 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25534 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0497 chi ∧
      PredecessorHalfFin13Atom0856 chi ∧
      PredecessorHalfFin13Atom0857 chi ∧
      PredecessorHalfFin13Atom0860 chi ∧
      PredecessorHalfFin13Atom0866 chi ∧
      PredecessorHalfFin13Atom0987 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 7, 8, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 7, 8, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0408 PredecessorHalfFin13Atom0409 PredecessorHalfFin13Atom0410
    PredecessorHalfFin13Atom0413 PredecessorHalfFin13Atom0414 PredecessorHalfFin13Atom0417
    PredecessorHalfFin13Atom0487 PredecessorHalfFin13Atom0488 PredecessorHalfFin13Atom0491
    PredecessorHalfFin13Atom0497 PredecessorHalfFin13Atom0856 PredecessorHalfFin13Atom0857
    PredecessorHalfFin13Atom0860 PredecessorHalfFin13Atom0866 PredecessorHalfFin13Atom0987 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25536 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0499 chi ∧
      PredecessorHalfFin13Atom0856 chi ∧
      PredecessorHalfFin13Atom0859 chi ∧
      PredecessorHalfFin13Atom0862 chi ∧
      PredecessorHalfFin13Atom0868 chi ∧
      PredecessorHalfFin13Atom0989 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 7, 8, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 7, 8, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0408 PredecessorHalfFin13Atom0409 PredecessorHalfFin13Atom0412
    PredecessorHalfFin13Atom0413 PredecessorHalfFin13Atom0416 PredecessorHalfFin13Atom0419
    PredecessorHalfFin13Atom0487 PredecessorHalfFin13Atom0490 PredecessorHalfFin13Atom0493
    PredecessorHalfFin13Atom0499 PredecessorHalfFin13Atom0856 PredecessorHalfFin13Atom0859
    PredecessorHalfFin13Atom0862 PredecessorHalfFin13Atom0868 PredecessorHalfFin13Atom0989 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25538 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0501 chi ∧
      PredecessorHalfFin13Atom0857 chi ∧
      PredecessorHalfFin13Atom0859 chi ∧
      PredecessorHalfFin13Atom0864 chi ∧
      PredecessorHalfFin13Atom0870 chi ∧
      PredecessorHalfFin13Atom0991 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 7, 8, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 7, 8, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0408 PredecessorHalfFin13Atom0410 PredecessorHalfFin13Atom0412
    PredecessorHalfFin13Atom0414 PredecessorHalfFin13Atom0416 PredecessorHalfFin13Atom0421
    PredecessorHalfFin13Atom0488 PredecessorHalfFin13Atom0490 PredecessorHalfFin13Atom0495
    PredecessorHalfFin13Atom0501 PredecessorHalfFin13Atom0857 PredecessorHalfFin13Atom0859
    PredecessorHalfFin13Atom0864 PredecessorHalfFin13Atom0870 PredecessorHalfFin13Atom0991 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25545 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0497 chi ∧
      PredecessorHalfFin13Atom0499 chi ∧
      PredecessorHalfFin13Atom0501 chi ∧
      PredecessorHalfFin13Atom0504 chi ∧
      PredecessorHalfFin13Atom0866 chi ∧
      PredecessorHalfFin13Atom0868 chi ∧
      PredecessorHalfFin13Atom0870 chi ∧
      PredecessorHalfFin13Atom0873 chi ∧
      PredecessorHalfFin13Atom0998 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 3, 8, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 8, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0413 PredecessorHalfFin13Atom0414 PredecessorHalfFin13Atom0416
    PredecessorHalfFin13Atom0417 PredecessorHalfFin13Atom0419 PredecessorHalfFin13Atom0421
    PredecessorHalfFin13Atom0497 PredecessorHalfFin13Atom0499 PredecessorHalfFin13Atom0501
    PredecessorHalfFin13Atom0504 PredecessorHalfFin13Atom0866 PredecessorHalfFin13Atom0868
    PredecessorHalfFin13Atom0870 PredecessorHalfFin13Atom0873 PredecessorHalfFin13Atom0998 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25549 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0451 chi ∧
      PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0876 chi ∧
      PredecessorHalfFin13Atom0877 chi ∧
      PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0897 chi ∧
      PredecessorHalfFin13Atom0932 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 4, 5, 6, 7, 8} := by
    intro hstrong
    exact hnoStrong ⟨{0, 4, 5, 6, 7, 8}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0423 PredecessorHalfFin13Atom0424 PredecessorHalfFin13Atom0425
    PredecessorHalfFin13Atom0430 PredecessorHalfFin13Atom0431 PredecessorHalfFin13Atom0436
    PredecessorHalfFin13Atom0451 PredecessorHalfFin13Atom0452 PredecessorHalfFin13Atom0457
    PredecessorHalfFin13Atom0472 PredecessorHalfFin13Atom0876 PredecessorHalfFin13Atom0877
    PredecessorHalfFin13Atom0882 PredecessorHalfFin13Atom0897 PredecessorHalfFin13Atom0932 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25550 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0451 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0473 chi ∧
      PredecessorHalfFin13Atom0876 chi ∧
      PredecessorHalfFin13Atom0878 chi ∧
      PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0898 chi ∧
      PredecessorHalfFin13Atom0933 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 4, 5, 6, 7, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 4, 5, 6, 7, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0423 PredecessorHalfFin13Atom0424 PredecessorHalfFin13Atom0426
    PredecessorHalfFin13Atom0430 PredecessorHalfFin13Atom0432 PredecessorHalfFin13Atom0437
    PredecessorHalfFin13Atom0451 PredecessorHalfFin13Atom0453 PredecessorHalfFin13Atom0458
    PredecessorHalfFin13Atom0473 PredecessorHalfFin13Atom0876 PredecessorHalfFin13Atom0878
    PredecessorHalfFin13Atom0883 PredecessorHalfFin13Atom0898 PredecessorHalfFin13Atom0933 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25554 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0877 chi ∧
      PredecessorHalfFin13Atom0878 chi ∧
      PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0902 chi ∧
      PredecessorHalfFin13Atom0937 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 4, 5, 6, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 4, 5, 6, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0423 PredecessorHalfFin13Atom0425 PredecessorHalfFin13Atom0426
    PredecessorHalfFin13Atom0431 PredecessorHalfFin13Atom0432 PredecessorHalfFin13Atom0441
    PredecessorHalfFin13Atom0452 PredecessorHalfFin13Atom0453 PredecessorHalfFin13Atom0462
    PredecessorHalfFin13Atom0477 PredecessorHalfFin13Atom0877 PredecessorHalfFin13Atom0878
    PredecessorHalfFin13Atom0887 PredecessorHalfFin13Atom0902 PredecessorHalfFin13Atom0937 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25555 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0454 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0877 chi ∧
      PredecessorHalfFin13Atom0879 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0938 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 4, 5, 6, 8, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 4, 5, 6, 8, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0423 PredecessorHalfFin13Atom0425 PredecessorHalfFin13Atom0427
    PredecessorHalfFin13Atom0431 PredecessorHalfFin13Atom0433 PredecessorHalfFin13Atom0442
    PredecessorHalfFin13Atom0452 PredecessorHalfFin13Atom0454 PredecessorHalfFin13Atom0463
    PredecessorHalfFin13Atom0478 PredecessorHalfFin13Atom0877 PredecessorHalfFin13Atom0879
    PredecessorHalfFin13Atom0888 PredecessorHalfFin13Atom0903 PredecessorHalfFin13Atom0938 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25557 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0456 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0877 chi ∧
      PredecessorHalfFin13Atom0881 chi ∧
      PredecessorHalfFin13Atom0890 chi ∧
      PredecessorHalfFin13Atom0905 chi ∧
      PredecessorHalfFin13Atom0940 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 4, 5, 6, 8, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 4, 5, 6, 8, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0423 PredecessorHalfFin13Atom0425 PredecessorHalfFin13Atom0429
    PredecessorHalfFin13Atom0431 PredecessorHalfFin13Atom0435 PredecessorHalfFin13Atom0444
    PredecessorHalfFin13Atom0452 PredecessorHalfFin13Atom0456 PredecessorHalfFin13Atom0465
    PredecessorHalfFin13Atom0480 PredecessorHalfFin13Atom0877 PredecessorHalfFin13Atom0881
    PredecessorHalfFin13Atom0890 PredecessorHalfFin13Atom0905 PredecessorHalfFin13Atom0940 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25558 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0454 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0878 chi ∧
      PredecessorHalfFin13Atom0879 chi ∧
      PredecessorHalfFin13Atom0891 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0941 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 4, 5, 6, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 4, 5, 6, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0423 PredecessorHalfFin13Atom0426 PredecessorHalfFin13Atom0427
    PredecessorHalfFin13Atom0432 PredecessorHalfFin13Atom0433 PredecessorHalfFin13Atom0445
    PredecessorHalfFin13Atom0453 PredecessorHalfFin13Atom0454 PredecessorHalfFin13Atom0466
    PredecessorHalfFin13Atom0481 PredecessorHalfFin13Atom0878 PredecessorHalfFin13Atom0879
    PredecessorHalfFin13Atom0891 PredecessorHalfFin13Atom0906 PredecessorHalfFin13Atom0941 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25560 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0456 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0878 chi ∧
      PredecessorHalfFin13Atom0881 chi ∧
      PredecessorHalfFin13Atom0893 chi ∧
      PredecessorHalfFin13Atom0908 chi ∧
      PredecessorHalfFin13Atom0943 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 4, 5, 6, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 4, 5, 6, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0423 PredecessorHalfFin13Atom0426 PredecessorHalfFin13Atom0429
    PredecessorHalfFin13Atom0432 PredecessorHalfFin13Atom0435 PredecessorHalfFin13Atom0447
    PredecessorHalfFin13Atom0453 PredecessorHalfFin13Atom0456 PredecessorHalfFin13Atom0468
    PredecessorHalfFin13Atom0483 PredecessorHalfFin13Atom0878 PredecessorHalfFin13Atom0881
    PredecessorHalfFin13Atom0893 PredecessorHalfFin13Atom0908 PredecessorHalfFin13Atom0943 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25562 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0454 chi ∧
      PredecessorHalfFin13Atom0456 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0879 chi ∧
      PredecessorHalfFin13Atom0881 chi ∧
      PredecessorHalfFin13Atom0895 chi ∧
      PredecessorHalfFin13Atom0910 chi ∧
      PredecessorHalfFin13Atom0945 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 4, 5, 6, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 4, 5, 6, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0423 PredecessorHalfFin13Atom0427 PredecessorHalfFin13Atom0429
    PredecessorHalfFin13Atom0433 PredecessorHalfFin13Atom0435 PredecessorHalfFin13Atom0449
    PredecessorHalfFin13Atom0454 PredecessorHalfFin13Atom0456 PredecessorHalfFin13Atom0470
    PredecessorHalfFin13Atom0485 PredecessorHalfFin13Atom0879 PredecessorHalfFin13Atom0881
    PredecessorHalfFin13Atom0895 PredecessorHalfFin13Atom0910 PredecessorHalfFin13Atom0945 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25564 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0947 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 4, 5, 7, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 4, 5, 7, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0424 PredecessorHalfFin13Atom0425 PredecessorHalfFin13Atom0426
    PredecessorHalfFin13Atom0436 PredecessorHalfFin13Atom0437 PredecessorHalfFin13Atom0441
    PredecessorHalfFin13Atom0457 PredecessorHalfFin13Atom0458 PredecessorHalfFin13Atom0462
    PredecessorHalfFin13Atom0487 PredecessorHalfFin13Atom0882 PredecessorHalfFin13Atom0883
    PredecessorHalfFin13Atom0887 PredecessorHalfFin13Atom0912 PredecessorHalfFin13Atom0947 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25565 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0459 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0884 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0913 chi ∧
      PredecessorHalfFin13Atom0948 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 4, 5, 7, 8, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 4, 5, 7, 8, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0424 PredecessorHalfFin13Atom0425 PredecessorHalfFin13Atom0427
    PredecessorHalfFin13Atom0436 PredecessorHalfFin13Atom0438 PredecessorHalfFin13Atom0442
    PredecessorHalfFin13Atom0457 PredecessorHalfFin13Atom0459 PredecessorHalfFin13Atom0463
    PredecessorHalfFin13Atom0488 PredecessorHalfFin13Atom0882 PredecessorHalfFin13Atom0884
    PredecessorHalfFin13Atom0888 PredecessorHalfFin13Atom0913 PredecessorHalfFin13Atom0948 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25567 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0461 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0886 chi ∧
      PredecessorHalfFin13Atom0890 chi ∧
      PredecessorHalfFin13Atom0915 chi ∧
      PredecessorHalfFin13Atom0950 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 4, 5, 7, 8, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 4, 5, 7, 8, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0424 PredecessorHalfFin13Atom0425 PredecessorHalfFin13Atom0429
    PredecessorHalfFin13Atom0436 PredecessorHalfFin13Atom0440 PredecessorHalfFin13Atom0444
    PredecessorHalfFin13Atom0457 PredecessorHalfFin13Atom0461 PredecessorHalfFin13Atom0465
    PredecessorHalfFin13Atom0490 PredecessorHalfFin13Atom0882 PredecessorHalfFin13Atom0886
    PredecessorHalfFin13Atom0890 PredecessorHalfFin13Atom0915 PredecessorHalfFin13Atom0950 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25568 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0459 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0884 chi ∧
      PredecessorHalfFin13Atom0891 chi ∧
      PredecessorHalfFin13Atom0916 chi ∧
      PredecessorHalfFin13Atom0951 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 4, 5, 7, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 4, 5, 7, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0424 PredecessorHalfFin13Atom0426 PredecessorHalfFin13Atom0427
    PredecessorHalfFin13Atom0437 PredecessorHalfFin13Atom0438 PredecessorHalfFin13Atom0445
    PredecessorHalfFin13Atom0458 PredecessorHalfFin13Atom0459 PredecessorHalfFin13Atom0466
    PredecessorHalfFin13Atom0491 PredecessorHalfFin13Atom0883 PredecessorHalfFin13Atom0884
    PredecessorHalfFin13Atom0891 PredecessorHalfFin13Atom0916 PredecessorHalfFin13Atom0951 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25570 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0461 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0886 chi ∧
      PredecessorHalfFin13Atom0893 chi ∧
      PredecessorHalfFin13Atom0918 chi ∧
      PredecessorHalfFin13Atom0953 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 4, 5, 7, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 4, 5, 7, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0424 PredecessorHalfFin13Atom0426 PredecessorHalfFin13Atom0429
    PredecessorHalfFin13Atom0437 PredecessorHalfFin13Atom0440 PredecessorHalfFin13Atom0447
    PredecessorHalfFin13Atom0458 PredecessorHalfFin13Atom0461 PredecessorHalfFin13Atom0468
    PredecessorHalfFin13Atom0493 PredecessorHalfFin13Atom0883 PredecessorHalfFin13Atom0886
    PredecessorHalfFin13Atom0893 PredecessorHalfFin13Atom0918 PredecessorHalfFin13Atom0953 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25574 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0497 chi ∧
      PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0891 chi ∧
      PredecessorHalfFin13Atom0922 chi ∧
      PredecessorHalfFin13Atom0957 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 4, 5, 8, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 4, 5, 8, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0425 PredecessorHalfFin13Atom0426 PredecessorHalfFin13Atom0427
    PredecessorHalfFin13Atom0441 PredecessorHalfFin13Atom0442 PredecessorHalfFin13Atom0445
    PredecessorHalfFin13Atom0462 PredecessorHalfFin13Atom0463 PredecessorHalfFin13Atom0466
    PredecessorHalfFin13Atom0497 PredecessorHalfFin13Atom0887 PredecessorHalfFin13Atom0888
    PredecessorHalfFin13Atom0891 PredecessorHalfFin13Atom0922 PredecessorHalfFin13Atom0957 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25576 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0499 chi ∧
      PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0890 chi ∧
      PredecessorHalfFin13Atom0893 chi ∧
      PredecessorHalfFin13Atom0924 chi ∧
      PredecessorHalfFin13Atom0959 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 4, 5, 8, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 4, 5, 8, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0425 PredecessorHalfFin13Atom0426 PredecessorHalfFin13Atom0429
    PredecessorHalfFin13Atom0441 PredecessorHalfFin13Atom0444 PredecessorHalfFin13Atom0447
    PredecessorHalfFin13Atom0462 PredecessorHalfFin13Atom0465 PredecessorHalfFin13Atom0468
    PredecessorHalfFin13Atom0499 PredecessorHalfFin13Atom0887 PredecessorHalfFin13Atom0890
    PredecessorHalfFin13Atom0893 PredecessorHalfFin13Atom0924 PredecessorHalfFin13Atom0959 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25578 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0501 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0890 chi ∧
      PredecessorHalfFin13Atom0895 chi ∧
      PredecessorHalfFin13Atom0926 chi ∧
      PredecessorHalfFin13Atom0961 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 4, 5, 8, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 4, 5, 8, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0425 PredecessorHalfFin13Atom0427 PredecessorHalfFin13Atom0429
    PredecessorHalfFin13Atom0442 PredecessorHalfFin13Atom0444 PredecessorHalfFin13Atom0449
    PredecessorHalfFin13Atom0463 PredecessorHalfFin13Atom0465 PredecessorHalfFin13Atom0470
    PredecessorHalfFin13Atom0501 PredecessorHalfFin13Atom0888 PredecessorHalfFin13Atom0890
    PredecessorHalfFin13Atom0895 PredecessorHalfFin13Atom0926 PredecessorHalfFin13Atom0961 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25581 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0504 chi ∧
      PredecessorHalfFin13Atom0891 chi ∧
      PredecessorHalfFin13Atom0893 chi ∧
      PredecessorHalfFin13Atom0895 chi ∧
      PredecessorHalfFin13Atom0929 chi ∧
      PredecessorHalfFin13Atom0964 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 4, 5, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 4, 5, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0426 PredecessorHalfFin13Atom0427 PredecessorHalfFin13Atom0429
    PredecessorHalfFin13Atom0445 PredecessorHalfFin13Atom0447 PredecessorHalfFin13Atom0449
    PredecessorHalfFin13Atom0466 PredecessorHalfFin13Atom0468 PredecessorHalfFin13Atom0470
    PredecessorHalfFin13Atom0504 PredecessorHalfFin13Atom0891 PredecessorHalfFin13Atom0893
    PredecessorHalfFin13Atom0895 PredecessorHalfFin13Atom0929 PredecessorHalfFin13Atom0964 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25584 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0473 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0897 chi ∧
      PredecessorHalfFin13Atom0898 chi ∧
      PredecessorHalfFin13Atom0902 chi ∧
      PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0967 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 4, 6, 7, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 4, 6, 7, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0430 PredecessorHalfFin13Atom0431 PredecessorHalfFin13Atom0432
    PredecessorHalfFin13Atom0436 PredecessorHalfFin13Atom0437 PredecessorHalfFin13Atom0441
    PredecessorHalfFin13Atom0472 PredecessorHalfFin13Atom0473 PredecessorHalfFin13Atom0477
    PredecessorHalfFin13Atom0487 PredecessorHalfFin13Atom0897 PredecessorHalfFin13Atom0898
    PredecessorHalfFin13Atom0902 PredecessorHalfFin13Atom0912 PredecessorHalfFin13Atom0967 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25585 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0897 chi ∧
      PredecessorHalfFin13Atom0899 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0913 chi ∧
      PredecessorHalfFin13Atom0968 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 4, 6, 7, 8, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 4, 6, 7, 8, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0430 PredecessorHalfFin13Atom0431 PredecessorHalfFin13Atom0433
    PredecessorHalfFin13Atom0436 PredecessorHalfFin13Atom0438 PredecessorHalfFin13Atom0442
    PredecessorHalfFin13Atom0472 PredecessorHalfFin13Atom0474 PredecessorHalfFin13Atom0478
    PredecessorHalfFin13Atom0488 PredecessorHalfFin13Atom0897 PredecessorHalfFin13Atom0899
    PredecessorHalfFin13Atom0903 PredecessorHalfFin13Atom0913 PredecessorHalfFin13Atom0968 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25587 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0476 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0897 chi ∧
      PredecessorHalfFin13Atom0901 chi ∧
      PredecessorHalfFin13Atom0905 chi ∧
      PredecessorHalfFin13Atom0915 chi ∧
      PredecessorHalfFin13Atom0970 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 4, 6, 7, 8, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 4, 6, 7, 8, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0430 PredecessorHalfFin13Atom0431 PredecessorHalfFin13Atom0435
    PredecessorHalfFin13Atom0436 PredecessorHalfFin13Atom0440 PredecessorHalfFin13Atom0444
    PredecessorHalfFin13Atom0472 PredecessorHalfFin13Atom0476 PredecessorHalfFin13Atom0480
    PredecessorHalfFin13Atom0490 PredecessorHalfFin13Atom0897 PredecessorHalfFin13Atom0901
    PredecessorHalfFin13Atom0905 PredecessorHalfFin13Atom0915 PredecessorHalfFin13Atom0970 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25588 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0473 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0898 chi ∧
      PredecessorHalfFin13Atom0899 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0916 chi ∧
      PredecessorHalfFin13Atom0971 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 4, 6, 7, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 4, 6, 7, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0430 PredecessorHalfFin13Atom0432 PredecessorHalfFin13Atom0433
    PredecessorHalfFin13Atom0437 PredecessorHalfFin13Atom0438 PredecessorHalfFin13Atom0445
    PredecessorHalfFin13Atom0473 PredecessorHalfFin13Atom0474 PredecessorHalfFin13Atom0481
    PredecessorHalfFin13Atom0491 PredecessorHalfFin13Atom0898 PredecessorHalfFin13Atom0899
    PredecessorHalfFin13Atom0906 PredecessorHalfFin13Atom0916 PredecessorHalfFin13Atom0971 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25592 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0476 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0899 chi ∧
      PredecessorHalfFin13Atom0901 chi ∧
      PredecessorHalfFin13Atom0910 chi ∧
      PredecessorHalfFin13Atom0920 chi ∧
      PredecessorHalfFin13Atom0975 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 4, 6, 7, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 4, 6, 7, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0430 PredecessorHalfFin13Atom0433 PredecessorHalfFin13Atom0435
    PredecessorHalfFin13Atom0438 PredecessorHalfFin13Atom0440 PredecessorHalfFin13Atom0449
    PredecessorHalfFin13Atom0474 PredecessorHalfFin13Atom0476 PredecessorHalfFin13Atom0485
    PredecessorHalfFin13Atom0495 PredecessorHalfFin13Atom0899 PredecessorHalfFin13Atom0901
    PredecessorHalfFin13Atom0910 PredecessorHalfFin13Atom0920 PredecessorHalfFin13Atom0975 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25594 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0497 chi ∧
      PredecessorHalfFin13Atom0902 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0922 chi ∧
      PredecessorHalfFin13Atom0977 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 4, 6, 8, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 4, 6, 8, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0431 PredecessorHalfFin13Atom0432 PredecessorHalfFin13Atom0433
    PredecessorHalfFin13Atom0441 PredecessorHalfFin13Atom0442 PredecessorHalfFin13Atom0445
    PredecessorHalfFin13Atom0477 PredecessorHalfFin13Atom0478 PredecessorHalfFin13Atom0481
    PredecessorHalfFin13Atom0497 PredecessorHalfFin13Atom0902 PredecessorHalfFin13Atom0903
    PredecessorHalfFin13Atom0906 PredecessorHalfFin13Atom0922 PredecessorHalfFin13Atom0977 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25598 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0501 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0905 chi ∧
      PredecessorHalfFin13Atom0910 chi ∧
      PredecessorHalfFin13Atom0926 chi ∧
      PredecessorHalfFin13Atom0981 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 4, 6, 8, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 4, 6, 8, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0431 PredecessorHalfFin13Atom0433 PredecessorHalfFin13Atom0435
    PredecessorHalfFin13Atom0442 PredecessorHalfFin13Atom0444 PredecessorHalfFin13Atom0449
    PredecessorHalfFin13Atom0478 PredecessorHalfFin13Atom0480 PredecessorHalfFin13Atom0485
    PredecessorHalfFin13Atom0501 PredecessorHalfFin13Atom0903 PredecessorHalfFin13Atom0905
    PredecessorHalfFin13Atom0910 PredecessorHalfFin13Atom0926 PredecessorHalfFin13Atom0981 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25601 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0504 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0908 chi ∧
      PredecessorHalfFin13Atom0910 chi ∧
      PredecessorHalfFin13Atom0929 chi ∧
      PredecessorHalfFin13Atom0984 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 4, 6, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 4, 6, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0432 PredecessorHalfFin13Atom0433 PredecessorHalfFin13Atom0435
    PredecessorHalfFin13Atom0445 PredecessorHalfFin13Atom0447 PredecessorHalfFin13Atom0449
    PredecessorHalfFin13Atom0481 PredecessorHalfFin13Atom0483 PredecessorHalfFin13Atom0485
    PredecessorHalfFin13Atom0504 PredecessorHalfFin13Atom0906 PredecessorHalfFin13Atom0908
    PredecessorHalfFin13Atom0910 PredecessorHalfFin13Atom0929 PredecessorHalfFin13Atom0984 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25604 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0497 chi ∧
      PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0913 chi ∧
      PredecessorHalfFin13Atom0916 chi ∧
      PredecessorHalfFin13Atom0922 chi ∧
      PredecessorHalfFin13Atom0987 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 4, 7, 8, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 4, 7, 8, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0436 PredecessorHalfFin13Atom0437 PredecessorHalfFin13Atom0438
    PredecessorHalfFin13Atom0441 PredecessorHalfFin13Atom0442 PredecessorHalfFin13Atom0445
    PredecessorHalfFin13Atom0487 PredecessorHalfFin13Atom0488 PredecessorHalfFin13Atom0491
    PredecessorHalfFin13Atom0497 PredecessorHalfFin13Atom0912 PredecessorHalfFin13Atom0913
    PredecessorHalfFin13Atom0916 PredecessorHalfFin13Atom0922 PredecessorHalfFin13Atom0987 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25606 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0499 chi ∧
      PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0915 chi ∧
      PredecessorHalfFin13Atom0918 chi ∧
      PredecessorHalfFin13Atom0924 chi ∧
      PredecessorHalfFin13Atom0989 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 4, 7, 8, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 4, 7, 8, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0436 PredecessorHalfFin13Atom0437 PredecessorHalfFin13Atom0440
    PredecessorHalfFin13Atom0441 PredecessorHalfFin13Atom0444 PredecessorHalfFin13Atom0447
    PredecessorHalfFin13Atom0487 PredecessorHalfFin13Atom0490 PredecessorHalfFin13Atom0493
    PredecessorHalfFin13Atom0499 PredecessorHalfFin13Atom0912 PredecessorHalfFin13Atom0915
    PredecessorHalfFin13Atom0918 PredecessorHalfFin13Atom0924 PredecessorHalfFin13Atom0989 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25608 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0501 chi ∧
      PredecessorHalfFin13Atom0913 chi ∧
      PredecessorHalfFin13Atom0915 chi ∧
      PredecessorHalfFin13Atom0920 chi ∧
      PredecessorHalfFin13Atom0926 chi ∧
      PredecessorHalfFin13Atom0991 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 4, 7, 8, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 4, 7, 8, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0436 PredecessorHalfFin13Atom0438 PredecessorHalfFin13Atom0440
    PredecessorHalfFin13Atom0442 PredecessorHalfFin13Atom0444 PredecessorHalfFin13Atom0449
    PredecessorHalfFin13Atom0488 PredecessorHalfFin13Atom0490 PredecessorHalfFin13Atom0495
    PredecessorHalfFin13Atom0501 PredecessorHalfFin13Atom0913 PredecessorHalfFin13Atom0915
    PredecessorHalfFin13Atom0920 PredecessorHalfFin13Atom0926 PredecessorHalfFin13Atom0991 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25611 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0504 chi ∧
      PredecessorHalfFin13Atom0916 chi ∧
      PredecessorHalfFin13Atom0918 chi ∧
      PredecessorHalfFin13Atom0920 chi ∧
      PredecessorHalfFin13Atom0929 chi ∧
      PredecessorHalfFin13Atom0994 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 4, 7, 9, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 4, 7, 9, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0437 PredecessorHalfFin13Atom0438 PredecessorHalfFin13Atom0440
    PredecessorHalfFin13Atom0445 PredecessorHalfFin13Atom0447 PredecessorHalfFin13Atom0449
    PredecessorHalfFin13Atom0491 PredecessorHalfFin13Atom0493 PredecessorHalfFin13Atom0495
    PredecessorHalfFin13Atom0504 PredecessorHalfFin13Atom0916 PredecessorHalfFin13Atom0918
    PredecessorHalfFin13Atom0920 PredecessorHalfFin13Atom0929 PredecessorHalfFin13Atom0994 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25627 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0451 chi ∧
      PredecessorHalfFin13Atom0454 chi ∧
      PredecessorHalfFin13Atom0456 chi ∧
      PredecessorHalfFin13Atom0459 chi ∧
      PredecessorHalfFin13Atom0461 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0476 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0934 chi ∧
      PredecessorHalfFin13Atom0936 chi ∧
      PredecessorHalfFin13Atom0945 chi ∧
      PredecessorHalfFin13Atom0955 chi ∧
      PredecessorHalfFin13Atom0975 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 5, 6, 7, 10, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 5, 6, 7, 10, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0451 PredecessorHalfFin13Atom0454 PredecessorHalfFin13Atom0456
    PredecessorHalfFin13Atom0459 PredecessorHalfFin13Atom0461 PredecessorHalfFin13Atom0470
    PredecessorHalfFin13Atom0474 PredecessorHalfFin13Atom0476 PredecessorHalfFin13Atom0485
    PredecessorHalfFin13Atom0495 PredecessorHalfFin13Atom0934 PredecessorHalfFin13Atom0936
    PredecessorHalfFin13Atom0945 PredecessorHalfFin13Atom0955 PredecessorHalfFin13Atom0975 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25629 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0454 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0497 chi ∧
      PredecessorHalfFin13Atom0937 chi ∧
      PredecessorHalfFin13Atom0938 chi ∧
      PredecessorHalfFin13Atom0941 chi ∧
      PredecessorHalfFin13Atom0957 chi ∧
      PredecessorHalfFin13Atom0977 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 5, 6, 8, 9, 10} := by
    intro hstrong
    exact hnoStrong ⟨{0, 5, 6, 8, 9, 10}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0452 PredecessorHalfFin13Atom0453 PredecessorHalfFin13Atom0454
    PredecessorHalfFin13Atom0462 PredecessorHalfFin13Atom0463 PredecessorHalfFin13Atom0466
    PredecessorHalfFin13Atom0477 PredecessorHalfFin13Atom0478 PredecessorHalfFin13Atom0481
    PredecessorHalfFin13Atom0497 PredecessorHalfFin13Atom0937 PredecessorHalfFin13Atom0938
    PredecessorHalfFin13Atom0941 PredecessorHalfFin13Atom0957 PredecessorHalfFin13Atom0977 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause25631 (chi : TripleColoring 13)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0456 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0499 chi ∧
      PredecessorHalfFin13Atom0937 chi ∧
      PredecessorHalfFin13Atom0940 chi ∧
      PredecessorHalfFin13Atom0943 chi ∧
      PredecessorHalfFin13Atom0959 chi ∧
      PredecessorHalfFin13Atom0979 chi) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet chi {0, 5, 6, 8, 9, 12} := by
    intro hstrong
    exact hnoStrong ⟨{0, 5, 6, 8, 9, 12}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold PredecessorHalfFin13Atom0452 PredecessorHalfFin13Atom0453 PredecessorHalfFin13Atom0456
    PredecessorHalfFin13Atom0462 PredecessorHalfFin13Atom0465 PredecessorHalfFin13Atom0468
    PredecessorHalfFin13Atom0477 PredecessorHalfFin13Atom0480 PredecessorHalfFin13Atom0483
    PredecessorHalfFin13Atom0499 PredecessorHalfFin13Atom0937 PredecessorHalfFin13Atom0940
    PredecessorHalfFin13Atom0943 PredecessorHalfFin13Atom0959 PredecessorHalfFin13Atom0979 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [PredecessorHalfFin13StrongQuad]

end ErdosSzekeres

end
