module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 064. -/

theorem predecessorHalfFin13_clause18673 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1254 chi ∧
      ¬PredecessorHalfFin13Atom0366 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0366 PredecessorHalfFin13Atom1254 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1221
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18674 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1254 chi ∧
      ¬PredecessorHalfFin13Atom0369 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0369 PredecessorHalfFin13Atom1254 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1221
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18675 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1254 chi ∧
      ¬PredecessorHalfFin13Atom0374 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0374 PredecessorHalfFin13Atom1254 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1221
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18676 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1254 chi ∧
      ¬PredecessorHalfFin13Atom0474 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0474 PredecessorHalfFin13Atom1254 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1221
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18677 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1254 chi ∧
      ¬PredecessorHalfFin13Atom0759 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0759 PredecessorHalfFin13Atom1254 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1221
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18678 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1254 chi ∧
      PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0759 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0366 PredecessorHalfFin13Atom0369 PredecessorHalfFin13Atom0374
    PredecessorHalfFin13Atom0474 PredecessorHalfFin13Atom0759 PredecessorHalfFin13Atom1254 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1221
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18685 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1256 chi ∧
      ¬PredecessorHalfFin13Atom0366 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0366 PredecessorHalfFin13Atom1256 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4293
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18686 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1256 chi ∧
      ¬PredecessorHalfFin13Atom0371 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0371 PredecessorHalfFin13Atom1256 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4293
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18687 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1256 chi ∧
      ¬PredecessorHalfFin13Atom0376 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0376 PredecessorHalfFin13Atom1256 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4293
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18688 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1256 chi ∧
      ¬PredecessorHalfFin13Atom0476 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0476 PredecessorHalfFin13Atom1256 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4293
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18689 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1256 chi ∧
      ¬PredecessorHalfFin13Atom0761 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0761 PredecessorHalfFin13Atom1256 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4293
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18690 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1256 chi ∧
      PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0476 chi ∧
      PredecessorHalfFin13Atom0761 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0366 PredecessorHalfFin13Atom0371 PredecessorHalfFin13Atom0376
    PredecessorHalfFin13Atom0476 PredecessorHalfFin13Atom0761 PredecessorHalfFin13Atom1256 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4293
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18691 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1257 chi ∧
      ¬PredecessorHalfFin13Atom0367 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0367 PredecessorHalfFin13Atom1257 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0837
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18692 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1257 chi ∧
      ¬PredecessorHalfFin13Atom0368 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0368 PredecessorHalfFin13Atom1257 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0837
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18693 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1257 chi ∧
      ¬PredecessorHalfFin13Atom0377 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0377 PredecessorHalfFin13Atom1257 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0837
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18694 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1257 chi ∧
      ¬PredecessorHalfFin13Atom0477 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0477 PredecessorHalfFin13Atom1257 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0837
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18695 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1257 chi ∧
      ¬PredecessorHalfFin13Atom0762 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0762 PredecessorHalfFin13Atom1257 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0837
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18696 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1257 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0762 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0367 PredecessorHalfFin13Atom0368 PredecessorHalfFin13Atom0377
    PredecessorHalfFin13Atom0477 PredecessorHalfFin13Atom0762 PredecessorHalfFin13Atom1257 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0837
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18697 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1258 chi ∧
      ¬PredecessorHalfFin13Atom0367 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0367 PredecessorHalfFin13Atom1258 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1349
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18698 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1258 chi ∧
      ¬PredecessorHalfFin13Atom0369 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0369 PredecessorHalfFin13Atom1258 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1349
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18699 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1258 chi ∧
      ¬PredecessorHalfFin13Atom0378 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0378 PredecessorHalfFin13Atom1258 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1349
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18700 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1258 chi ∧
      ¬PredecessorHalfFin13Atom0478 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0478 PredecessorHalfFin13Atom1258 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1349
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18701 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1258 chi ∧
      ¬PredecessorHalfFin13Atom0763 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0763 PredecessorHalfFin13Atom1258 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1349
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18702 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1258 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0763 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0367 PredecessorHalfFin13Atom0369 PredecessorHalfFin13Atom0378
    PredecessorHalfFin13Atom0478 PredecessorHalfFin13Atom0763 PredecessorHalfFin13Atom1258 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1349
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18709 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1260 chi ∧
      ¬PredecessorHalfFin13Atom0367 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0367 PredecessorHalfFin13Atom1260 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4421
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18710 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1260 chi ∧
      ¬PredecessorHalfFin13Atom0371 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0371 PredecessorHalfFin13Atom1260 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4421
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18711 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1260 chi ∧
      ¬PredecessorHalfFin13Atom0380 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0380 PredecessorHalfFin13Atom1260 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4421
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18712 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1260 chi ∧
      ¬PredecessorHalfFin13Atom0480 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0480 PredecessorHalfFin13Atom1260 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4421
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18713 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1260 chi ∧
      ¬PredecessorHalfFin13Atom0765 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0765 PredecessorHalfFin13Atom1260 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4421
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18714 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1260 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0765 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0367 PredecessorHalfFin13Atom0371 PredecessorHalfFin13Atom0380
    PredecessorHalfFin13Atom0480 PredecessorHalfFin13Atom0765 PredecessorHalfFin13Atom1260 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4421
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18715 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1261 chi ∧
      ¬PredecessorHalfFin13Atom0368 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0368 PredecessorHalfFin13Atom1261 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1605
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18716 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1261 chi ∧
      ¬PredecessorHalfFin13Atom0369 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0369 PredecessorHalfFin13Atom1261 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1605
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18717 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1261 chi ∧
      ¬PredecessorHalfFin13Atom0381 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0381 PredecessorHalfFin13Atom1261 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1605
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18718 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1261 chi ∧
      ¬PredecessorHalfFin13Atom0481 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0481 PredecessorHalfFin13Atom1261 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1605
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18719 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1261 chi ∧
      ¬PredecessorHalfFin13Atom0766 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0766 PredecessorHalfFin13Atom1261 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1605
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18720 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1261 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0766 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0368 PredecessorHalfFin13Atom0369 PredecessorHalfFin13Atom0381
    PredecessorHalfFin13Atom0481 PredecessorHalfFin13Atom0766 PredecessorHalfFin13Atom1261 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1605
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18727 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1263 chi ∧
      ¬PredecessorHalfFin13Atom0368 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0368 PredecessorHalfFin13Atom1263 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4677
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18728 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1263 chi ∧
      ¬PredecessorHalfFin13Atom0371 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0371 PredecessorHalfFin13Atom1263 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4677
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18729 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1263 chi ∧
      ¬PredecessorHalfFin13Atom0383 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0383 PredecessorHalfFin13Atom1263 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4677
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18730 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1263 chi ∧
      ¬PredecessorHalfFin13Atom0483 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0483 PredecessorHalfFin13Atom1263 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4677
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18731 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1263 chi ∧
      ¬PredecessorHalfFin13Atom0768 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0768 PredecessorHalfFin13Atom1263 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4677
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18732 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1263 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0768 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0368 PredecessorHalfFin13Atom0371 PredecessorHalfFin13Atom0383
    PredecessorHalfFin13Atom0483 PredecessorHalfFin13Atom0768 PredecessorHalfFin13Atom1263 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4677
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18739 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1265 chi ∧
      ¬PredecessorHalfFin13Atom0369 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0369 PredecessorHalfFin13Atom1265 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5189
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18740 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1265 chi ∧
      ¬PredecessorHalfFin13Atom0371 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0371 PredecessorHalfFin13Atom1265 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5189
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18741 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1265 chi ∧
      ¬PredecessorHalfFin13Atom0385 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0385 PredecessorHalfFin13Atom1265 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5189
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18742 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1265 chi ∧
      ¬PredecessorHalfFin13Atom0485 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0485 PredecessorHalfFin13Atom1265 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5189
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18743 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1265 chi ∧
      ¬PredecessorHalfFin13Atom0770 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0770 PredecessorHalfFin13Atom1265 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5189
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18744 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1265 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0770 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0369 PredecessorHalfFin13Atom0371 PredecessorHalfFin13Atom0385
    PredecessorHalfFin13Atom0485 PredecessorHalfFin13Atom0770 PredecessorHalfFin13Atom1265 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5189
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18751 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1267 chi ∧
      ¬PredecessorHalfFin13Atom0372 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0372 PredecessorHalfFin13Atom1267 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0901
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18752 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1267 chi ∧
      ¬PredecessorHalfFin13Atom0373 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0373 PredecessorHalfFin13Atom1267 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0901
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18753 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1267 chi ∧
      ¬PredecessorHalfFin13Atom0377 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0377 PredecessorHalfFin13Atom1267 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0901
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18754 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1267 chi ∧
      ¬PredecessorHalfFin13Atom0487 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0487 PredecessorHalfFin13Atom1267 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0901
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18755 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1267 chi ∧
      ¬PredecessorHalfFin13Atom0772 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0772 PredecessorHalfFin13Atom1267 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0901
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18756 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1267 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0772 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0372 PredecessorHalfFin13Atom0373 PredecessorHalfFin13Atom0377
    PredecessorHalfFin13Atom0487 PredecessorHalfFin13Atom0772 PredecessorHalfFin13Atom1267 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0901
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18757 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1268 chi ∧
      ¬PredecessorHalfFin13Atom0372 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0372 PredecessorHalfFin13Atom1268 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1413
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18758 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1268 chi ∧
      ¬PredecessorHalfFin13Atom0374 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0374 PredecessorHalfFin13Atom1268 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1413
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18759 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1268 chi ∧
      ¬PredecessorHalfFin13Atom0378 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0378 PredecessorHalfFin13Atom1268 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1413
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18760 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1268 chi ∧
      ¬PredecessorHalfFin13Atom0488 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0488 PredecessorHalfFin13Atom1268 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1413
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18761 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1268 chi ∧
      ¬PredecessorHalfFin13Atom0773 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0773 PredecessorHalfFin13Atom1268 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1413
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18762 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1268 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0773 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0372 PredecessorHalfFin13Atom0374 PredecessorHalfFin13Atom0378
    PredecessorHalfFin13Atom0488 PredecessorHalfFin13Atom0773 PredecessorHalfFin13Atom1268 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1413
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18769 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1270 chi ∧
      ¬PredecessorHalfFin13Atom0372 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0372 PredecessorHalfFin13Atom1270 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4485
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18770 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1270 chi ∧
      ¬PredecessorHalfFin13Atom0376 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0376 PredecessorHalfFin13Atom1270 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4485
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18771 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1270 chi ∧
      ¬PredecessorHalfFin13Atom0380 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0380 PredecessorHalfFin13Atom1270 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4485
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18772 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1270 chi ∧
      ¬PredecessorHalfFin13Atom0490 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0490 PredecessorHalfFin13Atom1270 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4485
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18773 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1270 chi ∧
      ¬PredecessorHalfFin13Atom0775 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0775 PredecessorHalfFin13Atom1270 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4485
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18774 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1270 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0775 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0372 PredecessorHalfFin13Atom0376 PredecessorHalfFin13Atom0380
    PredecessorHalfFin13Atom0490 PredecessorHalfFin13Atom0775 PredecessorHalfFin13Atom1270 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4485
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18775 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1271 chi ∧
      ¬PredecessorHalfFin13Atom0373 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0373 PredecessorHalfFin13Atom1271 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1669
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18776 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1271 chi ∧
      ¬PredecessorHalfFin13Atom0374 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0374 PredecessorHalfFin13Atom1271 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1669
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18777 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1271 chi ∧
      ¬PredecessorHalfFin13Atom0381 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0381 PredecessorHalfFin13Atom1271 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1669
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18778 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1271 chi ∧
      ¬PredecessorHalfFin13Atom0491 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0491 PredecessorHalfFin13Atom1271 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1669
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18779 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1271 chi ∧
      ¬PredecessorHalfFin13Atom0776 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0776 PredecessorHalfFin13Atom1271 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1669
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18780 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1271 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0776 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0373 PredecessorHalfFin13Atom0374 PredecessorHalfFin13Atom0381
    PredecessorHalfFin13Atom0491 PredecessorHalfFin13Atom0776 PredecessorHalfFin13Atom1271 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1669
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18787 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1273 chi ∧
      ¬PredecessorHalfFin13Atom0373 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0373 PredecessorHalfFin13Atom1273 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4741
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18788 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1273 chi ∧
      ¬PredecessorHalfFin13Atom0376 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0376 PredecessorHalfFin13Atom1273 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4741
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18789 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1273 chi ∧
      ¬PredecessorHalfFin13Atom0383 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0383 PredecessorHalfFin13Atom1273 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4741
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18790 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1273 chi ∧
      ¬PredecessorHalfFin13Atom0493 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0493 PredecessorHalfFin13Atom1273 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4741
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18791 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1273 chi ∧
      ¬PredecessorHalfFin13Atom0778 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0778 PredecessorHalfFin13Atom1273 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4741
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18792 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1273 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0778 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0373 PredecessorHalfFin13Atom0376 PredecessorHalfFin13Atom0383
    PredecessorHalfFin13Atom0493 PredecessorHalfFin13Atom0778 PredecessorHalfFin13Atom1273 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4741
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18799 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1275 chi ∧
      ¬PredecessorHalfFin13Atom0374 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0374 PredecessorHalfFin13Atom1275 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5253
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18800 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1275 chi ∧
      ¬PredecessorHalfFin13Atom0376 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0376 PredecessorHalfFin13Atom1275 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5253
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18801 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1275 chi ∧
      ¬PredecessorHalfFin13Atom0385 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0385 PredecessorHalfFin13Atom1275 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5253
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18802 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1275 chi ∧
      ¬PredecessorHalfFin13Atom0495 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0495 PredecessorHalfFin13Atom1275 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5253
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18803 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1275 chi ∧
      ¬PredecessorHalfFin13Atom0780 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0780 PredecessorHalfFin13Atom1275 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5253
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18804 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1275 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0780 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0374 PredecessorHalfFin13Atom0376 PredecessorHalfFin13Atom0385
    PredecessorHalfFin13Atom0495 PredecessorHalfFin13Atom0780 PredecessorHalfFin13Atom1275 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5253
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18811 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1277 chi ∧
      ¬PredecessorHalfFin13Atom0377 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0377 PredecessorHalfFin13Atom1277 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1797
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18812 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1277 chi ∧
      ¬PredecessorHalfFin13Atom0378 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0378 PredecessorHalfFin13Atom1277 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1797
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18813 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1277 chi ∧
      ¬PredecessorHalfFin13Atom0381 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0381 PredecessorHalfFin13Atom1277 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1797
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18814 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1277 chi ∧
      ¬PredecessorHalfFin13Atom0497 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0497 PredecessorHalfFin13Atom1277 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1797
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18815 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1277 chi ∧
      ¬PredecessorHalfFin13Atom0782 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0782 PredecessorHalfFin13Atom1277 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1797
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18816 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1277 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0497 chi ∧
      PredecessorHalfFin13Atom0782 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0377 PredecessorHalfFin13Atom0378 PredecessorHalfFin13Atom0381
    PredecessorHalfFin13Atom0497 PredecessorHalfFin13Atom0782 PredecessorHalfFin13Atom1277 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1797
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18823 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1279 chi ∧
      ¬PredecessorHalfFin13Atom0377 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0377 PredecessorHalfFin13Atom1279 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4869
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18824 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1279 chi ∧
      ¬PredecessorHalfFin13Atom0380 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0380 PredecessorHalfFin13Atom1279 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4869
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18825 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1279 chi ∧
      ¬PredecessorHalfFin13Atom0383 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0383 PredecessorHalfFin13Atom1279 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4869
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18826 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1279 chi ∧
      ¬PredecessorHalfFin13Atom0499 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0499 PredecessorHalfFin13Atom1279 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4869
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18827 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1279 chi ∧
      ¬PredecessorHalfFin13Atom0784 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0784 PredecessorHalfFin13Atom1279 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4869
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18828 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1279 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0499 chi ∧
      PredecessorHalfFin13Atom0784 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0377 PredecessorHalfFin13Atom0380 PredecessorHalfFin13Atom0383
    PredecessorHalfFin13Atom0499 PredecessorHalfFin13Atom0784 PredecessorHalfFin13Atom1279 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4869
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18835 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1281 chi ∧
      ¬PredecessorHalfFin13Atom0378 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0378 PredecessorHalfFin13Atom1281 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5381
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18836 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1281 chi ∧
      ¬PredecessorHalfFin13Atom0380 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0380 PredecessorHalfFin13Atom1281 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5381
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18837 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1281 chi ∧
      ¬PredecessorHalfFin13Atom0385 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0385 PredecessorHalfFin13Atom1281 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5381
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18838 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1281 chi ∧
      ¬PredecessorHalfFin13Atom0501 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0501 PredecessorHalfFin13Atom1281 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5381
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18839 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1281 chi ∧
      ¬PredecessorHalfFin13Atom0786 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0786 PredecessorHalfFin13Atom1281 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5381
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18853 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1284 chi ∧
      ¬PredecessorHalfFin13Atom0381 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0381 PredecessorHalfFin13Atom1284 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5637
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18854 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1284 chi ∧
      ¬PredecessorHalfFin13Atom0383 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0383 PredecessorHalfFin13Atom1284 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5637
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18855 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1284 chi ∧
      ¬PredecessorHalfFin13Atom0385 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0385 PredecessorHalfFin13Atom1284 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5637
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18856 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1284 chi ∧
      ¬PredecessorHalfFin13Atom0504 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0504 PredecessorHalfFin13Atom1284 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5637
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18857 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1284 chi ∧
      ¬PredecessorHalfFin13Atom0789 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0789 PredecessorHalfFin13Atom1284 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5637
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18858 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1284 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0504 chi ∧
      PredecessorHalfFin13Atom0789 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0381 PredecessorHalfFin13Atom0383 PredecessorHalfFin13Atom0385
    PredecessorHalfFin13Atom0504 PredecessorHalfFin13Atom0789 PredecessorHalfFin13Atom1284 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5637
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18871 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1287 chi ∧
      ¬PredecessorHalfFin13Atom0387 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0387 PredecessorHalfFin13Atom1287 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0121
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18872 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1287 chi ∧
      ¬PredecessorHalfFin13Atom0388 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0388 PredecessorHalfFin13Atom1287 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0121
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18873 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1287 chi ∧
      ¬PredecessorHalfFin13Atom0395 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0395 PredecessorHalfFin13Atom1287 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0121
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18874 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1287 chi ∧
      ¬PredecessorHalfFin13Atom0423 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0423 PredecessorHalfFin13Atom1287 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0121
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18875 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1287 chi ∧
      ¬PredecessorHalfFin13Atom0792 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0792 PredecessorHalfFin13Atom1287 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0121
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18877 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1288 chi ∧
      ¬PredecessorHalfFin13Atom0387 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0387 PredecessorHalfFin13Atom1288 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0185
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18878 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1288 chi ∧
      ¬PredecessorHalfFin13Atom0389 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0389 PredecessorHalfFin13Atom1288 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0185
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18879 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1288 chi ∧
      ¬PredecessorHalfFin13Atom0396 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0396 PredecessorHalfFin13Atom1288 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0185
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18880 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1288 chi ∧
      ¬PredecessorHalfFin13Atom0424 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0424 PredecessorHalfFin13Atom1288 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0185
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18881 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1288 chi ∧
      ¬PredecessorHalfFin13Atom0793 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0793 PredecessorHalfFin13Atom1288 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0185
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18882 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1288 chi ∧
      PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0793 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0387 PredecessorHalfFin13Atom0389 PredecessorHalfFin13Atom0396
    PredecessorHalfFin13Atom0424 PredecessorHalfFin13Atom0793 PredecessorHalfFin13Atom1288 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0185
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18883 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1289 chi ∧
      ¬PredecessorHalfFin13Atom0387 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0387 PredecessorHalfFin13Atom1289 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0313
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18884 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1289 chi ∧
      ¬PredecessorHalfFin13Atom0390 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0390 PredecessorHalfFin13Atom1289 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0313
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18885 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1289 chi ∧
      ¬PredecessorHalfFin13Atom0397 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0397 PredecessorHalfFin13Atom1289 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0313
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18886 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1289 chi ∧
      ¬PredecessorHalfFin13Atom0425 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0425 PredecessorHalfFin13Atom1289 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0313
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18887 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1289 chi ∧
      ¬PredecessorHalfFin13Atom0794 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0794 PredecessorHalfFin13Atom1289 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0313
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18888 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1289 chi ∧
      PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0794 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0387 PredecessorHalfFin13Atom0390 PredecessorHalfFin13Atom0397
    PredecessorHalfFin13Atom0425 PredecessorHalfFin13Atom0794 PredecessorHalfFin13Atom1289 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0313
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18889 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1290 chi ∧
      ¬PredecessorHalfFin13Atom0387 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0387 PredecessorHalfFin13Atom1290 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0569
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18890 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1290 chi ∧
      ¬PredecessorHalfFin13Atom0391 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0391 PredecessorHalfFin13Atom1290 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0569
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18891 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1290 chi ∧
      ¬PredecessorHalfFin13Atom0398 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0398 PredecessorHalfFin13Atom1290 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0569
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18892 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1290 chi ∧
      ¬PredecessorHalfFin13Atom0426 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0426 PredecessorHalfFin13Atom1290 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0569
  ] at hbad
  tauto

end ErdosSzekeres

end
