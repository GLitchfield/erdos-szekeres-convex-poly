module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 063. -/

theorem predecessorHalfFin13_clause18479 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1221 chi ∧
      ¬PredecessorHalfFin13Atom0726 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0726 PredecessorHalfFin13Atom1221 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0789
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18480 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1221 chi ∧
      PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0726 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0354 PredecessorHalfFin13Atom0355 PredecessorHalfFin13Atom0377
    PredecessorHalfFin13Atom0441 PredecessorHalfFin13Atom0726 PredecessorHalfFin13Atom1221 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0789
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18481 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1222 chi ∧
      ¬PredecessorHalfFin13Atom0354 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0354 PredecessorHalfFin13Atom1222 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1301
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18482 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1222 chi ∧
      ¬PredecessorHalfFin13Atom0356 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0356 PredecessorHalfFin13Atom1222 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1301
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18483 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1222 chi ∧
      ¬PredecessorHalfFin13Atom0378 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0378 PredecessorHalfFin13Atom1222 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1301
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18484 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1222 chi ∧
      ¬PredecessorHalfFin13Atom0442 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0442 PredecessorHalfFin13Atom1222 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1301
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18485 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1222 chi ∧
      ¬PredecessorHalfFin13Atom0727 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0727 PredecessorHalfFin13Atom1222 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1301
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18486 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1222 chi ∧
      PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0727 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0354 PredecessorHalfFin13Atom0356 PredecessorHalfFin13Atom0378
    PredecessorHalfFin13Atom0442 PredecessorHalfFin13Atom0727 PredecessorHalfFin13Atom1222 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1301
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18493 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1224 chi ∧
      ¬PredecessorHalfFin13Atom0354 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0354 PredecessorHalfFin13Atom1224 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4373
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18494 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1224 chi ∧
      ¬PredecessorHalfFin13Atom0358 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0358 PredecessorHalfFin13Atom1224 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4373
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18495 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1224 chi ∧
      ¬PredecessorHalfFin13Atom0380 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0380 PredecessorHalfFin13Atom1224 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4373
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18496 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1224 chi ∧
      ¬PredecessorHalfFin13Atom0444 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0444 PredecessorHalfFin13Atom1224 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4373
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18497 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1224 chi ∧
      ¬PredecessorHalfFin13Atom0729 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0729 PredecessorHalfFin13Atom1224 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4373
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18498 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1224 chi ∧
      PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0729 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0354 PredecessorHalfFin13Atom0358 PredecessorHalfFin13Atom0380
    PredecessorHalfFin13Atom0444 PredecessorHalfFin13Atom0729 PredecessorHalfFin13Atom1224 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4373
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18499 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1225 chi ∧
      ¬PredecessorHalfFin13Atom0355 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0355 PredecessorHalfFin13Atom1225 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1557
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18500 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1225 chi ∧
      ¬PredecessorHalfFin13Atom0356 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0356 PredecessorHalfFin13Atom1225 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1557
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18501 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1225 chi ∧
      ¬PredecessorHalfFin13Atom0381 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0381 PredecessorHalfFin13Atom1225 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1557
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18502 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1225 chi ∧
      ¬PredecessorHalfFin13Atom0445 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0445 PredecessorHalfFin13Atom1225 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1557
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18503 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1225 chi ∧
      ¬PredecessorHalfFin13Atom0730 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0730 PredecessorHalfFin13Atom1225 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1557
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18504 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1225 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0730 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0355 PredecessorHalfFin13Atom0356 PredecessorHalfFin13Atom0381
    PredecessorHalfFin13Atom0445 PredecessorHalfFin13Atom0730 PredecessorHalfFin13Atom1225 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1557
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18511 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1227 chi ∧
      ¬PredecessorHalfFin13Atom0355 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0355 PredecessorHalfFin13Atom1227 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4629
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18512 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1227 chi ∧
      ¬PredecessorHalfFin13Atom0358 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0358 PredecessorHalfFin13Atom1227 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4629
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18513 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1227 chi ∧
      ¬PredecessorHalfFin13Atom0383 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0383 PredecessorHalfFin13Atom1227 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4629
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18514 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1227 chi ∧
      ¬PredecessorHalfFin13Atom0447 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0447 PredecessorHalfFin13Atom1227 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4629
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18515 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1227 chi ∧
      ¬PredecessorHalfFin13Atom0732 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0732 PredecessorHalfFin13Atom1227 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4629
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18516 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1227 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0732 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0355 PredecessorHalfFin13Atom0358 PredecessorHalfFin13Atom0383
    PredecessorHalfFin13Atom0447 PredecessorHalfFin13Atom0732 PredecessorHalfFin13Atom1227 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4629
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18523 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1229 chi ∧
      ¬PredecessorHalfFin13Atom0356 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0356 PredecessorHalfFin13Atom1229 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5141
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18524 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1229 chi ∧
      ¬PredecessorHalfFin13Atom0358 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0358 PredecessorHalfFin13Atom1229 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5141
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18525 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1229 chi ∧
      ¬PredecessorHalfFin13Atom0385 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0385 PredecessorHalfFin13Atom1229 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5141
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18526 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1229 chi ∧
      ¬PredecessorHalfFin13Atom0449 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0449 PredecessorHalfFin13Atom1229 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5141
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18527 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1229 chi ∧
      ¬PredecessorHalfFin13Atom0734 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0734 PredecessorHalfFin13Atom1229 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5141
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18528 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1229 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0734 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0356 PredecessorHalfFin13Atom0358 PredecessorHalfFin13Atom0385
    PredecessorHalfFin13Atom0449 PredecessorHalfFin13Atom0734 PredecessorHalfFin13Atom1229 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5141
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18535 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1231 chi ∧
      ¬PredecessorHalfFin13Atom0359 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0359 PredecessorHalfFin13Atom1231 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0229
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18536 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1231 chi ∧
      ¬PredecessorHalfFin13Atom0360 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0360 PredecessorHalfFin13Atom1231 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0229
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18537 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1231 chi ∧
      ¬PredecessorHalfFin13Atom0366 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0366 PredecessorHalfFin13Atom1231 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0229
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18538 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1231 chi ∧
      ¬PredecessorHalfFin13Atom0451 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0451 PredecessorHalfFin13Atom1231 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0229
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18539 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1231 chi ∧
      ¬PredecessorHalfFin13Atom0736 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0736 PredecessorHalfFin13Atom1231 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0229
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18540 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1231 chi ∧
      PredecessorHalfFin13Atom0359 chi ∧
      PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0451 chi ∧
      PredecessorHalfFin13Atom0736 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0359 PredecessorHalfFin13Atom0360 PredecessorHalfFin13Atom0366
    PredecessorHalfFin13Atom0451 PredecessorHalfFin13Atom0736 PredecessorHalfFin13Atom1231 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0229
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18541 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1232 chi ∧
      ¬PredecessorHalfFin13Atom0359 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0359 PredecessorHalfFin13Atom1232 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0357
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18542 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1232 chi ∧
      ¬PredecessorHalfFin13Atom0361 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0361 PredecessorHalfFin13Atom1232 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0357
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18543 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1232 chi ∧
      ¬PredecessorHalfFin13Atom0367 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0367 PredecessorHalfFin13Atom1232 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0357
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18544 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1232 chi ∧
      ¬PredecessorHalfFin13Atom0452 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0452 PredecessorHalfFin13Atom1232 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0357
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18545 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1232 chi ∧
      ¬PredecessorHalfFin13Atom0737 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0737 PredecessorHalfFin13Atom1232 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0357
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18546 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1232 chi ∧
      PredecessorHalfFin13Atom0359 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0737 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0359 PredecessorHalfFin13Atom0361 PredecessorHalfFin13Atom0367
    PredecessorHalfFin13Atom0452 PredecessorHalfFin13Atom0737 PredecessorHalfFin13Atom1232 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0357
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18547 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1233 chi ∧
      ¬PredecessorHalfFin13Atom0359 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0359 PredecessorHalfFin13Atom1233 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0613
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18548 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1233 chi ∧
      ¬PredecessorHalfFin13Atom0362 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0362 PredecessorHalfFin13Atom1233 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0613
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18549 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1233 chi ∧
      ¬PredecessorHalfFin13Atom0368 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0368 PredecessorHalfFin13Atom1233 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0613
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18550 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1233 chi ∧
      ¬PredecessorHalfFin13Atom0453 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0453 PredecessorHalfFin13Atom1233 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0613
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18551 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1233 chi ∧
      ¬PredecessorHalfFin13Atom0738 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0738 PredecessorHalfFin13Atom1233 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0613
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18553 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1234 chi ∧
      ¬PredecessorHalfFin13Atom0359 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0359 PredecessorHalfFin13Atom1234 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1125
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18554 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1234 chi ∧
      ¬PredecessorHalfFin13Atom0363 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0363 PredecessorHalfFin13Atom1234 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1125
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18555 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1234 chi ∧
      ¬PredecessorHalfFin13Atom0369 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0369 PredecessorHalfFin13Atom1234 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1125
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18556 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1234 chi ∧
      ¬PredecessorHalfFin13Atom0454 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0454 PredecessorHalfFin13Atom1234 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1125
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18557 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1234 chi ∧
      ¬PredecessorHalfFin13Atom0739 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0739 PredecessorHalfFin13Atom1234 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1125
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18565 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1236 chi ∧
      ¬PredecessorHalfFin13Atom0359 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0359 PredecessorHalfFin13Atom1236 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4197
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18566 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1236 chi ∧
      ¬PredecessorHalfFin13Atom0365 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0365 PredecessorHalfFin13Atom1236 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4197
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18567 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1236 chi ∧
      ¬PredecessorHalfFin13Atom0371 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0371 PredecessorHalfFin13Atom1236 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4197
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18568 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1236 chi ∧
      ¬PredecessorHalfFin13Atom0456 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0456 PredecessorHalfFin13Atom1236 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4197
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18569 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1236 chi ∧
      ¬PredecessorHalfFin13Atom0741 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0741 PredecessorHalfFin13Atom1236 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4197
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18571 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1237 chi ∧
      ¬PredecessorHalfFin13Atom0360 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0360 PredecessorHalfFin13Atom1237 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0421
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18572 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1237 chi ∧
      ¬PredecessorHalfFin13Atom0361 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0361 PredecessorHalfFin13Atom1237 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0421
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18573 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1237 chi ∧
      ¬PredecessorHalfFin13Atom0372 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0372 PredecessorHalfFin13Atom1237 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0421
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18574 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1237 chi ∧
      ¬PredecessorHalfFin13Atom0457 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0457 PredecessorHalfFin13Atom1237 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0421
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18575 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1237 chi ∧
      ¬PredecessorHalfFin13Atom0742 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0742 PredecessorHalfFin13Atom1237 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0421
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18576 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1237 chi ∧
      PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0742 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0360 PredecessorHalfFin13Atom0361 PredecessorHalfFin13Atom0372
    PredecessorHalfFin13Atom0457 PredecessorHalfFin13Atom0742 PredecessorHalfFin13Atom1237 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0421
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18577 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1238 chi ∧
      ¬PredecessorHalfFin13Atom0360 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0360 PredecessorHalfFin13Atom1238 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0677
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18578 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1238 chi ∧
      ¬PredecessorHalfFin13Atom0362 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0362 PredecessorHalfFin13Atom1238 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0677
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18579 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1238 chi ∧
      ¬PredecessorHalfFin13Atom0373 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0373 PredecessorHalfFin13Atom1238 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0677
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18580 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1238 chi ∧
      ¬PredecessorHalfFin13Atom0458 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0458 PredecessorHalfFin13Atom1238 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0677
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18581 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1238 chi ∧
      ¬PredecessorHalfFin13Atom0743 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0743 PredecessorHalfFin13Atom1238 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0677
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18583 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1239 chi ∧
      ¬PredecessorHalfFin13Atom0360 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0360 PredecessorHalfFin13Atom1239 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1189
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18584 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1239 chi ∧
      ¬PredecessorHalfFin13Atom0363 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0363 PredecessorHalfFin13Atom1239 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1189
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18585 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1239 chi ∧
      ¬PredecessorHalfFin13Atom0374 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0374 PredecessorHalfFin13Atom1239 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1189
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18586 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1239 chi ∧
      ¬PredecessorHalfFin13Atom0459 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0459 PredecessorHalfFin13Atom1239 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1189
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18587 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1239 chi ∧
      ¬PredecessorHalfFin13Atom0744 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0744 PredecessorHalfFin13Atom1239 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1189
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18595 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1241 chi ∧
      ¬PredecessorHalfFin13Atom0360 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0360 PredecessorHalfFin13Atom1241 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4261
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18596 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1241 chi ∧
      ¬PredecessorHalfFin13Atom0365 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0365 PredecessorHalfFin13Atom1241 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4261
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18597 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1241 chi ∧
      ¬PredecessorHalfFin13Atom0376 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0376 PredecessorHalfFin13Atom1241 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4261
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18598 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1241 chi ∧
      ¬PredecessorHalfFin13Atom0461 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0461 PredecessorHalfFin13Atom1241 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4261
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18599 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1241 chi ∧
      ¬PredecessorHalfFin13Atom0746 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0746 PredecessorHalfFin13Atom1241 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4261
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18600 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1241 chi ∧
      PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0461 chi ∧
      PredecessorHalfFin13Atom0746 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0360 PredecessorHalfFin13Atom0365 PredecessorHalfFin13Atom0376
    PredecessorHalfFin13Atom0461 PredecessorHalfFin13Atom0746 PredecessorHalfFin13Atom1241 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4261
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18601 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1242 chi ∧
      ¬PredecessorHalfFin13Atom0361 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0361 PredecessorHalfFin13Atom1242 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0805
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18602 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1242 chi ∧
      ¬PredecessorHalfFin13Atom0362 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0362 PredecessorHalfFin13Atom1242 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0805
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18603 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1242 chi ∧
      ¬PredecessorHalfFin13Atom0377 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0377 PredecessorHalfFin13Atom1242 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0805
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18604 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1242 chi ∧
      ¬PredecessorHalfFin13Atom0462 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0462 PredecessorHalfFin13Atom1242 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0805
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18605 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1242 chi ∧
      ¬PredecessorHalfFin13Atom0747 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0747 PredecessorHalfFin13Atom1242 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0805
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18606 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1242 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0362 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0747 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0361 PredecessorHalfFin13Atom0362 PredecessorHalfFin13Atom0377
    PredecessorHalfFin13Atom0462 PredecessorHalfFin13Atom0747 PredecessorHalfFin13Atom1242 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0805
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18607 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1243 chi ∧
      ¬PredecessorHalfFin13Atom0361 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0361 PredecessorHalfFin13Atom1243 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1317
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18608 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1243 chi ∧
      ¬PredecessorHalfFin13Atom0363 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0363 PredecessorHalfFin13Atom1243 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1317
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18609 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1243 chi ∧
      ¬PredecessorHalfFin13Atom0378 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0378 PredecessorHalfFin13Atom1243 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1317
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18610 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1243 chi ∧
      ¬PredecessorHalfFin13Atom0463 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0463 PredecessorHalfFin13Atom1243 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1317
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18611 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1243 chi ∧
      ¬PredecessorHalfFin13Atom0748 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0748 PredecessorHalfFin13Atom1243 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1317
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18612 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1243 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0748 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0361 PredecessorHalfFin13Atom0363 PredecessorHalfFin13Atom0378
    PredecessorHalfFin13Atom0463 PredecessorHalfFin13Atom0748 PredecessorHalfFin13Atom1243 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1317
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18619 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1245 chi ∧
      ¬PredecessorHalfFin13Atom0361 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0361 PredecessorHalfFin13Atom1245 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4389
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18620 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1245 chi ∧
      ¬PredecessorHalfFin13Atom0365 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0365 PredecessorHalfFin13Atom1245 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4389
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18621 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1245 chi ∧
      ¬PredecessorHalfFin13Atom0380 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0380 PredecessorHalfFin13Atom1245 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4389
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18622 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1245 chi ∧
      ¬PredecessorHalfFin13Atom0465 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0465 PredecessorHalfFin13Atom1245 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4389
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18623 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1245 chi ∧
      ¬PredecessorHalfFin13Atom0750 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0750 PredecessorHalfFin13Atom1245 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4389
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18624 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1245 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0750 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0361 PredecessorHalfFin13Atom0365 PredecessorHalfFin13Atom0380
    PredecessorHalfFin13Atom0465 PredecessorHalfFin13Atom0750 PredecessorHalfFin13Atom1245 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4389
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18625 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1246 chi ∧
      ¬PredecessorHalfFin13Atom0362 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0362 PredecessorHalfFin13Atom1246 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1573
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18626 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1246 chi ∧
      ¬PredecessorHalfFin13Atom0363 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0363 PredecessorHalfFin13Atom1246 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1573
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18627 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1246 chi ∧
      ¬PredecessorHalfFin13Atom0381 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0381 PredecessorHalfFin13Atom1246 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1573
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18628 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1246 chi ∧
      ¬PredecessorHalfFin13Atom0466 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0466 PredecessorHalfFin13Atom1246 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1573
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18629 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1246 chi ∧
      ¬PredecessorHalfFin13Atom0751 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0751 PredecessorHalfFin13Atom1246 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1573
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18630 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1246 chi ∧
      PredecessorHalfFin13Atom0362 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0751 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0362 PredecessorHalfFin13Atom0363 PredecessorHalfFin13Atom0381
    PredecessorHalfFin13Atom0466 PredecessorHalfFin13Atom0751 PredecessorHalfFin13Atom1246 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1573
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18637 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1248 chi ∧
      ¬PredecessorHalfFin13Atom0362 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0362 PredecessorHalfFin13Atom1248 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4645
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18638 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1248 chi ∧
      ¬PredecessorHalfFin13Atom0365 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0365 PredecessorHalfFin13Atom1248 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4645
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18639 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1248 chi ∧
      ¬PredecessorHalfFin13Atom0383 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0383 PredecessorHalfFin13Atom1248 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4645
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18640 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1248 chi ∧
      ¬PredecessorHalfFin13Atom0468 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0468 PredecessorHalfFin13Atom1248 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4645
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18641 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1248 chi ∧
      ¬PredecessorHalfFin13Atom0753 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0753 PredecessorHalfFin13Atom1248 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4645
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18649 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1250 chi ∧
      ¬PredecessorHalfFin13Atom0363 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0363 PredecessorHalfFin13Atom1250 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5157
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18650 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1250 chi ∧
      ¬PredecessorHalfFin13Atom0365 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0365 PredecessorHalfFin13Atom1250 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5157
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18651 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1250 chi ∧
      ¬PredecessorHalfFin13Atom0385 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0385 PredecessorHalfFin13Atom1250 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5157
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18652 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1250 chi ∧
      ¬PredecessorHalfFin13Atom0470 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0470 PredecessorHalfFin13Atom1250 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5157
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18653 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1250 chi ∧
      ¬PredecessorHalfFin13Atom0755 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0755 PredecessorHalfFin13Atom1250 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5157
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18654 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1250 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0755 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0363 PredecessorHalfFin13Atom0365 PredecessorHalfFin13Atom0385
    PredecessorHalfFin13Atom0470 PredecessorHalfFin13Atom0755 PredecessorHalfFin13Atom1250 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5157
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18661 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1252 chi ∧
      ¬PredecessorHalfFin13Atom0366 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0366 PredecessorHalfFin13Atom1252 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0453
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18662 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1252 chi ∧
      ¬PredecessorHalfFin13Atom0367 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0367 PredecessorHalfFin13Atom1252 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0453
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18663 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1252 chi ∧
      ¬PredecessorHalfFin13Atom0372 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0372 PredecessorHalfFin13Atom1252 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0453
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18664 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1252 chi ∧
      ¬PredecessorHalfFin13Atom0472 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0472 PredecessorHalfFin13Atom1252 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0453
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18665 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1252 chi ∧
      ¬PredecessorHalfFin13Atom0757 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0757 PredecessorHalfFin13Atom1252 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0453
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18666 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1252 chi ∧
      PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0757 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0366 PredecessorHalfFin13Atom0367 PredecessorHalfFin13Atom0372
    PredecessorHalfFin13Atom0472 PredecessorHalfFin13Atom0757 PredecessorHalfFin13Atom1252 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0453
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18667 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1253 chi ∧
      ¬PredecessorHalfFin13Atom0366 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0366 PredecessorHalfFin13Atom1253 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0709
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18668 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1253 chi ∧
      ¬PredecessorHalfFin13Atom0368 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0368 PredecessorHalfFin13Atom1253 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0709
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18669 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1253 chi ∧
      ¬PredecessorHalfFin13Atom0373 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0373 PredecessorHalfFin13Atom1253 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0709
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18670 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1253 chi ∧
      ¬PredecessorHalfFin13Atom0473 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0473 PredecessorHalfFin13Atom1253 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0709
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18671 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1253 chi ∧
      ¬PredecessorHalfFin13Atom0758 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0758 PredecessorHalfFin13Atom1253 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0709
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18672 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1253 chi ∧
      PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0473 chi ∧
      PredecessorHalfFin13Atom0758 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0366 PredecessorHalfFin13Atom0368 PredecessorHalfFin13Atom0373
    PredecessorHalfFin13Atom0473 PredecessorHalfFin13Atom0758 PredecessorHalfFin13Atom1253 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0709
  ] at hbad
  tauto

end ErdosSzekeres

end
