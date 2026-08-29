module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 062. -/

theorem predecessorHalfFin13_clause18308 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1193 chi ∧
      ¬PredecessorHalfFin13Atom0347 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0347 PredecessorHalfFin13Atom1193 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0781
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18309 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1193 chi ∧
      ¬PredecessorHalfFin13Atom0377 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0377 PredecessorHalfFin13Atom1193 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0781
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18310 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1193 chi ∧
      ¬PredecessorHalfFin13Atom0413 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0413 PredecessorHalfFin13Atom1193 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0781
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18311 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1193 chi ∧
      ¬PredecessorHalfFin13Atom0698 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0698 PredecessorHalfFin13Atom1193 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0781
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18312 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1193 chi ∧
      PredecessorHalfFin13Atom0346 chi ∧
      PredecessorHalfFin13Atom0347 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0698 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0346 PredecessorHalfFin13Atom0347 PredecessorHalfFin13Atom0377
    PredecessorHalfFin13Atom0413 PredecessorHalfFin13Atom0698 PredecessorHalfFin13Atom1193 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0781
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18313 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1194 chi ∧
      ¬PredecessorHalfFin13Atom0346 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0346 PredecessorHalfFin13Atom1194 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1293
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18314 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1194 chi ∧
      ¬PredecessorHalfFin13Atom0348 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0348 PredecessorHalfFin13Atom1194 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1293
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18315 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1194 chi ∧
      ¬PredecessorHalfFin13Atom0378 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0378 PredecessorHalfFin13Atom1194 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1293
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18316 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1194 chi ∧
      ¬PredecessorHalfFin13Atom0414 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0414 PredecessorHalfFin13Atom1194 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1293
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18317 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1194 chi ∧
      ¬PredecessorHalfFin13Atom0699 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0699 PredecessorHalfFin13Atom1194 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1293
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18325 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1196 chi ∧
      ¬PredecessorHalfFin13Atom0346 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0346 PredecessorHalfFin13Atom1196 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4365
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18326 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1196 chi ∧
      ¬PredecessorHalfFin13Atom0350 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0350 PredecessorHalfFin13Atom1196 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4365
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18327 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1196 chi ∧
      ¬PredecessorHalfFin13Atom0380 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0380 PredecessorHalfFin13Atom1196 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4365
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18328 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1196 chi ∧
      ¬PredecessorHalfFin13Atom0416 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0416 PredecessorHalfFin13Atom1196 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4365
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18329 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1196 chi ∧
      ¬PredecessorHalfFin13Atom0701 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0701 PredecessorHalfFin13Atom1196 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4365
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18330 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1196 chi ∧
      PredecessorHalfFin13Atom0346 chi ∧
      PredecessorHalfFin13Atom0350 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0701 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0346 PredecessorHalfFin13Atom0350 PredecessorHalfFin13Atom0380
    PredecessorHalfFin13Atom0416 PredecessorHalfFin13Atom0701 PredecessorHalfFin13Atom1196 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4365
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18331 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1197 chi ∧
      ¬PredecessorHalfFin13Atom0347 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0347 PredecessorHalfFin13Atom1197 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1549
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18332 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1197 chi ∧
      ¬PredecessorHalfFin13Atom0348 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0348 PredecessorHalfFin13Atom1197 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1549
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18333 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1197 chi ∧
      ¬PredecessorHalfFin13Atom0381 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0381 PredecessorHalfFin13Atom1197 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1549
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18334 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1197 chi ∧
      ¬PredecessorHalfFin13Atom0417 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0417 PredecessorHalfFin13Atom1197 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1549
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18335 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1197 chi ∧
      ¬PredecessorHalfFin13Atom0702 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0702 PredecessorHalfFin13Atom1197 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1549
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18336 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1197 chi ∧
      PredecessorHalfFin13Atom0347 chi ∧
      PredecessorHalfFin13Atom0348 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0702 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0347 PredecessorHalfFin13Atom0348 PredecessorHalfFin13Atom0381
    PredecessorHalfFin13Atom0417 PredecessorHalfFin13Atom0702 PredecessorHalfFin13Atom1197 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1549
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18343 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1199 chi ∧
      ¬PredecessorHalfFin13Atom0347 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0347 PredecessorHalfFin13Atom1199 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4621
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18344 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1199 chi ∧
      ¬PredecessorHalfFin13Atom0350 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0350 PredecessorHalfFin13Atom1199 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4621
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18345 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1199 chi ∧
      ¬PredecessorHalfFin13Atom0383 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0383 PredecessorHalfFin13Atom1199 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4621
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18346 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1199 chi ∧
      ¬PredecessorHalfFin13Atom0419 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0419 PredecessorHalfFin13Atom1199 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4621
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18347 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1199 chi ∧
      ¬PredecessorHalfFin13Atom0704 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0704 PredecessorHalfFin13Atom1199 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4621
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18348 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1199 chi ∧
      PredecessorHalfFin13Atom0347 chi ∧
      PredecessorHalfFin13Atom0350 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0704 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0347 PredecessorHalfFin13Atom0350 PredecessorHalfFin13Atom0383
    PredecessorHalfFin13Atom0419 PredecessorHalfFin13Atom0704 PredecessorHalfFin13Atom1199 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4621
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18355 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1201 chi ∧
      ¬PredecessorHalfFin13Atom0348 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0348 PredecessorHalfFin13Atom1201 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5133
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18356 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1201 chi ∧
      ¬PredecessorHalfFin13Atom0350 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0350 PredecessorHalfFin13Atom1201 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5133
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18357 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1201 chi ∧
      ¬PredecessorHalfFin13Atom0385 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0385 PredecessorHalfFin13Atom1201 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5133
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18358 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1201 chi ∧
      ¬PredecessorHalfFin13Atom0421 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0421 PredecessorHalfFin13Atom1201 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5133
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18359 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1201 chi ∧
      ¬PredecessorHalfFin13Atom0706 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0706 PredecessorHalfFin13Atom1201 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5133
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18360 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1201 chi ∧
      PredecessorHalfFin13Atom0348 chi ∧
      PredecessorHalfFin13Atom0350 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0706 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0348 PredecessorHalfFin13Atom0350 PredecessorHalfFin13Atom0385
    PredecessorHalfFin13Atom0421 PredecessorHalfFin13Atom0706 PredecessorHalfFin13Atom1201 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5133
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18367 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1203 chi ∧
      ¬PredecessorHalfFin13Atom0351 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0351 PredecessorHalfFin13Atom1203 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0117
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18368 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1203 chi ∧
      ¬PredecessorHalfFin13Atom0352 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0352 PredecessorHalfFin13Atom1203 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0117
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18369 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1203 chi ∧
      ¬PredecessorHalfFin13Atom0359 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0359 PredecessorHalfFin13Atom1203 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0117
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18370 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1203 chi ∧
      ¬PredecessorHalfFin13Atom0423 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0423 PredecessorHalfFin13Atom1203 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0117
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18371 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1203 chi ∧
      ¬PredecessorHalfFin13Atom0708 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0708 PredecessorHalfFin13Atom1203 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0117
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18372 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1203 chi ∧
      PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0359 chi ∧
      PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0708 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0351 PredecessorHalfFin13Atom0352 PredecessorHalfFin13Atom0359
    PredecessorHalfFin13Atom0423 PredecessorHalfFin13Atom0708 PredecessorHalfFin13Atom1203 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0117
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18373 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1204 chi ∧
      ¬PredecessorHalfFin13Atom0351 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0351 PredecessorHalfFin13Atom1204 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0181
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18374 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1204 chi ∧
      ¬PredecessorHalfFin13Atom0353 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0353 PredecessorHalfFin13Atom1204 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0181
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18375 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1204 chi ∧
      ¬PredecessorHalfFin13Atom0360 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0360 PredecessorHalfFin13Atom1204 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0181
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18376 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1204 chi ∧
      ¬PredecessorHalfFin13Atom0424 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0424 PredecessorHalfFin13Atom1204 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0181
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18377 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1204 chi ∧
      ¬PredecessorHalfFin13Atom0709 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0709 PredecessorHalfFin13Atom1204 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0181
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18378 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1204 chi ∧
      PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0709 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0351 PredecessorHalfFin13Atom0353 PredecessorHalfFin13Atom0360
    PredecessorHalfFin13Atom0424 PredecessorHalfFin13Atom0709 PredecessorHalfFin13Atom1204 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0181
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18379 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1205 chi ∧
      ¬PredecessorHalfFin13Atom0351 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0351 PredecessorHalfFin13Atom1205 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0309
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18380 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1205 chi ∧
      ¬PredecessorHalfFin13Atom0354 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0354 PredecessorHalfFin13Atom1205 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0309
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18381 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1205 chi ∧
      ¬PredecessorHalfFin13Atom0361 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0361 PredecessorHalfFin13Atom1205 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0309
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18382 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1205 chi ∧
      ¬PredecessorHalfFin13Atom0425 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0425 PredecessorHalfFin13Atom1205 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0309
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18383 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1205 chi ∧
      ¬PredecessorHalfFin13Atom0710 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0710 PredecessorHalfFin13Atom1205 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0309
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18384 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1205 chi ∧
      PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0710 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0351 PredecessorHalfFin13Atom0354 PredecessorHalfFin13Atom0361
    PredecessorHalfFin13Atom0425 PredecessorHalfFin13Atom0710 PredecessorHalfFin13Atom1205 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0309
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18385 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1206 chi ∧
      ¬PredecessorHalfFin13Atom0351 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0351 PredecessorHalfFin13Atom1206 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0565
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18386 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1206 chi ∧
      ¬PredecessorHalfFin13Atom0355 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0355 PredecessorHalfFin13Atom1206 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0565
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18387 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1206 chi ∧
      ¬PredecessorHalfFin13Atom0362 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0362 PredecessorHalfFin13Atom1206 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0565
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18388 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1206 chi ∧
      ¬PredecessorHalfFin13Atom0426 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0426 PredecessorHalfFin13Atom1206 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0565
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18389 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1206 chi ∧
      ¬PredecessorHalfFin13Atom0711 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0711 PredecessorHalfFin13Atom1206 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0565
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18390 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1206 chi ∧
      PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0362 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0711 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0351 PredecessorHalfFin13Atom0355 PredecessorHalfFin13Atom0362
    PredecessorHalfFin13Atom0426 PredecessorHalfFin13Atom0711 PredecessorHalfFin13Atom1206 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0565
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18391 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1207 chi ∧
      ¬PredecessorHalfFin13Atom0351 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0351 PredecessorHalfFin13Atom1207 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1077
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18392 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1207 chi ∧
      ¬PredecessorHalfFin13Atom0356 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0356 PredecessorHalfFin13Atom1207 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1077
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18393 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1207 chi ∧
      ¬PredecessorHalfFin13Atom0363 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0363 PredecessorHalfFin13Atom1207 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1077
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18394 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1207 chi ∧
      ¬PredecessorHalfFin13Atom0427 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0427 PredecessorHalfFin13Atom1207 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1077
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18395 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1207 chi ∧
      ¬PredecessorHalfFin13Atom0712 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0712 PredecessorHalfFin13Atom1207 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1077
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18396 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1207 chi ∧
      PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0712 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0351 PredecessorHalfFin13Atom0356 PredecessorHalfFin13Atom0363
    PredecessorHalfFin13Atom0427 PredecessorHalfFin13Atom0712 PredecessorHalfFin13Atom1207 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1077
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18403 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1209 chi ∧
      ¬PredecessorHalfFin13Atom0351 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0351 PredecessorHalfFin13Atom1209 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4149
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18404 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1209 chi ∧
      ¬PredecessorHalfFin13Atom0358 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0358 PredecessorHalfFin13Atom1209 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4149
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18405 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1209 chi ∧
      ¬PredecessorHalfFin13Atom0365 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0365 PredecessorHalfFin13Atom1209 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4149
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18406 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1209 chi ∧
      ¬PredecessorHalfFin13Atom0429 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0429 PredecessorHalfFin13Atom1209 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4149
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18407 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1209 chi ∧
      ¬PredecessorHalfFin13Atom0714 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0714 PredecessorHalfFin13Atom1209 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4149
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18408 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1209 chi ∧
      PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0714 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0351 PredecessorHalfFin13Atom0358 PredecessorHalfFin13Atom0365
    PredecessorHalfFin13Atom0429 PredecessorHalfFin13Atom0714 PredecessorHalfFin13Atom1209 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4149
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18409 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1210 chi ∧
      ¬PredecessorHalfFin13Atom0352 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0352 PredecessorHalfFin13Atom1210 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0213
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18410 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1210 chi ∧
      ¬PredecessorHalfFin13Atom0353 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0353 PredecessorHalfFin13Atom1210 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0213
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18411 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1210 chi ∧
      ¬PredecessorHalfFin13Atom0366 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0366 PredecessorHalfFin13Atom1210 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0213
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18412 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1210 chi ∧
      ¬PredecessorHalfFin13Atom0430 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0430 PredecessorHalfFin13Atom1210 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0213
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18413 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1210 chi ∧
      ¬PredecessorHalfFin13Atom0715 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0715 PredecessorHalfFin13Atom1210 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0213
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18414 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1210 chi ∧
      PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0715 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0352 PredecessorHalfFin13Atom0353 PredecessorHalfFin13Atom0366
    PredecessorHalfFin13Atom0430 PredecessorHalfFin13Atom0715 PredecessorHalfFin13Atom1210 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0213
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18415 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1211 chi ∧
      ¬PredecessorHalfFin13Atom0352 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0352 PredecessorHalfFin13Atom1211 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0341
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18416 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1211 chi ∧
      ¬PredecessorHalfFin13Atom0354 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0354 PredecessorHalfFin13Atom1211 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0341
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18417 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1211 chi ∧
      ¬PredecessorHalfFin13Atom0367 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0367 PredecessorHalfFin13Atom1211 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0341
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18418 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1211 chi ∧
      ¬PredecessorHalfFin13Atom0431 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0431 PredecessorHalfFin13Atom1211 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0341
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18419 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1211 chi ∧
      ¬PredecessorHalfFin13Atom0716 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0716 PredecessorHalfFin13Atom1211 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0341
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18420 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1211 chi ∧
      PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0716 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0352 PredecessorHalfFin13Atom0354 PredecessorHalfFin13Atom0367
    PredecessorHalfFin13Atom0431 PredecessorHalfFin13Atom0716 PredecessorHalfFin13Atom1211 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0341
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18421 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1212 chi ∧
      ¬PredecessorHalfFin13Atom0352 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0352 PredecessorHalfFin13Atom1212 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0597
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18422 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1212 chi ∧
      ¬PredecessorHalfFin13Atom0355 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0355 PredecessorHalfFin13Atom1212 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0597
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18423 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1212 chi ∧
      ¬PredecessorHalfFin13Atom0368 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0368 PredecessorHalfFin13Atom1212 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0597
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18424 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1212 chi ∧
      ¬PredecessorHalfFin13Atom0432 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0432 PredecessorHalfFin13Atom1212 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0597
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18425 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1212 chi ∧
      ¬PredecessorHalfFin13Atom0717 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0717 PredecessorHalfFin13Atom1212 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0597
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18426 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1212 chi ∧
      PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0717 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0352 PredecessorHalfFin13Atom0355 PredecessorHalfFin13Atom0368
    PredecessorHalfFin13Atom0432 PredecessorHalfFin13Atom0717 PredecessorHalfFin13Atom1212 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0597
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18427 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1213 chi ∧
      ¬PredecessorHalfFin13Atom0352 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0352 PredecessorHalfFin13Atom1213 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1109
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18428 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1213 chi ∧
      ¬PredecessorHalfFin13Atom0356 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0356 PredecessorHalfFin13Atom1213 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1109
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18429 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1213 chi ∧
      ¬PredecessorHalfFin13Atom0369 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0369 PredecessorHalfFin13Atom1213 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1109
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18430 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1213 chi ∧
      ¬PredecessorHalfFin13Atom0433 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0433 PredecessorHalfFin13Atom1213 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1109
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18431 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1213 chi ∧
      ¬PredecessorHalfFin13Atom0718 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0718 PredecessorHalfFin13Atom1213 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1109
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18432 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1213 chi ∧
      PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0718 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0352 PredecessorHalfFin13Atom0356 PredecessorHalfFin13Atom0369
    PredecessorHalfFin13Atom0433 PredecessorHalfFin13Atom0718 PredecessorHalfFin13Atom1213 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1109
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18439 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1215 chi ∧
      ¬PredecessorHalfFin13Atom0352 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0352 PredecessorHalfFin13Atom1215 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4181
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18440 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1215 chi ∧
      ¬PredecessorHalfFin13Atom0358 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0358 PredecessorHalfFin13Atom1215 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4181
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18441 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1215 chi ∧
      ¬PredecessorHalfFin13Atom0371 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0371 PredecessorHalfFin13Atom1215 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4181
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18442 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1215 chi ∧
      ¬PredecessorHalfFin13Atom0435 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0435 PredecessorHalfFin13Atom1215 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4181
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18443 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1215 chi ∧
      ¬PredecessorHalfFin13Atom0720 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0720 PredecessorHalfFin13Atom1215 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4181
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18444 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1215 chi ∧
      PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0720 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0352 PredecessorHalfFin13Atom0358 PredecessorHalfFin13Atom0371
    PredecessorHalfFin13Atom0435 PredecessorHalfFin13Atom0720 PredecessorHalfFin13Atom1215 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4181
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18445 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1216 chi ∧
      ¬PredecessorHalfFin13Atom0353 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0353 PredecessorHalfFin13Atom1216 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0405
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18446 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1216 chi ∧
      ¬PredecessorHalfFin13Atom0354 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0354 PredecessorHalfFin13Atom1216 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0405
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18447 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1216 chi ∧
      ¬PredecessorHalfFin13Atom0372 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0372 PredecessorHalfFin13Atom1216 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0405
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18448 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1216 chi ∧
      ¬PredecessorHalfFin13Atom0436 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0436 PredecessorHalfFin13Atom1216 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0405
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18449 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1216 chi ∧
      ¬PredecessorHalfFin13Atom0721 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0721 PredecessorHalfFin13Atom1216 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0405
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18450 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1216 chi ∧
      PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0721 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0353 PredecessorHalfFin13Atom0354 PredecessorHalfFin13Atom0372
    PredecessorHalfFin13Atom0436 PredecessorHalfFin13Atom0721 PredecessorHalfFin13Atom1216 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0405
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18451 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1217 chi ∧
      ¬PredecessorHalfFin13Atom0353 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0353 PredecessorHalfFin13Atom1217 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0661
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18452 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1217 chi ∧
      ¬PredecessorHalfFin13Atom0355 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0355 PredecessorHalfFin13Atom1217 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0661
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18453 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1217 chi ∧
      ¬PredecessorHalfFin13Atom0373 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0373 PredecessorHalfFin13Atom1217 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0661
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18454 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1217 chi ∧
      ¬PredecessorHalfFin13Atom0437 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0437 PredecessorHalfFin13Atom1217 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0661
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18455 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1217 chi ∧
      ¬PredecessorHalfFin13Atom0722 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0722 PredecessorHalfFin13Atom1217 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0661
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18456 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1217 chi ∧
      PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0722 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0353 PredecessorHalfFin13Atom0355 PredecessorHalfFin13Atom0373
    PredecessorHalfFin13Atom0437 PredecessorHalfFin13Atom0722 PredecessorHalfFin13Atom1217 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0661
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18457 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1218 chi ∧
      ¬PredecessorHalfFin13Atom0353 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0353 PredecessorHalfFin13Atom1218 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1173
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18458 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1218 chi ∧
      ¬PredecessorHalfFin13Atom0356 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0356 PredecessorHalfFin13Atom1218 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1173
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18459 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1218 chi ∧
      ¬PredecessorHalfFin13Atom0374 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0374 PredecessorHalfFin13Atom1218 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1173
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18460 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1218 chi ∧
      ¬PredecessorHalfFin13Atom0438 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0438 PredecessorHalfFin13Atom1218 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1173
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18461 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1218 chi ∧
      ¬PredecessorHalfFin13Atom0723 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0723 PredecessorHalfFin13Atom1218 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1173
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18462 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1218 chi ∧
      PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0723 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0353 PredecessorHalfFin13Atom0356 PredecessorHalfFin13Atom0374
    PredecessorHalfFin13Atom0438 PredecessorHalfFin13Atom0723 PredecessorHalfFin13Atom1218 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1173
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18469 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1220 chi ∧
      ¬PredecessorHalfFin13Atom0353 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0353 PredecessorHalfFin13Atom1220 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4245
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18470 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1220 chi ∧
      ¬PredecessorHalfFin13Atom0358 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0358 PredecessorHalfFin13Atom1220 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4245
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18471 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1220 chi ∧
      ¬PredecessorHalfFin13Atom0376 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0376 PredecessorHalfFin13Atom1220 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4245
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18472 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1220 chi ∧
      ¬PredecessorHalfFin13Atom0440 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0440 PredecessorHalfFin13Atom1220 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4245
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18473 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1220 chi ∧
      ¬PredecessorHalfFin13Atom0725 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0725 PredecessorHalfFin13Atom1220 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4245
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18474 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1220 chi ∧
      PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0725 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0353 PredecessorHalfFin13Atom0358 PredecessorHalfFin13Atom0376
    PredecessorHalfFin13Atom0440 PredecessorHalfFin13Atom0725 PredecessorHalfFin13Atom1220 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4245
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18475 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1221 chi ∧
      ¬PredecessorHalfFin13Atom0354 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0354 PredecessorHalfFin13Atom1221 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0789
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18476 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1221 chi ∧
      ¬PredecessorHalfFin13Atom0355 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0355 PredecessorHalfFin13Atom1221 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0789
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18477 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1221 chi ∧
      ¬PredecessorHalfFin13Atom0377 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0377 PredecessorHalfFin13Atom1221 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0789
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18478 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1221 chi ∧
      ¬PredecessorHalfFin13Atom0441 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0441 PredecessorHalfFin13Atom1221 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0789
  ] at hbad
  tauto

end ErdosSzekeres

end
