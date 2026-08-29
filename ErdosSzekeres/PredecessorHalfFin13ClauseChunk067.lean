module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 067. -/

theorem predecessorHalfFin13_clause19265 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1352 chi ∧
      ¬PredecessorHalfFin13Atom0857 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0857 PredecessorHalfFin13Atom1352 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1417
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19266 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1352 chi ∧
      PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0857 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0408 PredecessorHalfFin13Atom0410 PredecessorHalfFin13Atom0414
    PredecessorHalfFin13Atom0488 PredecessorHalfFin13Atom0857 PredecessorHalfFin13Atom1352 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1417
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19273 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1354 chi ∧
      ¬PredecessorHalfFin13Atom0408 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0408 PredecessorHalfFin13Atom1354 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4489
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19274 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1354 chi ∧
      ¬PredecessorHalfFin13Atom0412 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0412 PredecessorHalfFin13Atom1354 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4489
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19275 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1354 chi ∧
      ¬PredecessorHalfFin13Atom0416 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0416 PredecessorHalfFin13Atom1354 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4489
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19276 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1354 chi ∧
      ¬PredecessorHalfFin13Atom0490 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0490 PredecessorHalfFin13Atom1354 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4489
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19277 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1354 chi ∧
      ¬PredecessorHalfFin13Atom0859 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0859 PredecessorHalfFin13Atom1354 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4489
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19278 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1354 chi ∧
      PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0859 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0408 PredecessorHalfFin13Atom0412 PredecessorHalfFin13Atom0416
    PredecessorHalfFin13Atom0490 PredecessorHalfFin13Atom0859 PredecessorHalfFin13Atom1354 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4489
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19279 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1355 chi ∧
      ¬PredecessorHalfFin13Atom0409 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0409 PredecessorHalfFin13Atom1355 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1673
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19280 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1355 chi ∧
      ¬PredecessorHalfFin13Atom0410 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0410 PredecessorHalfFin13Atom1355 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1673
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19281 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1355 chi ∧
      ¬PredecessorHalfFin13Atom0417 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0417 PredecessorHalfFin13Atom1355 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1673
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19282 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1355 chi ∧
      ¬PredecessorHalfFin13Atom0491 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0491 PredecessorHalfFin13Atom1355 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1673
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19283 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1355 chi ∧
      ¬PredecessorHalfFin13Atom0860 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0860 PredecessorHalfFin13Atom1355 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1673
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19284 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1355 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0860 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0409 PredecessorHalfFin13Atom0410 PredecessorHalfFin13Atom0417
    PredecessorHalfFin13Atom0491 PredecessorHalfFin13Atom0860 PredecessorHalfFin13Atom1355 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1673
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19291 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1357 chi ∧
      ¬PredecessorHalfFin13Atom0409 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0409 PredecessorHalfFin13Atom1357 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4745
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19292 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1357 chi ∧
      ¬PredecessorHalfFin13Atom0412 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0412 PredecessorHalfFin13Atom1357 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4745
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19293 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1357 chi ∧
      ¬PredecessorHalfFin13Atom0419 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0419 PredecessorHalfFin13Atom1357 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4745
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19294 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1357 chi ∧
      ¬PredecessorHalfFin13Atom0493 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0493 PredecessorHalfFin13Atom1357 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4745
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19295 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1357 chi ∧
      ¬PredecessorHalfFin13Atom0862 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0862 PredecessorHalfFin13Atom1357 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4745
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19296 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1357 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0862 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0409 PredecessorHalfFin13Atom0412 PredecessorHalfFin13Atom0419
    PredecessorHalfFin13Atom0493 PredecessorHalfFin13Atom0862 PredecessorHalfFin13Atom1357 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4745
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19303 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1359 chi ∧
      ¬PredecessorHalfFin13Atom0410 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0410 PredecessorHalfFin13Atom1359 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5257
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19304 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1359 chi ∧
      ¬PredecessorHalfFin13Atom0412 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0412 PredecessorHalfFin13Atom1359 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5257
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19305 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1359 chi ∧
      ¬PredecessorHalfFin13Atom0421 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0421 PredecessorHalfFin13Atom1359 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5257
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19306 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1359 chi ∧
      ¬PredecessorHalfFin13Atom0495 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0495 PredecessorHalfFin13Atom1359 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5257
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19307 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1359 chi ∧
      ¬PredecessorHalfFin13Atom0864 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0864 PredecessorHalfFin13Atom1359 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5257
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19308 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1359 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0864 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0410 PredecessorHalfFin13Atom0412 PredecessorHalfFin13Atom0421
    PredecessorHalfFin13Atom0495 PredecessorHalfFin13Atom0864 PredecessorHalfFin13Atom1359 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5257
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19315 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1361 chi ∧
      ¬PredecessorHalfFin13Atom0413 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0413 PredecessorHalfFin13Atom1361 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1801
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19316 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1361 chi ∧
      ¬PredecessorHalfFin13Atom0414 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0414 PredecessorHalfFin13Atom1361 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1801
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19317 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1361 chi ∧
      ¬PredecessorHalfFin13Atom0417 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0417 PredecessorHalfFin13Atom1361 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1801
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19318 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1361 chi ∧
      ¬PredecessorHalfFin13Atom0497 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0497 PredecessorHalfFin13Atom1361 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1801
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19319 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1361 chi ∧
      ¬PredecessorHalfFin13Atom0866 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0866 PredecessorHalfFin13Atom1361 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1801
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19320 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1361 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0497 chi ∧
      PredecessorHalfFin13Atom0866 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0413 PredecessorHalfFin13Atom0414 PredecessorHalfFin13Atom0417
    PredecessorHalfFin13Atom0497 PredecessorHalfFin13Atom0866 PredecessorHalfFin13Atom1361 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1801
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19327 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1363 chi ∧
      ¬PredecessorHalfFin13Atom0413 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0413 PredecessorHalfFin13Atom1363 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4873
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19328 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1363 chi ∧
      ¬PredecessorHalfFin13Atom0416 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0416 PredecessorHalfFin13Atom1363 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4873
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19329 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1363 chi ∧
      ¬PredecessorHalfFin13Atom0419 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0419 PredecessorHalfFin13Atom1363 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4873
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19330 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1363 chi ∧
      ¬PredecessorHalfFin13Atom0499 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0499 PredecessorHalfFin13Atom1363 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4873
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19331 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1363 chi ∧
      ¬PredecessorHalfFin13Atom0868 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0868 PredecessorHalfFin13Atom1363 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4873
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19332 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1363 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0499 chi ∧
      PredecessorHalfFin13Atom0868 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0413 PredecessorHalfFin13Atom0416 PredecessorHalfFin13Atom0419
    PredecessorHalfFin13Atom0499 PredecessorHalfFin13Atom0868 PredecessorHalfFin13Atom1363 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4873
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19339 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1365 chi ∧
      ¬PredecessorHalfFin13Atom0414 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0414 PredecessorHalfFin13Atom1365 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5385
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19340 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1365 chi ∧
      ¬PredecessorHalfFin13Atom0416 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0416 PredecessorHalfFin13Atom1365 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5385
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19341 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1365 chi ∧
      ¬PredecessorHalfFin13Atom0421 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0421 PredecessorHalfFin13Atom1365 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5385
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19342 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1365 chi ∧
      ¬PredecessorHalfFin13Atom0501 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0501 PredecessorHalfFin13Atom1365 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5385
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19343 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1365 chi ∧
      ¬PredecessorHalfFin13Atom0870 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0870 PredecessorHalfFin13Atom1365 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5385
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19344 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1365 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0501 chi ∧
      PredecessorHalfFin13Atom0870 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0414 PredecessorHalfFin13Atom0416 PredecessorHalfFin13Atom0421
    PredecessorHalfFin13Atom0501 PredecessorHalfFin13Atom0870 PredecessorHalfFin13Atom1365 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5385
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19357 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1368 chi ∧
      ¬PredecessorHalfFin13Atom0417 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0417 PredecessorHalfFin13Atom1368 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5641
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19358 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1368 chi ∧
      ¬PredecessorHalfFin13Atom0419 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0419 PredecessorHalfFin13Atom1368 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5641
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19359 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1368 chi ∧
      ¬PredecessorHalfFin13Atom0421 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0421 PredecessorHalfFin13Atom1368 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5641
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19360 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1368 chi ∧
      ¬PredecessorHalfFin13Atom0504 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0504 PredecessorHalfFin13Atom1368 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5641
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19361 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1368 chi ∧
      ¬PredecessorHalfFin13Atom0873 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0873 PredecessorHalfFin13Atom1368 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5641
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19362 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1368 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0504 chi ∧
      PredecessorHalfFin13Atom0873 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0417 PredecessorHalfFin13Atom0419 PredecessorHalfFin13Atom0421
    PredecessorHalfFin13Atom0504 PredecessorHalfFin13Atom0873 PredecessorHalfFin13Atom1368 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5641
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19375 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1371 chi ∧
      ¬PredecessorHalfFin13Atom0423 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0423 PredecessorHalfFin13Atom1371 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0241
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19376 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1371 chi ∧
      ¬PredecessorHalfFin13Atom0424 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0424 PredecessorHalfFin13Atom1371 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0241
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19377 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1371 chi ∧
      ¬PredecessorHalfFin13Atom0430 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0430 PredecessorHalfFin13Atom1371 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0241
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19378 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1371 chi ∧
      ¬PredecessorHalfFin13Atom0451 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0451 PredecessorHalfFin13Atom1371 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0241
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19379 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1371 chi ∧
      ¬PredecessorHalfFin13Atom0876 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0876 PredecessorHalfFin13Atom1371 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0241
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19380 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1371 chi ∧
      PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0451 chi ∧
      PredecessorHalfFin13Atom0876 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0423 PredecessorHalfFin13Atom0424 PredecessorHalfFin13Atom0430
    PredecessorHalfFin13Atom0451 PredecessorHalfFin13Atom0876 PredecessorHalfFin13Atom1371 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0241
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19381 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1372 chi ∧
      ¬PredecessorHalfFin13Atom0423 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0423 PredecessorHalfFin13Atom1372 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0369
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19382 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1372 chi ∧
      ¬PredecessorHalfFin13Atom0425 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0425 PredecessorHalfFin13Atom1372 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0369
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19383 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1372 chi ∧
      ¬PredecessorHalfFin13Atom0431 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0431 PredecessorHalfFin13Atom1372 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0369
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19384 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1372 chi ∧
      ¬PredecessorHalfFin13Atom0452 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0452 PredecessorHalfFin13Atom1372 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0369
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19385 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1372 chi ∧
      ¬PredecessorHalfFin13Atom0877 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0877 PredecessorHalfFin13Atom1372 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0369
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19386 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1372 chi ∧
      PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0877 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0423 PredecessorHalfFin13Atom0425 PredecessorHalfFin13Atom0431
    PredecessorHalfFin13Atom0452 PredecessorHalfFin13Atom0877 PredecessorHalfFin13Atom1372 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0369
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19387 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1373 chi ∧
      ¬PredecessorHalfFin13Atom0423 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0423 PredecessorHalfFin13Atom1373 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0625
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19388 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1373 chi ∧
      ¬PredecessorHalfFin13Atom0426 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0426 PredecessorHalfFin13Atom1373 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0625
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19389 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1373 chi ∧
      ¬PredecessorHalfFin13Atom0432 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0432 PredecessorHalfFin13Atom1373 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0625
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19390 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1373 chi ∧
      ¬PredecessorHalfFin13Atom0453 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0453 PredecessorHalfFin13Atom1373 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0625
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19391 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1373 chi ∧
      ¬PredecessorHalfFin13Atom0878 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0878 PredecessorHalfFin13Atom1373 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0625
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19392 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1373 chi ∧
      PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0878 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0423 PredecessorHalfFin13Atom0426 PredecessorHalfFin13Atom0432
    PredecessorHalfFin13Atom0453 PredecessorHalfFin13Atom0878 PredecessorHalfFin13Atom1373 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0625
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19393 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1374 chi ∧
      ¬PredecessorHalfFin13Atom0423 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0423 PredecessorHalfFin13Atom1374 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1137
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19394 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1374 chi ∧
      ¬PredecessorHalfFin13Atom0427 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0427 PredecessorHalfFin13Atom1374 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1137
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19395 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1374 chi ∧
      ¬PredecessorHalfFin13Atom0433 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0433 PredecessorHalfFin13Atom1374 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1137
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19396 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1374 chi ∧
      ¬PredecessorHalfFin13Atom0454 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0454 PredecessorHalfFin13Atom1374 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1137
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19397 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1374 chi ∧
      ¬PredecessorHalfFin13Atom0879 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0879 PredecessorHalfFin13Atom1374 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1137
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19398 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1374 chi ∧
      PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0454 chi ∧
      PredecessorHalfFin13Atom0879 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0423 PredecessorHalfFin13Atom0427 PredecessorHalfFin13Atom0433
    PredecessorHalfFin13Atom0454 PredecessorHalfFin13Atom0879 PredecessorHalfFin13Atom1374 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1137
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19405 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1376 chi ∧
      ¬PredecessorHalfFin13Atom0423 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0423 PredecessorHalfFin13Atom1376 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4209
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19406 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1376 chi ∧
      ¬PredecessorHalfFin13Atom0429 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0429 PredecessorHalfFin13Atom1376 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4209
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19407 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1376 chi ∧
      ¬PredecessorHalfFin13Atom0435 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0435 PredecessorHalfFin13Atom1376 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4209
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19408 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1376 chi ∧
      ¬PredecessorHalfFin13Atom0456 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0456 PredecessorHalfFin13Atom1376 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4209
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19409 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1376 chi ∧
      ¬PredecessorHalfFin13Atom0881 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0881 PredecessorHalfFin13Atom1376 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4209
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19411 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1377 chi ∧
      ¬PredecessorHalfFin13Atom0424 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0424 PredecessorHalfFin13Atom1377 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0433
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19412 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1377 chi ∧
      ¬PredecessorHalfFin13Atom0425 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0425 PredecessorHalfFin13Atom1377 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0433
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19413 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1377 chi ∧
      ¬PredecessorHalfFin13Atom0436 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0436 PredecessorHalfFin13Atom1377 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0433
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19414 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1377 chi ∧
      ¬PredecessorHalfFin13Atom0457 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0457 PredecessorHalfFin13Atom1377 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0433
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19415 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1377 chi ∧
      ¬PredecessorHalfFin13Atom0882 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0882 PredecessorHalfFin13Atom1377 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0433
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19416 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1377 chi ∧
      PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0882 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0424 PredecessorHalfFin13Atom0425 PredecessorHalfFin13Atom0436
    PredecessorHalfFin13Atom0457 PredecessorHalfFin13Atom0882 PredecessorHalfFin13Atom1377 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0433
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19417 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1378 chi ∧
      ¬PredecessorHalfFin13Atom0424 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0424 PredecessorHalfFin13Atom1378 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0689
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19418 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1378 chi ∧
      ¬PredecessorHalfFin13Atom0426 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0426 PredecessorHalfFin13Atom1378 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0689
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19419 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1378 chi ∧
      ¬PredecessorHalfFin13Atom0437 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0437 PredecessorHalfFin13Atom1378 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0689
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19420 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1378 chi ∧
      ¬PredecessorHalfFin13Atom0458 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0458 PredecessorHalfFin13Atom1378 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0689
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19421 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1378 chi ∧
      ¬PredecessorHalfFin13Atom0883 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0883 PredecessorHalfFin13Atom1378 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0689
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19422 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1378 chi ∧
      PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0883 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0424 PredecessorHalfFin13Atom0426 PredecessorHalfFin13Atom0437
    PredecessorHalfFin13Atom0458 PredecessorHalfFin13Atom0883 PredecessorHalfFin13Atom1378 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0689
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19423 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1379 chi ∧
      ¬PredecessorHalfFin13Atom0424 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0424 PredecessorHalfFin13Atom1379 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1201
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19424 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1379 chi ∧
      ¬PredecessorHalfFin13Atom0427 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0427 PredecessorHalfFin13Atom1379 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1201
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19425 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1379 chi ∧
      ¬PredecessorHalfFin13Atom0438 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0438 PredecessorHalfFin13Atom1379 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1201
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19426 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1379 chi ∧
      ¬PredecessorHalfFin13Atom0459 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0459 PredecessorHalfFin13Atom1379 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1201
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19427 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1379 chi ∧
      ¬PredecessorHalfFin13Atom0884 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0884 PredecessorHalfFin13Atom1379 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1201
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19435 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1381 chi ∧
      ¬PredecessorHalfFin13Atom0424 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0424 PredecessorHalfFin13Atom1381 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4273
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19436 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1381 chi ∧
      ¬PredecessorHalfFin13Atom0429 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0429 PredecessorHalfFin13Atom1381 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4273
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19437 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1381 chi ∧
      ¬PredecessorHalfFin13Atom0440 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0440 PredecessorHalfFin13Atom1381 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4273
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19438 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1381 chi ∧
      ¬PredecessorHalfFin13Atom0461 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0461 PredecessorHalfFin13Atom1381 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4273
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19439 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1381 chi ∧
      ¬PredecessorHalfFin13Atom0886 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0886 PredecessorHalfFin13Atom1381 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4273
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19440 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1381 chi ∧
      PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0461 chi ∧
      PredecessorHalfFin13Atom0886 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0424 PredecessorHalfFin13Atom0429 PredecessorHalfFin13Atom0440
    PredecessorHalfFin13Atom0461 PredecessorHalfFin13Atom0886 PredecessorHalfFin13Atom1381 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4273
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19441 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1382 chi ∧
      ¬PredecessorHalfFin13Atom0425 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0425 PredecessorHalfFin13Atom1382 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0817
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19442 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1382 chi ∧
      ¬PredecessorHalfFin13Atom0426 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0426 PredecessorHalfFin13Atom1382 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0817
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19443 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1382 chi ∧
      ¬PredecessorHalfFin13Atom0441 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0441 PredecessorHalfFin13Atom1382 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0817
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19444 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1382 chi ∧
      ¬PredecessorHalfFin13Atom0462 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0462 PredecessorHalfFin13Atom1382 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0817
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19445 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1382 chi ∧
      ¬PredecessorHalfFin13Atom0887 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0887 PredecessorHalfFin13Atom1382 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0817
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19446 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1382 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0887 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0425 PredecessorHalfFin13Atom0426 PredecessorHalfFin13Atom0441
    PredecessorHalfFin13Atom0462 PredecessorHalfFin13Atom0887 PredecessorHalfFin13Atom1382 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0817
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19447 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1383 chi ∧
      ¬PredecessorHalfFin13Atom0425 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0425 PredecessorHalfFin13Atom1383 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1329
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19448 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1383 chi ∧
      ¬PredecessorHalfFin13Atom0427 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0427 PredecessorHalfFin13Atom1383 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1329
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19449 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1383 chi ∧
      ¬PredecessorHalfFin13Atom0442 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0442 PredecessorHalfFin13Atom1383 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1329
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19450 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1383 chi ∧
      ¬PredecessorHalfFin13Atom0463 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0463 PredecessorHalfFin13Atom1383 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1329
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19451 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1383 chi ∧
      ¬PredecessorHalfFin13Atom0888 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0888 PredecessorHalfFin13Atom1383 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1329
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19452 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1383 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0888 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0425 PredecessorHalfFin13Atom0427 PredecessorHalfFin13Atom0442
    PredecessorHalfFin13Atom0463 PredecessorHalfFin13Atom0888 PredecessorHalfFin13Atom1383 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1329
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19459 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1385 chi ∧
      ¬PredecessorHalfFin13Atom0425 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0425 PredecessorHalfFin13Atom1385 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4401
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19460 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1385 chi ∧
      ¬PredecessorHalfFin13Atom0429 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0429 PredecessorHalfFin13Atom1385 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4401
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19461 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1385 chi ∧
      ¬PredecessorHalfFin13Atom0444 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0444 PredecessorHalfFin13Atom1385 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4401
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19462 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1385 chi ∧
      ¬PredecessorHalfFin13Atom0465 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0465 PredecessorHalfFin13Atom1385 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4401
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19463 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1385 chi ∧
      ¬PredecessorHalfFin13Atom0890 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0890 PredecessorHalfFin13Atom1385 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4401
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19464 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1385 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0890 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0425 PredecessorHalfFin13Atom0429 PredecessorHalfFin13Atom0444
    PredecessorHalfFin13Atom0465 PredecessorHalfFin13Atom0890 PredecessorHalfFin13Atom1385 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4401
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19465 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1386 chi ∧
      ¬PredecessorHalfFin13Atom0426 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0426 PredecessorHalfFin13Atom1386 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1585
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19466 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1386 chi ∧
      ¬PredecessorHalfFin13Atom0427 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0427 PredecessorHalfFin13Atom1386 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1585
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19467 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1386 chi ∧
      ¬PredecessorHalfFin13Atom0445 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0445 PredecessorHalfFin13Atom1386 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1585
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19468 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1386 chi ∧
      ¬PredecessorHalfFin13Atom0466 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0466 PredecessorHalfFin13Atom1386 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1585
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19469 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1386 chi ∧
      ¬PredecessorHalfFin13Atom0891 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0891 PredecessorHalfFin13Atom1386 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1585
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19470 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1386 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0891 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0426 PredecessorHalfFin13Atom0427 PredecessorHalfFin13Atom0445
    PredecessorHalfFin13Atom0466 PredecessorHalfFin13Atom0891 PredecessorHalfFin13Atom1386 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1585
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19477 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1388 chi ∧
      ¬PredecessorHalfFin13Atom0426 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0426 PredecessorHalfFin13Atom1388 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4657
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19478 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1388 chi ∧
      ¬PredecessorHalfFin13Atom0429 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0429 PredecessorHalfFin13Atom1388 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4657
  ] at hbad
  tauto

end ErdosSzekeres

end
