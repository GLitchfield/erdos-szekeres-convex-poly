module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 143. -/

theorem fin15Anchored_clause18304 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom0619 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0619 Fin15AnchoredAtom2410 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01225
  ] at hbad
  tauto

theorem fin15Anchored_clause18305 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom0622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0622 Fin15AnchoredAtom2410 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01225
  ] at hbad
  tauto

theorem fin15Anchored_clause18306 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom0629 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0629 Fin15AnchoredAtom2410 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01225
  ] at hbad
  tauto

theorem fin15Anchored_clause18307 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom0738 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0738 Fin15AnchoredAtom2410 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01225
  ] at hbad
  tauto

theorem fin15Anchored_clause18308 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom1409 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1409 Fin15AnchoredAtom2410 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01225
  ] at hbad
  tauto

theorem fin15Anchored_clause18309 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2410 chi ∧
      Fin15AnchoredAtom0619 chi ∧
      Fin15AnchoredAtom0622 chi ∧
      Fin15AnchoredAtom0629 chi ∧
      Fin15AnchoredAtom0738 chi ∧
      Fin15AnchoredAtom1409 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0619 Fin15AnchoredAtom0622 Fin15AnchoredAtom0629
    Fin15AnchoredAtom0738 Fin15AnchoredAtom1409 Fin15AnchoredAtom2410 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01225
  ] at hbad
  tauto

theorem fin15Anchored_clause18310 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2411 chi ∧
      ¬Fin15AnchoredAtom0619 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0619 Fin15AnchoredAtom2411 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02249
  ] at hbad
  tauto

theorem fin15Anchored_clause18311 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2411 chi ∧
      ¬Fin15AnchoredAtom0623 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0623 Fin15AnchoredAtom2411 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02249
  ] at hbad
  tauto

theorem fin15Anchored_clause18312 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2411 chi ∧
      ¬Fin15AnchoredAtom0630 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0630 Fin15AnchoredAtom2411 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02249
  ] at hbad
  tauto

theorem fin15Anchored_clause18313 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2411 chi ∧
      ¬Fin15AnchoredAtom0739 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0739 Fin15AnchoredAtom2411 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02249
  ] at hbad
  tauto

theorem fin15Anchored_clause18314 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2411 chi ∧
      ¬Fin15AnchoredAtom1410 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1410 Fin15AnchoredAtom2411 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02249
  ] at hbad
  tauto

theorem fin15Anchored_clause18315 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2411 chi ∧
      Fin15AnchoredAtom0619 chi ∧
      Fin15AnchoredAtom0623 chi ∧
      Fin15AnchoredAtom0630 chi ∧
      Fin15AnchoredAtom0739 chi ∧
      Fin15AnchoredAtom1410 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0619 Fin15AnchoredAtom0623 Fin15AnchoredAtom0630
    Fin15AnchoredAtom0739 Fin15AnchoredAtom1410 Fin15AnchoredAtom2411 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02249
  ] at hbad
  tauto

theorem fin15Anchored_clause18316 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom0619 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0619 Fin15AnchoredAtom2412 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04297
  ] at hbad
  tauto

theorem fin15Anchored_clause18317 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom0624 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0624 Fin15AnchoredAtom2412 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04297
  ] at hbad
  tauto

theorem fin15Anchored_clause18318 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom0631 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0631 Fin15AnchoredAtom2412 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04297
  ] at hbad
  tauto

theorem fin15Anchored_clause18319 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom0740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0740 Fin15AnchoredAtom2412 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04297
  ] at hbad
  tauto

theorem fin15Anchored_clause18320 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom1411 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1411 Fin15AnchoredAtom2412 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04297
  ] at hbad
  tauto

theorem fin15Anchored_clause18321 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2412 chi ∧
      Fin15AnchoredAtom0619 chi ∧
      Fin15AnchoredAtom0624 chi ∧
      Fin15AnchoredAtom0631 chi ∧
      Fin15AnchoredAtom0740 chi ∧
      Fin15AnchoredAtom1411 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0619 Fin15AnchoredAtom0624 Fin15AnchoredAtom0631
    Fin15AnchoredAtom0740 Fin15AnchoredAtom1411 Fin15AnchoredAtom2412 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04297
  ] at hbad
  tauto

theorem fin15Anchored_clause18322 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom0619 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0619 Fin15AnchoredAtom2413 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08393
  ] at hbad
  tauto

theorem fin15Anchored_clause18323 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom0625 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0625 Fin15AnchoredAtom2413 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08393
  ] at hbad
  tauto

theorem fin15Anchored_clause18324 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom0632 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0632 Fin15AnchoredAtom2413 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08393
  ] at hbad
  tauto

theorem fin15Anchored_clause18325 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom0741 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0741 Fin15AnchoredAtom2413 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08393
  ] at hbad
  tauto

theorem fin15Anchored_clause18326 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom1412 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1412 Fin15AnchoredAtom2413 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08393
  ] at hbad
  tauto

theorem fin15Anchored_clause18327 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2413 chi ∧
      Fin15AnchoredAtom0619 chi ∧
      Fin15AnchoredAtom0625 chi ∧
      Fin15AnchoredAtom0632 chi ∧
      Fin15AnchoredAtom0741 chi ∧
      Fin15AnchoredAtom1412 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0619 Fin15AnchoredAtom0625 Fin15AnchoredAtom0632
    Fin15AnchoredAtom0741 Fin15AnchoredAtom1412 Fin15AnchoredAtom2413 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08393
  ] at hbad
  tauto

theorem fin15Anchored_clause18328 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom0619 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0619 Fin15AnchoredAtom2414 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16585
  ] at hbad
  tauto

theorem fin15Anchored_clause18329 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom0626 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0626 Fin15AnchoredAtom2414 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16585
  ] at hbad
  tauto

theorem fin15Anchored_clause18330 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom0633 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0633 Fin15AnchoredAtom2414 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16585
  ] at hbad
  tauto

theorem fin15Anchored_clause18331 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom0742 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0742 Fin15AnchoredAtom2414 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16585
  ] at hbad
  tauto

theorem fin15Anchored_clause18332 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom1413 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1413 Fin15AnchoredAtom2414 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16585
  ] at hbad
  tauto

theorem fin15Anchored_clause18333 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2414 chi ∧
      Fin15AnchoredAtom0619 chi ∧
      Fin15AnchoredAtom0626 chi ∧
      Fin15AnchoredAtom0633 chi ∧
      Fin15AnchoredAtom0742 chi ∧
      Fin15AnchoredAtom1413 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0619 Fin15AnchoredAtom0626 Fin15AnchoredAtom0633
    Fin15AnchoredAtom0742 Fin15AnchoredAtom1413 Fin15AnchoredAtom2414 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16585
  ] at hbad
  tauto

theorem fin15Anchored_clause18334 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2415 chi ∧
      ¬Fin15AnchoredAtom0620 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0620 Fin15AnchoredAtom2415 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00841
  ] at hbad
  tauto

theorem fin15Anchored_clause18335 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2415 chi ∧
      ¬Fin15AnchoredAtom0621 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0621 Fin15AnchoredAtom2415 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00841
  ] at hbad
  tauto

theorem fin15Anchored_clause18336 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2415 chi ∧
      ¬Fin15AnchoredAtom0634 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0634 Fin15AnchoredAtom2415 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00841
  ] at hbad
  tauto

theorem fin15Anchored_clause18337 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2415 chi ∧
      ¬Fin15AnchoredAtom0743 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0743 Fin15AnchoredAtom2415 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00841
  ] at hbad
  tauto

theorem fin15Anchored_clause18338 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2415 chi ∧
      ¬Fin15AnchoredAtom1414 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1414 Fin15AnchoredAtom2415 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00841
  ] at hbad
  tauto

theorem fin15Anchored_clause18339 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2415 chi ∧
      Fin15AnchoredAtom0620 chi ∧
      Fin15AnchoredAtom0621 chi ∧
      Fin15AnchoredAtom0634 chi ∧
      Fin15AnchoredAtom0743 chi ∧
      Fin15AnchoredAtom1414 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0620 Fin15AnchoredAtom0621 Fin15AnchoredAtom0634
    Fin15AnchoredAtom0743 Fin15AnchoredAtom1414 Fin15AnchoredAtom2415 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00841
  ] at hbad
  tauto

theorem fin15Anchored_clause18340 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2416 chi ∧
      ¬Fin15AnchoredAtom0620 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0620 Fin15AnchoredAtom2416 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01353
  ] at hbad
  tauto

theorem fin15Anchored_clause18341 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2416 chi ∧
      ¬Fin15AnchoredAtom0622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0622 Fin15AnchoredAtom2416 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01353
  ] at hbad
  tauto

theorem fin15Anchored_clause18342 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2416 chi ∧
      ¬Fin15AnchoredAtom0635 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0635 Fin15AnchoredAtom2416 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01353
  ] at hbad
  tauto

theorem fin15Anchored_clause18343 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2416 chi ∧
      ¬Fin15AnchoredAtom0744 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0744 Fin15AnchoredAtom2416 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01353
  ] at hbad
  tauto

theorem fin15Anchored_clause18344 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2416 chi ∧
      ¬Fin15AnchoredAtom1415 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1415 Fin15AnchoredAtom2416 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01353
  ] at hbad
  tauto

theorem fin15Anchored_clause18345 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2416 chi ∧
      Fin15AnchoredAtom0620 chi ∧
      Fin15AnchoredAtom0622 chi ∧
      Fin15AnchoredAtom0635 chi ∧
      Fin15AnchoredAtom0744 chi ∧
      Fin15AnchoredAtom1415 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0620 Fin15AnchoredAtom0622 Fin15AnchoredAtom0635
    Fin15AnchoredAtom0744 Fin15AnchoredAtom1415 Fin15AnchoredAtom2416 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01353
  ] at hbad
  tauto

theorem fin15Anchored_clause18346 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2418 chi ∧
      ¬Fin15AnchoredAtom0620 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0620 Fin15AnchoredAtom2418 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04425
  ] at hbad
  tauto

theorem fin15Anchored_clause18347 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2418 chi ∧
      ¬Fin15AnchoredAtom0624 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0624 Fin15AnchoredAtom2418 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04425
  ] at hbad
  tauto

theorem fin15Anchored_clause18348 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2418 chi ∧
      ¬Fin15AnchoredAtom0637 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0637 Fin15AnchoredAtom2418 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04425
  ] at hbad
  tauto

theorem fin15Anchored_clause18349 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2418 chi ∧
      ¬Fin15AnchoredAtom0746 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0746 Fin15AnchoredAtom2418 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04425
  ] at hbad
  tauto

theorem fin15Anchored_clause18350 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2418 chi ∧
      ¬Fin15AnchoredAtom1417 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1417 Fin15AnchoredAtom2418 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04425
  ] at hbad
  tauto

theorem fin15Anchored_clause18351 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2418 chi ∧
      Fin15AnchoredAtom0620 chi ∧
      Fin15AnchoredAtom0624 chi ∧
      Fin15AnchoredAtom0637 chi ∧
      Fin15AnchoredAtom0746 chi ∧
      Fin15AnchoredAtom1417 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0620 Fin15AnchoredAtom0624 Fin15AnchoredAtom0637
    Fin15AnchoredAtom0746 Fin15AnchoredAtom1417 Fin15AnchoredAtom2418 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04425
  ] at hbad
  tauto

theorem fin15Anchored_clause18352 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2419 chi ∧
      ¬Fin15AnchoredAtom0620 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0620 Fin15AnchoredAtom2419 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08521
  ] at hbad
  tauto

theorem fin15Anchored_clause18353 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2419 chi ∧
      ¬Fin15AnchoredAtom0625 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0625 Fin15AnchoredAtom2419 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08521
  ] at hbad
  tauto

theorem fin15Anchored_clause18354 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2419 chi ∧
      ¬Fin15AnchoredAtom0638 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0638 Fin15AnchoredAtom2419 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08521
  ] at hbad
  tauto

theorem fin15Anchored_clause18355 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2419 chi ∧
      ¬Fin15AnchoredAtom0747 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0747 Fin15AnchoredAtom2419 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08521
  ] at hbad
  tauto

theorem fin15Anchored_clause18356 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2419 chi ∧
      ¬Fin15AnchoredAtom1418 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1418 Fin15AnchoredAtom2419 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08521
  ] at hbad
  tauto

theorem fin15Anchored_clause18357 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2419 chi ∧
      Fin15AnchoredAtom0620 chi ∧
      Fin15AnchoredAtom0625 chi ∧
      Fin15AnchoredAtom0638 chi ∧
      Fin15AnchoredAtom0747 chi ∧
      Fin15AnchoredAtom1418 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0620 Fin15AnchoredAtom0625 Fin15AnchoredAtom0638
    Fin15AnchoredAtom0747 Fin15AnchoredAtom1418 Fin15AnchoredAtom2419 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08521
  ] at hbad
  tauto

theorem fin15Anchored_clause18358 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2420 chi ∧
      ¬Fin15AnchoredAtom0620 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0620 Fin15AnchoredAtom2420 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16713
  ] at hbad
  tauto

theorem fin15Anchored_clause18359 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2420 chi ∧
      ¬Fin15AnchoredAtom0626 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0626 Fin15AnchoredAtom2420 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16713
  ] at hbad
  tauto

theorem fin15Anchored_clause18360 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2420 chi ∧
      ¬Fin15AnchoredAtom0639 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0639 Fin15AnchoredAtom2420 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16713
  ] at hbad
  tauto

theorem fin15Anchored_clause18361 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2420 chi ∧
      ¬Fin15AnchoredAtom0748 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0748 Fin15AnchoredAtom2420 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16713
  ] at hbad
  tauto

theorem fin15Anchored_clause18362 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2420 chi ∧
      ¬Fin15AnchoredAtom1419 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1419 Fin15AnchoredAtom2420 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16713
  ] at hbad
  tauto

theorem fin15Anchored_clause18363 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2420 chi ∧
      Fin15AnchoredAtom0620 chi ∧
      Fin15AnchoredAtom0626 chi ∧
      Fin15AnchoredAtom0639 chi ∧
      Fin15AnchoredAtom0748 chi ∧
      Fin15AnchoredAtom1419 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0620 Fin15AnchoredAtom0626 Fin15AnchoredAtom0639
    Fin15AnchoredAtom0748 Fin15AnchoredAtom1419 Fin15AnchoredAtom2420 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16713
  ] at hbad
  tauto

theorem fin15Anchored_clause18364 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom0621 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0621 Fin15AnchoredAtom2421 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01609
  ] at hbad
  tauto

theorem fin15Anchored_clause18365 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom0622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0622 Fin15AnchoredAtom2421 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01609
  ] at hbad
  tauto

theorem fin15Anchored_clause18366 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom0640 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0640 Fin15AnchoredAtom2421 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01609
  ] at hbad
  tauto

theorem fin15Anchored_clause18367 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom0749 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0749 Fin15AnchoredAtom2421 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01609
  ] at hbad
  tauto

theorem fin15Anchored_clause18368 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom1420 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1420 Fin15AnchoredAtom2421 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01609
  ] at hbad
  tauto

theorem fin15Anchored_clause18369 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2421 chi ∧
      Fin15AnchoredAtom0621 chi ∧
      Fin15AnchoredAtom0622 chi ∧
      Fin15AnchoredAtom0640 chi ∧
      Fin15AnchoredAtom0749 chi ∧
      Fin15AnchoredAtom1420 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0621 Fin15AnchoredAtom0622 Fin15AnchoredAtom0640
    Fin15AnchoredAtom0749 Fin15AnchoredAtom1420 Fin15AnchoredAtom2421 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01609
  ] at hbad
  tauto

theorem fin15Anchored_clause18370 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2422 chi ∧
      ¬Fin15AnchoredAtom0621 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0621 Fin15AnchoredAtom2422 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02633
  ] at hbad
  tauto

theorem fin15Anchored_clause18371 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2422 chi ∧
      ¬Fin15AnchoredAtom0623 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0623 Fin15AnchoredAtom2422 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02633
  ] at hbad
  tauto

theorem fin15Anchored_clause18372 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2422 chi ∧
      ¬Fin15AnchoredAtom0750 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0750 Fin15AnchoredAtom2422 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02633
  ] at hbad
  tauto

theorem fin15Anchored_clause18373 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2422 chi ∧
      ¬Fin15AnchoredAtom1421 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1421 Fin15AnchoredAtom2422 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02633
  ] at hbad
  tauto

theorem fin15Anchored_clause18374 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2422 chi ∧
      Fin15AnchoredAtom0621 chi ∧
      Fin15AnchoredAtom0623 chi ∧
      Fin15AnchoredAtom0641 chi ∧
      Fin15AnchoredAtom0750 chi ∧
      Fin15AnchoredAtom1421 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0621 Fin15AnchoredAtom0623 Fin15AnchoredAtom0641
    Fin15AnchoredAtom0750 Fin15AnchoredAtom1421 Fin15AnchoredAtom2422 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02633
  ] at hbad
  tauto

theorem fin15Anchored_clause18375 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom0621 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0621 Fin15AnchoredAtom2423 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04681
  ] at hbad
  tauto

theorem fin15Anchored_clause18376 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom0624 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0624 Fin15AnchoredAtom2423 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04681
  ] at hbad
  tauto

theorem fin15Anchored_clause18377 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom0642 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0642 Fin15AnchoredAtom2423 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04681
  ] at hbad
  tauto

theorem fin15Anchored_clause18378 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom0751 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0751 Fin15AnchoredAtom2423 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04681
  ] at hbad
  tauto

theorem fin15Anchored_clause18379 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom1422 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1422 Fin15AnchoredAtom2423 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04681
  ] at hbad
  tauto

theorem fin15Anchored_clause18380 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2423 chi ∧
      Fin15AnchoredAtom0621 chi ∧
      Fin15AnchoredAtom0624 chi ∧
      Fin15AnchoredAtom0642 chi ∧
      Fin15AnchoredAtom0751 chi ∧
      Fin15AnchoredAtom1422 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0621 Fin15AnchoredAtom0624 Fin15AnchoredAtom0642
    Fin15AnchoredAtom0751 Fin15AnchoredAtom1422 Fin15AnchoredAtom2423 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04681
  ] at hbad
  tauto

theorem fin15Anchored_clause18381 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom0621 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0621 Fin15AnchoredAtom2424 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08777
  ] at hbad
  tauto

theorem fin15Anchored_clause18382 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom0625 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0625 Fin15AnchoredAtom2424 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08777
  ] at hbad
  tauto

theorem fin15Anchored_clause18383 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom0643 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0643 Fin15AnchoredAtom2424 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08777
  ] at hbad
  tauto

theorem fin15Anchored_clause18384 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom0752 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0752 Fin15AnchoredAtom2424 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08777
  ] at hbad
  tauto

theorem fin15Anchored_clause18385 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom1423 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1423 Fin15AnchoredAtom2424 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08777
  ] at hbad
  tauto

theorem fin15Anchored_clause18386 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2424 chi ∧
      Fin15AnchoredAtom0621 chi ∧
      Fin15AnchoredAtom0625 chi ∧
      Fin15AnchoredAtom0643 chi ∧
      Fin15AnchoredAtom0752 chi ∧
      Fin15AnchoredAtom1423 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0621 Fin15AnchoredAtom0625 Fin15AnchoredAtom0643
    Fin15AnchoredAtom0752 Fin15AnchoredAtom1423 Fin15AnchoredAtom2424 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08777
  ] at hbad
  tauto

theorem fin15Anchored_clause18387 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2425 chi ∧
      ¬Fin15AnchoredAtom0621 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0621 Fin15AnchoredAtom2425 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16969
  ] at hbad
  tauto

theorem fin15Anchored_clause18388 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2425 chi ∧
      ¬Fin15AnchoredAtom0626 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0626 Fin15AnchoredAtom2425 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16969
  ] at hbad
  tauto

theorem fin15Anchored_clause18389 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2425 chi ∧
      ¬Fin15AnchoredAtom0644 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0644 Fin15AnchoredAtom2425 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16969
  ] at hbad
  tauto

theorem fin15Anchored_clause18390 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2425 chi ∧
      ¬Fin15AnchoredAtom0753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0753 Fin15AnchoredAtom2425 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16969
  ] at hbad
  tauto

theorem fin15Anchored_clause18391 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2425 chi ∧
      ¬Fin15AnchoredAtom1424 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1424 Fin15AnchoredAtom2425 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16969
  ] at hbad
  tauto

theorem fin15Anchored_clause18392 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2425 chi ∧
      Fin15AnchoredAtom0621 chi ∧
      Fin15AnchoredAtom0626 chi ∧
      Fin15AnchoredAtom0644 chi ∧
      Fin15AnchoredAtom0753 chi ∧
      Fin15AnchoredAtom1424 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0621 Fin15AnchoredAtom0626 Fin15AnchoredAtom0644
    Fin15AnchoredAtom0753 Fin15AnchoredAtom1424 Fin15AnchoredAtom2425 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16969
  ] at hbad
  tauto

theorem fin15Anchored_clause18393 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2426 chi ∧
      ¬Fin15AnchoredAtom0622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0622 Fin15AnchoredAtom2426 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03145
  ] at hbad
  tauto

theorem fin15Anchored_clause18394 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2426 chi ∧
      ¬Fin15AnchoredAtom0623 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0623 Fin15AnchoredAtom2426 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03145
  ] at hbad
  tauto

theorem fin15Anchored_clause18395 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2426 chi ∧
      ¬Fin15AnchoredAtom0645 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0645 Fin15AnchoredAtom2426 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03145
  ] at hbad
  tauto

theorem fin15Anchored_clause18396 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2426 chi ∧
      ¬Fin15AnchoredAtom0754 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0754 Fin15AnchoredAtom2426 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03145
  ] at hbad
  tauto

theorem fin15Anchored_clause18397 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2426 chi ∧
      ¬Fin15AnchoredAtom1425 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1425 Fin15AnchoredAtom2426 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03145
  ] at hbad
  tauto

theorem fin15Anchored_clause18398 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2426 chi ∧
      Fin15AnchoredAtom0622 chi ∧
      Fin15AnchoredAtom0623 chi ∧
      Fin15AnchoredAtom0645 chi ∧
      Fin15AnchoredAtom0754 chi ∧
      Fin15AnchoredAtom1425 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0622 Fin15AnchoredAtom0623 Fin15AnchoredAtom0645
    Fin15AnchoredAtom0754 Fin15AnchoredAtom1425 Fin15AnchoredAtom2426 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03145
  ] at hbad
  tauto

theorem fin15Anchored_clause18399 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom0622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0622 Fin15AnchoredAtom2427 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05193
  ] at hbad
  tauto

theorem fin15Anchored_clause18400 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom0624 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0624 Fin15AnchoredAtom2427 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05193
  ] at hbad
  tauto

theorem fin15Anchored_clause18401 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom0646 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0646 Fin15AnchoredAtom2427 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05193
  ] at hbad
  tauto

theorem fin15Anchored_clause18402 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom0755 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0755 Fin15AnchoredAtom2427 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05193
  ] at hbad
  tauto

theorem fin15Anchored_clause18403 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom1426 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1426 Fin15AnchoredAtom2427 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05193
  ] at hbad
  tauto

theorem fin15Anchored_clause18404 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2427 chi ∧
      Fin15AnchoredAtom0622 chi ∧
      Fin15AnchoredAtom0624 chi ∧
      Fin15AnchoredAtom0646 chi ∧
      Fin15AnchoredAtom0755 chi ∧
      Fin15AnchoredAtom1426 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0622 Fin15AnchoredAtom0624 Fin15AnchoredAtom0646
    Fin15AnchoredAtom0755 Fin15AnchoredAtom1426 Fin15AnchoredAtom2427 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05193
  ] at hbad
  tauto

theorem fin15Anchored_clause18405 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom0622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0622 Fin15AnchoredAtom2428 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09289
  ] at hbad
  tauto

theorem fin15Anchored_clause18406 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom0625 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0625 Fin15AnchoredAtom2428 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09289
  ] at hbad
  tauto

theorem fin15Anchored_clause18407 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom0647 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0647 Fin15AnchoredAtom2428 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09289
  ] at hbad
  tauto

theorem fin15Anchored_clause18408 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom0756 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0756 Fin15AnchoredAtom2428 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09289
  ] at hbad
  tauto

theorem fin15Anchored_clause18409 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom1427 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1427 Fin15AnchoredAtom2428 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09289
  ] at hbad
  tauto

theorem fin15Anchored_clause18410 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2428 chi ∧
      Fin15AnchoredAtom0622 chi ∧
      Fin15AnchoredAtom0625 chi ∧
      Fin15AnchoredAtom0647 chi ∧
      Fin15AnchoredAtom0756 chi ∧
      Fin15AnchoredAtom1427 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0622 Fin15AnchoredAtom0625 Fin15AnchoredAtom0647
    Fin15AnchoredAtom0756 Fin15AnchoredAtom1427 Fin15AnchoredAtom2428 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09289
  ] at hbad
  tauto

theorem fin15Anchored_clause18411 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2429 chi ∧
      ¬Fin15AnchoredAtom0622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0622 Fin15AnchoredAtom2429 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17481
  ] at hbad
  tauto

theorem fin15Anchored_clause18412 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2429 chi ∧
      ¬Fin15AnchoredAtom0626 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0626 Fin15AnchoredAtom2429 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17481
  ] at hbad
  tauto

theorem fin15Anchored_clause18413 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2429 chi ∧
      ¬Fin15AnchoredAtom0648 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0648 Fin15AnchoredAtom2429 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17481
  ] at hbad
  tauto

theorem fin15Anchored_clause18414 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2429 chi ∧
      ¬Fin15AnchoredAtom0757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0757 Fin15AnchoredAtom2429 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17481
  ] at hbad
  tauto

theorem fin15Anchored_clause18415 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2429 chi ∧
      ¬Fin15AnchoredAtom1428 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1428 Fin15AnchoredAtom2429 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17481
  ] at hbad
  tauto

theorem fin15Anchored_clause18416 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2429 chi ∧
      Fin15AnchoredAtom0622 chi ∧
      Fin15AnchoredAtom0626 chi ∧
      Fin15AnchoredAtom0648 chi ∧
      Fin15AnchoredAtom0757 chi ∧
      Fin15AnchoredAtom1428 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0622 Fin15AnchoredAtom0626 Fin15AnchoredAtom0648
    Fin15AnchoredAtom0757 Fin15AnchoredAtom1428 Fin15AnchoredAtom2429 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17481
  ] at hbad
  tauto

theorem fin15Anchored_clause18417 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2430 chi ∧
      ¬Fin15AnchoredAtom0624 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0624 Fin15AnchoredAtom2430 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06217
  ] at hbad
  tauto

theorem fin15Anchored_clause18418 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2430 chi ∧
      Fin15AnchoredAtom0623 chi ∧
      Fin15AnchoredAtom0624 chi ∧
      Fin15AnchoredAtom0649 chi ∧
      Fin15AnchoredAtom0758 chi ∧
      Fin15AnchoredAtom1429 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0623 Fin15AnchoredAtom0624 Fin15AnchoredAtom0649
    Fin15AnchoredAtom0758 Fin15AnchoredAtom1429 Fin15AnchoredAtom2430 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06217
  ] at hbad
  tauto

theorem fin15Anchored_clause18419 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2431 chi ∧
      ¬Fin15AnchoredAtom0623 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0623 Fin15AnchoredAtom2431 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10313
  ] at hbad
  tauto

theorem fin15Anchored_clause18420 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2431 chi ∧
      ¬Fin15AnchoredAtom0625 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0625 Fin15AnchoredAtom2431 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10313
  ] at hbad
  tauto

theorem fin15Anchored_clause18421 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2431 chi ∧
      ¬Fin15AnchoredAtom0650 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0650 Fin15AnchoredAtom2431 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10313
  ] at hbad
  tauto

theorem fin15Anchored_clause18422 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2431 chi ∧
      ¬Fin15AnchoredAtom0759 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0759 Fin15AnchoredAtom2431 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10313
  ] at hbad
  tauto

theorem fin15Anchored_clause18423 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2431 chi ∧
      ¬Fin15AnchoredAtom1430 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1430 Fin15AnchoredAtom2431 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10313
  ] at hbad
  tauto

theorem fin15Anchored_clause18424 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2431 chi ∧
      Fin15AnchoredAtom0623 chi ∧
      Fin15AnchoredAtom0625 chi ∧
      Fin15AnchoredAtom0650 chi ∧
      Fin15AnchoredAtom0759 chi ∧
      Fin15AnchoredAtom1430 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0623 Fin15AnchoredAtom0625 Fin15AnchoredAtom0650
    Fin15AnchoredAtom0759 Fin15AnchoredAtom1430 Fin15AnchoredAtom2431 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10313
  ] at hbad
  tauto

theorem fin15Anchored_clause18425 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2433 chi ∧
      ¬Fin15AnchoredAtom0624 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0624 Fin15AnchoredAtom2433 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12361
  ] at hbad
  tauto

theorem fin15Anchored_clause18426 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2433 chi ∧
      ¬Fin15AnchoredAtom0625 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0625 Fin15AnchoredAtom2433 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12361
  ] at hbad
  tauto

theorem fin15Anchored_clause18427 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2433 chi ∧
      ¬Fin15AnchoredAtom0652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0652 Fin15AnchoredAtom2433 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12361
  ] at hbad
  tauto

theorem fin15Anchored_clause18428 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2433 chi ∧
      ¬Fin15AnchoredAtom0761 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0761 Fin15AnchoredAtom2433 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12361
  ] at hbad
  tauto

theorem fin15Anchored_clause18429 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2433 chi ∧
      ¬Fin15AnchoredAtom1432 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1432 Fin15AnchoredAtom2433 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12361
  ] at hbad
  tauto

theorem fin15Anchored_clause18430 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2433 chi ∧
      Fin15AnchoredAtom0624 chi ∧
      Fin15AnchoredAtom0625 chi ∧
      Fin15AnchoredAtom0652 chi ∧
      Fin15AnchoredAtom0761 chi ∧
      Fin15AnchoredAtom1432 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0624 Fin15AnchoredAtom0625 Fin15AnchoredAtom0652
    Fin15AnchoredAtom0761 Fin15AnchoredAtom1432 Fin15AnchoredAtom2433 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12361
  ] at hbad
  tauto

theorem fin15Anchored_clause18431 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2434 chi ∧
      ¬Fin15AnchoredAtom0624 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0624 Fin15AnchoredAtom2434 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20553
  ] at hbad
  tauto

end ErdosSzekeres

end
