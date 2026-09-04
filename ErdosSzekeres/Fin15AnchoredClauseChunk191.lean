module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 191. -/

theorem fin15Anchored_clause24448 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3840 chi ∧
      ¬Fin15AnchoredAtom1260 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1260 Fin15AnchoredAtom3840 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03172
  ] at hbad
  tauto

theorem fin15Anchored_clause24449 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3840 chi ∧
      ¬Fin15AnchoredAtom1629 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1629 Fin15AnchoredAtom3840 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03172
  ] at hbad
  tauto

theorem fin15Anchored_clause24450 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3840 chi ∧
      Fin15AnchoredAtom1209 chi ∧
      Fin15AnchoredAtom1210 chi ∧
      Fin15AnchoredAtom1232 chi ∧
      Fin15AnchoredAtom1260 chi ∧
      Fin15AnchoredAtom1629 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1209 Fin15AnchoredAtom1210 Fin15AnchoredAtom1232
    Fin15AnchoredAtom1260 Fin15AnchoredAtom1629 Fin15AnchoredAtom3840 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03172
  ] at hbad
  tauto

theorem fin15Anchored_clause24451 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom1209 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1209 Fin15AnchoredAtom3841 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05220
  ] at hbad
  tauto

theorem fin15Anchored_clause24452 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom1211 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1211 Fin15AnchoredAtom3841 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05220
  ] at hbad
  tauto

theorem fin15Anchored_clause24453 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom1233 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1233 Fin15AnchoredAtom3841 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05220
  ] at hbad
  tauto

theorem fin15Anchored_clause24454 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom1261 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1261 Fin15AnchoredAtom3841 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05220
  ] at hbad
  tauto

theorem fin15Anchored_clause24455 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom1630 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1630 Fin15AnchoredAtom3841 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05220
  ] at hbad
  tauto

theorem fin15Anchored_clause24456 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3841 chi ∧
      Fin15AnchoredAtom1209 chi ∧
      Fin15AnchoredAtom1211 chi ∧
      Fin15AnchoredAtom1233 chi ∧
      Fin15AnchoredAtom1261 chi ∧
      Fin15AnchoredAtom1630 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1209 Fin15AnchoredAtom1211 Fin15AnchoredAtom1233
    Fin15AnchoredAtom1261 Fin15AnchoredAtom1630 Fin15AnchoredAtom3841 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05220
  ] at hbad
  tauto

theorem fin15Anchored_clause24457 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom1209 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1209 Fin15AnchoredAtom3842 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09316
  ] at hbad
  tauto

theorem fin15Anchored_clause24458 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom1212 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1212 Fin15AnchoredAtom3842 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09316
  ] at hbad
  tauto

theorem fin15Anchored_clause24459 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom1234 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1234 Fin15AnchoredAtom3842 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09316
  ] at hbad
  tauto

theorem fin15Anchored_clause24460 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom1262 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1262 Fin15AnchoredAtom3842 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09316
  ] at hbad
  tauto

theorem fin15Anchored_clause24461 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom1631 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1631 Fin15AnchoredAtom3842 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09316
  ] at hbad
  tauto

theorem fin15Anchored_clause24462 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3842 chi ∧
      Fin15AnchoredAtom1209 chi ∧
      Fin15AnchoredAtom1212 chi ∧
      Fin15AnchoredAtom1234 chi ∧
      Fin15AnchoredAtom1262 chi ∧
      Fin15AnchoredAtom1631 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1209 Fin15AnchoredAtom1212 Fin15AnchoredAtom1234
    Fin15AnchoredAtom1262 Fin15AnchoredAtom1631 Fin15AnchoredAtom3842 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09316
  ] at hbad
  tauto

theorem fin15Anchored_clause24463 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom1209 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1209 Fin15AnchoredAtom3843 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17508
  ] at hbad
  tauto

theorem fin15Anchored_clause24464 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom1213 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1213 Fin15AnchoredAtom3843 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17508
  ] at hbad
  tauto

theorem fin15Anchored_clause24465 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom1235 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1235 Fin15AnchoredAtom3843 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17508
  ] at hbad
  tauto

theorem fin15Anchored_clause24466 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom1263 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1263 Fin15AnchoredAtom3843 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17508
  ] at hbad
  tauto

theorem fin15Anchored_clause24467 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom1632 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1632 Fin15AnchoredAtom3843 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17508
  ] at hbad
  tauto

theorem fin15Anchored_clause24468 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3843 chi ∧
      Fin15AnchoredAtom1209 chi ∧
      Fin15AnchoredAtom1213 chi ∧
      Fin15AnchoredAtom1235 chi ∧
      Fin15AnchoredAtom1263 chi ∧
      Fin15AnchoredAtom1632 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1209 Fin15AnchoredAtom1213 Fin15AnchoredAtom1235
    Fin15AnchoredAtom1263 Fin15AnchoredAtom1632 Fin15AnchoredAtom3843 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17508
  ] at hbad
  tauto

theorem fin15Anchored_clause24469 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3844 chi ∧
      ¬Fin15AnchoredAtom1211 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1211 Fin15AnchoredAtom3844 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06244
  ] at hbad
  tauto

theorem fin15Anchored_clause24470 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3844 chi ∧
      ¬Fin15AnchoredAtom1264 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1264 Fin15AnchoredAtom3844 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06244
  ] at hbad
  tauto

theorem fin15Anchored_clause24471 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3844 chi ∧
      ¬Fin15AnchoredAtom1633 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1633 Fin15AnchoredAtom3844 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06244
  ] at hbad
  tauto

theorem fin15Anchored_clause24472 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3844 chi ∧
      Fin15AnchoredAtom1210 chi ∧
      Fin15AnchoredAtom1211 chi ∧
      Fin15AnchoredAtom1236 chi ∧
      Fin15AnchoredAtom1264 chi ∧
      Fin15AnchoredAtom1633 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1210 Fin15AnchoredAtom1211 Fin15AnchoredAtom1236
    Fin15AnchoredAtom1264 Fin15AnchoredAtom1633 Fin15AnchoredAtom3844 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06244
  ] at hbad
  tauto

theorem fin15Anchored_clause24473 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3845 chi ∧
      ¬Fin15AnchoredAtom1212 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1212 Fin15AnchoredAtom3845 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10340
  ] at hbad
  tauto

theorem fin15Anchored_clause24474 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3846 chi ∧
      ¬Fin15AnchoredAtom1213 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1213 Fin15AnchoredAtom3846 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18532
  ] at hbad
  tauto

theorem fin15Anchored_clause24475 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom1211 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1211 Fin15AnchoredAtom3847 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12388
  ] at hbad
  tauto

theorem fin15Anchored_clause24476 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom1212 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1212 Fin15AnchoredAtom3847 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12388
  ] at hbad
  tauto

theorem fin15Anchored_clause24477 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom1239 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1239 Fin15AnchoredAtom3847 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12388
  ] at hbad
  tauto

theorem fin15Anchored_clause24478 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom1267 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1267 Fin15AnchoredAtom3847 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12388
  ] at hbad
  tauto

theorem fin15Anchored_clause24479 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom1636 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1636 Fin15AnchoredAtom3847 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12388
  ] at hbad
  tauto

theorem fin15Anchored_clause24480 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3847 chi ∧
      Fin15AnchoredAtom1211 chi ∧
      Fin15AnchoredAtom1212 chi ∧
      Fin15AnchoredAtom1239 chi ∧
      Fin15AnchoredAtom1267 chi ∧
      Fin15AnchoredAtom1636 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1211 Fin15AnchoredAtom1212 Fin15AnchoredAtom1239
    Fin15AnchoredAtom1267 Fin15AnchoredAtom1636 Fin15AnchoredAtom3847 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12388
  ] at hbad
  tauto

theorem fin15Anchored_clause24481 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom1211 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1211 Fin15AnchoredAtom3848 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20580
  ] at hbad
  tauto

theorem fin15Anchored_clause24482 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom1213 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1213 Fin15AnchoredAtom3848 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20580
  ] at hbad
  tauto

theorem fin15Anchored_clause24483 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom1240 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1240 Fin15AnchoredAtom3848 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20580
  ] at hbad
  tauto

theorem fin15Anchored_clause24484 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom1268 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1268 Fin15AnchoredAtom3848 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20580
  ] at hbad
  tauto

theorem fin15Anchored_clause24485 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom1637 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1637 Fin15AnchoredAtom3848 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20580
  ] at hbad
  tauto

theorem fin15Anchored_clause24486 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3848 chi ∧
      Fin15AnchoredAtom1211 chi ∧
      Fin15AnchoredAtom1213 chi ∧
      Fin15AnchoredAtom1240 chi ∧
      Fin15AnchoredAtom1268 chi ∧
      Fin15AnchoredAtom1637 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1211 Fin15AnchoredAtom1213 Fin15AnchoredAtom1240
    Fin15AnchoredAtom1268 Fin15AnchoredAtom1637 Fin15AnchoredAtom3848 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20580
  ] at hbad
  tauto

theorem fin15Anchored_clause24487 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom1212 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1212 Fin15AnchoredAtom3849 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24676
  ] at hbad
  tauto

theorem fin15Anchored_clause24488 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom1213 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1213 Fin15AnchoredAtom3849 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24676
  ] at hbad
  tauto

theorem fin15Anchored_clause24489 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom1241 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1241 Fin15AnchoredAtom3849 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24676
  ] at hbad
  tauto

theorem fin15Anchored_clause24490 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom1269 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1269 Fin15AnchoredAtom3849 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24676
  ] at hbad
  tauto

theorem fin15Anchored_clause24491 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom1638 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1638 Fin15AnchoredAtom3849 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24676
  ] at hbad
  tauto

theorem fin15Anchored_clause24492 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3849 chi ∧
      Fin15AnchoredAtom1212 chi ∧
      Fin15AnchoredAtom1213 chi ∧
      Fin15AnchoredAtom1241 chi ∧
      Fin15AnchoredAtom1269 chi ∧
      Fin15AnchoredAtom1638 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1212 Fin15AnchoredAtom1213 Fin15AnchoredAtom1241
    Fin15AnchoredAtom1269 Fin15AnchoredAtom1638 Fin15AnchoredAtom3849 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24676
  ] at hbad
  tauto

theorem fin15Anchored_clause24493 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3851 chi ∧
      ¬Fin15AnchoredAtom1214 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1214 Fin15AnchoredAtom3851 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01444
  ] at hbad
  tauto

theorem fin15Anchored_clause24494 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3854 chi ∧
      ¬Fin15AnchoredAtom1214 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1214 Fin15AnchoredAtom3854 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08612
  ] at hbad
  tauto

theorem fin15Anchored_clause24495 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom1215 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1215 Fin15AnchoredAtom3856 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01700
  ] at hbad
  tauto

theorem fin15Anchored_clause24496 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom1216 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1216 Fin15AnchoredAtom3856 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01700
  ] at hbad
  tauto

theorem fin15Anchored_clause24497 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom1227 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1227 Fin15AnchoredAtom3856 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01700
  ] at hbad
  tauto

theorem fin15Anchored_clause24498 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom1276 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1276 Fin15AnchoredAtom3856 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01700
  ] at hbad
  tauto

theorem fin15Anchored_clause24499 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom1645 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1645 Fin15AnchoredAtom3856 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01700
  ] at hbad
  tauto

theorem fin15Anchored_clause24500 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3856 chi ∧
      Fin15AnchoredAtom1215 chi ∧
      Fin15AnchoredAtom1216 chi ∧
      Fin15AnchoredAtom1227 chi ∧
      Fin15AnchoredAtom1276 chi ∧
      Fin15AnchoredAtom1645 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1215 Fin15AnchoredAtom1216 Fin15AnchoredAtom1227
    Fin15AnchoredAtom1276 Fin15AnchoredAtom1645 Fin15AnchoredAtom3856 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01700
  ] at hbad
  tauto

theorem fin15Anchored_clause24501 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3857 chi ∧
      ¬Fin15AnchoredAtom1215 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1215 Fin15AnchoredAtom3857 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02724
  ] at hbad
  tauto

theorem fin15Anchored_clause24502 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom1215 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1215 Fin15AnchoredAtom3858 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04772
  ] at hbad
  tauto

theorem fin15Anchored_clause24503 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom1218 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1218 Fin15AnchoredAtom3858 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04772
  ] at hbad
  tauto

theorem fin15Anchored_clause24504 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom1229 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1229 Fin15AnchoredAtom3858 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04772
  ] at hbad
  tauto

theorem fin15Anchored_clause24505 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom1278 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1278 Fin15AnchoredAtom3858 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04772
  ] at hbad
  tauto

theorem fin15Anchored_clause24506 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom1647 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1647 Fin15AnchoredAtom3858 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04772
  ] at hbad
  tauto

theorem fin15Anchored_clause24507 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3858 chi ∧
      Fin15AnchoredAtom1215 chi ∧
      Fin15AnchoredAtom1218 chi ∧
      Fin15AnchoredAtom1229 chi ∧
      Fin15AnchoredAtom1278 chi ∧
      Fin15AnchoredAtom1647 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1215 Fin15AnchoredAtom1218 Fin15AnchoredAtom1229
    Fin15AnchoredAtom1278 Fin15AnchoredAtom1647 Fin15AnchoredAtom3858 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04772
  ] at hbad
  tauto

theorem fin15Anchored_clause24508 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom1215 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1215 Fin15AnchoredAtom3859 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08868
  ] at hbad
  tauto

theorem fin15Anchored_clause24509 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom1219 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1219 Fin15AnchoredAtom3859 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08868
  ] at hbad
  tauto

theorem fin15Anchored_clause24510 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom1230 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1230 Fin15AnchoredAtom3859 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08868
  ] at hbad
  tauto

theorem fin15Anchored_clause24511 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom1279 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1279 Fin15AnchoredAtom3859 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08868
  ] at hbad
  tauto

theorem fin15Anchored_clause24512 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom1648 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1648 Fin15AnchoredAtom3859 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08868
  ] at hbad
  tauto

theorem fin15Anchored_clause24513 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3859 chi ∧
      Fin15AnchoredAtom1215 chi ∧
      Fin15AnchoredAtom1219 chi ∧
      Fin15AnchoredAtom1230 chi ∧
      Fin15AnchoredAtom1279 chi ∧
      Fin15AnchoredAtom1648 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1215 Fin15AnchoredAtom1219 Fin15AnchoredAtom1230
    Fin15AnchoredAtom1279 Fin15AnchoredAtom1648 Fin15AnchoredAtom3859 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08868
  ] at hbad
  tauto

theorem fin15Anchored_clause24514 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom1215 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1215 Fin15AnchoredAtom3860 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17060
  ] at hbad
  tauto

theorem fin15Anchored_clause24515 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom1220 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1220 Fin15AnchoredAtom3860 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17060
  ] at hbad
  tauto

theorem fin15Anchored_clause24516 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom1231 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1231 Fin15AnchoredAtom3860 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17060
  ] at hbad
  tauto

theorem fin15Anchored_clause24517 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom1280 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1280 Fin15AnchoredAtom3860 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17060
  ] at hbad
  tauto

theorem fin15Anchored_clause24518 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom1649 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1649 Fin15AnchoredAtom3860 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17060
  ] at hbad
  tauto

theorem fin15Anchored_clause24519 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3860 chi ∧
      Fin15AnchoredAtom1215 chi ∧
      Fin15AnchoredAtom1220 chi ∧
      Fin15AnchoredAtom1231 chi ∧
      Fin15AnchoredAtom1280 chi ∧
      Fin15AnchoredAtom1649 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1215 Fin15AnchoredAtom1220 Fin15AnchoredAtom1231
    Fin15AnchoredAtom1280 Fin15AnchoredAtom1649 Fin15AnchoredAtom3860 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17060
  ] at hbad
  tauto

theorem fin15Anchored_clause24520 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3861 chi ∧
      ¬Fin15AnchoredAtom1216 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1216 Fin15AnchoredAtom3861 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03236
  ] at hbad
  tauto

theorem fin15Anchored_clause24521 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3861 chi ∧
      ¬Fin15AnchoredAtom1217 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1217 Fin15AnchoredAtom3861 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03236
  ] at hbad
  tauto

theorem fin15Anchored_clause24522 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3861 chi ∧
      ¬Fin15AnchoredAtom1281 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1281 Fin15AnchoredAtom3861 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03236
  ] at hbad
  tauto

theorem fin15Anchored_clause24523 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3861 chi ∧
      ¬Fin15AnchoredAtom1650 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1650 Fin15AnchoredAtom3861 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03236
  ] at hbad
  tauto

theorem fin15Anchored_clause24524 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3861 chi ∧
      Fin15AnchoredAtom1216 chi ∧
      Fin15AnchoredAtom1217 chi ∧
      Fin15AnchoredAtom1232 chi ∧
      Fin15AnchoredAtom1281 chi ∧
      Fin15AnchoredAtom1650 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1216 Fin15AnchoredAtom1217 Fin15AnchoredAtom1232
    Fin15AnchoredAtom1281 Fin15AnchoredAtom1650 Fin15AnchoredAtom3861 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03236
  ] at hbad
  tauto

theorem fin15Anchored_clause24525 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom1216 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1216 Fin15AnchoredAtom3862 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05284
  ] at hbad
  tauto

theorem fin15Anchored_clause24526 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom1218 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1218 Fin15AnchoredAtom3862 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05284
  ] at hbad
  tauto

theorem fin15Anchored_clause24527 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom1233 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1233 Fin15AnchoredAtom3862 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05284
  ] at hbad
  tauto

theorem fin15Anchored_clause24528 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom1282 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1282 Fin15AnchoredAtom3862 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05284
  ] at hbad
  tauto

theorem fin15Anchored_clause24529 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom1651 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1651 Fin15AnchoredAtom3862 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05284
  ] at hbad
  tauto

theorem fin15Anchored_clause24530 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3862 chi ∧
      Fin15AnchoredAtom1216 chi ∧
      Fin15AnchoredAtom1218 chi ∧
      Fin15AnchoredAtom1233 chi ∧
      Fin15AnchoredAtom1282 chi ∧
      Fin15AnchoredAtom1651 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1216 Fin15AnchoredAtom1218 Fin15AnchoredAtom1233
    Fin15AnchoredAtom1282 Fin15AnchoredAtom1651 Fin15AnchoredAtom3862 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05284
  ] at hbad
  tauto

theorem fin15Anchored_clause24531 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom1216 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1216 Fin15AnchoredAtom3863 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09380
  ] at hbad
  tauto

theorem fin15Anchored_clause24532 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom1219 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1219 Fin15AnchoredAtom3863 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09380
  ] at hbad
  tauto

theorem fin15Anchored_clause24533 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom1234 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1234 Fin15AnchoredAtom3863 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09380
  ] at hbad
  tauto

theorem fin15Anchored_clause24534 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom1283 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1283 Fin15AnchoredAtom3863 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09380
  ] at hbad
  tauto

theorem fin15Anchored_clause24535 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom1652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1652 Fin15AnchoredAtom3863 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09380
  ] at hbad
  tauto

theorem fin15Anchored_clause24536 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3863 chi ∧
      Fin15AnchoredAtom1216 chi ∧
      Fin15AnchoredAtom1219 chi ∧
      Fin15AnchoredAtom1234 chi ∧
      Fin15AnchoredAtom1283 chi ∧
      Fin15AnchoredAtom1652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1216 Fin15AnchoredAtom1219 Fin15AnchoredAtom1234
    Fin15AnchoredAtom1283 Fin15AnchoredAtom1652 Fin15AnchoredAtom3863 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09380
  ] at hbad
  tauto

theorem fin15Anchored_clause24537 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom1216 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1216 Fin15AnchoredAtom3864 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17572
  ] at hbad
  tauto

theorem fin15Anchored_clause24538 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom1220 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1220 Fin15AnchoredAtom3864 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17572
  ] at hbad
  tauto

theorem fin15Anchored_clause24539 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom1235 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1235 Fin15AnchoredAtom3864 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17572
  ] at hbad
  tauto

theorem fin15Anchored_clause24540 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom1284 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1284 Fin15AnchoredAtom3864 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17572
  ] at hbad
  tauto

theorem fin15Anchored_clause24541 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom1653 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1653 Fin15AnchoredAtom3864 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17572
  ] at hbad
  tauto

theorem fin15Anchored_clause24542 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3864 chi ∧
      Fin15AnchoredAtom1216 chi ∧
      Fin15AnchoredAtom1220 chi ∧
      Fin15AnchoredAtom1235 chi ∧
      Fin15AnchoredAtom1284 chi ∧
      Fin15AnchoredAtom1653 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1216 Fin15AnchoredAtom1220 Fin15AnchoredAtom1235
    Fin15AnchoredAtom1284 Fin15AnchoredAtom1653 Fin15AnchoredAtom3864 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17572
  ] at hbad
  tauto

theorem fin15Anchored_clause24543 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3865 chi ∧
      ¬Fin15AnchoredAtom1218 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1218 Fin15AnchoredAtom3865 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06308
  ] at hbad
  tauto

theorem fin15Anchored_clause24544 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3865 chi ∧
      ¬Fin15AnchoredAtom1285 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1285 Fin15AnchoredAtom3865 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06308
  ] at hbad
  tauto

theorem fin15Anchored_clause24545 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3865 chi ∧
      ¬Fin15AnchoredAtom1654 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1654 Fin15AnchoredAtom3865 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06308
  ] at hbad
  tauto

theorem fin15Anchored_clause24546 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3866 chi ∧
      ¬Fin15AnchoredAtom1219 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1219 Fin15AnchoredAtom3866 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10404
  ] at hbad
  tauto

theorem fin15Anchored_clause24547 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3867 chi ∧
      ¬Fin15AnchoredAtom1220 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1220 Fin15AnchoredAtom3867 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18596
  ] at hbad
  tauto

theorem fin15Anchored_clause24548 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3867 chi ∧
      ¬Fin15AnchoredAtom1656 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1656 Fin15AnchoredAtom3867 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18596
  ] at hbad
  tauto

theorem fin15Anchored_clause24549 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom1218 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1218 Fin15AnchoredAtom3868 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12452
  ] at hbad
  tauto

theorem fin15Anchored_clause24550 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom1219 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1219 Fin15AnchoredAtom3868 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12452
  ] at hbad
  tauto

theorem fin15Anchored_clause24551 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom1239 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1239 Fin15AnchoredAtom3868 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12452
  ] at hbad
  tauto

theorem fin15Anchored_clause24552 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom1288 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1288 Fin15AnchoredAtom3868 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12452
  ] at hbad
  tauto

theorem fin15Anchored_clause24553 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom1657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1657 Fin15AnchoredAtom3868 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12452
  ] at hbad
  tauto

theorem fin15Anchored_clause24554 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3868 chi ∧
      Fin15AnchoredAtom1218 chi ∧
      Fin15AnchoredAtom1219 chi ∧
      Fin15AnchoredAtom1239 chi ∧
      Fin15AnchoredAtom1288 chi ∧
      Fin15AnchoredAtom1657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1218 Fin15AnchoredAtom1219 Fin15AnchoredAtom1239
    Fin15AnchoredAtom1288 Fin15AnchoredAtom1657 Fin15AnchoredAtom3868 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12452
  ] at hbad
  tauto

theorem fin15Anchored_clause24555 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom1218 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1218 Fin15AnchoredAtom3869 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20644
  ] at hbad
  tauto

theorem fin15Anchored_clause24556 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom1220 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1220 Fin15AnchoredAtom3869 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20644
  ] at hbad
  tauto

theorem fin15Anchored_clause24557 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom1240 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1240 Fin15AnchoredAtom3869 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20644
  ] at hbad
  tauto

theorem fin15Anchored_clause24558 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom1289 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1289 Fin15AnchoredAtom3869 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20644
  ] at hbad
  tauto

theorem fin15Anchored_clause24559 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom1658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1658 Fin15AnchoredAtom3869 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20644
  ] at hbad
  tauto

theorem fin15Anchored_clause24560 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3869 chi ∧
      Fin15AnchoredAtom1218 chi ∧
      Fin15AnchoredAtom1220 chi ∧
      Fin15AnchoredAtom1240 chi ∧
      Fin15AnchoredAtom1289 chi ∧
      Fin15AnchoredAtom1658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1218 Fin15AnchoredAtom1220 Fin15AnchoredAtom1240
    Fin15AnchoredAtom1289 Fin15AnchoredAtom1658 Fin15AnchoredAtom3869 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20644
  ] at hbad
  tauto

theorem fin15Anchored_clause24561 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom1219 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1219 Fin15AnchoredAtom3870 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24740
  ] at hbad
  tauto

theorem fin15Anchored_clause24562 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom1220 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1220 Fin15AnchoredAtom3870 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24740
  ] at hbad
  tauto

theorem fin15Anchored_clause24563 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom1241 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1241 Fin15AnchoredAtom3870 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24740
  ] at hbad
  tauto

theorem fin15Anchored_clause24564 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom1290 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1290 Fin15AnchoredAtom3870 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24740
  ] at hbad
  tauto

theorem fin15Anchored_clause24565 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom1659 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1659 Fin15AnchoredAtom3870 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24740
  ] at hbad
  tauto

theorem fin15Anchored_clause24566 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3870 chi ∧
      Fin15AnchoredAtom1219 chi ∧
      Fin15AnchoredAtom1220 chi ∧
      Fin15AnchoredAtom1241 chi ∧
      Fin15AnchoredAtom1290 chi ∧
      Fin15AnchoredAtom1659 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1219 Fin15AnchoredAtom1220 Fin15AnchoredAtom1241
    Fin15AnchoredAtom1290 Fin15AnchoredAtom1659 Fin15AnchoredAtom3870 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24740
  ] at hbad
  tauto

theorem fin15Anchored_clause24567 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3877 chi ∧
      ¬Fin15AnchoredAtom1222 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1222 Fin15AnchoredAtom3877 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05412
  ] at hbad
  tauto

theorem fin15Anchored_clause24568 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3877 chi ∧
      ¬Fin15AnchoredAtom1297 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1297 Fin15AnchoredAtom3877 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05412
  ] at hbad
  tauto

theorem fin15Anchored_clause24569 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3878 chi ∧
      ¬Fin15AnchoredAtom1222 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1222 Fin15AnchoredAtom3878 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09508
  ] at hbad
  tauto

theorem fin15Anchored_clause24570 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3878 chi ∧
      ¬Fin15AnchoredAtom1234 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1234 Fin15AnchoredAtom3878 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09508
  ] at hbad
  tauto

theorem fin15Anchored_clause24571 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3878 chi ∧
      ¬Fin15AnchoredAtom1298 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1298 Fin15AnchoredAtom3878 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09508
  ] at hbad
  tauto

theorem fin15Anchored_clause24572 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3883 chi ∧
      ¬Fin15AnchoredAtom1672 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1672 Fin15AnchoredAtom3883 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12580
  ] at hbad
  tauto

theorem fin15Anchored_clause24573 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3886 chi ∧
      ¬Fin15AnchoredAtom1227 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1227 Fin15AnchoredAtom3886 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03620
  ] at hbad
  tauto

theorem fin15Anchored_clause24574 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3886 chi ∧
      ¬Fin15AnchoredAtom1306 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1306 Fin15AnchoredAtom3886 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03620
  ] at hbad
  tauto

theorem fin15Anchored_clause24575 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3886 chi ∧
      ¬Fin15AnchoredAtom1675 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1675 Fin15AnchoredAtom3886 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03620
  ] at hbad
  tauto

end ErdosSzekeres

end
