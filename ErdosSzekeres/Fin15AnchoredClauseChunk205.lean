module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 205. -/

theorem fin15Anchored_clause26240 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4316 chi ∧
      Fin15AnchoredAtom1444 chi ∧
      Fin15AnchoredAtom1445 chi ∧
      Fin15AnchoredAtom1455 chi ∧
      Fin15AnchoredAtom1480 chi ∧
      Fin15AnchoredAtom1775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1444 Fin15AnchoredAtom1445 Fin15AnchoredAtom1455
    Fin15AnchoredAtom1480 Fin15AnchoredAtom1775 Fin15AnchoredAtom4316 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25224
  ] at hbad
  tauto

theorem fin15Anchored_clause26241 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4317 chi ∧
      ¬Fin15AnchoredAtom1447 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1447 Fin15AnchoredAtom4317 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07304
  ] at hbad
  tauto

theorem fin15Anchored_clause26242 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4317 chi ∧
      ¬Fin15AnchoredAtom1481 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1481 Fin15AnchoredAtom4317 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07304
  ] at hbad
  tauto

theorem fin15Anchored_clause26243 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4317 chi ∧
      ¬Fin15AnchoredAtom1776 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1776 Fin15AnchoredAtom4317 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07304
  ] at hbad
  tauto

theorem fin15Anchored_clause26244 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4318 chi ∧
      ¬Fin15AnchoredAtom1448 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1448 Fin15AnchoredAtom4318 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11400
  ] at hbad
  tauto

theorem fin15Anchored_clause26245 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4318 chi ∧
      ¬Fin15AnchoredAtom1777 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1777 Fin15AnchoredAtom4318 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11400
  ] at hbad
  tauto

theorem fin15Anchored_clause26246 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4319 chi ∧
      ¬Fin15AnchoredAtom1449 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1449 Fin15AnchoredAtom4319 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19592
  ] at hbad
  tauto

theorem fin15Anchored_clause26247 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4319 chi ∧
      ¬Fin15AnchoredAtom1483 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1483 Fin15AnchoredAtom4319 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19592
  ] at hbad
  tauto

theorem fin15Anchored_clause26248 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom1447 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1447 Fin15AnchoredAtom4320 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13448
  ] at hbad
  tauto

theorem fin15Anchored_clause26249 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom1448 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1448 Fin15AnchoredAtom4320 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13448
  ] at hbad
  tauto

theorem fin15Anchored_clause26250 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom1453 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1453 Fin15AnchoredAtom4320 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13448
  ] at hbad
  tauto

theorem fin15Anchored_clause26251 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom1484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1484 Fin15AnchoredAtom4320 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13448
  ] at hbad
  tauto

theorem fin15Anchored_clause26252 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom1779 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1779 Fin15AnchoredAtom4320 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13448
  ] at hbad
  tauto

theorem fin15Anchored_clause26253 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4320 chi ∧
      Fin15AnchoredAtom1447 chi ∧
      Fin15AnchoredAtom1448 chi ∧
      Fin15AnchoredAtom1453 chi ∧
      Fin15AnchoredAtom1484 chi ∧
      Fin15AnchoredAtom1779 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1447 Fin15AnchoredAtom1448 Fin15AnchoredAtom1453
    Fin15AnchoredAtom1484 Fin15AnchoredAtom1779 Fin15AnchoredAtom4320 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13448
  ] at hbad
  tauto

theorem fin15Anchored_clause26254 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom1447 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1447 Fin15AnchoredAtom4321 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21640
  ] at hbad
  tauto

theorem fin15Anchored_clause26255 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom1449 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1449 Fin15AnchoredAtom4321 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21640
  ] at hbad
  tauto

theorem fin15Anchored_clause26256 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom1454 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1454 Fin15AnchoredAtom4321 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21640
  ] at hbad
  tauto

theorem fin15Anchored_clause26257 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom1485 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1485 Fin15AnchoredAtom4321 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21640
  ] at hbad
  tauto

theorem fin15Anchored_clause26258 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom1780 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1780 Fin15AnchoredAtom4321 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21640
  ] at hbad
  tauto

theorem fin15Anchored_clause26259 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4321 chi ∧
      Fin15AnchoredAtom1447 chi ∧
      Fin15AnchoredAtom1449 chi ∧
      Fin15AnchoredAtom1454 chi ∧
      Fin15AnchoredAtom1485 chi ∧
      Fin15AnchoredAtom1780 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1447 Fin15AnchoredAtom1449 Fin15AnchoredAtom1454
    Fin15AnchoredAtom1485 Fin15AnchoredAtom1780 Fin15AnchoredAtom4321 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21640
  ] at hbad
  tauto

theorem fin15Anchored_clause26260 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom1448 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1448 Fin15AnchoredAtom4322 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25736
  ] at hbad
  tauto

theorem fin15Anchored_clause26261 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom1449 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1449 Fin15AnchoredAtom4322 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25736
  ] at hbad
  tauto

theorem fin15Anchored_clause26262 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom1455 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1455 Fin15AnchoredAtom4322 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25736
  ] at hbad
  tauto

theorem fin15Anchored_clause26263 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom1486 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1486 Fin15AnchoredAtom4322 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25736
  ] at hbad
  tauto

theorem fin15Anchored_clause26264 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom1781 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1781 Fin15AnchoredAtom4322 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25736
  ] at hbad
  tauto

theorem fin15Anchored_clause26265 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4322 chi ∧
      Fin15AnchoredAtom1448 chi ∧
      Fin15AnchoredAtom1449 chi ∧
      Fin15AnchoredAtom1455 chi ∧
      Fin15AnchoredAtom1486 chi ∧
      Fin15AnchoredAtom1781 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1448 Fin15AnchoredAtom1449 Fin15AnchoredAtom1455
    Fin15AnchoredAtom1486 Fin15AnchoredAtom1781 Fin15AnchoredAtom4322 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25736
  ] at hbad
  tauto

theorem fin15Anchored_clause26266 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4323 chi ∧
      ¬Fin15AnchoredAtom1487 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1487 Fin15AnchoredAtom4323 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14472
  ] at hbad
  tauto

theorem fin15Anchored_clause26267 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4324 chi ∧
      ¬Fin15AnchoredAtom1454 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1454 Fin15AnchoredAtom4324 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22664
  ] at hbad
  tauto

theorem fin15Anchored_clause26268 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4324 chi ∧
      ¬Fin15AnchoredAtom1488 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1488 Fin15AnchoredAtom4324 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22664
  ] at hbad
  tauto

theorem fin15Anchored_clause26269 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom1453 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1453 Fin15AnchoredAtom4326 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28808
  ] at hbad
  tauto

theorem fin15Anchored_clause26270 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom1454 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1454 Fin15AnchoredAtom4326 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28808
  ] at hbad
  tauto

theorem fin15Anchored_clause26271 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom1455 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1455 Fin15AnchoredAtom4326 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28808
  ] at hbad
  tauto

theorem fin15Anchored_clause26272 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom1490 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1490 Fin15AnchoredAtom4326 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28808
  ] at hbad
  tauto

theorem fin15Anchored_clause26273 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom1785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1785 Fin15AnchoredAtom4326 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28808
  ] at hbad
  tauto

theorem fin15Anchored_clause26274 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4326 chi ∧
      Fin15AnchoredAtom1453 chi ∧
      Fin15AnchoredAtom1454 chi ∧
      Fin15AnchoredAtom1455 chi ∧
      Fin15AnchoredAtom1490 chi ∧
      Fin15AnchoredAtom1785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1453 Fin15AnchoredAtom1454 Fin15AnchoredAtom1455
    Fin15AnchoredAtom1490 Fin15AnchoredAtom1785 Fin15AnchoredAtom4326 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28808
  ] at hbad
  tauto

theorem fin15Anchored_clause26275 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4328 chi ∧
      ¬Fin15AnchoredAtom1456 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1456 Fin15AnchoredAtom4328 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05896
  ] at hbad
  tauto

theorem fin15Anchored_clause26276 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4328 chi ∧
      ¬Fin15AnchoredAtom1458 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1458 Fin15AnchoredAtom4328 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05896
  ] at hbad
  tauto

theorem fin15Anchored_clause26277 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4328 chi ∧
      ¬Fin15AnchoredAtom1472 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1472 Fin15AnchoredAtom4328 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05896
  ] at hbad
  tauto

theorem fin15Anchored_clause26278 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4328 chi ∧
      ¬Fin15AnchoredAtom1787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1787 Fin15AnchoredAtom4328 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05896
  ] at hbad
  tauto

theorem fin15Anchored_clause26279 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4328 chi ∧
      Fin15AnchoredAtom1456 chi ∧
      Fin15AnchoredAtom1458 chi ∧
      Fin15AnchoredAtom1462 chi ∧
      Fin15AnchoredAtom1472 chi ∧
      Fin15AnchoredAtom1787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1456 Fin15AnchoredAtom1458 Fin15AnchoredAtom1462
    Fin15AnchoredAtom1472 Fin15AnchoredAtom1787 Fin15AnchoredAtom4328 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05896
  ] at hbad
  tauto

theorem fin15Anchored_clause26280 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4329 chi ∧
      ¬Fin15AnchoredAtom1456 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1456 Fin15AnchoredAtom4329 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09992
  ] at hbad
  tauto

theorem fin15Anchored_clause26281 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4329 chi ∧
      ¬Fin15AnchoredAtom1459 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1459 Fin15AnchoredAtom4329 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09992
  ] at hbad
  tauto

theorem fin15Anchored_clause26282 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4329 chi ∧
      ¬Fin15AnchoredAtom1463 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1463 Fin15AnchoredAtom4329 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09992
  ] at hbad
  tauto

theorem fin15Anchored_clause26283 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4329 chi ∧
      ¬Fin15AnchoredAtom1473 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1473 Fin15AnchoredAtom4329 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09992
  ] at hbad
  tauto

theorem fin15Anchored_clause26284 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4329 chi ∧
      ¬Fin15AnchoredAtom1788 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1788 Fin15AnchoredAtom4329 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09992
  ] at hbad
  tauto

theorem fin15Anchored_clause26285 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4329 chi ∧
      Fin15AnchoredAtom1456 chi ∧
      Fin15AnchoredAtom1459 chi ∧
      Fin15AnchoredAtom1463 chi ∧
      Fin15AnchoredAtom1473 chi ∧
      Fin15AnchoredAtom1788 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1456 Fin15AnchoredAtom1459 Fin15AnchoredAtom1463
    Fin15AnchoredAtom1473 Fin15AnchoredAtom1788 Fin15AnchoredAtom4329 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09992
  ] at hbad
  tauto

theorem fin15Anchored_clause26286 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4330 chi ∧
      ¬Fin15AnchoredAtom1456 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1456 Fin15AnchoredAtom4330 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18184
  ] at hbad
  tauto

theorem fin15Anchored_clause26287 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4330 chi ∧
      ¬Fin15AnchoredAtom1460 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1460 Fin15AnchoredAtom4330 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18184
  ] at hbad
  tauto

theorem fin15Anchored_clause26288 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4330 chi ∧
      ¬Fin15AnchoredAtom1474 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1474 Fin15AnchoredAtom4330 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18184
  ] at hbad
  tauto

theorem fin15Anchored_clause26289 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4330 chi ∧
      ¬Fin15AnchoredAtom1789 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1789 Fin15AnchoredAtom4330 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18184
  ] at hbad
  tauto

theorem fin15Anchored_clause26290 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4334 chi ∧
      ¬Fin15AnchoredAtom1458 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1458 Fin15AnchoredAtom4334 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13064
  ] at hbad
  tauto

theorem fin15Anchored_clause26291 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4334 chi ∧
      ¬Fin15AnchoredAtom1459 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1459 Fin15AnchoredAtom4334 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13064
  ] at hbad
  tauto

theorem fin15Anchored_clause26292 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4334 chi ∧
      ¬Fin15AnchoredAtom1468 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1468 Fin15AnchoredAtom4334 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13064
  ] at hbad
  tauto

theorem fin15Anchored_clause26293 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4334 chi ∧
      ¬Fin15AnchoredAtom1478 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1478 Fin15AnchoredAtom4334 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13064
  ] at hbad
  tauto

theorem fin15Anchored_clause26294 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4334 chi ∧
      ¬Fin15AnchoredAtom1793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1793 Fin15AnchoredAtom4334 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13064
  ] at hbad
  tauto

theorem fin15Anchored_clause26295 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4334 chi ∧
      Fin15AnchoredAtom1458 chi ∧
      Fin15AnchoredAtom1459 chi ∧
      Fin15AnchoredAtom1468 chi ∧
      Fin15AnchoredAtom1478 chi ∧
      Fin15AnchoredAtom1793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1458 Fin15AnchoredAtom1459 Fin15AnchoredAtom1468
    Fin15AnchoredAtom1478 Fin15AnchoredAtom1793 Fin15AnchoredAtom4334 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13064
  ] at hbad
  tauto

theorem fin15Anchored_clause26296 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4335 chi ∧
      ¬Fin15AnchoredAtom1458 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1458 Fin15AnchoredAtom4335 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21256
  ] at hbad
  tauto

theorem fin15Anchored_clause26297 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4335 chi ∧
      ¬Fin15AnchoredAtom1460 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1460 Fin15AnchoredAtom4335 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21256
  ] at hbad
  tauto

theorem fin15Anchored_clause26298 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4335 chi ∧
      ¬Fin15AnchoredAtom1469 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1469 Fin15AnchoredAtom4335 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21256
  ] at hbad
  tauto

theorem fin15Anchored_clause26299 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4335 chi ∧
      ¬Fin15AnchoredAtom1479 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1479 Fin15AnchoredAtom4335 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21256
  ] at hbad
  tauto

theorem fin15Anchored_clause26300 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4335 chi ∧
      ¬Fin15AnchoredAtom1794 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1794 Fin15AnchoredAtom4335 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21256
  ] at hbad
  tauto

theorem fin15Anchored_clause26301 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4335 chi ∧
      Fin15AnchoredAtom1458 chi ∧
      Fin15AnchoredAtom1460 chi ∧
      Fin15AnchoredAtom1469 chi ∧
      Fin15AnchoredAtom1479 chi ∧
      Fin15AnchoredAtom1794 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1458 Fin15AnchoredAtom1460 Fin15AnchoredAtom1469
    Fin15AnchoredAtom1479 Fin15AnchoredAtom1794 Fin15AnchoredAtom4335 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21256
  ] at hbad
  tauto

theorem fin15Anchored_clause26302 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4336 chi ∧
      ¬Fin15AnchoredAtom1459 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1459 Fin15AnchoredAtom4336 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25352
  ] at hbad
  tauto

theorem fin15Anchored_clause26303 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4336 chi ∧
      ¬Fin15AnchoredAtom1460 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1460 Fin15AnchoredAtom4336 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25352
  ] at hbad
  tauto

theorem fin15Anchored_clause26304 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4336 chi ∧
      ¬Fin15AnchoredAtom1470 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1470 Fin15AnchoredAtom4336 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25352
  ] at hbad
  tauto

theorem fin15Anchored_clause26305 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4336 chi ∧
      ¬Fin15AnchoredAtom1480 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1480 Fin15AnchoredAtom4336 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25352
  ] at hbad
  tauto

theorem fin15Anchored_clause26306 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4336 chi ∧
      ¬Fin15AnchoredAtom1795 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1795 Fin15AnchoredAtom4336 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25352
  ] at hbad
  tauto

theorem fin15Anchored_clause26307 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4336 chi ∧
      Fin15AnchoredAtom1459 chi ∧
      Fin15AnchoredAtom1460 chi ∧
      Fin15AnchoredAtom1470 chi ∧
      Fin15AnchoredAtom1480 chi ∧
      Fin15AnchoredAtom1795 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1459 Fin15AnchoredAtom1460 Fin15AnchoredAtom1470
    Fin15AnchoredAtom1480 Fin15AnchoredAtom1795 Fin15AnchoredAtom4336 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25352
  ] at hbad
  tauto

theorem fin15Anchored_clause26308 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4340 chi ∧
      ¬Fin15AnchoredAtom1462 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1462 Fin15AnchoredAtom4340 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13576
  ] at hbad
  tauto

theorem fin15Anchored_clause26309 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4340 chi ∧
      ¬Fin15AnchoredAtom1463 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1463 Fin15AnchoredAtom4340 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13576
  ] at hbad
  tauto

theorem fin15Anchored_clause26310 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4340 chi ∧
      ¬Fin15AnchoredAtom1468 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1468 Fin15AnchoredAtom4340 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13576
  ] at hbad
  tauto

theorem fin15Anchored_clause26311 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4340 chi ∧
      ¬Fin15AnchoredAtom1484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1484 Fin15AnchoredAtom4340 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13576
  ] at hbad
  tauto

theorem fin15Anchored_clause26312 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4340 chi ∧
      ¬Fin15AnchoredAtom1799 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1799 Fin15AnchoredAtom4340 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13576
  ] at hbad
  tauto

theorem fin15Anchored_clause26313 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4340 chi ∧
      Fin15AnchoredAtom1462 chi ∧
      Fin15AnchoredAtom1463 chi ∧
      Fin15AnchoredAtom1468 chi ∧
      Fin15AnchoredAtom1484 chi ∧
      Fin15AnchoredAtom1799 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1462 Fin15AnchoredAtom1463 Fin15AnchoredAtom1468
    Fin15AnchoredAtom1484 Fin15AnchoredAtom1799 Fin15AnchoredAtom4340 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13576
  ] at hbad
  tauto

theorem fin15Anchored_clause26314 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4341 chi ∧
      ¬Fin15AnchoredAtom1462 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1462 Fin15AnchoredAtom4341 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21768
  ] at hbad
  tauto

theorem fin15Anchored_clause26315 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4341 chi ∧
      ¬Fin15AnchoredAtom1464 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1464 Fin15AnchoredAtom4341 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21768
  ] at hbad
  tauto

theorem fin15Anchored_clause26316 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4341 chi ∧
      ¬Fin15AnchoredAtom1469 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1469 Fin15AnchoredAtom4341 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21768
  ] at hbad
  tauto

theorem fin15Anchored_clause26317 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4341 chi ∧
      ¬Fin15AnchoredAtom1485 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1485 Fin15AnchoredAtom4341 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21768
  ] at hbad
  tauto

theorem fin15Anchored_clause26318 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4341 chi ∧
      ¬Fin15AnchoredAtom1800 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1800 Fin15AnchoredAtom4341 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21768
  ] at hbad
  tauto

theorem fin15Anchored_clause26319 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4341 chi ∧
      Fin15AnchoredAtom1462 chi ∧
      Fin15AnchoredAtom1464 chi ∧
      Fin15AnchoredAtom1469 chi ∧
      Fin15AnchoredAtom1485 chi ∧
      Fin15AnchoredAtom1800 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1462 Fin15AnchoredAtom1464 Fin15AnchoredAtom1469
    Fin15AnchoredAtom1485 Fin15AnchoredAtom1800 Fin15AnchoredAtom4341 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21768
  ] at hbad
  tauto

theorem fin15Anchored_clause26320 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4342 chi ∧
      ¬Fin15AnchoredAtom1463 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1463 Fin15AnchoredAtom4342 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25864
  ] at hbad
  tauto

theorem fin15Anchored_clause26321 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4342 chi ∧
      ¬Fin15AnchoredAtom1464 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1464 Fin15AnchoredAtom4342 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25864
  ] at hbad
  tauto

theorem fin15Anchored_clause26322 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4342 chi ∧
      ¬Fin15AnchoredAtom1470 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1470 Fin15AnchoredAtom4342 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25864
  ] at hbad
  tauto

theorem fin15Anchored_clause26323 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4342 chi ∧
      ¬Fin15AnchoredAtom1486 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1486 Fin15AnchoredAtom4342 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25864
  ] at hbad
  tauto

theorem fin15Anchored_clause26324 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4342 chi ∧
      ¬Fin15AnchoredAtom1801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1801 Fin15AnchoredAtom4342 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25864
  ] at hbad
  tauto

theorem fin15Anchored_clause26325 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4342 chi ∧
      Fin15AnchoredAtom1463 chi ∧
      Fin15AnchoredAtom1464 chi ∧
      Fin15AnchoredAtom1470 chi ∧
      Fin15AnchoredAtom1486 chi ∧
      Fin15AnchoredAtom1801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1463 Fin15AnchoredAtom1464 Fin15AnchoredAtom1470
    Fin15AnchoredAtom1486 Fin15AnchoredAtom1801 Fin15AnchoredAtom4342 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25864
  ] at hbad
  tauto

theorem fin15Anchored_clause26326 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4346 chi ∧
      ¬Fin15AnchoredAtom1468 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1468 Fin15AnchoredAtom4346 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28936
  ] at hbad
  tauto

theorem fin15Anchored_clause26327 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4346 chi ∧
      ¬Fin15AnchoredAtom1469 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1469 Fin15AnchoredAtom4346 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28936
  ] at hbad
  tauto

theorem fin15Anchored_clause26328 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4346 chi ∧
      ¬Fin15AnchoredAtom1490 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1490 Fin15AnchoredAtom4346 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28936
  ] at hbad
  tauto

theorem fin15Anchored_clause26329 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4346 chi ∧
      ¬Fin15AnchoredAtom1805 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1805 Fin15AnchoredAtom4346 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28936
  ] at hbad
  tauto

theorem fin15Anchored_clause26330 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4346 chi ∧
      Fin15AnchoredAtom1468 chi ∧
      Fin15AnchoredAtom1469 chi ∧
      Fin15AnchoredAtom1470 chi ∧
      Fin15AnchoredAtom1490 chi ∧
      Fin15AnchoredAtom1805 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1468 Fin15AnchoredAtom1469 Fin15AnchoredAtom1470
    Fin15AnchoredAtom1490 Fin15AnchoredAtom1805 Fin15AnchoredAtom4346 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28936
  ] at hbad
  tauto

theorem fin15Anchored_clause26331 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4347 chi ∧
      ¬Fin15AnchoredAtom1472 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1472 Fin15AnchoredAtom4347 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07688
  ] at hbad
  tauto

theorem fin15Anchored_clause26332 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4347 chi ∧
      ¬Fin15AnchoredAtom1806 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1806 Fin15AnchoredAtom4347 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07688
  ] at hbad
  tauto

theorem fin15Anchored_clause26333 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4347 chi ∧
      Fin15AnchoredAtom1471 chi ∧
      Fin15AnchoredAtom1472 chi ∧
      Fin15AnchoredAtom1475 chi ∧
      Fin15AnchoredAtom1481 chi ∧
      Fin15AnchoredAtom1806 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1471 Fin15AnchoredAtom1472 Fin15AnchoredAtom1475
    Fin15AnchoredAtom1481 Fin15AnchoredAtom1806 Fin15AnchoredAtom4347 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07688
  ] at hbad
  tauto

theorem fin15Anchored_clause26334 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4348 chi ∧
      ¬Fin15AnchoredAtom1471 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1471 Fin15AnchoredAtom4348 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11784
  ] at hbad
  tauto

theorem fin15Anchored_clause26335 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4348 chi ∧
      ¬Fin15AnchoredAtom1473 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1473 Fin15AnchoredAtom4348 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11784
  ] at hbad
  tauto

theorem fin15Anchored_clause26336 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4348 chi ∧
      ¬Fin15AnchoredAtom1476 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1476 Fin15AnchoredAtom4348 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11784
  ] at hbad
  tauto

theorem fin15Anchored_clause26337 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom1472 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1472 Fin15AnchoredAtom4350 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13832
  ] at hbad
  tauto

theorem fin15Anchored_clause26338 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom1473 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1473 Fin15AnchoredAtom4350 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13832
  ] at hbad
  tauto

theorem fin15Anchored_clause26339 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom1478 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1478 Fin15AnchoredAtom4350 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13832
  ] at hbad
  tauto

theorem fin15Anchored_clause26340 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom1484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1484 Fin15AnchoredAtom4350 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13832
  ] at hbad
  tauto

theorem fin15Anchored_clause26341 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom1809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1809 Fin15AnchoredAtom4350 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13832
  ] at hbad
  tauto

theorem fin15Anchored_clause26342 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4350 chi ∧
      Fin15AnchoredAtom1472 chi ∧
      Fin15AnchoredAtom1473 chi ∧
      Fin15AnchoredAtom1478 chi ∧
      Fin15AnchoredAtom1484 chi ∧
      Fin15AnchoredAtom1809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1472 Fin15AnchoredAtom1473 Fin15AnchoredAtom1478
    Fin15AnchoredAtom1484 Fin15AnchoredAtom1809 Fin15AnchoredAtom4350 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13832
  ] at hbad
  tauto

theorem fin15Anchored_clause26343 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom1472 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1472 Fin15AnchoredAtom4351 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22024
  ] at hbad
  tauto

theorem fin15Anchored_clause26344 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom1474 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1474 Fin15AnchoredAtom4351 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22024
  ] at hbad
  tauto

theorem fin15Anchored_clause26345 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom1479 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1479 Fin15AnchoredAtom4351 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22024
  ] at hbad
  tauto

theorem fin15Anchored_clause26346 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom1485 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1485 Fin15AnchoredAtom4351 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22024
  ] at hbad
  tauto

theorem fin15Anchored_clause26347 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom1810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1810 Fin15AnchoredAtom4351 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22024
  ] at hbad
  tauto

theorem fin15Anchored_clause26348 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4351 chi ∧
      Fin15AnchoredAtom1472 chi ∧
      Fin15AnchoredAtom1474 chi ∧
      Fin15AnchoredAtom1479 chi ∧
      Fin15AnchoredAtom1485 chi ∧
      Fin15AnchoredAtom1810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1472 Fin15AnchoredAtom1474 Fin15AnchoredAtom1479
    Fin15AnchoredAtom1485 Fin15AnchoredAtom1810 Fin15AnchoredAtom4351 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22024
  ] at hbad
  tauto

theorem fin15Anchored_clause26349 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom1473 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1473 Fin15AnchoredAtom4352 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26120
  ] at hbad
  tauto

theorem fin15Anchored_clause26350 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom1474 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1474 Fin15AnchoredAtom4352 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26120
  ] at hbad
  tauto

theorem fin15Anchored_clause26351 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom1480 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1480 Fin15AnchoredAtom4352 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26120
  ] at hbad
  tauto

theorem fin15Anchored_clause26352 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom1486 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1486 Fin15AnchoredAtom4352 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26120
  ] at hbad
  tauto

theorem fin15Anchored_clause26353 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom1811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1811 Fin15AnchoredAtom4352 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26120
  ] at hbad
  tauto

theorem fin15Anchored_clause26354 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4352 chi ∧
      Fin15AnchoredAtom1473 chi ∧
      Fin15AnchoredAtom1474 chi ∧
      Fin15AnchoredAtom1480 chi ∧
      Fin15AnchoredAtom1486 chi ∧
      Fin15AnchoredAtom1811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1473 Fin15AnchoredAtom1474 Fin15AnchoredAtom1480
    Fin15AnchoredAtom1486 Fin15AnchoredAtom1811 Fin15AnchoredAtom4352 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26120
  ] at hbad
  tauto

theorem fin15Anchored_clause26355 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4353 chi ∧
      ¬Fin15AnchoredAtom1478 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1478 Fin15AnchoredAtom4353 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14856
  ] at hbad
  tauto

theorem fin15Anchored_clause26356 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4354 chi ∧
      ¬Fin15AnchoredAtom1475 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1475 Fin15AnchoredAtom4354 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask23048
  ] at hbad
  tauto

theorem fin15Anchored_clause26357 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4354 chi ∧
      ¬Fin15AnchoredAtom1479 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1479 Fin15AnchoredAtom4354 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask23048
  ] at hbad
  tauto

theorem fin15Anchored_clause26358 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom1478 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1478 Fin15AnchoredAtom4356 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29192
  ] at hbad
  tauto

theorem fin15Anchored_clause26359 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom1479 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1479 Fin15AnchoredAtom4356 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29192
  ] at hbad
  tauto

theorem fin15Anchored_clause26360 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom1480 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1480 Fin15AnchoredAtom4356 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29192
  ] at hbad
  tauto

theorem fin15Anchored_clause26361 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom1490 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1490 Fin15AnchoredAtom4356 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29192
  ] at hbad
  tauto

theorem fin15Anchored_clause26362 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom1815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1815 Fin15AnchoredAtom4356 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29192
  ] at hbad
  tauto

theorem fin15Anchored_clause26363 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4356 chi ∧
      Fin15AnchoredAtom1478 chi ∧
      Fin15AnchoredAtom1479 chi ∧
      Fin15AnchoredAtom1480 chi ∧
      Fin15AnchoredAtom1490 chi ∧
      Fin15AnchoredAtom1815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1478 Fin15AnchoredAtom1479 Fin15AnchoredAtom1480
    Fin15AnchoredAtom1490 Fin15AnchoredAtom1815 Fin15AnchoredAtom4356 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29192
  ] at hbad
  tauto

theorem fin15Anchored_clause26364 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4357 chi ∧
      ¬Fin15AnchoredAtom1484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1484 Fin15AnchoredAtom4357 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask15368
  ] at hbad
  tauto

theorem fin15Anchored_clause26365 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4357 chi ∧
      ¬Fin15AnchoredAtom1487 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1487 Fin15AnchoredAtom4357 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask15368
  ] at hbad
  tauto

theorem fin15Anchored_clause26366 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4357 chi ∧
      Fin15AnchoredAtom1481 chi ∧
      Fin15AnchoredAtom1482 chi ∧
      Fin15AnchoredAtom1484 chi ∧
      Fin15AnchoredAtom1487 chi ∧
      Fin15AnchoredAtom1816 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1481 Fin15AnchoredAtom1482 Fin15AnchoredAtom1484
    Fin15AnchoredAtom1487 Fin15AnchoredAtom1816 Fin15AnchoredAtom4357 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask15368
  ] at hbad
  tauto

theorem fin15Anchored_clause26367 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4358 chi ∧
      ¬Fin15AnchoredAtom1485 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1485 Fin15AnchoredAtom4358 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask23560
  ] at hbad
  tauto

end ErdosSzekeres

end
