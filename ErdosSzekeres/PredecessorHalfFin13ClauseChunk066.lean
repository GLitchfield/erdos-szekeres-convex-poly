module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 066. -/

theorem predecessorHalfFin13_clause19071 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1320 chi ∧
      ¬PredecessorHalfFin13Atom0407 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0407 PredecessorHalfFin13Atom1320 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4201
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19072 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1320 chi ∧
      ¬PredecessorHalfFin13Atom0456 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0456 PredecessorHalfFin13Atom1320 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4201
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19073 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1320 chi ∧
      ¬PredecessorHalfFin13Atom0825 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0825 PredecessorHalfFin13Atom1320 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4201
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19075 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1321 chi ∧
      ¬PredecessorHalfFin13Atom0396 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0396 PredecessorHalfFin13Atom1321 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0425
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19076 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1321 chi ∧
      ¬PredecessorHalfFin13Atom0397 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0397 PredecessorHalfFin13Atom1321 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0425
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19077 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1321 chi ∧
      ¬PredecessorHalfFin13Atom0408 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0408 PredecessorHalfFin13Atom1321 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0425
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19078 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1321 chi ∧
      ¬PredecessorHalfFin13Atom0457 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0457 PredecessorHalfFin13Atom1321 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0425
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19079 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1321 chi ∧
      ¬PredecessorHalfFin13Atom0826 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0826 PredecessorHalfFin13Atom1321 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0425
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19081 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1322 chi ∧
      ¬PredecessorHalfFin13Atom0396 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0396 PredecessorHalfFin13Atom1322 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0681
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19082 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1322 chi ∧
      ¬PredecessorHalfFin13Atom0398 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0398 PredecessorHalfFin13Atom1322 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0681
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19083 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1322 chi ∧
      ¬PredecessorHalfFin13Atom0409 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0409 PredecessorHalfFin13Atom1322 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0681
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19084 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1322 chi ∧
      ¬PredecessorHalfFin13Atom0458 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0458 PredecessorHalfFin13Atom1322 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0681
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19085 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1322 chi ∧
      ¬PredecessorHalfFin13Atom0827 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0827 PredecessorHalfFin13Atom1322 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0681
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19086 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1322 chi ∧
      PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0827 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0396 PredecessorHalfFin13Atom0398 PredecessorHalfFin13Atom0409
    PredecessorHalfFin13Atom0458 PredecessorHalfFin13Atom0827 PredecessorHalfFin13Atom1322 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0681
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19087 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1323 chi ∧
      ¬PredecessorHalfFin13Atom0396 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0396 PredecessorHalfFin13Atom1323 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1193
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19088 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1323 chi ∧
      ¬PredecessorHalfFin13Atom0399 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0399 PredecessorHalfFin13Atom1323 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1193
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19089 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1323 chi ∧
      ¬PredecessorHalfFin13Atom0410 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0410 PredecessorHalfFin13Atom1323 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1193
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19090 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1323 chi ∧
      ¬PredecessorHalfFin13Atom0459 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0459 PredecessorHalfFin13Atom1323 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1193
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19091 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1323 chi ∧
      ¬PredecessorHalfFin13Atom0828 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0828 PredecessorHalfFin13Atom1323 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1193
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19092 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1323 chi ∧
      PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0459 chi ∧
      PredecessorHalfFin13Atom0828 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0396 PredecessorHalfFin13Atom0399 PredecessorHalfFin13Atom0410
    PredecessorHalfFin13Atom0459 PredecessorHalfFin13Atom0828 PredecessorHalfFin13Atom1323 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1193
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19099 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1325 chi ∧
      ¬PredecessorHalfFin13Atom0396 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0396 PredecessorHalfFin13Atom1325 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4265
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19100 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1325 chi ∧
      ¬PredecessorHalfFin13Atom0401 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0401 PredecessorHalfFin13Atom1325 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4265
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19101 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1325 chi ∧
      ¬PredecessorHalfFin13Atom0412 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0412 PredecessorHalfFin13Atom1325 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4265
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19102 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1325 chi ∧
      ¬PredecessorHalfFin13Atom0461 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0461 PredecessorHalfFin13Atom1325 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4265
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19103 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1325 chi ∧
      ¬PredecessorHalfFin13Atom0830 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0830 PredecessorHalfFin13Atom1325 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4265
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19105 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1326 chi ∧
      ¬PredecessorHalfFin13Atom0397 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0397 PredecessorHalfFin13Atom1326 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0809
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19106 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1326 chi ∧
      ¬PredecessorHalfFin13Atom0398 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0398 PredecessorHalfFin13Atom1326 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0809
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19107 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1326 chi ∧
      ¬PredecessorHalfFin13Atom0413 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0413 PredecessorHalfFin13Atom1326 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0809
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19108 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1326 chi ∧
      ¬PredecessorHalfFin13Atom0462 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0462 PredecessorHalfFin13Atom1326 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0809
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19109 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1326 chi ∧
      ¬PredecessorHalfFin13Atom0831 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0831 PredecessorHalfFin13Atom1326 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0809
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19110 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1326 chi ∧
      PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0831 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0397 PredecessorHalfFin13Atom0398 PredecessorHalfFin13Atom0413
    PredecessorHalfFin13Atom0462 PredecessorHalfFin13Atom0831 PredecessorHalfFin13Atom1326 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0809
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19111 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1327 chi ∧
      ¬PredecessorHalfFin13Atom0397 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0397 PredecessorHalfFin13Atom1327 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1321
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19112 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1327 chi ∧
      ¬PredecessorHalfFin13Atom0399 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0399 PredecessorHalfFin13Atom1327 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1321
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19113 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1327 chi ∧
      ¬PredecessorHalfFin13Atom0414 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0414 PredecessorHalfFin13Atom1327 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1321
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19114 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1327 chi ∧
      ¬PredecessorHalfFin13Atom0463 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0463 PredecessorHalfFin13Atom1327 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1321
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19115 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1327 chi ∧
      ¬PredecessorHalfFin13Atom0832 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0832 PredecessorHalfFin13Atom1327 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1321
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19123 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1329 chi ∧
      ¬PredecessorHalfFin13Atom0397 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0397 PredecessorHalfFin13Atom1329 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4393
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19124 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1329 chi ∧
      ¬PredecessorHalfFin13Atom0401 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0401 PredecessorHalfFin13Atom1329 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4393
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19125 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1329 chi ∧
      ¬PredecessorHalfFin13Atom0416 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0416 PredecessorHalfFin13Atom1329 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4393
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19126 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1329 chi ∧
      ¬PredecessorHalfFin13Atom0465 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0465 PredecessorHalfFin13Atom1329 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4393
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19127 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1329 chi ∧
      ¬PredecessorHalfFin13Atom0834 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0834 PredecessorHalfFin13Atom1329 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4393
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19129 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1330 chi ∧
      ¬PredecessorHalfFin13Atom0398 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0398 PredecessorHalfFin13Atom1330 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1577
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19130 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1330 chi ∧
      ¬PredecessorHalfFin13Atom0399 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0399 PredecessorHalfFin13Atom1330 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1577
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19131 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1330 chi ∧
      ¬PredecessorHalfFin13Atom0417 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0417 PredecessorHalfFin13Atom1330 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1577
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19132 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1330 chi ∧
      ¬PredecessorHalfFin13Atom0466 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0466 PredecessorHalfFin13Atom1330 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1577
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19133 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1330 chi ∧
      ¬PredecessorHalfFin13Atom0835 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0835 PredecessorHalfFin13Atom1330 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1577
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19134 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1330 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0835 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0398 PredecessorHalfFin13Atom0399 PredecessorHalfFin13Atom0417
    PredecessorHalfFin13Atom0466 PredecessorHalfFin13Atom0835 PredecessorHalfFin13Atom1330 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1577
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19141 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1332 chi ∧
      ¬PredecessorHalfFin13Atom0398 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0398 PredecessorHalfFin13Atom1332 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4649
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19142 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1332 chi ∧
      ¬PredecessorHalfFin13Atom0401 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0401 PredecessorHalfFin13Atom1332 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4649
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19143 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1332 chi ∧
      ¬PredecessorHalfFin13Atom0419 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0419 PredecessorHalfFin13Atom1332 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4649
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19144 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1332 chi ∧
      ¬PredecessorHalfFin13Atom0468 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0468 PredecessorHalfFin13Atom1332 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4649
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19145 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1332 chi ∧
      ¬PredecessorHalfFin13Atom0837 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0837 PredecessorHalfFin13Atom1332 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4649
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19153 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1334 chi ∧
      ¬PredecessorHalfFin13Atom0399 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0399 PredecessorHalfFin13Atom1334 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5161
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19154 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1334 chi ∧
      ¬PredecessorHalfFin13Atom0401 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0401 PredecessorHalfFin13Atom1334 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5161
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19155 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1334 chi ∧
      ¬PredecessorHalfFin13Atom0421 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0421 PredecessorHalfFin13Atom1334 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5161
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19156 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1334 chi ∧
      ¬PredecessorHalfFin13Atom0470 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0470 PredecessorHalfFin13Atom1334 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5161
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19157 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1334 chi ∧
      ¬PredecessorHalfFin13Atom0839 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0839 PredecessorHalfFin13Atom1334 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5161
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19158 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1334 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0401 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0839 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0399 PredecessorHalfFin13Atom0401 PredecessorHalfFin13Atom0421
    PredecessorHalfFin13Atom0470 PredecessorHalfFin13Atom0839 PredecessorHalfFin13Atom1334 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5161
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19165 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1336 chi ∧
      ¬PredecessorHalfFin13Atom0402 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0402 PredecessorHalfFin13Atom1336 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0457
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19166 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1336 chi ∧
      ¬PredecessorHalfFin13Atom0403 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0403 PredecessorHalfFin13Atom1336 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0457
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19167 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1336 chi ∧
      ¬PredecessorHalfFin13Atom0408 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0408 PredecessorHalfFin13Atom1336 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0457
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19168 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1336 chi ∧
      ¬PredecessorHalfFin13Atom0472 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0472 PredecessorHalfFin13Atom1336 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0457
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19169 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1336 chi ∧
      ¬PredecessorHalfFin13Atom0841 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0841 PredecessorHalfFin13Atom1336 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0457
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19170 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1336 chi ∧
      PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0841 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0402 PredecessorHalfFin13Atom0403 PredecessorHalfFin13Atom0408
    PredecessorHalfFin13Atom0472 PredecessorHalfFin13Atom0841 PredecessorHalfFin13Atom1336 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0457
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19171 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1337 chi ∧
      ¬PredecessorHalfFin13Atom0402 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0402 PredecessorHalfFin13Atom1337 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0713
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19172 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1337 chi ∧
      ¬PredecessorHalfFin13Atom0404 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0404 PredecessorHalfFin13Atom1337 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0713
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19173 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1337 chi ∧
      ¬PredecessorHalfFin13Atom0409 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0409 PredecessorHalfFin13Atom1337 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0713
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19174 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1337 chi ∧
      ¬PredecessorHalfFin13Atom0473 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0473 PredecessorHalfFin13Atom1337 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0713
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19175 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1337 chi ∧
      ¬PredecessorHalfFin13Atom0842 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0842 PredecessorHalfFin13Atom1337 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0713
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19176 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1337 chi ∧
      PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0473 chi ∧
      PredecessorHalfFin13Atom0842 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0402 PredecessorHalfFin13Atom0404 PredecessorHalfFin13Atom0409
    PredecessorHalfFin13Atom0473 PredecessorHalfFin13Atom0842 PredecessorHalfFin13Atom1337 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0713
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19177 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1338 chi ∧
      ¬PredecessorHalfFin13Atom0402 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0402 PredecessorHalfFin13Atom1338 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1225
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19178 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1338 chi ∧
      ¬PredecessorHalfFin13Atom0405 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0405 PredecessorHalfFin13Atom1338 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1225
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19179 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1338 chi ∧
      ¬PredecessorHalfFin13Atom0410 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0410 PredecessorHalfFin13Atom1338 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1225
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19180 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1338 chi ∧
      ¬PredecessorHalfFin13Atom0474 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0474 PredecessorHalfFin13Atom1338 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1225
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19181 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1338 chi ∧
      ¬PredecessorHalfFin13Atom0843 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0843 PredecessorHalfFin13Atom1338 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1225
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19182 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1338 chi ∧
      PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0843 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0402 PredecessorHalfFin13Atom0405 PredecessorHalfFin13Atom0410
    PredecessorHalfFin13Atom0474 PredecessorHalfFin13Atom0843 PredecessorHalfFin13Atom1338 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1225
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19189 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1340 chi ∧
      ¬PredecessorHalfFin13Atom0402 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0402 PredecessorHalfFin13Atom1340 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4297
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19190 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1340 chi ∧
      ¬PredecessorHalfFin13Atom0407 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0407 PredecessorHalfFin13Atom1340 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4297
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19191 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1340 chi ∧
      ¬PredecessorHalfFin13Atom0412 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0412 PredecessorHalfFin13Atom1340 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4297
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19192 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1340 chi ∧
      ¬PredecessorHalfFin13Atom0476 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0476 PredecessorHalfFin13Atom1340 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4297
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19193 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1340 chi ∧
      ¬PredecessorHalfFin13Atom0845 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0845 PredecessorHalfFin13Atom1340 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4297
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19194 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1340 chi ∧
      PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0476 chi ∧
      PredecessorHalfFin13Atom0845 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0402 PredecessorHalfFin13Atom0407 PredecessorHalfFin13Atom0412
    PredecessorHalfFin13Atom0476 PredecessorHalfFin13Atom0845 PredecessorHalfFin13Atom1340 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4297
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19195 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1341 chi ∧
      ¬PredecessorHalfFin13Atom0403 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0403 PredecessorHalfFin13Atom1341 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0841
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19196 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1341 chi ∧
      ¬PredecessorHalfFin13Atom0404 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0404 PredecessorHalfFin13Atom1341 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0841
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19197 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1341 chi ∧
      ¬PredecessorHalfFin13Atom0413 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0413 PredecessorHalfFin13Atom1341 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0841
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19198 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1341 chi ∧
      ¬PredecessorHalfFin13Atom0477 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0477 PredecessorHalfFin13Atom1341 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0841
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19199 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1341 chi ∧
      ¬PredecessorHalfFin13Atom0846 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0846 PredecessorHalfFin13Atom1341 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0841
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19200 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1341 chi ∧
      PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0846 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0403 PredecessorHalfFin13Atom0404 PredecessorHalfFin13Atom0413
    PredecessorHalfFin13Atom0477 PredecessorHalfFin13Atom0846 PredecessorHalfFin13Atom1341 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0841
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19201 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1342 chi ∧
      ¬PredecessorHalfFin13Atom0403 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0403 PredecessorHalfFin13Atom1342 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1353
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19202 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1342 chi ∧
      ¬PredecessorHalfFin13Atom0405 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0405 PredecessorHalfFin13Atom1342 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1353
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19203 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1342 chi ∧
      ¬PredecessorHalfFin13Atom0414 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0414 PredecessorHalfFin13Atom1342 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1353
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19204 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1342 chi ∧
      ¬PredecessorHalfFin13Atom0478 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0478 PredecessorHalfFin13Atom1342 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1353
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19205 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1342 chi ∧
      ¬PredecessorHalfFin13Atom0847 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0847 PredecessorHalfFin13Atom1342 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1353
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19206 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1342 chi ∧
      PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0847 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0403 PredecessorHalfFin13Atom0405 PredecessorHalfFin13Atom0414
    PredecessorHalfFin13Atom0478 PredecessorHalfFin13Atom0847 PredecessorHalfFin13Atom1342 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1353
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19213 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1344 chi ∧
      ¬PredecessorHalfFin13Atom0403 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0403 PredecessorHalfFin13Atom1344 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4425
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19214 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1344 chi ∧
      ¬PredecessorHalfFin13Atom0407 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0407 PredecessorHalfFin13Atom1344 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4425
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19215 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1344 chi ∧
      ¬PredecessorHalfFin13Atom0416 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0416 PredecessorHalfFin13Atom1344 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4425
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19216 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1344 chi ∧
      ¬PredecessorHalfFin13Atom0480 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0480 PredecessorHalfFin13Atom1344 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4425
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19217 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1344 chi ∧
      ¬PredecessorHalfFin13Atom0849 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0849 PredecessorHalfFin13Atom1344 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4425
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19218 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1344 chi ∧
      PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0849 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0403 PredecessorHalfFin13Atom0407 PredecessorHalfFin13Atom0416
    PredecessorHalfFin13Atom0480 PredecessorHalfFin13Atom0849 PredecessorHalfFin13Atom1344 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4425
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19219 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1345 chi ∧
      ¬PredecessorHalfFin13Atom0404 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0404 PredecessorHalfFin13Atom1345 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1609
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19220 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1345 chi ∧
      ¬PredecessorHalfFin13Atom0405 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0405 PredecessorHalfFin13Atom1345 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1609
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19221 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1345 chi ∧
      ¬PredecessorHalfFin13Atom0417 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0417 PredecessorHalfFin13Atom1345 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1609
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19222 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1345 chi ∧
      ¬PredecessorHalfFin13Atom0481 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0481 PredecessorHalfFin13Atom1345 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1609
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19223 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1345 chi ∧
      ¬PredecessorHalfFin13Atom0850 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0850 PredecessorHalfFin13Atom1345 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1609
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19224 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1345 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0850 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0404 PredecessorHalfFin13Atom0405 PredecessorHalfFin13Atom0417
    PredecessorHalfFin13Atom0481 PredecessorHalfFin13Atom0850 PredecessorHalfFin13Atom1345 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1609
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19231 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1347 chi ∧
      ¬PredecessorHalfFin13Atom0404 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0404 PredecessorHalfFin13Atom1347 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4681
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19232 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1347 chi ∧
      ¬PredecessorHalfFin13Atom0407 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0407 PredecessorHalfFin13Atom1347 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4681
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19233 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1347 chi ∧
      ¬PredecessorHalfFin13Atom0419 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0419 PredecessorHalfFin13Atom1347 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4681
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19234 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1347 chi ∧
      ¬PredecessorHalfFin13Atom0483 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0483 PredecessorHalfFin13Atom1347 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4681
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19235 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1347 chi ∧
      ¬PredecessorHalfFin13Atom0852 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0852 PredecessorHalfFin13Atom1347 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4681
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19236 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1347 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0852 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0404 PredecessorHalfFin13Atom0407 PredecessorHalfFin13Atom0419
    PredecessorHalfFin13Atom0483 PredecessorHalfFin13Atom0852 PredecessorHalfFin13Atom1347 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4681
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19243 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1349 chi ∧
      ¬PredecessorHalfFin13Atom0405 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0405 PredecessorHalfFin13Atom1349 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5193
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19244 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1349 chi ∧
      ¬PredecessorHalfFin13Atom0407 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0407 PredecessorHalfFin13Atom1349 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5193
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19245 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1349 chi ∧
      ¬PredecessorHalfFin13Atom0421 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0421 PredecessorHalfFin13Atom1349 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5193
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19246 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1349 chi ∧
      ¬PredecessorHalfFin13Atom0485 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0485 PredecessorHalfFin13Atom1349 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5193
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19247 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1349 chi ∧
      ¬PredecessorHalfFin13Atom0854 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0854 PredecessorHalfFin13Atom1349 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5193
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19248 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1349 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0854 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0405 PredecessorHalfFin13Atom0407 PredecessorHalfFin13Atom0421
    PredecessorHalfFin13Atom0485 PredecessorHalfFin13Atom0854 PredecessorHalfFin13Atom1349 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5193
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19255 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1351 chi ∧
      ¬PredecessorHalfFin13Atom0408 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0408 PredecessorHalfFin13Atom1351 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0905
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19256 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1351 chi ∧
      ¬PredecessorHalfFin13Atom0409 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0409 PredecessorHalfFin13Atom1351 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0905
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19257 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1351 chi ∧
      ¬PredecessorHalfFin13Atom0413 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0413 PredecessorHalfFin13Atom1351 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0905
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19258 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1351 chi ∧
      ¬PredecessorHalfFin13Atom0487 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0487 PredecessorHalfFin13Atom1351 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0905
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19259 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1351 chi ∧
      ¬PredecessorHalfFin13Atom0856 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0856 PredecessorHalfFin13Atom1351 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0905
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19260 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1351 chi ∧
      PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0856 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0408 PredecessorHalfFin13Atom0409 PredecessorHalfFin13Atom0413
    PredecessorHalfFin13Atom0487 PredecessorHalfFin13Atom0856 PredecessorHalfFin13Atom1351 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0905
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19261 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1352 chi ∧
      ¬PredecessorHalfFin13Atom0408 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0408 PredecessorHalfFin13Atom1352 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1417
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19262 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1352 chi ∧
      ¬PredecessorHalfFin13Atom0410 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0410 PredecessorHalfFin13Atom1352 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1417
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19263 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1352 chi ∧
      ¬PredecessorHalfFin13Atom0414 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0414 PredecessorHalfFin13Atom1352 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1417
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19264 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1352 chi ∧
      ¬PredecessorHalfFin13Atom0488 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0488 PredecessorHalfFin13Atom1352 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1417
  ] at hbad
  tauto

end ErdosSzekeres

end
