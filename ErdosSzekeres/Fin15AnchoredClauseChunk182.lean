module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 182. -/

theorem fin15Anchored_clause23296 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3536 chi ∧
      ¬Fin15AnchoredAtom1105 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1105 Fin15AnchoredAtom3536 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask30722
  ] at hbad
  tauto

theorem fin15Anchored_clause23297 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom1106 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1106 Fin15AnchoredAtom3537 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00124
  ] at hbad
  tauto

theorem fin15Anchored_clause23298 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom1107 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1107 Fin15AnchoredAtom3537 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00124
  ] at hbad
  tauto

theorem fin15Anchored_clause23299 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom1116 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1116 Fin15AnchoredAtom3537 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00124
  ] at hbad
  tauto

theorem fin15Anchored_clause23300 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom1161 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1161 Fin15AnchoredAtom3537 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00124
  ] at hbad
  tauto

theorem fin15Anchored_clause23301 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom1326 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1326 Fin15AnchoredAtom3537 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00124
  ] at hbad
  tauto

theorem fin15Anchored_clause23302 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3537 chi ∧
      Fin15AnchoredAtom1106 chi ∧
      Fin15AnchoredAtom1107 chi ∧
      Fin15AnchoredAtom1116 chi ∧
      Fin15AnchoredAtom1161 chi ∧
      Fin15AnchoredAtom1326 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1106 Fin15AnchoredAtom1107 Fin15AnchoredAtom1116
    Fin15AnchoredAtom1161 Fin15AnchoredAtom1326 Fin15AnchoredAtom3537 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00124
  ] at hbad
  tauto

theorem fin15Anchored_clause23303 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom1106 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1106 Fin15AnchoredAtom3538 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00188
  ] at hbad
  tauto

theorem fin15Anchored_clause23304 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom1108 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1108 Fin15AnchoredAtom3538 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00188
  ] at hbad
  tauto

theorem fin15Anchored_clause23305 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom1117 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1117 Fin15AnchoredAtom3538 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00188
  ] at hbad
  tauto

theorem fin15Anchored_clause23306 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom1162 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1162 Fin15AnchoredAtom3538 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00188
  ] at hbad
  tauto

theorem fin15Anchored_clause23307 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom1327 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1327 Fin15AnchoredAtom3538 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00188
  ] at hbad
  tauto

theorem fin15Anchored_clause23308 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3538 chi ∧
      Fin15AnchoredAtom1106 chi ∧
      Fin15AnchoredAtom1108 chi ∧
      Fin15AnchoredAtom1117 chi ∧
      Fin15AnchoredAtom1162 chi ∧
      Fin15AnchoredAtom1327 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1106 Fin15AnchoredAtom1108 Fin15AnchoredAtom1117
    Fin15AnchoredAtom1162 Fin15AnchoredAtom1327 Fin15AnchoredAtom3538 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00188
  ] at hbad
  tauto

theorem fin15Anchored_clause23309 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3539 chi ∧
      ¬Fin15AnchoredAtom1328 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1328 Fin15AnchoredAtom3539 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00316
  ] at hbad
  tauto

theorem fin15Anchored_clause23310 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom1106 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1106 Fin15AnchoredAtom3540 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00572
  ] at hbad
  tauto

theorem fin15Anchored_clause23311 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom1110 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1110 Fin15AnchoredAtom3540 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00572
  ] at hbad
  tauto

theorem fin15Anchored_clause23312 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom1119 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1119 Fin15AnchoredAtom3540 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00572
  ] at hbad
  tauto

theorem fin15Anchored_clause23313 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom1164 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1164 Fin15AnchoredAtom3540 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00572
  ] at hbad
  tauto

theorem fin15Anchored_clause23314 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom1329 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1329 Fin15AnchoredAtom3540 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00572
  ] at hbad
  tauto

theorem fin15Anchored_clause23315 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3540 chi ∧
      Fin15AnchoredAtom1106 chi ∧
      Fin15AnchoredAtom1110 chi ∧
      Fin15AnchoredAtom1119 chi ∧
      Fin15AnchoredAtom1164 chi ∧
      Fin15AnchoredAtom1329 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1106 Fin15AnchoredAtom1110 Fin15AnchoredAtom1119
    Fin15AnchoredAtom1164 Fin15AnchoredAtom1329 Fin15AnchoredAtom3540 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00572
  ] at hbad
  tauto

theorem fin15Anchored_clause23316 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom1106 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1106 Fin15AnchoredAtom3541 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01084
  ] at hbad
  tauto

theorem fin15Anchored_clause23317 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom1111 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1111 Fin15AnchoredAtom3541 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01084
  ] at hbad
  tauto

theorem fin15Anchored_clause23318 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom1120 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1120 Fin15AnchoredAtom3541 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01084
  ] at hbad
  tauto

theorem fin15Anchored_clause23319 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom1165 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1165 Fin15AnchoredAtom3541 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01084
  ] at hbad
  tauto

theorem fin15Anchored_clause23320 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom1330 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1330 Fin15AnchoredAtom3541 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01084
  ] at hbad
  tauto

theorem fin15Anchored_clause23321 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3541 chi ∧
      Fin15AnchoredAtom1106 chi ∧
      Fin15AnchoredAtom1111 chi ∧
      Fin15AnchoredAtom1120 chi ∧
      Fin15AnchoredAtom1165 chi ∧
      Fin15AnchoredAtom1330 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1106 Fin15AnchoredAtom1111 Fin15AnchoredAtom1120
    Fin15AnchoredAtom1165 Fin15AnchoredAtom1330 Fin15AnchoredAtom3541 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01084
  ] at hbad
  tauto

theorem fin15Anchored_clause23322 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3542 chi ∧
      ¬Fin15AnchoredAtom1106 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1106 Fin15AnchoredAtom3542 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02108
  ] at hbad
  tauto

theorem fin15Anchored_clause23323 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3542 chi ∧
      ¬Fin15AnchoredAtom1112 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1112 Fin15AnchoredAtom3542 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02108
  ] at hbad
  tauto

theorem fin15Anchored_clause23324 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3542 chi ∧
      ¬Fin15AnchoredAtom1166 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1166 Fin15AnchoredAtom3542 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02108
  ] at hbad
  tauto

theorem fin15Anchored_clause23325 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3542 chi ∧
      ¬Fin15AnchoredAtom1331 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1331 Fin15AnchoredAtom3542 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02108
  ] at hbad
  tauto

theorem fin15Anchored_clause23326 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3542 chi ∧
      Fin15AnchoredAtom1106 chi ∧
      Fin15AnchoredAtom1112 chi ∧
      Fin15AnchoredAtom1121 chi ∧
      Fin15AnchoredAtom1166 chi ∧
      Fin15AnchoredAtom1331 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1106 Fin15AnchoredAtom1112 Fin15AnchoredAtom1121
    Fin15AnchoredAtom1166 Fin15AnchoredAtom1331 Fin15AnchoredAtom3542 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02108
  ] at hbad
  tauto

theorem fin15Anchored_clause23327 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom1106 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1106 Fin15AnchoredAtom3543 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04156
  ] at hbad
  tauto

theorem fin15Anchored_clause23328 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom1113 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1113 Fin15AnchoredAtom3543 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04156
  ] at hbad
  tauto

theorem fin15Anchored_clause23329 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom1122 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1122 Fin15AnchoredAtom3543 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04156
  ] at hbad
  tauto

theorem fin15Anchored_clause23330 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom1167 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1167 Fin15AnchoredAtom3543 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04156
  ] at hbad
  tauto

theorem fin15Anchored_clause23331 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom1332 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1332 Fin15AnchoredAtom3543 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04156
  ] at hbad
  tauto

theorem fin15Anchored_clause23332 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3543 chi ∧
      Fin15AnchoredAtom1106 chi ∧
      Fin15AnchoredAtom1113 chi ∧
      Fin15AnchoredAtom1122 chi ∧
      Fin15AnchoredAtom1167 chi ∧
      Fin15AnchoredAtom1332 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1106 Fin15AnchoredAtom1113 Fin15AnchoredAtom1122
    Fin15AnchoredAtom1167 Fin15AnchoredAtom1332 Fin15AnchoredAtom3543 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04156
  ] at hbad
  tauto

theorem fin15Anchored_clause23333 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom1106 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1106 Fin15AnchoredAtom3544 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08252
  ] at hbad
  tauto

theorem fin15Anchored_clause23334 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom1114 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1114 Fin15AnchoredAtom3544 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08252
  ] at hbad
  tauto

theorem fin15Anchored_clause23335 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom1123 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1123 Fin15AnchoredAtom3544 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08252
  ] at hbad
  tauto

theorem fin15Anchored_clause23336 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom1168 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1168 Fin15AnchoredAtom3544 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08252
  ] at hbad
  tauto

theorem fin15Anchored_clause23337 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom1333 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1333 Fin15AnchoredAtom3544 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08252
  ] at hbad
  tauto

theorem fin15Anchored_clause23338 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3544 chi ∧
      Fin15AnchoredAtom1106 chi ∧
      Fin15AnchoredAtom1114 chi ∧
      Fin15AnchoredAtom1123 chi ∧
      Fin15AnchoredAtom1168 chi ∧
      Fin15AnchoredAtom1333 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1106 Fin15AnchoredAtom1114 Fin15AnchoredAtom1123
    Fin15AnchoredAtom1168 Fin15AnchoredAtom1333 Fin15AnchoredAtom3544 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08252
  ] at hbad
  tauto

theorem fin15Anchored_clause23339 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom1106 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1106 Fin15AnchoredAtom3545 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16444
  ] at hbad
  tauto

theorem fin15Anchored_clause23340 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom1115 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1115 Fin15AnchoredAtom3545 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16444
  ] at hbad
  tauto

theorem fin15Anchored_clause23341 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom1124 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1124 Fin15AnchoredAtom3545 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16444
  ] at hbad
  tauto

theorem fin15Anchored_clause23342 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom1169 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1169 Fin15AnchoredAtom3545 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16444
  ] at hbad
  tauto

theorem fin15Anchored_clause23343 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom1334 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1334 Fin15AnchoredAtom3545 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16444
  ] at hbad
  tauto

theorem fin15Anchored_clause23344 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3545 chi ∧
      Fin15AnchoredAtom1106 chi ∧
      Fin15AnchoredAtom1115 chi ∧
      Fin15AnchoredAtom1124 chi ∧
      Fin15AnchoredAtom1169 chi ∧
      Fin15AnchoredAtom1334 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1106 Fin15AnchoredAtom1115 Fin15AnchoredAtom1124
    Fin15AnchoredAtom1169 Fin15AnchoredAtom1334 Fin15AnchoredAtom3545 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16444
  ] at hbad
  tauto

theorem fin15Anchored_clause23345 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom1107 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1107 Fin15AnchoredAtom3546 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00220
  ] at hbad
  tauto

theorem fin15Anchored_clause23346 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom1108 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1108 Fin15AnchoredAtom3546 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00220
  ] at hbad
  tauto

theorem fin15Anchored_clause23347 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom1125 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1125 Fin15AnchoredAtom3546 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00220
  ] at hbad
  tauto

theorem fin15Anchored_clause23348 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom1170 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1170 Fin15AnchoredAtom3546 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00220
  ] at hbad
  tauto

theorem fin15Anchored_clause23349 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom1335 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1335 Fin15AnchoredAtom3546 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00220
  ] at hbad
  tauto

theorem fin15Anchored_clause23350 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3546 chi ∧
      Fin15AnchoredAtom1107 chi ∧
      Fin15AnchoredAtom1108 chi ∧
      Fin15AnchoredAtom1125 chi ∧
      Fin15AnchoredAtom1170 chi ∧
      Fin15AnchoredAtom1335 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1107 Fin15AnchoredAtom1108 Fin15AnchoredAtom1125
    Fin15AnchoredAtom1170 Fin15AnchoredAtom1335 Fin15AnchoredAtom3546 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00220
  ] at hbad
  tauto

theorem fin15Anchored_clause23351 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3547 chi ∧
      ¬Fin15AnchoredAtom1107 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1107 Fin15AnchoredAtom3547 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00348
  ] at hbad
  tauto

theorem fin15Anchored_clause23352 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3547 chi ∧
      ¬Fin15AnchoredAtom1336 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1336 Fin15AnchoredAtom3547 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00348
  ] at hbad
  tauto

theorem fin15Anchored_clause23353 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom1107 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1107 Fin15AnchoredAtom3548 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00604
  ] at hbad
  tauto

theorem fin15Anchored_clause23354 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom1110 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1110 Fin15AnchoredAtom3548 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00604
  ] at hbad
  tauto

theorem fin15Anchored_clause23355 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom1127 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1127 Fin15AnchoredAtom3548 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00604
  ] at hbad
  tauto

theorem fin15Anchored_clause23356 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom1172 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1172 Fin15AnchoredAtom3548 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00604
  ] at hbad
  tauto

theorem fin15Anchored_clause23357 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom1337 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1337 Fin15AnchoredAtom3548 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00604
  ] at hbad
  tauto

theorem fin15Anchored_clause23358 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3548 chi ∧
      Fin15AnchoredAtom1107 chi ∧
      Fin15AnchoredAtom1110 chi ∧
      Fin15AnchoredAtom1127 chi ∧
      Fin15AnchoredAtom1172 chi ∧
      Fin15AnchoredAtom1337 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1107 Fin15AnchoredAtom1110 Fin15AnchoredAtom1127
    Fin15AnchoredAtom1172 Fin15AnchoredAtom1337 Fin15AnchoredAtom3548 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00604
  ] at hbad
  tauto

theorem fin15Anchored_clause23359 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom1107 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1107 Fin15AnchoredAtom3549 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01116
  ] at hbad
  tauto

theorem fin15Anchored_clause23360 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom1111 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1111 Fin15AnchoredAtom3549 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01116
  ] at hbad
  tauto

theorem fin15Anchored_clause23361 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom1128 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1128 Fin15AnchoredAtom3549 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01116
  ] at hbad
  tauto

theorem fin15Anchored_clause23362 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom1173 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1173 Fin15AnchoredAtom3549 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01116
  ] at hbad
  tauto

theorem fin15Anchored_clause23363 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom1338 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1338 Fin15AnchoredAtom3549 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01116
  ] at hbad
  tauto

theorem fin15Anchored_clause23364 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3549 chi ∧
      Fin15AnchoredAtom1107 chi ∧
      Fin15AnchoredAtom1111 chi ∧
      Fin15AnchoredAtom1128 chi ∧
      Fin15AnchoredAtom1173 chi ∧
      Fin15AnchoredAtom1338 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1107 Fin15AnchoredAtom1111 Fin15AnchoredAtom1128
    Fin15AnchoredAtom1173 Fin15AnchoredAtom1338 Fin15AnchoredAtom3549 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01116
  ] at hbad
  tauto

theorem fin15Anchored_clause23365 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3550 chi ∧
      ¬Fin15AnchoredAtom1107 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1107 Fin15AnchoredAtom3550 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02140
  ] at hbad
  tauto

theorem fin15Anchored_clause23366 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom1107 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1107 Fin15AnchoredAtom3551 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04188
  ] at hbad
  tauto

theorem fin15Anchored_clause23367 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom1113 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1113 Fin15AnchoredAtom3551 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04188
  ] at hbad
  tauto

theorem fin15Anchored_clause23368 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom1130 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1130 Fin15AnchoredAtom3551 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04188
  ] at hbad
  tauto

theorem fin15Anchored_clause23369 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom1175 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1175 Fin15AnchoredAtom3551 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04188
  ] at hbad
  tauto

theorem fin15Anchored_clause23370 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom1340 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1340 Fin15AnchoredAtom3551 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04188
  ] at hbad
  tauto

theorem fin15Anchored_clause23371 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3551 chi ∧
      Fin15AnchoredAtom1107 chi ∧
      Fin15AnchoredAtom1113 chi ∧
      Fin15AnchoredAtom1130 chi ∧
      Fin15AnchoredAtom1175 chi ∧
      Fin15AnchoredAtom1340 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1107 Fin15AnchoredAtom1113 Fin15AnchoredAtom1130
    Fin15AnchoredAtom1175 Fin15AnchoredAtom1340 Fin15AnchoredAtom3551 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04188
  ] at hbad
  tauto

theorem fin15Anchored_clause23372 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom1107 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1107 Fin15AnchoredAtom3552 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08284
  ] at hbad
  tauto

theorem fin15Anchored_clause23373 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom1114 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1114 Fin15AnchoredAtom3552 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08284
  ] at hbad
  tauto

theorem fin15Anchored_clause23374 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom1131 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1131 Fin15AnchoredAtom3552 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08284
  ] at hbad
  tauto

theorem fin15Anchored_clause23375 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom1176 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1176 Fin15AnchoredAtom3552 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08284
  ] at hbad
  tauto

theorem fin15Anchored_clause23376 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom1341 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1341 Fin15AnchoredAtom3552 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08284
  ] at hbad
  tauto

theorem fin15Anchored_clause23377 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3552 chi ∧
      Fin15AnchoredAtom1107 chi ∧
      Fin15AnchoredAtom1114 chi ∧
      Fin15AnchoredAtom1131 chi ∧
      Fin15AnchoredAtom1176 chi ∧
      Fin15AnchoredAtom1341 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1107 Fin15AnchoredAtom1114 Fin15AnchoredAtom1131
    Fin15AnchoredAtom1176 Fin15AnchoredAtom1341 Fin15AnchoredAtom3552 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08284
  ] at hbad
  tauto

theorem fin15Anchored_clause23378 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom1107 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1107 Fin15AnchoredAtom3553 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16476
  ] at hbad
  tauto

theorem fin15Anchored_clause23379 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom1115 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1115 Fin15AnchoredAtom3553 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16476
  ] at hbad
  tauto

theorem fin15Anchored_clause23380 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom1132 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1132 Fin15AnchoredAtom3553 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16476
  ] at hbad
  tauto

theorem fin15Anchored_clause23381 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom1177 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1177 Fin15AnchoredAtom3553 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16476
  ] at hbad
  tauto

theorem fin15Anchored_clause23382 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom1342 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1342 Fin15AnchoredAtom3553 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16476
  ] at hbad
  tauto

theorem fin15Anchored_clause23383 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3553 chi ∧
      Fin15AnchoredAtom1107 chi ∧
      Fin15AnchoredAtom1115 chi ∧
      Fin15AnchoredAtom1132 chi ∧
      Fin15AnchoredAtom1177 chi ∧
      Fin15AnchoredAtom1342 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1107 Fin15AnchoredAtom1115 Fin15AnchoredAtom1132
    Fin15AnchoredAtom1177 Fin15AnchoredAtom1342 Fin15AnchoredAtom3553 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16476
  ] at hbad
  tauto

theorem fin15Anchored_clause23384 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3554 chi ∧
      ¬Fin15AnchoredAtom1108 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1108 Fin15AnchoredAtom3554 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00412
  ] at hbad
  tauto

theorem fin15Anchored_clause23385 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3554 chi ∧
      Fin15AnchoredAtom1108 chi ∧
      Fin15AnchoredAtom1109 chi ∧
      Fin15AnchoredAtom1133 chi ∧
      Fin15AnchoredAtom1178 chi ∧
      Fin15AnchoredAtom1343 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1108 Fin15AnchoredAtom1109 Fin15AnchoredAtom1133
    Fin15AnchoredAtom1178 Fin15AnchoredAtom1343 Fin15AnchoredAtom3554 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00412
  ] at hbad
  tauto

theorem fin15Anchored_clause23386 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom1108 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1108 Fin15AnchoredAtom3555 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00668
  ] at hbad
  tauto

theorem fin15Anchored_clause23387 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom1110 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1110 Fin15AnchoredAtom3555 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00668
  ] at hbad
  tauto

theorem fin15Anchored_clause23388 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom1134 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1134 Fin15AnchoredAtom3555 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00668
  ] at hbad
  tauto

theorem fin15Anchored_clause23389 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom1179 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1179 Fin15AnchoredAtom3555 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00668
  ] at hbad
  tauto

theorem fin15Anchored_clause23390 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom1344 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1344 Fin15AnchoredAtom3555 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00668
  ] at hbad
  tauto

theorem fin15Anchored_clause23391 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3555 chi ∧
      Fin15AnchoredAtom1108 chi ∧
      Fin15AnchoredAtom1110 chi ∧
      Fin15AnchoredAtom1134 chi ∧
      Fin15AnchoredAtom1179 chi ∧
      Fin15AnchoredAtom1344 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1108 Fin15AnchoredAtom1110 Fin15AnchoredAtom1134
    Fin15AnchoredAtom1179 Fin15AnchoredAtom1344 Fin15AnchoredAtom3555 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00668
  ] at hbad
  tauto

theorem fin15Anchored_clause23392 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom1108 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1108 Fin15AnchoredAtom3556 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01180
  ] at hbad
  tauto

theorem fin15Anchored_clause23393 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom1111 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1111 Fin15AnchoredAtom3556 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01180
  ] at hbad
  tauto

theorem fin15Anchored_clause23394 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom1135 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1135 Fin15AnchoredAtom3556 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01180
  ] at hbad
  tauto

theorem fin15Anchored_clause23395 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom1180 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1180 Fin15AnchoredAtom3556 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01180
  ] at hbad
  tauto

theorem fin15Anchored_clause23396 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom1345 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1345 Fin15AnchoredAtom3556 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01180
  ] at hbad
  tauto

theorem fin15Anchored_clause23397 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3556 chi ∧
      Fin15AnchoredAtom1108 chi ∧
      Fin15AnchoredAtom1111 chi ∧
      Fin15AnchoredAtom1135 chi ∧
      Fin15AnchoredAtom1180 chi ∧
      Fin15AnchoredAtom1345 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1108 Fin15AnchoredAtom1111 Fin15AnchoredAtom1135
    Fin15AnchoredAtom1180 Fin15AnchoredAtom1345 Fin15AnchoredAtom3556 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01180
  ] at hbad
  tauto

theorem fin15Anchored_clause23398 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3557 chi ∧
      ¬Fin15AnchoredAtom1108 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1108 Fin15AnchoredAtom3557 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02204
  ] at hbad
  tauto

theorem fin15Anchored_clause23399 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3557 chi ∧
      Fin15AnchoredAtom1108 chi ∧
      Fin15AnchoredAtom1112 chi ∧
      Fin15AnchoredAtom1136 chi ∧
      Fin15AnchoredAtom1181 chi ∧
      Fin15AnchoredAtom1346 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1108 Fin15AnchoredAtom1112 Fin15AnchoredAtom1136
    Fin15AnchoredAtom1181 Fin15AnchoredAtom1346 Fin15AnchoredAtom3557 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02204
  ] at hbad
  tauto

theorem fin15Anchored_clause23400 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom1108 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1108 Fin15AnchoredAtom3558 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04252
  ] at hbad
  tauto

theorem fin15Anchored_clause23401 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom1113 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1113 Fin15AnchoredAtom3558 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04252
  ] at hbad
  tauto

theorem fin15Anchored_clause23402 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom1137 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1137 Fin15AnchoredAtom3558 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04252
  ] at hbad
  tauto

theorem fin15Anchored_clause23403 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom1182 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1182 Fin15AnchoredAtom3558 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04252
  ] at hbad
  tauto

theorem fin15Anchored_clause23404 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom1347 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1347 Fin15AnchoredAtom3558 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04252
  ] at hbad
  tauto

theorem fin15Anchored_clause23405 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3558 chi ∧
      Fin15AnchoredAtom1108 chi ∧
      Fin15AnchoredAtom1113 chi ∧
      Fin15AnchoredAtom1137 chi ∧
      Fin15AnchoredAtom1182 chi ∧
      Fin15AnchoredAtom1347 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1108 Fin15AnchoredAtom1113 Fin15AnchoredAtom1137
    Fin15AnchoredAtom1182 Fin15AnchoredAtom1347 Fin15AnchoredAtom3558 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04252
  ] at hbad
  tauto

theorem fin15Anchored_clause23406 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom1108 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1108 Fin15AnchoredAtom3559 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08348
  ] at hbad
  tauto

theorem fin15Anchored_clause23407 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom1114 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1114 Fin15AnchoredAtom3559 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08348
  ] at hbad
  tauto

theorem fin15Anchored_clause23408 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom1138 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1138 Fin15AnchoredAtom3559 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08348
  ] at hbad
  tauto

theorem fin15Anchored_clause23409 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom1183 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1183 Fin15AnchoredAtom3559 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08348
  ] at hbad
  tauto

theorem fin15Anchored_clause23410 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom1348 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1348 Fin15AnchoredAtom3559 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08348
  ] at hbad
  tauto

theorem fin15Anchored_clause23411 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3559 chi ∧
      Fin15AnchoredAtom1108 chi ∧
      Fin15AnchoredAtom1114 chi ∧
      Fin15AnchoredAtom1138 chi ∧
      Fin15AnchoredAtom1183 chi ∧
      Fin15AnchoredAtom1348 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1108 Fin15AnchoredAtom1114 Fin15AnchoredAtom1138
    Fin15AnchoredAtom1183 Fin15AnchoredAtom1348 Fin15AnchoredAtom3559 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08348
  ] at hbad
  tauto

theorem fin15Anchored_clause23412 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom1108 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1108 Fin15AnchoredAtom3560 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16540
  ] at hbad
  tauto

theorem fin15Anchored_clause23413 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom1115 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1115 Fin15AnchoredAtom3560 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16540
  ] at hbad
  tauto

theorem fin15Anchored_clause23414 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom1139 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1139 Fin15AnchoredAtom3560 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16540
  ] at hbad
  tauto

theorem fin15Anchored_clause23415 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom1184 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1184 Fin15AnchoredAtom3560 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16540
  ] at hbad
  tauto

theorem fin15Anchored_clause23416 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom1349 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1349 Fin15AnchoredAtom3560 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16540
  ] at hbad
  tauto

theorem fin15Anchored_clause23417 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3560 chi ∧
      Fin15AnchoredAtom1108 chi ∧
      Fin15AnchoredAtom1115 chi ∧
      Fin15AnchoredAtom1139 chi ∧
      Fin15AnchoredAtom1184 chi ∧
      Fin15AnchoredAtom1349 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1108 Fin15AnchoredAtom1115 Fin15AnchoredAtom1139
    Fin15AnchoredAtom1184 Fin15AnchoredAtom1349 Fin15AnchoredAtom3560 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16540
  ] at hbad
  tauto

theorem fin15Anchored_clause23418 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3561 chi ∧
      Fin15AnchoredAtom1109 chi ∧
      Fin15AnchoredAtom1110 chi ∧
      Fin15AnchoredAtom1140 chi ∧
      Fin15AnchoredAtom1185 chi ∧
      Fin15AnchoredAtom1350 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1109 Fin15AnchoredAtom1110 Fin15AnchoredAtom1140
    Fin15AnchoredAtom1185 Fin15AnchoredAtom1350 Fin15AnchoredAtom3561 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00796
  ] at hbad
  tauto

theorem fin15Anchored_clause23419 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3562 chi ∧
      Fin15AnchoredAtom1109 chi ∧
      Fin15AnchoredAtom1111 chi ∧
      Fin15AnchoredAtom1141 chi ∧
      Fin15AnchoredAtom1186 chi ∧
      Fin15AnchoredAtom1351 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1109 Fin15AnchoredAtom1111 Fin15AnchoredAtom1141
    Fin15AnchoredAtom1186 Fin15AnchoredAtom1351 Fin15AnchoredAtom3562 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01308
  ] at hbad
  tauto

theorem fin15Anchored_clause23420 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3565 chi ∧
      ¬Fin15AnchoredAtom1144 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1144 Fin15AnchoredAtom3565 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08476
  ] at hbad
  tauto

theorem fin15Anchored_clause23421 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3566 chi ∧
      ¬Fin15AnchoredAtom1115 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1115 Fin15AnchoredAtom3566 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16668
  ] at hbad
  tauto

theorem fin15Anchored_clause23422 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom1110 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1110 Fin15AnchoredAtom3567 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01564
  ] at hbad
  tauto

theorem fin15Anchored_clause23423 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom1111 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1111 Fin15AnchoredAtom3567 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01564
  ] at hbad
  tauto

end ErdosSzekeres

end
