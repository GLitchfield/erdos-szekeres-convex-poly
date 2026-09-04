module

public import ErdosSzekeres.Fin15AnchoredClauseChunk183
public import ErdosSzekeres.Fin15AnchoredClauseChunk184
public import ErdosSzekeres.Fin15AnchoredClauseChunk185

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 093. -/

theorem fin15Anchored_rejectSemanticSegment093
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom3577 chi ∧
      ¬Fin15AnchoredAtom1114 chi) ∨
      ((Fin15AnchoredAtom3578 chi ∧
      ¬Fin15AnchoredAtom1115 chi) ∨
      (Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom1113 chi))) ∨
      (((Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom1114 chi) ∨
      (Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom1158 chi)) ∨
      ((Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom1203 chi) ∨
      (Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom1368 chi)))) ∨
      ((((¬Fin15AnchoredAtom3579 chi ∧
      Fin15AnchoredAtom1113 chi ∧
      Fin15AnchoredAtom1114 chi ∧
      Fin15AnchoredAtom1158 chi ∧
      Fin15AnchoredAtom1203 chi ∧
      Fin15AnchoredAtom1368 chi) ∨
      (Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom1113 chi)) ∨
      ((Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom1115 chi) ∨
      (Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom1159 chi))) ∨
      (((Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom1204 chi) ∨
      (Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom1369 chi)) ∨
      ((¬Fin15AnchoredAtom3580 chi ∧
      Fin15AnchoredAtom1113 chi ∧
      Fin15AnchoredAtom1115 chi ∧
      Fin15AnchoredAtom1159 chi ∧
      Fin15AnchoredAtom1204 chi ∧
      Fin15AnchoredAtom1369 chi) ∨
      (Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom1114 chi))))) ∨
      (((((Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom1115 chi) ∨
      (Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom1160 chi)) ∨
      ((Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom1205 chi) ∨
      (Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom1370 chi))) ∨
      (((¬Fin15AnchoredAtom3581 chi ∧
      Fin15AnchoredAtom1114 chi ∧
      Fin15AnchoredAtom1115 chi ∧
      Fin15AnchoredAtom1160 chi ∧
      Fin15AnchoredAtom1205 chi ∧
      Fin15AnchoredAtom1370 chi) ∨
      (Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom1116 chi)) ∨
      ((Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom1117 chi) ∨
      (Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom1125 chi)))) ∨
      ((((Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom1206 chi) ∨
      (Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom1371 chi)) ∨
      ((¬Fin15AnchoredAtom3582 chi ∧
      Fin15AnchoredAtom1116 chi ∧
      Fin15AnchoredAtom1117 chi ∧
      Fin15AnchoredAtom1125 chi ∧
      Fin15AnchoredAtom1206 chi ∧
      Fin15AnchoredAtom1371 chi) ∨
      (Fin15AnchoredAtom3583 chi ∧
      ¬Fin15AnchoredAtom1116 chi))) ∨
      (((Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom1116 chi) ∨
      (Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom1119 chi)) ∨
      ((Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom1127 chi) ∨
      (Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom1208 chi)))))) ∨
      ((((((Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom1373 chi) ∨
      (¬Fin15AnchoredAtom3584 chi ∧
      Fin15AnchoredAtom1116 chi ∧
      Fin15AnchoredAtom1119 chi ∧
      Fin15AnchoredAtom1127 chi ∧
      Fin15AnchoredAtom1208 chi ∧
      Fin15AnchoredAtom1373 chi)) ∨
      ((Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom1116 chi) ∨
      (Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom1120 chi))) ∨
      (((Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom1128 chi) ∨
      (Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom1209 chi)) ∨
      ((Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom1374 chi) ∨
      (¬Fin15AnchoredAtom3585 chi ∧
      Fin15AnchoredAtom1116 chi ∧
      Fin15AnchoredAtom1120 chi ∧
      Fin15AnchoredAtom1128 chi ∧
      Fin15AnchoredAtom1209 chi ∧
      Fin15AnchoredAtom1374 chi)))) ∨
      ((((Fin15AnchoredAtom3586 chi ∧
      ¬Fin15AnchoredAtom1375 chi) ∨
      (Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom1116 chi)) ∨
      ((Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom1122 chi) ∨
      (Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom1130 chi))) ∨
      (((Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom1211 chi) ∨
      (Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom1376 chi)) ∨
      ((¬Fin15AnchoredAtom3587 chi ∧
      Fin15AnchoredAtom1116 chi ∧
      Fin15AnchoredAtom1122 chi ∧
      Fin15AnchoredAtom1130 chi ∧
      Fin15AnchoredAtom1211 chi ∧
      Fin15AnchoredAtom1376 chi) ∨
      (Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom1116 chi))))) ∨
      (((((Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom1123 chi) ∨
      (Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom1131 chi)) ∨
      ((Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom1212 chi) ∨
      (Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom1377 chi))) ∨
      (((¬Fin15AnchoredAtom3588 chi ∧
      Fin15AnchoredAtom1116 chi ∧
      Fin15AnchoredAtom1123 chi ∧
      Fin15AnchoredAtom1131 chi ∧
      Fin15AnchoredAtom1212 chi ∧
      Fin15AnchoredAtom1377 chi) ∨
      (Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom1116 chi)) ∨
      ((Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom1124 chi) ∨
      (Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom1132 chi)))) ∨
      ((((Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom1213 chi) ∨
      (Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom1378 chi)) ∨
      ((¬Fin15AnchoredAtom3589 chi ∧
      Fin15AnchoredAtom1116 chi ∧
      Fin15AnchoredAtom1124 chi ∧
      Fin15AnchoredAtom1132 chi ∧
      Fin15AnchoredAtom1213 chi ∧
      Fin15AnchoredAtom1378 chi) ∨
      (Fin15AnchoredAtom3590 chi ∧
      ¬Fin15AnchoredAtom1117 chi))) ∨
      (((¬Fin15AnchoredAtom3590 chi ∧
      Fin15AnchoredAtom1117 chi ∧
      Fin15AnchoredAtom1118 chi ∧
      Fin15AnchoredAtom1133 chi ∧
      Fin15AnchoredAtom1214 chi ∧
      Fin15AnchoredAtom1379 chi) ∨
      (Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom1117 chi)) ∨
      ((Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom1119 chi) ∨
      (Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom1134 chi))))))) ∨
      ((((((Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom1215 chi) ∨
      ((Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom1380 chi) ∨
      (¬Fin15AnchoredAtom3591 chi ∧
      Fin15AnchoredAtom1117 chi ∧
      Fin15AnchoredAtom1119 chi ∧
      Fin15AnchoredAtom1134 chi ∧
      Fin15AnchoredAtom1215 chi ∧
      Fin15AnchoredAtom1380 chi))) ∨
      (((Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom1117 chi) ∨
      (Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom1120 chi)) ∨
      ((Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom1135 chi) ∨
      (Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom1216 chi)))) ∨
      ((((Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom1381 chi) ∨
      (¬Fin15AnchoredAtom3592 chi ∧
      Fin15AnchoredAtom1117 chi ∧
      Fin15AnchoredAtom1120 chi ∧
      Fin15AnchoredAtom1135 chi ∧
      Fin15AnchoredAtom1216 chi ∧
      Fin15AnchoredAtom1381 chi)) ∨
      ((Fin15AnchoredAtom3593 chi ∧
      ¬Fin15AnchoredAtom1117 chi) ∨
      (Fin15AnchoredAtom3593 chi ∧
      ¬Fin15AnchoredAtom1382 chi))) ∨
      (((¬Fin15AnchoredAtom3593 chi ∧
      Fin15AnchoredAtom1117 chi ∧
      Fin15AnchoredAtom1121 chi ∧
      Fin15AnchoredAtom1136 chi ∧
      Fin15AnchoredAtom1217 chi ∧
      Fin15AnchoredAtom1382 chi) ∨
      (Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom1117 chi)) ∨
      ((Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom1122 chi) ∨
      (Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom1137 chi))))) ∨
      (((((Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom1218 chi) ∨
      (Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom1383 chi)) ∨
      ((¬Fin15AnchoredAtom3594 chi ∧
      Fin15AnchoredAtom1117 chi ∧
      Fin15AnchoredAtom1122 chi ∧
      Fin15AnchoredAtom1137 chi ∧
      Fin15AnchoredAtom1218 chi ∧
      Fin15AnchoredAtom1383 chi) ∨
      (Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom1117 chi))) ∨
      (((Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom1123 chi) ∨
      (Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom1138 chi)) ∨
      ((Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom1219 chi) ∨
      (Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom1384 chi)))) ∨
      ((((¬Fin15AnchoredAtom3595 chi ∧
      Fin15AnchoredAtom1117 chi ∧
      Fin15AnchoredAtom1123 chi ∧
      Fin15AnchoredAtom1138 chi ∧
      Fin15AnchoredAtom1219 chi ∧
      Fin15AnchoredAtom1384 chi) ∨
      (Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom1117 chi)) ∨
      ((Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom1124 chi) ∨
      (Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom1139 chi))) ∨
      (((Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom1220 chi) ∨
      (Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom1385 chi)) ∨
      ((¬Fin15AnchoredAtom3596 chi ∧
      Fin15AnchoredAtom1117 chi ∧
      Fin15AnchoredAtom1124 chi ∧
      Fin15AnchoredAtom1139 chi ∧
      Fin15AnchoredAtom1220 chi ∧
      Fin15AnchoredAtom1385 chi) ∨
      (¬Fin15AnchoredAtom3597 chi ∧
      Fin15AnchoredAtom1118 chi ∧
      Fin15AnchoredAtom1119 chi ∧
      Fin15AnchoredAtom1140 chi ∧
      Fin15AnchoredAtom1221 chi ∧
      Fin15AnchoredAtom1386 chi)))))) ∨
      ((((((Fin15AnchoredAtom3598 chi ∧
      ¬Fin15AnchoredAtom1120 chi) ∨
      (Fin15AnchoredAtom3598 chi ∧
      ¬Fin15AnchoredAtom1387 chi)) ∨
      ((¬Fin15AnchoredAtom3598 chi ∧
      Fin15AnchoredAtom1118 chi ∧
      Fin15AnchoredAtom1120 chi ∧
      Fin15AnchoredAtom1141 chi ∧
      Fin15AnchoredAtom1222 chi ∧
      Fin15AnchoredAtom1387 chi) ∨
      (Fin15AnchoredAtom3600 chi ∧
      ¬Fin15AnchoredAtom1122 chi))) ∨
      (((Fin15AnchoredAtom3601 chi ∧
      ¬Fin15AnchoredAtom1123 chi) ∨
      (Fin15AnchoredAtom3601 chi ∧
      ¬Fin15AnchoredAtom1390 chi)) ∨
      ((¬Fin15AnchoredAtom3602 chi ∧
      Fin15AnchoredAtom1118 chi ∧
      Fin15AnchoredAtom1124 chi ∧
      Fin15AnchoredAtom1145 chi ∧
      Fin15AnchoredAtom1226 chi ∧
      Fin15AnchoredAtom1391 chi) ∨
      (Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom1119 chi)))) ∨
      ((((Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom1120 chi) ∨
      (Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom1146 chi)) ∨
      ((Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom1227 chi) ∨
      (Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom1392 chi))) ∨
      (((¬Fin15AnchoredAtom3603 chi ∧
      Fin15AnchoredAtom1119 chi ∧
      Fin15AnchoredAtom1120 chi ∧
      Fin15AnchoredAtom1146 chi ∧
      Fin15AnchoredAtom1227 chi ∧
      Fin15AnchoredAtom1392 chi) ∨
      (Fin15AnchoredAtom3604 chi ∧
      ¬Fin15AnchoredAtom1119 chi)) ∨
      ((Fin15AnchoredAtom3604 chi ∧
      ¬Fin15AnchoredAtom1147 chi) ∨
      (Fin15AnchoredAtom3604 chi ∧
      ¬Fin15AnchoredAtom1228 chi))))) ∨
      (((((Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom1119 chi) ∨
      (Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom1122 chi)) ∨
      ((Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom1148 chi) ∨
      (Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom1229 chi))) ∨
      (((Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom1394 chi) ∨
      (¬Fin15AnchoredAtom3605 chi ∧
      Fin15AnchoredAtom1119 chi ∧
      Fin15AnchoredAtom1122 chi ∧
      Fin15AnchoredAtom1148 chi ∧
      Fin15AnchoredAtom1229 chi ∧
      Fin15AnchoredAtom1394 chi)) ∨
      ((Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom1119 chi) ∨
      (Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom1123 chi)))) ∨
      ((((Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom1149 chi) ∨
      (Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom1230 chi)) ∨
      ((Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom1395 chi) ∨
      (¬Fin15AnchoredAtom3606 chi ∧
      Fin15AnchoredAtom1119 chi ∧
      Fin15AnchoredAtom1123 chi ∧
      Fin15AnchoredAtom1149 chi ∧
      Fin15AnchoredAtom1230 chi ∧
      Fin15AnchoredAtom1395 chi))) ∨
      (((Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom1119 chi) ∨
      (Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom1124 chi)) ∨
      ((Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom1150 chi) ∨
      (Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom1231 chi)))))))) ∨
      (((((((Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom1396 chi) ∨
      ((¬Fin15AnchoredAtom3607 chi ∧
      Fin15AnchoredAtom1119 chi ∧
      Fin15AnchoredAtom1124 chi ∧
      Fin15AnchoredAtom1150 chi ∧
      Fin15AnchoredAtom1231 chi ∧
      Fin15AnchoredAtom1396 chi) ∨
      (Fin15AnchoredAtom3608 chi ∧
      ¬Fin15AnchoredAtom1120 chi))) ∨
      (((Fin15AnchoredAtom3608 chi ∧
      ¬Fin15AnchoredAtom1121 chi) ∨
      (Fin15AnchoredAtom3608 chi ∧
      ¬Fin15AnchoredAtom1151 chi)) ∨
      ((Fin15AnchoredAtom3608 chi ∧
      ¬Fin15AnchoredAtom1232 chi) ∨
      (Fin15AnchoredAtom3608 chi ∧
      ¬Fin15AnchoredAtom1397 chi)))) ∨
      ((((¬Fin15AnchoredAtom3608 chi ∧
      Fin15AnchoredAtom1120 chi ∧
      Fin15AnchoredAtom1121 chi ∧
      Fin15AnchoredAtom1151 chi ∧
      Fin15AnchoredAtom1232 chi ∧
      Fin15AnchoredAtom1397 chi) ∨
      (Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom1120 chi)) ∨
      ((Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom1122 chi) ∨
      (Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom1152 chi))) ∨
      (((Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom1233 chi) ∨
      (Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom1398 chi)) ∨
      ((¬Fin15AnchoredAtom3609 chi ∧
      Fin15AnchoredAtom1120 chi ∧
      Fin15AnchoredAtom1122 chi ∧
      Fin15AnchoredAtom1152 chi ∧
      Fin15AnchoredAtom1233 chi ∧
      Fin15AnchoredAtom1398 chi) ∨
      (Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom1120 chi))))) ∨
      (((((Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom1123 chi) ∨
      (Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom1153 chi)) ∨
      ((Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom1234 chi) ∨
      (Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom1399 chi))) ∨
      (((¬Fin15AnchoredAtom3610 chi ∧
      Fin15AnchoredAtom1120 chi ∧
      Fin15AnchoredAtom1123 chi ∧
      Fin15AnchoredAtom1153 chi ∧
      Fin15AnchoredAtom1234 chi ∧
      Fin15AnchoredAtom1399 chi) ∨
      (Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom1120 chi)) ∨
      ((Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom1124 chi) ∨
      (Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom1154 chi)))) ∨
      ((((Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom1235 chi) ∨
      (Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom1400 chi)) ∨
      ((¬Fin15AnchoredAtom3611 chi ∧
      Fin15AnchoredAtom1120 chi ∧
      Fin15AnchoredAtom1124 chi ∧
      Fin15AnchoredAtom1154 chi ∧
      Fin15AnchoredAtom1235 chi ∧
      Fin15AnchoredAtom1400 chi) ∨
      (Fin15AnchoredAtom3612 chi ∧
      ¬Fin15AnchoredAtom1122 chi))) ∨
      (((Fin15AnchoredAtom3612 chi ∧
      ¬Fin15AnchoredAtom1401 chi) ∨
      (Fin15AnchoredAtom3613 chi ∧
      ¬Fin15AnchoredAtom1121 chi)) ∨
      ((Fin15AnchoredAtom3613 chi ∧
      ¬Fin15AnchoredAtom1123 chi) ∨
      (Fin15AnchoredAtom3613 chi ∧
      ¬Fin15AnchoredAtom1402 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom3613 chi ∧
      Fin15AnchoredAtom1121 chi ∧
      Fin15AnchoredAtom1123 chi ∧
      Fin15AnchoredAtom1156 chi ∧
      Fin15AnchoredAtom1237 chi ∧
      Fin15AnchoredAtom1402 chi) ∨
      (Fin15AnchoredAtom3614 chi ∧
      ¬Fin15AnchoredAtom1238 chi)) ∨
      ((Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom1122 chi) ∨
      (Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom1123 chi))) ∨
      (((Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom1158 chi) ∨
      (Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom1239 chi)) ∨
      ((Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom1404 chi) ∨
      (¬Fin15AnchoredAtom3615 chi ∧
      Fin15AnchoredAtom1122 chi ∧
      Fin15AnchoredAtom1123 chi ∧
      Fin15AnchoredAtom1158 chi ∧
      Fin15AnchoredAtom1239 chi ∧
      Fin15AnchoredAtom1404 chi)))) ∨
      ((((Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom1122 chi) ∨
      (Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom1124 chi)) ∨
      ((Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom1159 chi) ∨
      (Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom1240 chi))) ∨
      (((Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom1405 chi) ∨
      (¬Fin15AnchoredAtom3616 chi ∧
      Fin15AnchoredAtom1122 chi ∧
      Fin15AnchoredAtom1124 chi ∧
      Fin15AnchoredAtom1159 chi ∧
      Fin15AnchoredAtom1240 chi ∧
      Fin15AnchoredAtom1405 chi)) ∨
      ((Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom1123 chi) ∨
      (Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom1124 chi))))) ∨
      (((((Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom1160 chi) ∨
      (Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom1241 chi)) ∨
      ((Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom1406 chi) ∨
      (¬Fin15AnchoredAtom3617 chi ∧
      Fin15AnchoredAtom1123 chi ∧
      Fin15AnchoredAtom1124 chi ∧
      Fin15AnchoredAtom1160 chi ∧
      Fin15AnchoredAtom1241 chi ∧
      Fin15AnchoredAtom1406 chi))) ∨
      (((Fin15AnchoredAtom3618 chi ∧
      ¬Fin15AnchoredAtom1407 chi) ∨
      (Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom1125 chi)) ∨
      ((Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom1127 chi) ∨
      (Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom1134 chi)))) ∨
      ((((Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom1243 chi) ∨
      (Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom1408 chi)) ∨
      ((¬Fin15AnchoredAtom3619 chi ∧
      Fin15AnchoredAtom1125 chi ∧
      Fin15AnchoredAtom1127 chi ∧
      Fin15AnchoredAtom1134 chi ∧
      Fin15AnchoredAtom1243 chi ∧
      Fin15AnchoredAtom1408 chi) ∨
      (Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom1125 chi))) ∨
      (((Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom1128 chi) ∨
      (Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom1135 chi)) ∨
      ((Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom1244 chi) ∨
      (Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom1409 chi))))))) ∨
      (((((((¬Fin15AnchoredAtom3620 chi ∧
      Fin15AnchoredAtom1125 chi ∧
      Fin15AnchoredAtom1128 chi ∧
      Fin15AnchoredAtom1135 chi ∧
      Fin15AnchoredAtom1244 chi ∧
      Fin15AnchoredAtom1409 chi) ∨
      (Fin15AnchoredAtom3621 chi ∧
      ¬Fin15AnchoredAtom1245 chi)) ∨
      ((Fin15AnchoredAtom3621 chi ∧
      ¬Fin15AnchoredAtom1410 chi) ∨
      (¬Fin15AnchoredAtom3621 chi ∧
      Fin15AnchoredAtom1125 chi ∧
      Fin15AnchoredAtom1129 chi ∧
      Fin15AnchoredAtom1136 chi ∧
      Fin15AnchoredAtom1245 chi ∧
      Fin15AnchoredAtom1410 chi))) ∨
      (((Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom1125 chi) ∨
      (Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom1130 chi)) ∨
      ((Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom1137 chi) ∨
      (Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom1246 chi)))) ∨
      ((((Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom1411 chi) ∨
      (¬Fin15AnchoredAtom3622 chi ∧
      Fin15AnchoredAtom1125 chi ∧
      Fin15AnchoredAtom1130 chi ∧
      Fin15AnchoredAtom1137 chi ∧
      Fin15AnchoredAtom1246 chi ∧
      Fin15AnchoredAtom1411 chi)) ∨
      ((Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom1125 chi) ∨
      (Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom1131 chi))) ∨
      (((Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom1138 chi) ∨
      (Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom1247 chi)) ∨
      ((Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom1412 chi) ∨
      (¬Fin15AnchoredAtom3623 chi ∧
      Fin15AnchoredAtom1125 chi ∧
      Fin15AnchoredAtom1131 chi ∧
      Fin15AnchoredAtom1138 chi ∧
      Fin15AnchoredAtom1247 chi ∧
      Fin15AnchoredAtom1412 chi))))) ∨
      (((((Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom1125 chi) ∨
      (Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom1132 chi)) ∨
      ((Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom1139 chi) ∨
      (Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom1248 chi))) ∨
      (((Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom1413 chi) ∨
      (¬Fin15AnchoredAtom3624 chi ∧
      Fin15AnchoredAtom1125 chi ∧
      Fin15AnchoredAtom1132 chi ∧
      Fin15AnchoredAtom1139 chi ∧
      Fin15AnchoredAtom1248 chi ∧
      Fin15AnchoredAtom1413 chi)) ∨
      ((¬Fin15AnchoredAtom3625 chi ∧
      Fin15AnchoredAtom1126 chi ∧
      Fin15AnchoredAtom1127 chi ∧
      Fin15AnchoredAtom1140 chi ∧
      Fin15AnchoredAtom1249 chi ∧
      Fin15AnchoredAtom1414 chi) ∨
      (¬Fin15AnchoredAtom3626 chi ∧
      Fin15AnchoredAtom1126 chi ∧
      Fin15AnchoredAtom1128 chi ∧
      Fin15AnchoredAtom1141 chi ∧
      Fin15AnchoredAtom1250 chi ∧
      Fin15AnchoredAtom1415 chi)))) ∨
      ((((¬Fin15AnchoredAtom3628 chi ∧
      Fin15AnchoredAtom1126 chi ∧
      Fin15AnchoredAtom1130 chi ∧
      Fin15AnchoredAtom1143 chi ∧
      Fin15AnchoredAtom1252 chi ∧
      Fin15AnchoredAtom1417 chi) ∨
      (Fin15AnchoredAtom3629 chi ∧
      ¬Fin15AnchoredAtom1144 chi)) ∨
      ((Fin15AnchoredAtom3630 chi ∧
      ¬Fin15AnchoredAtom1132 chi) ∨
      (Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom1127 chi))) ∨
      (((Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom1128 chi) ∨
      (Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom1146 chi)) ∨
      ((Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom1255 chi) ∨
      (Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom1420 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom3631 chi ∧
      Fin15AnchoredAtom1127 chi ∧
      Fin15AnchoredAtom1128 chi ∧
      Fin15AnchoredAtom1146 chi ∧
      Fin15AnchoredAtom1255 chi ∧
      Fin15AnchoredAtom1420 chi) ∨
      (Fin15AnchoredAtom3632 chi ∧
      ¬Fin15AnchoredAtom1127 chi)) ∨
      ((Fin15AnchoredAtom3632 chi ∧
      ¬Fin15AnchoredAtom1256 chi) ∨
      (Fin15AnchoredAtom3632 chi ∧
      ¬Fin15AnchoredAtom1421 chi))) ∨
      (((Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom1127 chi) ∨
      (Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom1130 chi)) ∨
      ((Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom1148 chi) ∨
      (Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom1257 chi)))) ∨
      ((((Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom1422 chi) ∨
      (¬Fin15AnchoredAtom3633 chi ∧
      Fin15AnchoredAtom1127 chi ∧
      Fin15AnchoredAtom1130 chi ∧
      Fin15AnchoredAtom1148 chi ∧
      Fin15AnchoredAtom1257 chi ∧
      Fin15AnchoredAtom1422 chi)) ∨
      ((Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom1127 chi) ∨
      (Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom1131 chi))) ∨
      (((Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom1149 chi) ∨
      (Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom1258 chi)) ∨
      ((Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom1423 chi) ∨
      (¬Fin15AnchoredAtom3634 chi ∧
      Fin15AnchoredAtom1127 chi ∧
      Fin15AnchoredAtom1131 chi ∧
      Fin15AnchoredAtom1149 chi ∧
      Fin15AnchoredAtom1258 chi ∧
      Fin15AnchoredAtom1423 chi))))) ∨
      (((((Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom1127 chi) ∨
      (Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom1132 chi)) ∨
      ((Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom1150 chi) ∨
      (Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom1259 chi))) ∨
      (((Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom1424 chi) ∨
      (¬Fin15AnchoredAtom3635 chi ∧
      Fin15AnchoredAtom1127 chi ∧
      Fin15AnchoredAtom1132 chi ∧
      Fin15AnchoredAtom1150 chi ∧
      Fin15AnchoredAtom1259 chi ∧
      Fin15AnchoredAtom1424 chi)) ∨
      ((Fin15AnchoredAtom3636 chi ∧
      ¬Fin15AnchoredAtom1129 chi) ∨
      (Fin15AnchoredAtom3636 chi ∧
      ¬Fin15AnchoredAtom1425 chi)))) ∨
      ((((¬Fin15AnchoredAtom3636 chi ∧
      Fin15AnchoredAtom1128 chi ∧
      Fin15AnchoredAtom1129 chi ∧
      Fin15AnchoredAtom1151 chi ∧
      Fin15AnchoredAtom1260 chi ∧
      Fin15AnchoredAtom1425 chi) ∨
      (Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom1128 chi)) ∨
      ((Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom1130 chi) ∨
      (Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom1152 chi))) ∨
      (((Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom1261 chi) ∨
      (Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom1426 chi)) ∨
      ((¬Fin15AnchoredAtom3637 chi ∧
      Fin15AnchoredAtom1128 chi ∧
      Fin15AnchoredAtom1130 chi ∧
      Fin15AnchoredAtom1152 chi ∧
      Fin15AnchoredAtom1261 chi ∧
      Fin15AnchoredAtom1426 chi) ∨
      (Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom1128 chi)))))))))) := by
  intro hbad
  rcases hbad with hbad | hbad
  ·
    rcases hbad with hbad | hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact fin15Anchored_clause23473 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23474 chi hbad
                ·
                  exact fin15Anchored_clause23475 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23476 chi hbad
                ·
                  exact fin15Anchored_clause23477 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23478 chi hbad
                ·
                  exact fin15Anchored_clause23479 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23480 chi hbad
                ·
                  exact fin15Anchored_clause23481 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23482 chi hbad
                ·
                  exact fin15Anchored_clause23483 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23484 chi hbad
                ·
                  exact fin15Anchored_clause23485 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23486 chi hbad
                ·
                  exact fin15Anchored_clause23487 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23488 chi hbad
                ·
                  exact fin15Anchored_clause23489 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23490 chi hbad
                ·
                  exact fin15Anchored_clause23491 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23492 chi hbad
                ·
                  exact fin15Anchored_clause23493 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23494 chi hbad
                ·
                  exact fin15Anchored_clause23495 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23496 chi hbad
                ·
                  exact fin15Anchored_clause23497 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23498 chi hbad
                ·
                  exact fin15Anchored_clause23499 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23500 chi hbad
                ·
                  exact fin15Anchored_clause23501 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23502 chi hbad
                ·
                  exact fin15Anchored_clause23503 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23504 chi hbad
                ·
                  exact fin15Anchored_clause23505 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23506 chi hbad
                ·
                  exact fin15Anchored_clause23507 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23508 chi hbad
                ·
                  exact fin15Anchored_clause23509 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23510 chi hbad
                ·
                  exact fin15Anchored_clause23511 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23512 chi hbad
                ·
                  exact fin15Anchored_clause23513 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23514 chi hbad
                ·
                  exact fin15Anchored_clause23515 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23516 chi hbad
                ·
                  exact fin15Anchored_clause23517 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23518 chi hbad
                ·
                  exact fin15Anchored_clause23519 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23520 chi hbad
                ·
                  exact fin15Anchored_clause23521 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23522 chi hbad
                ·
                  exact fin15Anchored_clause23523 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23524 chi hbad
                ·
                  exact fin15Anchored_clause23525 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23526 chi hbad
                ·
                  exact fin15Anchored_clause23527 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23528 chi hbad
                ·
                  exact fin15Anchored_clause23529 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23530 chi hbad
                ·
                  exact fin15Anchored_clause23531 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23532 chi hbad
                ·
                  exact fin15Anchored_clause23533 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23534 chi hbad
                ·
                  exact fin15Anchored_clause23535 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact fin15Anchored_clause23536 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23537 chi hbad
                ·
                  exact fin15Anchored_clause23538 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23539 chi hbad
                ·
                  exact fin15Anchored_clause23540 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23541 chi hbad
                ·
                  exact fin15Anchored_clause23542 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23543 chi hbad
                ·
                  exact fin15Anchored_clause23544 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23545 chi hbad
                ·
                  exact fin15Anchored_clause23546 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23547 chi hbad
                ·
                  exact fin15Anchored_clause23548 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23549 chi hbad
                ·
                  exact fin15Anchored_clause23550 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23551 chi hbad
                ·
                  exact fin15Anchored_clause23552 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23553 chi hbad
                ·
                  exact fin15Anchored_clause23554 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23555 chi hbad
                ·
                  exact fin15Anchored_clause23556 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23557 chi hbad
                ·
                  exact fin15Anchored_clause23558 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23559 chi hbad
                ·
                  exact fin15Anchored_clause23560 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23561 chi hbad
                ·
                  exact fin15Anchored_clause23562 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23563 chi hbad
                ·
                  exact fin15Anchored_clause23564 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23565 chi hbad
                ·
                  exact fin15Anchored_clause23566 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23567 chi hbad
                ·
                  exact fin15Anchored_clause23568 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23569 chi hbad
                ·
                  exact fin15Anchored_clause23570 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23571 chi hbad
                ·
                  exact fin15Anchored_clause23572 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23573 chi hbad
                ·
                  exact fin15Anchored_clause23574 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23575 chi hbad
                ·
                  exact fin15Anchored_clause23576 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23577 chi hbad
                ·
                  exact fin15Anchored_clause23578 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23579 chi hbad
                ·
                  exact fin15Anchored_clause23580 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23581 chi hbad
                ·
                  exact fin15Anchored_clause23582 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23583 chi hbad
                ·
                  exact fin15Anchored_clause23584 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23585 chi hbad
                ·
                  exact fin15Anchored_clause23586 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23587 chi hbad
                ·
                  exact fin15Anchored_clause23588 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23589 chi hbad
                ·
                  exact fin15Anchored_clause23590 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23591 chi hbad
                ·
                  exact fin15Anchored_clause23592 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23593 chi hbad
                ·
                  exact fin15Anchored_clause23594 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23595 chi hbad
                ·
                  exact fin15Anchored_clause23596 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23597 chi hbad
                ·
                  exact fin15Anchored_clause23598 chi hbad
  ·
    rcases hbad with hbad | hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact fin15Anchored_clause23599 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23600 chi hbad
                ·
                  exact fin15Anchored_clause23601 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23602 chi hbad
                ·
                  exact fin15Anchored_clause23603 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23604 chi hbad
                ·
                  exact fin15Anchored_clause23605 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23606 chi hbad
                ·
                  exact fin15Anchored_clause23607 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23608 chi hbad
                ·
                  exact fin15Anchored_clause23609 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23610 chi hbad
                ·
                  exact fin15Anchored_clause23611 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23612 chi hbad
                ·
                  exact fin15Anchored_clause23613 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23614 chi hbad
                ·
                  exact fin15Anchored_clause23615 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23616 chi hbad
                ·
                  exact fin15Anchored_clause23617 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23618 chi hbad
                ·
                  exact fin15Anchored_clause23619 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23620 chi hbad
                ·
                  exact fin15Anchored_clause23621 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23622 chi hbad
                ·
                  exact fin15Anchored_clause23623 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23624 chi hbad
                ·
                  exact fin15Anchored_clause23625 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23626 chi hbad
                ·
                  exact fin15Anchored_clause23627 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23628 chi hbad
                ·
                  exact fin15Anchored_clause23629 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23630 chi hbad
                ·
                  exact fin15Anchored_clause23631 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23632 chi hbad
                ·
                  exact fin15Anchored_clause23633 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23634 chi hbad
                ·
                  exact fin15Anchored_clause23635 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23636 chi hbad
                ·
                  exact fin15Anchored_clause23637 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23638 chi hbad
                ·
                  exact fin15Anchored_clause23639 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23640 chi hbad
                ·
                  exact fin15Anchored_clause23641 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23642 chi hbad
                ·
                  exact fin15Anchored_clause23643 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23644 chi hbad
                ·
                  exact fin15Anchored_clause23645 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23646 chi hbad
                ·
                  exact fin15Anchored_clause23647 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23648 chi hbad
                ·
                  exact fin15Anchored_clause23649 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23650 chi hbad
                ·
                  exact fin15Anchored_clause23651 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23652 chi hbad
                ·
                  exact fin15Anchored_clause23653 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23654 chi hbad
                ·
                  exact fin15Anchored_clause23655 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23656 chi hbad
                ·
                  exact fin15Anchored_clause23657 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23658 chi hbad
                ·
                  exact fin15Anchored_clause23659 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23660 chi hbad
                ·
                  exact fin15Anchored_clause23661 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23662 chi hbad
                ·
                  exact fin15Anchored_clause23663 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23664 chi hbad
                ·
                  exact fin15Anchored_clause23665 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23666 chi hbad
                ·
                  exact fin15Anchored_clause23667 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23668 chi hbad
                ·
                  exact fin15Anchored_clause23669 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23670 chi hbad
                ·
                  exact fin15Anchored_clause23671 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23672 chi hbad
                ·
                  exact fin15Anchored_clause23673 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23674 chi hbad
                ·
                  exact fin15Anchored_clause23675 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23676 chi hbad
                ·
                  exact fin15Anchored_clause23677 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23678 chi hbad
                ·
                  exact fin15Anchored_clause23679 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23680 chi hbad
                ·
                  exact fin15Anchored_clause23681 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23682 chi hbad
                ·
                  exact fin15Anchored_clause23683 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23684 chi hbad
                ·
                  exact fin15Anchored_clause23685 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23686 chi hbad
                ·
                  exact fin15Anchored_clause23687 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23688 chi hbad
                ·
                  exact fin15Anchored_clause23689 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23690 chi hbad
                ·
                  exact fin15Anchored_clause23691 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23692 chi hbad
                ·
                  exact fin15Anchored_clause23693 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23694 chi hbad
                ·
                  exact fin15Anchored_clause23695 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23696 chi hbad
                ·
                  exact fin15Anchored_clause23697 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23698 chi hbad
                ·
                  exact fin15Anchored_clause23699 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23700 chi hbad
                ·
                  exact fin15Anchored_clause23701 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23702 chi hbad
                ·
                  exact fin15Anchored_clause23703 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23704 chi hbad
                ·
                  exact fin15Anchored_clause23705 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23706 chi hbad
                ·
                  exact fin15Anchored_clause23707 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23708 chi hbad
                ·
                  exact fin15Anchored_clause23709 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23710 chi hbad
                ·
                  exact fin15Anchored_clause23711 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23712 chi hbad
                ·
                  exact fin15Anchored_clause23713 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23714 chi hbad
                ·
                  exact fin15Anchored_clause23715 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23716 chi hbad
                ·
                  exact fin15Anchored_clause23717 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23718 chi hbad
                ·
                  exact fin15Anchored_clause23719 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23720 chi hbad
                ·
                  exact fin15Anchored_clause23721 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23722 chi hbad
                ·
                  exact fin15Anchored_clause23723 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23724 chi hbad
                ·
                  exact fin15Anchored_clause23725 chi hbad

end ErdosSzekeres

end
