module

public import ErdosSzekeres.Fin15AnchoredClauseChunk185
public import ErdosSzekeres.Fin15AnchoredClauseChunk186
public import ErdosSzekeres.Fin15AnchoredClauseChunk187

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 094. -/

theorem fin15Anchored_rejectSemanticSegment094
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom1131 chi) ∨
      ((Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom1153 chi) ∨
      (Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom1262 chi))) ∨
      (((Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom1427 chi) ∨
      (¬Fin15AnchoredAtom3638 chi ∧
      Fin15AnchoredAtom1128 chi ∧
      Fin15AnchoredAtom1131 chi ∧
      Fin15AnchoredAtom1153 chi ∧
      Fin15AnchoredAtom1262 chi ∧
      Fin15AnchoredAtom1427 chi)) ∨
      ((Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom1128 chi) ∨
      (Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom1132 chi)))) ∨
      ((((Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom1154 chi) ∨
      (Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom1263 chi)) ∨
      ((Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom1428 chi) ∨
      (¬Fin15AnchoredAtom3639 chi ∧
      Fin15AnchoredAtom1128 chi ∧
      Fin15AnchoredAtom1132 chi ∧
      Fin15AnchoredAtom1154 chi ∧
      Fin15AnchoredAtom1263 chi ∧
      Fin15AnchoredAtom1428 chi))) ∨
      (((Fin15AnchoredAtom3640 chi ∧
      ¬Fin15AnchoredAtom1429 chi) ∨
      (¬Fin15AnchoredAtom3640 chi ∧
      Fin15AnchoredAtom1129 chi ∧
      Fin15AnchoredAtom1130 chi ∧
      Fin15AnchoredAtom1155 chi ∧
      Fin15AnchoredAtom1264 chi ∧
      Fin15AnchoredAtom1429 chi)) ∨
      ((Fin15AnchoredAtom3641 chi ∧
      ¬Fin15AnchoredAtom1129 chi) ∨
      (Fin15AnchoredAtom3641 chi ∧
      ¬Fin15AnchoredAtom1156 chi))))) ∨
      (((((Fin15AnchoredAtom3641 chi ∧
      ¬Fin15AnchoredAtom1430 chi) ∨
      (¬Fin15AnchoredAtom3641 chi ∧
      Fin15AnchoredAtom1129 chi ∧
      Fin15AnchoredAtom1131 chi ∧
      Fin15AnchoredAtom1156 chi ∧
      Fin15AnchoredAtom1265 chi ∧
      Fin15AnchoredAtom1430 chi)) ∨
      ((Fin15AnchoredAtom3642 chi ∧
      ¬Fin15AnchoredAtom1266 chi) ∨
      (Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom1130 chi))) ∨
      (((Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom1131 chi) ∨
      (Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom1158 chi)) ∨
      ((Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom1267 chi) ∨
      (Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom1432 chi)))) ∨
      ((((¬Fin15AnchoredAtom3643 chi ∧
      Fin15AnchoredAtom1130 chi ∧
      Fin15AnchoredAtom1131 chi ∧
      Fin15AnchoredAtom1158 chi ∧
      Fin15AnchoredAtom1267 chi ∧
      Fin15AnchoredAtom1432 chi) ∨
      (Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom1130 chi)) ∨
      ((Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom1132 chi) ∨
      (Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom1159 chi))) ∨
      (((Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom1268 chi) ∨
      (Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom1433 chi)) ∨
      ((¬Fin15AnchoredAtom3644 chi ∧
      Fin15AnchoredAtom1130 chi ∧
      Fin15AnchoredAtom1132 chi ∧
      Fin15AnchoredAtom1159 chi ∧
      Fin15AnchoredAtom1268 chi ∧
      Fin15AnchoredAtom1433 chi) ∨
      (Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom1131 chi)))))) ∨
      ((((((Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom1132 chi) ∨
      (Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom1160 chi)) ∨
      ((Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom1269 chi) ∨
      (Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom1434 chi))) ∨
      (((¬Fin15AnchoredAtom3645 chi ∧
      Fin15AnchoredAtom1131 chi ∧
      Fin15AnchoredAtom1132 chi ∧
      Fin15AnchoredAtom1160 chi ∧
      Fin15AnchoredAtom1269 chi ∧
      Fin15AnchoredAtom1434 chi) ∨
      (Fin15AnchoredAtom3647 chi ∧
      ¬Fin15AnchoredAtom1135 chi)) ∨
      ((¬Fin15AnchoredAtom3647 chi ∧
      Fin15AnchoredAtom1133 chi ∧
      Fin15AnchoredAtom1135 chi ∧
      Fin15AnchoredAtom1141 chi ∧
      Fin15AnchoredAtom1271 chi ∧
      Fin15AnchoredAtom1436 chi) ∨
      (Fin15AnchoredAtom3650 chi ∧
      ¬Fin15AnchoredAtom1138 chi)))) ∨
      ((((Fin15AnchoredAtom3651 chi ∧
      ¬Fin15AnchoredAtom1139 chi) ∨
      (¬Fin15AnchoredAtom3651 chi ∧
      Fin15AnchoredAtom1133 chi ∧
      Fin15AnchoredAtom1139 chi ∧
      Fin15AnchoredAtom1145 chi ∧
      Fin15AnchoredAtom1275 chi ∧
      Fin15AnchoredAtom1440 chi)) ∨
      ((Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom1134 chi) ∨
      (Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom1135 chi))) ∨
      (((Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom1146 chi) ∨
      (Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom1276 chi)) ∨
      ((Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom1441 chi) ∨
      (¬Fin15AnchoredAtom3652 chi ∧
      Fin15AnchoredAtom1134 chi ∧
      Fin15AnchoredAtom1135 chi ∧
      Fin15AnchoredAtom1146 chi ∧
      Fin15AnchoredAtom1276 chi ∧
      Fin15AnchoredAtom1441 chi))))) ∨
      (((((Fin15AnchoredAtom3653 chi ∧
      ¬Fin15AnchoredAtom1277 chi) ∨
      (Fin15AnchoredAtom3653 chi ∧
      ¬Fin15AnchoredAtom1442 chi)) ∨
      ((¬Fin15AnchoredAtom3653 chi ∧
      Fin15AnchoredAtom1134 chi ∧
      Fin15AnchoredAtom1136 chi ∧
      Fin15AnchoredAtom1147 chi ∧
      Fin15AnchoredAtom1277 chi ∧
      Fin15AnchoredAtom1442 chi) ∨
      (Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom1134 chi))) ∨
      (((Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom1137 chi) ∨
      (Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom1148 chi)) ∨
      ((Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom1278 chi) ∨
      (Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom1443 chi)))) ∨
      ((((¬Fin15AnchoredAtom3654 chi ∧
      Fin15AnchoredAtom1134 chi ∧
      Fin15AnchoredAtom1137 chi ∧
      Fin15AnchoredAtom1148 chi ∧
      Fin15AnchoredAtom1278 chi ∧
      Fin15AnchoredAtom1443 chi) ∨
      (Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom1134 chi)) ∨
      ((Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom1138 chi) ∨
      (Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom1149 chi))) ∨
      (((Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom1279 chi) ∨
      (Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom1444 chi)) ∨
      ((¬Fin15AnchoredAtom3655 chi ∧
      Fin15AnchoredAtom1134 chi ∧
      Fin15AnchoredAtom1138 chi ∧
      Fin15AnchoredAtom1149 chi ∧
      Fin15AnchoredAtom1279 chi ∧
      Fin15AnchoredAtom1444 chi) ∨
      (Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom1134 chi))))))) ∨
      ((((((Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom1139 chi) ∨
      ((Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom1150 chi) ∨
      (Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom1280 chi))) ∨
      (((Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom1445 chi) ∨
      (¬Fin15AnchoredAtom3656 chi ∧
      Fin15AnchoredAtom1134 chi ∧
      Fin15AnchoredAtom1139 chi ∧
      Fin15AnchoredAtom1150 chi ∧
      Fin15AnchoredAtom1280 chi ∧
      Fin15AnchoredAtom1445 chi)) ∨
      ((Fin15AnchoredAtom3657 chi ∧
      ¬Fin15AnchoredAtom1135 chi) ∨
      (Fin15AnchoredAtom3657 chi ∧
      ¬Fin15AnchoredAtom1136 chi)))) ∨
      ((((Fin15AnchoredAtom3657 chi ∧
      ¬Fin15AnchoredAtom1151 chi) ∨
      (Fin15AnchoredAtom3657 chi ∧
      ¬Fin15AnchoredAtom1281 chi)) ∨
      ((Fin15AnchoredAtom3657 chi ∧
      ¬Fin15AnchoredAtom1446 chi) ∨
      (¬Fin15AnchoredAtom3657 chi ∧
      Fin15AnchoredAtom1135 chi ∧
      Fin15AnchoredAtom1136 chi ∧
      Fin15AnchoredAtom1151 chi ∧
      Fin15AnchoredAtom1281 chi ∧
      Fin15AnchoredAtom1446 chi))) ∨
      (((Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom1135 chi) ∨
      (Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom1137 chi)) ∨
      ((Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom1152 chi) ∨
      (Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom1282 chi))))) ∨
      (((((Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom1447 chi) ∨
      (¬Fin15AnchoredAtom3658 chi ∧
      Fin15AnchoredAtom1135 chi ∧
      Fin15AnchoredAtom1137 chi ∧
      Fin15AnchoredAtom1152 chi ∧
      Fin15AnchoredAtom1282 chi ∧
      Fin15AnchoredAtom1447 chi)) ∨
      ((Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom1135 chi) ∨
      (Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom1138 chi))) ∨
      (((Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom1153 chi) ∨
      (Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom1283 chi)) ∨
      ((Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom1448 chi) ∨
      (¬Fin15AnchoredAtom3659 chi ∧
      Fin15AnchoredAtom1135 chi ∧
      Fin15AnchoredAtom1138 chi ∧
      Fin15AnchoredAtom1153 chi ∧
      Fin15AnchoredAtom1283 chi ∧
      Fin15AnchoredAtom1448 chi)))) ∨
      ((((Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom1135 chi) ∨
      (Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom1139 chi)) ∨
      ((Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom1154 chi) ∨
      (Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom1284 chi))) ∨
      (((Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom1449 chi) ∨
      (¬Fin15AnchoredAtom3660 chi ∧
      Fin15AnchoredAtom1135 chi ∧
      Fin15AnchoredAtom1139 chi ∧
      Fin15AnchoredAtom1154 chi ∧
      Fin15AnchoredAtom1284 chi ∧
      Fin15AnchoredAtom1449 chi)) ∨
      ((Fin15AnchoredAtom3661 chi ∧
      ¬Fin15AnchoredAtom1137 chi) ∨
      (Fin15AnchoredAtom3661 chi ∧
      ¬Fin15AnchoredAtom1155 chi)))))) ∨
      ((((((Fin15AnchoredAtom3663 chi ∧
      ¬Fin15AnchoredAtom1139 chi) ∨
      (¬Fin15AnchoredAtom3663 chi ∧
      Fin15AnchoredAtom1136 chi ∧
      Fin15AnchoredAtom1139 chi ∧
      Fin15AnchoredAtom1157 chi ∧
      Fin15AnchoredAtom1287 chi ∧
      Fin15AnchoredAtom1452 chi)) ∨
      ((Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom1137 chi) ∨
      (Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom1138 chi))) ∨
      (((Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom1158 chi) ∨
      (Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom1288 chi)) ∨
      ((Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom1453 chi) ∨
      (¬Fin15AnchoredAtom3664 chi ∧
      Fin15AnchoredAtom1137 chi ∧
      Fin15AnchoredAtom1138 chi ∧
      Fin15AnchoredAtom1158 chi ∧
      Fin15AnchoredAtom1288 chi ∧
      Fin15AnchoredAtom1453 chi)))) ∨
      ((((Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom1137 chi) ∨
      (Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom1139 chi)) ∨
      ((Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom1159 chi) ∨
      (Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom1289 chi))) ∨
      (((Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom1454 chi) ∨
      (¬Fin15AnchoredAtom3665 chi ∧
      Fin15AnchoredAtom1137 chi ∧
      Fin15AnchoredAtom1139 chi ∧
      Fin15AnchoredAtom1159 chi ∧
      Fin15AnchoredAtom1289 chi ∧
      Fin15AnchoredAtom1454 chi)) ∨
      ((Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom1138 chi) ∨
      (Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom1139 chi))))) ∨
      (((((Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom1160 chi) ∨
      (Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom1290 chi)) ∨
      ((Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom1455 chi) ∨
      (¬Fin15AnchoredAtom3666 chi ∧
      Fin15AnchoredAtom1138 chi ∧
      Fin15AnchoredAtom1139 chi ∧
      Fin15AnchoredAtom1160 chi ∧
      Fin15AnchoredAtom1290 chi ∧
      Fin15AnchoredAtom1455 chi))) ∨
      (((¬Fin15AnchoredAtom3667 chi ∧
      Fin15AnchoredAtom1140 chi ∧
      Fin15AnchoredAtom1141 chi ∧
      Fin15AnchoredAtom1146 chi ∧
      Fin15AnchoredAtom1291 chi ∧
      Fin15AnchoredAtom1456 chi) ∨
      (Fin15AnchoredAtom3673 chi ∧
      ¬Fin15AnchoredAtom1462 chi)) ∨
      ((Fin15AnchoredAtom3674 chi ∧
      ¬Fin15AnchoredAtom1463 chi) ∨
      (Fin15AnchoredAtom3679 chi ∧
      ¬Fin15AnchoredAtom1303 chi)))) ∨
      ((((Fin15AnchoredAtom3682 chi ∧
      ¬Fin15AnchoredAtom1146 chi) ∨
      (Fin15AnchoredAtom3682 chi ∧
      ¬Fin15AnchoredAtom1147 chi)) ∨
      ((Fin15AnchoredAtom3682 chi ∧
      ¬Fin15AnchoredAtom1151 chi) ∨
      (Fin15AnchoredAtom3682 chi ∧
      ¬Fin15AnchoredAtom1306 chi))) ∨
      (((Fin15AnchoredAtom3682 chi ∧
      ¬Fin15AnchoredAtom1471 chi) ∨
      (¬Fin15AnchoredAtom3682 chi ∧
      Fin15AnchoredAtom1146 chi ∧
      Fin15AnchoredAtom1147 chi ∧
      Fin15AnchoredAtom1151 chi ∧
      Fin15AnchoredAtom1306 chi ∧
      Fin15AnchoredAtom1471 chi)) ∨
      ((Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom1146 chi) ∨
      (Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom1148 chi)))))))) ∨
      (((((((Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom1152 chi) ∨
      ((Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom1307 chi) ∨
      (Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom1472 chi))) ∨
      (((¬Fin15AnchoredAtom3683 chi ∧
      Fin15AnchoredAtom1146 chi ∧
      Fin15AnchoredAtom1148 chi ∧
      Fin15AnchoredAtom1152 chi ∧
      Fin15AnchoredAtom1307 chi ∧
      Fin15AnchoredAtom1472 chi) ∨
      (Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom1146 chi)) ∨
      ((Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom1149 chi) ∨
      (Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom1153 chi)))) ∨
      ((((Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom1308 chi) ∨
      (Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom1473 chi)) ∨
      ((¬Fin15AnchoredAtom3684 chi ∧
      Fin15AnchoredAtom1146 chi ∧
      Fin15AnchoredAtom1149 chi ∧
      Fin15AnchoredAtom1153 chi ∧
      Fin15AnchoredAtom1308 chi ∧
      Fin15AnchoredAtom1473 chi) ∨
      (Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom1146 chi))) ∨
      (((Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom1150 chi) ∨
      (Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom1154 chi)) ∨
      ((Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom1309 chi) ∨
      (Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom1474 chi))))) ∨
      (((((¬Fin15AnchoredAtom3685 chi ∧
      Fin15AnchoredAtom1146 chi ∧
      Fin15AnchoredAtom1150 chi ∧
      Fin15AnchoredAtom1154 chi ∧
      Fin15AnchoredAtom1309 chi ∧
      Fin15AnchoredAtom1474 chi) ∨
      (Fin15AnchoredAtom3686 chi ∧
      ¬Fin15AnchoredAtom1148 chi)) ∨
      ((Fin15AnchoredAtom3686 chi ∧
      ¬Fin15AnchoredAtom1155 chi) ∨
      (Fin15AnchoredAtom3686 chi ∧
      ¬Fin15AnchoredAtom1310 chi))) ∨
      (((Fin15AnchoredAtom3686 chi ∧
      ¬Fin15AnchoredAtom1475 chi) ∨
      (¬Fin15AnchoredAtom3686 chi ∧
      Fin15AnchoredAtom1147 chi ∧
      Fin15AnchoredAtom1148 chi ∧
      Fin15AnchoredAtom1155 chi ∧
      Fin15AnchoredAtom1310 chi ∧
      Fin15AnchoredAtom1475 chi)) ∨
      ((Fin15AnchoredAtom3687 chi ∧
      ¬Fin15AnchoredAtom1149 chi) ∨
      (Fin15AnchoredAtom3687 chi ∧
      ¬Fin15AnchoredAtom1311 chi)))) ∨
      ((((Fin15AnchoredAtom3687 chi ∧
      ¬Fin15AnchoredAtom1476 chi) ∨
      (Fin15AnchoredAtom3688 chi ∧
      ¬Fin15AnchoredAtom1150 chi)) ∨
      ((Fin15AnchoredAtom3688 chi ∧
      ¬Fin15AnchoredAtom1312 chi) ∨
      (Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom1148 chi))) ∨
      (((Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom1149 chi) ∨
      (Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom1158 chi)) ∨
      ((Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom1313 chi) ∨
      (Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom1478 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom3689 chi ∧
      Fin15AnchoredAtom1148 chi ∧
      Fin15AnchoredAtom1149 chi ∧
      Fin15AnchoredAtom1158 chi ∧
      Fin15AnchoredAtom1313 chi ∧
      Fin15AnchoredAtom1478 chi) ∨
      (Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom1148 chi)) ∨
      ((Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom1150 chi) ∨
      (Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom1159 chi))) ∨
      (((Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom1314 chi) ∨
      (Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom1479 chi)) ∨
      ((¬Fin15AnchoredAtom3690 chi ∧
      Fin15AnchoredAtom1148 chi ∧
      Fin15AnchoredAtom1150 chi ∧
      Fin15AnchoredAtom1159 chi ∧
      Fin15AnchoredAtom1314 chi ∧
      Fin15AnchoredAtom1479 chi) ∨
      (Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom1149 chi)))) ∨
      ((((Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom1150 chi) ∨
      (Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom1160 chi)) ∨
      ((Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom1315 chi) ∨
      (Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom1480 chi))) ∨
      (((¬Fin15AnchoredAtom3691 chi ∧
      Fin15AnchoredAtom1149 chi ∧
      Fin15AnchoredAtom1150 chi ∧
      Fin15AnchoredAtom1160 chi ∧
      Fin15AnchoredAtom1315 chi ∧
      Fin15AnchoredAtom1480 chi) ∨
      (Fin15AnchoredAtom3692 chi ∧
      ¬Fin15AnchoredAtom1316 chi)) ∨
      ((Fin15AnchoredAtom3692 chi ∧
      ¬Fin15AnchoredAtom1481 chi) ∨
      (¬Fin15AnchoredAtom3692 chi ∧
      Fin15AnchoredAtom1151 chi ∧
      Fin15AnchoredAtom1152 chi ∧
      Fin15AnchoredAtom1155 chi ∧
      Fin15AnchoredAtom1316 chi ∧
      Fin15AnchoredAtom1481 chi))))) ∨
      (((((Fin15AnchoredAtom3693 chi ∧
      ¬Fin15AnchoredAtom1153 chi) ∨
      (Fin15AnchoredAtom3693 chi ∧
      ¬Fin15AnchoredAtom1156 chi)) ∨
      ((Fin15AnchoredAtom3693 chi ∧
      ¬Fin15AnchoredAtom1317 chi) ∨
      (Fin15AnchoredAtom3693 chi ∧
      ¬Fin15AnchoredAtom1482 chi))) ∨
      (((¬Fin15AnchoredAtom3693 chi ∧
      Fin15AnchoredAtom1151 chi ∧
      Fin15AnchoredAtom1153 chi ∧
      Fin15AnchoredAtom1156 chi ∧
      Fin15AnchoredAtom1317 chi ∧
      Fin15AnchoredAtom1482 chi) ∨
      (Fin15AnchoredAtom3694 chi ∧
      ¬Fin15AnchoredAtom1483 chi)) ∨
      ((Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom1152 chi) ∨
      (Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom1153 chi)))) ∨
      ((((Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom1158 chi) ∨
      (Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom1319 chi)) ∨
      ((Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom1484 chi) ∨
      (¬Fin15AnchoredAtom3695 chi ∧
      Fin15AnchoredAtom1152 chi ∧
      Fin15AnchoredAtom1153 chi ∧
      Fin15AnchoredAtom1158 chi ∧
      Fin15AnchoredAtom1319 chi ∧
      Fin15AnchoredAtom1484 chi))) ∨
      (((Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom1152 chi) ∨
      (Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom1154 chi)) ∨
      ((Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom1159 chi) ∨
      (Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom1320 chi))))))) ∨
      ((((((Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom1485 chi) ∨
      ((¬Fin15AnchoredAtom3696 chi ∧
      Fin15AnchoredAtom1152 chi ∧
      Fin15AnchoredAtom1154 chi ∧
      Fin15AnchoredAtom1159 chi ∧
      Fin15AnchoredAtom1320 chi ∧
      Fin15AnchoredAtom1485 chi) ∨
      (Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom1153 chi))) ∨
      (((Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom1154 chi) ∨
      (Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom1160 chi)) ∨
      ((Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom1321 chi) ∨
      (Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom1486 chi)))) ∨
      ((((¬Fin15AnchoredAtom3697 chi ∧
      Fin15AnchoredAtom1153 chi ∧
      Fin15AnchoredAtom1154 chi ∧
      Fin15AnchoredAtom1160 chi ∧
      Fin15AnchoredAtom1321 chi ∧
      Fin15AnchoredAtom1486 chi) ∨
      (Fin15AnchoredAtom3698 chi ∧
      ¬Fin15AnchoredAtom1158 chi)) ∨
      ((Fin15AnchoredAtom3698 chi ∧
      ¬Fin15AnchoredAtom1322 chi) ∨
      (Fin15AnchoredAtom3698 chi ∧
      ¬Fin15AnchoredAtom1487 chi))) ∨
      (((¬Fin15AnchoredAtom3698 chi ∧
      Fin15AnchoredAtom1155 chi ∧
      Fin15AnchoredAtom1156 chi ∧
      Fin15AnchoredAtom1158 chi ∧
      Fin15AnchoredAtom1322 chi ∧
      Fin15AnchoredAtom1487 chi) ∨
      (Fin15AnchoredAtom3699 chi ∧
      ¬Fin15AnchoredAtom1155 chi)) ∨
      ((Fin15AnchoredAtom3699 chi ∧
      ¬Fin15AnchoredAtom1157 chi) ∨
      (Fin15AnchoredAtom3699 chi ∧
      ¬Fin15AnchoredAtom1323 chi))))) ∨
      (((((Fin15AnchoredAtom3699 chi ∧
      ¬Fin15AnchoredAtom1488 chi) ∨
      (Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom1158 chi)) ∨
      ((Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom1159 chi) ∨
      (Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom1160 chi))) ∨
      (((Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom1325 chi) ∨
      (Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom1490 chi)) ∨
      ((¬Fin15AnchoredAtom3701 chi ∧
      Fin15AnchoredAtom1158 chi ∧
      Fin15AnchoredAtom1159 chi ∧
      Fin15AnchoredAtom1160 chi ∧
      Fin15AnchoredAtom1325 chi ∧
      Fin15AnchoredAtom1490 chi) ∨
      (Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom1161 chi)))) ∨
      ((((Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom1162 chi) ∨
      (Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom1170 chi)) ∨
      ((Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom1206 chi) ∨
      (Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom1491 chi))) ∨
      (((¬Fin15AnchoredAtom3702 chi ∧
      Fin15AnchoredAtom1161 chi ∧
      Fin15AnchoredAtom1162 chi ∧
      Fin15AnchoredAtom1170 chi ∧
      Fin15AnchoredAtom1206 chi ∧
      Fin15AnchoredAtom1491 chi) ∨
      (Fin15AnchoredAtom3703 chi ∧
      ¬Fin15AnchoredAtom1161 chi)) ∨
      ((Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom1161 chi) ∨
      (Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom1164 chi)))))) ∨
      ((((((Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom1172 chi) ∨
      (Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom1208 chi)) ∨
      ((Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom1493 chi) ∨
      (¬Fin15AnchoredAtom3704 chi ∧
      Fin15AnchoredAtom1161 chi ∧
      Fin15AnchoredAtom1164 chi ∧
      Fin15AnchoredAtom1172 chi ∧
      Fin15AnchoredAtom1208 chi ∧
      Fin15AnchoredAtom1493 chi))) ∨
      (((Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom1161 chi) ∨
      (Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom1165 chi)) ∨
      ((Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom1173 chi) ∨
      (Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom1209 chi)))) ∨
      ((((Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom1494 chi) ∨
      (¬Fin15AnchoredAtom3705 chi ∧
      Fin15AnchoredAtom1161 chi ∧
      Fin15AnchoredAtom1165 chi ∧
      Fin15AnchoredAtom1173 chi ∧
      Fin15AnchoredAtom1209 chi ∧
      Fin15AnchoredAtom1494 chi)) ∨
      ((Fin15AnchoredAtom3706 chi ∧
      ¬Fin15AnchoredAtom1210 chi) ∨
      (Fin15AnchoredAtom3706 chi ∧
      ¬Fin15AnchoredAtom1495 chi))) ∨
      (((Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom1161 chi) ∨
      (Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom1167 chi)) ∨
      ((Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom1175 chi) ∨
      (Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom1211 chi))))) ∨
      (((((Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom1496 chi) ∨
      (¬Fin15AnchoredAtom3707 chi ∧
      Fin15AnchoredAtom1161 chi ∧
      Fin15AnchoredAtom1167 chi ∧
      Fin15AnchoredAtom1175 chi ∧
      Fin15AnchoredAtom1211 chi ∧
      Fin15AnchoredAtom1496 chi)) ∨
      ((Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom1161 chi) ∨
      (Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom1168 chi))) ∨
      (((Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom1176 chi) ∨
      (Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom1212 chi)) ∨
      ((Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom1497 chi) ∨
      (¬Fin15AnchoredAtom3708 chi ∧
      Fin15AnchoredAtom1161 chi ∧
      Fin15AnchoredAtom1168 chi ∧
      Fin15AnchoredAtom1176 chi ∧
      Fin15AnchoredAtom1212 chi ∧
      Fin15AnchoredAtom1497 chi)))) ∨
      ((((Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom1161 chi) ∨
      (Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom1169 chi)) ∨
      ((Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom1177 chi) ∨
      (Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom1213 chi))) ∨
      (((Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom1498 chi) ∨
      (¬Fin15AnchoredAtom3709 chi ∧
      Fin15AnchoredAtom1161 chi ∧
      Fin15AnchoredAtom1169 chi ∧
      Fin15AnchoredAtom1177 chi ∧
      Fin15AnchoredAtom1213 chi ∧
      Fin15AnchoredAtom1498 chi)) ∨
      ((Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom1162 chi) ∨
      (Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom1164 chi)))))))))) := by
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
                exact fin15Anchored_clause23726 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23727 chi hbad
                ·
                  exact fin15Anchored_clause23728 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23729 chi hbad
                ·
                  exact fin15Anchored_clause23730 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23731 chi hbad
                ·
                  exact fin15Anchored_clause23732 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23733 chi hbad
                ·
                  exact fin15Anchored_clause23734 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23735 chi hbad
                ·
                  exact fin15Anchored_clause23736 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23737 chi hbad
                ·
                  exact fin15Anchored_clause23738 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23739 chi hbad
                ·
                  exact fin15Anchored_clause23740 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23741 chi hbad
                ·
                  exact fin15Anchored_clause23742 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23743 chi hbad
                ·
                  exact fin15Anchored_clause23744 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23745 chi hbad
                ·
                  exact fin15Anchored_clause23746 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23747 chi hbad
                ·
                  exact fin15Anchored_clause23748 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23749 chi hbad
                ·
                  exact fin15Anchored_clause23750 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23751 chi hbad
                ·
                  exact fin15Anchored_clause23752 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23753 chi hbad
                ·
                  exact fin15Anchored_clause23754 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23755 chi hbad
                ·
                  exact fin15Anchored_clause23756 chi hbad
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
                  exact fin15Anchored_clause23757 chi hbad
                ·
                  exact fin15Anchored_clause23758 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23759 chi hbad
                ·
                  exact fin15Anchored_clause23760 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23761 chi hbad
                ·
                  exact fin15Anchored_clause23762 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23763 chi hbad
                ·
                  exact fin15Anchored_clause23764 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23765 chi hbad
                ·
                  exact fin15Anchored_clause23766 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23767 chi hbad
                ·
                  exact fin15Anchored_clause23768 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23769 chi hbad
                ·
                  exact fin15Anchored_clause23770 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23771 chi hbad
                ·
                  exact fin15Anchored_clause23772 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23773 chi hbad
                ·
                  exact fin15Anchored_clause23774 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23775 chi hbad
                ·
                  exact fin15Anchored_clause23776 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23777 chi hbad
                ·
                  exact fin15Anchored_clause23778 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23779 chi hbad
                ·
                  exact fin15Anchored_clause23780 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23781 chi hbad
                ·
                  exact fin15Anchored_clause23782 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23783 chi hbad
                ·
                  exact fin15Anchored_clause23784 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23785 chi hbad
                ·
                  exact fin15Anchored_clause23786 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23787 chi hbad
                ·
                  exact fin15Anchored_clause23788 chi hbad
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
                exact fin15Anchored_clause23789 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23790 chi hbad
                ·
                  exact fin15Anchored_clause23791 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23792 chi hbad
                ·
                  exact fin15Anchored_clause23793 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23794 chi hbad
                ·
                  exact fin15Anchored_clause23795 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23796 chi hbad
                ·
                  exact fin15Anchored_clause23797 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23798 chi hbad
                ·
                  exact fin15Anchored_clause23799 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23800 chi hbad
                ·
                  exact fin15Anchored_clause23801 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23802 chi hbad
                ·
                  exact fin15Anchored_clause23803 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23804 chi hbad
                ·
                  exact fin15Anchored_clause23805 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23806 chi hbad
                ·
                  exact fin15Anchored_clause23807 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23808 chi hbad
                ·
                  exact fin15Anchored_clause23809 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23810 chi hbad
                ·
                  exact fin15Anchored_clause23811 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23812 chi hbad
                ·
                  exact fin15Anchored_clause23813 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23814 chi hbad
                ·
                  exact fin15Anchored_clause23815 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23816 chi hbad
                ·
                  exact fin15Anchored_clause23817 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23818 chi hbad
                ·
                  exact fin15Anchored_clause23819 chi hbad
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
                  exact fin15Anchored_clause23820 chi hbad
                ·
                  exact fin15Anchored_clause23821 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23822 chi hbad
                ·
                  exact fin15Anchored_clause23823 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23824 chi hbad
                ·
                  exact fin15Anchored_clause23825 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23826 chi hbad
                ·
                  exact fin15Anchored_clause23827 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23828 chi hbad
                ·
                  exact fin15Anchored_clause23829 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23830 chi hbad
                ·
                  exact fin15Anchored_clause23831 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23832 chi hbad
                ·
                  exact fin15Anchored_clause23833 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23834 chi hbad
                ·
                  exact fin15Anchored_clause23835 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23836 chi hbad
                ·
                  exact fin15Anchored_clause23837 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23838 chi hbad
                ·
                  exact fin15Anchored_clause23839 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23840 chi hbad
                ·
                  exact fin15Anchored_clause23841 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23842 chi hbad
                ·
                  exact fin15Anchored_clause23843 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23844 chi hbad
                ·
                  exact fin15Anchored_clause23845 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23846 chi hbad
                ·
                  exact fin15Anchored_clause23847 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23848 chi hbad
                ·
                  exact fin15Anchored_clause23849 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23850 chi hbad
                ·
                  exact fin15Anchored_clause23851 chi hbad
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
                exact fin15Anchored_clause23852 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23853 chi hbad
                ·
                  exact fin15Anchored_clause23854 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23855 chi hbad
                ·
                  exact fin15Anchored_clause23856 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23857 chi hbad
                ·
                  exact fin15Anchored_clause23858 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23859 chi hbad
                ·
                  exact fin15Anchored_clause23860 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23861 chi hbad
                ·
                  exact fin15Anchored_clause23862 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23863 chi hbad
                ·
                  exact fin15Anchored_clause23864 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23865 chi hbad
                ·
                  exact fin15Anchored_clause23866 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23867 chi hbad
                ·
                  exact fin15Anchored_clause23868 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23869 chi hbad
                ·
                  exact fin15Anchored_clause23870 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23871 chi hbad
                ·
                  exact fin15Anchored_clause23872 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23873 chi hbad
                ·
                  exact fin15Anchored_clause23874 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23875 chi hbad
                ·
                  exact fin15Anchored_clause23876 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23877 chi hbad
                ·
                  exact fin15Anchored_clause23878 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23879 chi hbad
                ·
                  exact fin15Anchored_clause23880 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23881 chi hbad
                ·
                  exact fin15Anchored_clause23882 chi hbad
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
                  exact fin15Anchored_clause23883 chi hbad
                ·
                  exact fin15Anchored_clause23884 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23885 chi hbad
                ·
                  exact fin15Anchored_clause23886 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23887 chi hbad
                ·
                  exact fin15Anchored_clause23888 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23889 chi hbad
                ·
                  exact fin15Anchored_clause23890 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23891 chi hbad
                ·
                  exact fin15Anchored_clause23892 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23893 chi hbad
                ·
                  exact fin15Anchored_clause23894 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23895 chi hbad
                ·
                  exact fin15Anchored_clause23896 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23897 chi hbad
                ·
                  exact fin15Anchored_clause23898 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23899 chi hbad
                ·
                  exact fin15Anchored_clause23900 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23901 chi hbad
                ·
                  exact fin15Anchored_clause23902 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23903 chi hbad
                ·
                  exact fin15Anchored_clause23904 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23905 chi hbad
                ·
                  exact fin15Anchored_clause23906 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23907 chi hbad
                ·
                  exact fin15Anchored_clause23908 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23909 chi hbad
                ·
                  exact fin15Anchored_clause23910 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23911 chi hbad
                ·
                  exact fin15Anchored_clause23912 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23913 chi hbad
                ·
                  exact fin15Anchored_clause23914 chi hbad
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
                exact fin15Anchored_clause23915 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23916 chi hbad
                ·
                  exact fin15Anchored_clause23917 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23918 chi hbad
                ·
                  exact fin15Anchored_clause23919 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23920 chi hbad
                ·
                  exact fin15Anchored_clause23921 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23922 chi hbad
                ·
                  exact fin15Anchored_clause23923 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23924 chi hbad
                ·
                  exact fin15Anchored_clause23925 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23926 chi hbad
                ·
                  exact fin15Anchored_clause23927 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23928 chi hbad
                ·
                  exact fin15Anchored_clause23929 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23930 chi hbad
                ·
                  exact fin15Anchored_clause23931 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23932 chi hbad
                ·
                  exact fin15Anchored_clause23933 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23934 chi hbad
                ·
                  exact fin15Anchored_clause23935 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23936 chi hbad
                ·
                  exact fin15Anchored_clause23937 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23938 chi hbad
                ·
                  exact fin15Anchored_clause23939 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23940 chi hbad
                ·
                  exact fin15Anchored_clause23941 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23942 chi hbad
                ·
                  exact fin15Anchored_clause23943 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23944 chi hbad
                ·
                  exact fin15Anchored_clause23945 chi hbad
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
                  exact fin15Anchored_clause23946 chi hbad
                ·
                  exact fin15Anchored_clause23947 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23948 chi hbad
                ·
                  exact fin15Anchored_clause23949 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23950 chi hbad
                ·
                  exact fin15Anchored_clause23951 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23952 chi hbad
                ·
                  exact fin15Anchored_clause23953 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23954 chi hbad
                ·
                  exact fin15Anchored_clause23955 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23956 chi hbad
                ·
                  exact fin15Anchored_clause23957 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23958 chi hbad
                ·
                  exact fin15Anchored_clause23959 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23960 chi hbad
                ·
                  exact fin15Anchored_clause23961 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23962 chi hbad
                ·
                  exact fin15Anchored_clause23963 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23964 chi hbad
                ·
                  exact fin15Anchored_clause23965 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23966 chi hbad
                ·
                  exact fin15Anchored_clause23967 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23968 chi hbad
                ·
                  exact fin15Anchored_clause23969 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23970 chi hbad
                ·
                  exact fin15Anchored_clause23971 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23972 chi hbad
                ·
                  exact fin15Anchored_clause23973 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23974 chi hbad
                ·
                  exact fin15Anchored_clause23975 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23976 chi hbad
                ·
                  exact fin15Anchored_clause23977 chi hbad

end ErdosSzekeres

end
