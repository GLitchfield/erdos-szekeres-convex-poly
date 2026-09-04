module

public import ErdosSzekeres.Fin15AnchoredClauseChunk181
public import ErdosSzekeres.Fin15AnchoredClauseChunk182
public import ErdosSzekeres.Fin15AnchoredClauseChunk183

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 092. -/

theorem fin15Anchored_rejectSemanticSegment092
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom3510 chi ∧
      ¬Fin15AnchoredAtom1794 chi) ∨
      ((¬Fin15AnchoredAtom3510 chi ∧
      Fin15AnchoredAtom1073 chi ∧
      Fin15AnchoredAtom1075 chi ∧
      Fin15AnchoredAtom1084 chi ∧
      Fin15AnchoredAtom1094 chi ∧
      Fin15AnchoredAtom1794 chi) ∨
      (Fin15AnchoredAtom3511 chi ∧
      ¬Fin15AnchoredAtom1074 chi))) ∨
      (((Fin15AnchoredAtom3511 chi ∧
      ¬Fin15AnchoredAtom1075 chi) ∨
      (Fin15AnchoredAtom3511 chi ∧
      ¬Fin15AnchoredAtom1085 chi)) ∨
      ((Fin15AnchoredAtom3511 chi ∧
      ¬Fin15AnchoredAtom1095 chi) ∨
      (Fin15AnchoredAtom3511 chi ∧
      ¬Fin15AnchoredAtom1795 chi)))) ∨
      ((((Fin15AnchoredAtom3515 chi ∧
      ¬Fin15AnchoredAtom1077 chi) ∨
      (Fin15AnchoredAtom3515 chi ∧
      ¬Fin15AnchoredAtom1078 chi)) ∨
      ((Fin15AnchoredAtom3515 chi ∧
      ¬Fin15AnchoredAtom1083 chi) ∨
      (Fin15AnchoredAtom3515 chi ∧
      ¬Fin15AnchoredAtom1099 chi))) ∨
      (((Fin15AnchoredAtom3515 chi ∧
      ¬Fin15AnchoredAtom1799 chi) ∨
      (¬Fin15AnchoredAtom3515 chi ∧
      Fin15AnchoredAtom1077 chi ∧
      Fin15AnchoredAtom1078 chi ∧
      Fin15AnchoredAtom1083 chi ∧
      Fin15AnchoredAtom1099 chi ∧
      Fin15AnchoredAtom1799 chi)) ∨
      ((Fin15AnchoredAtom3516 chi ∧
      ¬Fin15AnchoredAtom1079 chi) ∨
      (Fin15AnchoredAtom3516 chi ∧
      ¬Fin15AnchoredAtom1100 chi))))) ∨
      (((((Fin15AnchoredAtom3516 chi ∧
      ¬Fin15AnchoredAtom1800 chi) ∨
      (¬Fin15AnchoredAtom3516 chi ∧
      Fin15AnchoredAtom1077 chi ∧
      Fin15AnchoredAtom1079 chi ∧
      Fin15AnchoredAtom1084 chi ∧
      Fin15AnchoredAtom1100 chi ∧
      Fin15AnchoredAtom1800 chi)) ∨
      ((Fin15AnchoredAtom3517 chi ∧
      ¬Fin15AnchoredAtom1078 chi) ∨
      (Fin15AnchoredAtom3517 chi ∧
      ¬Fin15AnchoredAtom1079 chi))) ∨
      (((Fin15AnchoredAtom3517 chi ∧
      ¬Fin15AnchoredAtom1101 chi) ∨
      (Fin15AnchoredAtom3517 chi ∧
      ¬Fin15AnchoredAtom1801 chi)) ∨
      ((¬Fin15AnchoredAtom3517 chi ∧
      Fin15AnchoredAtom1078 chi ∧
      Fin15AnchoredAtom1079 chi ∧
      Fin15AnchoredAtom1085 chi ∧
      Fin15AnchoredAtom1101 chi ∧
      Fin15AnchoredAtom1801 chi) ∨
      (Fin15AnchoredAtom3521 chi ∧
      ¬Fin15AnchoredAtom1084 chi)))) ∨
      ((((Fin15AnchoredAtom3521 chi ∧
      ¬Fin15AnchoredAtom1105 chi) ∨
      (Fin15AnchoredAtom3521 chi ∧
      ¬Fin15AnchoredAtom1805 chi)) ∨
      ((¬Fin15AnchoredAtom3521 chi ∧
      Fin15AnchoredAtom1083 chi ∧
      Fin15AnchoredAtom1084 chi ∧
      Fin15AnchoredAtom1085 chi ∧
      Fin15AnchoredAtom1105 chi ∧
      Fin15AnchoredAtom1805 chi) ∨
      (Fin15AnchoredAtom3522 chi ∧
      ¬Fin15AnchoredAtom1086 chi))) ∨
      (((Fin15AnchoredAtom3522 chi ∧
      ¬Fin15AnchoredAtom1087 chi) ∨
      (Fin15AnchoredAtom3522 chi ∧
      ¬Fin15AnchoredAtom1096 chi)) ∨
      ((Fin15AnchoredAtom3522 chi ∧
      ¬Fin15AnchoredAtom1806 chi) ∨
      (¬Fin15AnchoredAtom3522 chi ∧
      Fin15AnchoredAtom1086 chi ∧
      Fin15AnchoredAtom1087 chi ∧
      Fin15AnchoredAtom1090 chi ∧
      Fin15AnchoredAtom1096 chi ∧
      Fin15AnchoredAtom1806 chi)))))) ∨
      ((((((Fin15AnchoredAtom3523 chi ∧
      ¬Fin15AnchoredAtom1086 chi) ∨
      (Fin15AnchoredAtom3523 chi ∧
      ¬Fin15AnchoredAtom1088 chi)) ∨
      ((Fin15AnchoredAtom3524 chi ∧
      ¬Fin15AnchoredAtom1086 chi) ∨
      (Fin15AnchoredAtom3525 chi ∧
      ¬Fin15AnchoredAtom1087 chi))) ∨
      (((Fin15AnchoredAtom3525 chi ∧
      ¬Fin15AnchoredAtom1088 chi) ∨
      (Fin15AnchoredAtom3525 chi ∧
      ¬Fin15AnchoredAtom1093 chi)) ∨
      ((Fin15AnchoredAtom3525 chi ∧
      ¬Fin15AnchoredAtom1099 chi) ∨
      (Fin15AnchoredAtom3525 chi ∧
      ¬Fin15AnchoredAtom1809 chi)))) ∨
      ((((¬Fin15AnchoredAtom3525 chi ∧
      Fin15AnchoredAtom1087 chi ∧
      Fin15AnchoredAtom1088 chi ∧
      Fin15AnchoredAtom1093 chi ∧
      Fin15AnchoredAtom1099 chi ∧
      Fin15AnchoredAtom1809 chi) ∨
      (Fin15AnchoredAtom3526 chi ∧
      ¬Fin15AnchoredAtom1087 chi)) ∨
      ((Fin15AnchoredAtom3526 chi ∧
      ¬Fin15AnchoredAtom1089 chi) ∨
      (Fin15AnchoredAtom3526 chi ∧
      ¬Fin15AnchoredAtom1094 chi))) ∨
      (((Fin15AnchoredAtom3526 chi ∧
      ¬Fin15AnchoredAtom1100 chi) ∨
      (Fin15AnchoredAtom3526 chi ∧
      ¬Fin15AnchoredAtom1810 chi)) ∨
      ((¬Fin15AnchoredAtom3526 chi ∧
      Fin15AnchoredAtom1087 chi ∧
      Fin15AnchoredAtom1089 chi ∧
      Fin15AnchoredAtom1094 chi ∧
      Fin15AnchoredAtom1100 chi ∧
      Fin15AnchoredAtom1810 chi) ∨
      (Fin15AnchoredAtom3527 chi ∧
      ¬Fin15AnchoredAtom1088 chi))))) ∨
      (((((Fin15AnchoredAtom3527 chi ∧
      ¬Fin15AnchoredAtom1089 chi) ∨
      (Fin15AnchoredAtom3527 chi ∧
      ¬Fin15AnchoredAtom1095 chi)) ∨
      ((Fin15AnchoredAtom3527 chi ∧
      ¬Fin15AnchoredAtom1101 chi) ∨
      (Fin15AnchoredAtom3527 chi ∧
      ¬Fin15AnchoredAtom1811 chi))) ∨
      (((¬Fin15AnchoredAtom3527 chi ∧
      Fin15AnchoredAtom1088 chi ∧
      Fin15AnchoredAtom1089 chi ∧
      Fin15AnchoredAtom1095 chi ∧
      Fin15AnchoredAtom1101 chi ∧
      Fin15AnchoredAtom1811 chi) ∨
      (Fin15AnchoredAtom3528 chi ∧
      ¬Fin15AnchoredAtom1090 chi)) ∨
      ((Fin15AnchoredAtom3528 chi ∧
      ¬Fin15AnchoredAtom1093 chi) ∨
      (Fin15AnchoredAtom3529 chi ∧
      ¬Fin15AnchoredAtom1090 chi)))) ∨
      ((((Fin15AnchoredAtom3529 chi ∧
      ¬Fin15AnchoredAtom1094 chi) ∨
      (Fin15AnchoredAtom3529 chi ∧
      ¬Fin15AnchoredAtom1103 chi)) ∨
      ((Fin15AnchoredAtom3531 chi ∧
      ¬Fin15AnchoredAtom1093 chi) ∨
      (Fin15AnchoredAtom3531 chi ∧
      ¬Fin15AnchoredAtom1094 chi))) ∨
      (((Fin15AnchoredAtom3531 chi ∧
      ¬Fin15AnchoredAtom1095 chi) ∨
      (Fin15AnchoredAtom3531 chi ∧
      ¬Fin15AnchoredAtom1105 chi)) ∨
      ((Fin15AnchoredAtom3531 chi ∧
      ¬Fin15AnchoredAtom1815 chi) ∨
      (¬Fin15AnchoredAtom3531 chi ∧
      Fin15AnchoredAtom1093 chi ∧
      Fin15AnchoredAtom1094 chi ∧
      Fin15AnchoredAtom1095 chi ∧
      Fin15AnchoredAtom1105 chi ∧
      Fin15AnchoredAtom1815 chi))))))) ∨
      ((((((Fin15AnchoredAtom3532 chi ∧
      ¬Fin15AnchoredAtom1099 chi) ∨
      ((Fin15AnchoredAtom3532 chi ∧
      ¬Fin15AnchoredAtom1102 chi) ∨
      (Fin15AnchoredAtom3532 chi ∧
      ¬Fin15AnchoredAtom1816 chi))) ∨
      (((¬Fin15AnchoredAtom3532 chi ∧
      Fin15AnchoredAtom1096 chi ∧
      Fin15AnchoredAtom1097 chi ∧
      Fin15AnchoredAtom1099 chi ∧
      Fin15AnchoredAtom1102 chi ∧
      Fin15AnchoredAtom1816 chi) ∨
      (Fin15AnchoredAtom3533 chi ∧
      ¬Fin15AnchoredAtom1100 chi)) ∨
      ((Fin15AnchoredAtom3534 chi ∧
      ¬Fin15AnchoredAtom1101 chi) ∨
      (Fin15AnchoredAtom3535 chi ∧
      ¬Fin15AnchoredAtom1099 chi)))) ∨
      ((((Fin15AnchoredAtom3535 chi ∧
      ¬Fin15AnchoredAtom1100 chi) ∨
      (Fin15AnchoredAtom3535 chi ∧
      ¬Fin15AnchoredAtom1101 chi)) ∨
      ((Fin15AnchoredAtom3535 chi ∧
      ¬Fin15AnchoredAtom1105 chi) ∨
      (Fin15AnchoredAtom3535 chi ∧
      ¬Fin15AnchoredAtom1819 chi))) ∨
      (((¬Fin15AnchoredAtom3535 chi ∧
      Fin15AnchoredAtom1099 chi ∧
      Fin15AnchoredAtom1100 chi ∧
      Fin15AnchoredAtom1101 chi ∧
      Fin15AnchoredAtom1105 chi ∧
      Fin15AnchoredAtom1819 chi) ∨
      (Fin15AnchoredAtom3536 chi ∧
      ¬Fin15AnchoredAtom1105 chi)) ∨
      ((Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom1106 chi) ∨
      (Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom1107 chi))))) ∨
      (((((Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom1116 chi) ∨
      (Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom1161 chi)) ∨
      ((Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom1326 chi) ∨
      (¬Fin15AnchoredAtom3537 chi ∧
      Fin15AnchoredAtom1106 chi ∧
      Fin15AnchoredAtom1107 chi ∧
      Fin15AnchoredAtom1116 chi ∧
      Fin15AnchoredAtom1161 chi ∧
      Fin15AnchoredAtom1326 chi))) ∨
      (((Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom1106 chi) ∨
      (Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom1108 chi)) ∨
      ((Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom1117 chi) ∨
      (Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom1162 chi)))) ∨
      ((((Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom1327 chi) ∨
      (¬Fin15AnchoredAtom3538 chi ∧
      Fin15AnchoredAtom1106 chi ∧
      Fin15AnchoredAtom1108 chi ∧
      Fin15AnchoredAtom1117 chi ∧
      Fin15AnchoredAtom1162 chi ∧
      Fin15AnchoredAtom1327 chi)) ∨
      ((Fin15AnchoredAtom3539 chi ∧
      ¬Fin15AnchoredAtom1328 chi) ∨
      (Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom1106 chi))) ∨
      (((Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom1110 chi) ∨
      (Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom1119 chi)) ∨
      ((Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom1164 chi) ∨
      (Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom1329 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom3540 chi ∧
      Fin15AnchoredAtom1106 chi ∧
      Fin15AnchoredAtom1110 chi ∧
      Fin15AnchoredAtom1119 chi ∧
      Fin15AnchoredAtom1164 chi ∧
      Fin15AnchoredAtom1329 chi) ∨
      (Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom1106 chi)) ∨
      ((Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom1111 chi) ∨
      (Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom1120 chi))) ∨
      (((Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom1165 chi) ∨
      (Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom1330 chi)) ∨
      ((¬Fin15AnchoredAtom3541 chi ∧
      Fin15AnchoredAtom1106 chi ∧
      Fin15AnchoredAtom1111 chi ∧
      Fin15AnchoredAtom1120 chi ∧
      Fin15AnchoredAtom1165 chi ∧
      Fin15AnchoredAtom1330 chi) ∨
      (Fin15AnchoredAtom3542 chi ∧
      ¬Fin15AnchoredAtom1106 chi)))) ∨
      ((((Fin15AnchoredAtom3542 chi ∧
      ¬Fin15AnchoredAtom1112 chi) ∨
      (Fin15AnchoredAtom3542 chi ∧
      ¬Fin15AnchoredAtom1166 chi)) ∨
      ((Fin15AnchoredAtom3542 chi ∧
      ¬Fin15AnchoredAtom1331 chi) ∨
      (¬Fin15AnchoredAtom3542 chi ∧
      Fin15AnchoredAtom1106 chi ∧
      Fin15AnchoredAtom1112 chi ∧
      Fin15AnchoredAtom1121 chi ∧
      Fin15AnchoredAtom1166 chi ∧
      Fin15AnchoredAtom1331 chi))) ∨
      (((Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom1106 chi) ∨
      (Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom1113 chi)) ∨
      ((Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom1122 chi) ∨
      (Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom1167 chi))))) ∨
      (((((Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom1332 chi) ∨
      (¬Fin15AnchoredAtom3543 chi ∧
      Fin15AnchoredAtom1106 chi ∧
      Fin15AnchoredAtom1113 chi ∧
      Fin15AnchoredAtom1122 chi ∧
      Fin15AnchoredAtom1167 chi ∧
      Fin15AnchoredAtom1332 chi)) ∨
      ((Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom1106 chi) ∨
      (Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom1114 chi))) ∨
      (((Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom1123 chi) ∨
      (Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom1168 chi)) ∨
      ((Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom1333 chi) ∨
      (¬Fin15AnchoredAtom3544 chi ∧
      Fin15AnchoredAtom1106 chi ∧
      Fin15AnchoredAtom1114 chi ∧
      Fin15AnchoredAtom1123 chi ∧
      Fin15AnchoredAtom1168 chi ∧
      Fin15AnchoredAtom1333 chi)))) ∨
      ((((Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom1106 chi) ∨
      (Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom1115 chi)) ∨
      ((Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom1124 chi) ∨
      (Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom1169 chi))) ∨
      (((Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom1334 chi) ∨
      (¬Fin15AnchoredAtom3545 chi ∧
      Fin15AnchoredAtom1106 chi ∧
      Fin15AnchoredAtom1115 chi ∧
      Fin15AnchoredAtom1124 chi ∧
      Fin15AnchoredAtom1169 chi ∧
      Fin15AnchoredAtom1334 chi)) ∨
      ((Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom1107 chi) ∨
      (Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom1108 chi)))))))) ∨
      (((((((Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom1125 chi) ∨
      ((Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom1170 chi) ∨
      (Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom1335 chi))) ∨
      (((¬Fin15AnchoredAtom3546 chi ∧
      Fin15AnchoredAtom1107 chi ∧
      Fin15AnchoredAtom1108 chi ∧
      Fin15AnchoredAtom1125 chi ∧
      Fin15AnchoredAtom1170 chi ∧
      Fin15AnchoredAtom1335 chi) ∨
      (Fin15AnchoredAtom3547 chi ∧
      ¬Fin15AnchoredAtom1107 chi)) ∨
      ((Fin15AnchoredAtom3547 chi ∧
      ¬Fin15AnchoredAtom1336 chi) ∨
      (Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom1107 chi)))) ∨
      ((((Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom1110 chi) ∨
      (Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom1127 chi)) ∨
      ((Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom1172 chi) ∨
      (Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom1337 chi))) ∨
      (((¬Fin15AnchoredAtom3548 chi ∧
      Fin15AnchoredAtom1107 chi ∧
      Fin15AnchoredAtom1110 chi ∧
      Fin15AnchoredAtom1127 chi ∧
      Fin15AnchoredAtom1172 chi ∧
      Fin15AnchoredAtom1337 chi) ∨
      (Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom1107 chi)) ∨
      ((Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom1111 chi) ∨
      (Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom1128 chi))))) ∨
      (((((Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom1173 chi) ∨
      (Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom1338 chi)) ∨
      ((¬Fin15AnchoredAtom3549 chi ∧
      Fin15AnchoredAtom1107 chi ∧
      Fin15AnchoredAtom1111 chi ∧
      Fin15AnchoredAtom1128 chi ∧
      Fin15AnchoredAtom1173 chi ∧
      Fin15AnchoredAtom1338 chi) ∨
      (Fin15AnchoredAtom3550 chi ∧
      ¬Fin15AnchoredAtom1107 chi))) ∨
      (((Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom1107 chi) ∨
      (Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom1113 chi)) ∨
      ((Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom1130 chi) ∨
      (Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom1175 chi)))) ∨
      ((((Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom1340 chi) ∨
      (¬Fin15AnchoredAtom3551 chi ∧
      Fin15AnchoredAtom1107 chi ∧
      Fin15AnchoredAtom1113 chi ∧
      Fin15AnchoredAtom1130 chi ∧
      Fin15AnchoredAtom1175 chi ∧
      Fin15AnchoredAtom1340 chi)) ∨
      ((Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom1107 chi) ∨
      (Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom1114 chi))) ∨
      (((Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom1131 chi) ∨
      (Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom1176 chi)) ∨
      ((Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom1341 chi) ∨
      (¬Fin15AnchoredAtom3552 chi ∧
      Fin15AnchoredAtom1107 chi ∧
      Fin15AnchoredAtom1114 chi ∧
      Fin15AnchoredAtom1131 chi ∧
      Fin15AnchoredAtom1176 chi ∧
      Fin15AnchoredAtom1341 chi)))))) ∨
      ((((((Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom1107 chi) ∨
      (Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom1115 chi)) ∨
      ((Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom1132 chi) ∨
      (Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom1177 chi))) ∨
      (((Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom1342 chi) ∨
      (¬Fin15AnchoredAtom3553 chi ∧
      Fin15AnchoredAtom1107 chi ∧
      Fin15AnchoredAtom1115 chi ∧
      Fin15AnchoredAtom1132 chi ∧
      Fin15AnchoredAtom1177 chi ∧
      Fin15AnchoredAtom1342 chi)) ∨
      ((Fin15AnchoredAtom3554 chi ∧
      ¬Fin15AnchoredAtom1108 chi) ∨
      (¬Fin15AnchoredAtom3554 chi ∧
      Fin15AnchoredAtom1108 chi ∧
      Fin15AnchoredAtom1109 chi ∧
      Fin15AnchoredAtom1133 chi ∧
      Fin15AnchoredAtom1178 chi ∧
      Fin15AnchoredAtom1343 chi)))) ∨
      ((((Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom1108 chi) ∨
      (Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom1110 chi)) ∨
      ((Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom1134 chi) ∨
      (Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom1179 chi))) ∨
      (((Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom1344 chi) ∨
      (¬Fin15AnchoredAtom3555 chi ∧
      Fin15AnchoredAtom1108 chi ∧
      Fin15AnchoredAtom1110 chi ∧
      Fin15AnchoredAtom1134 chi ∧
      Fin15AnchoredAtom1179 chi ∧
      Fin15AnchoredAtom1344 chi)) ∨
      ((Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom1108 chi) ∨
      (Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom1111 chi))))) ∨
      (((((Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom1135 chi) ∨
      (Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom1180 chi)) ∨
      ((Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom1345 chi) ∨
      (¬Fin15AnchoredAtom3556 chi ∧
      Fin15AnchoredAtom1108 chi ∧
      Fin15AnchoredAtom1111 chi ∧
      Fin15AnchoredAtom1135 chi ∧
      Fin15AnchoredAtom1180 chi ∧
      Fin15AnchoredAtom1345 chi))) ∨
      (((Fin15AnchoredAtom3557 chi ∧
      ¬Fin15AnchoredAtom1108 chi) ∨
      (¬Fin15AnchoredAtom3557 chi ∧
      Fin15AnchoredAtom1108 chi ∧
      Fin15AnchoredAtom1112 chi ∧
      Fin15AnchoredAtom1136 chi ∧
      Fin15AnchoredAtom1181 chi ∧
      Fin15AnchoredAtom1346 chi)) ∨
      ((Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom1108 chi) ∨
      (Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom1113 chi)))) ∨
      ((((Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom1137 chi) ∨
      (Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom1182 chi)) ∨
      ((Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom1347 chi) ∨
      (¬Fin15AnchoredAtom3558 chi ∧
      Fin15AnchoredAtom1108 chi ∧
      Fin15AnchoredAtom1113 chi ∧
      Fin15AnchoredAtom1137 chi ∧
      Fin15AnchoredAtom1182 chi ∧
      Fin15AnchoredAtom1347 chi))) ∨
      (((Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom1108 chi) ∨
      (Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom1114 chi)) ∨
      ((Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom1138 chi) ∨
      (Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom1183 chi))))))) ∨
      ((((((Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom1348 chi) ∨
      ((¬Fin15AnchoredAtom3559 chi ∧
      Fin15AnchoredAtom1108 chi ∧
      Fin15AnchoredAtom1114 chi ∧
      Fin15AnchoredAtom1138 chi ∧
      Fin15AnchoredAtom1183 chi ∧
      Fin15AnchoredAtom1348 chi) ∨
      (Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom1108 chi))) ∨
      (((Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom1115 chi) ∨
      (Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom1139 chi)) ∨
      ((Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom1184 chi) ∨
      (Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom1349 chi)))) ∨
      ((((¬Fin15AnchoredAtom3560 chi ∧
      Fin15AnchoredAtom1108 chi ∧
      Fin15AnchoredAtom1115 chi ∧
      Fin15AnchoredAtom1139 chi ∧
      Fin15AnchoredAtom1184 chi ∧
      Fin15AnchoredAtom1349 chi) ∨
      (¬Fin15AnchoredAtom3561 chi ∧
      Fin15AnchoredAtom1109 chi ∧
      Fin15AnchoredAtom1110 chi ∧
      Fin15AnchoredAtom1140 chi ∧
      Fin15AnchoredAtom1185 chi ∧
      Fin15AnchoredAtom1350 chi)) ∨
      ((¬Fin15AnchoredAtom3562 chi ∧
      Fin15AnchoredAtom1109 chi ∧
      Fin15AnchoredAtom1111 chi ∧
      Fin15AnchoredAtom1141 chi ∧
      Fin15AnchoredAtom1186 chi ∧
      Fin15AnchoredAtom1351 chi) ∨
      (Fin15AnchoredAtom3565 chi ∧
      ¬Fin15AnchoredAtom1144 chi))) ∨
      (((Fin15AnchoredAtom3566 chi ∧
      ¬Fin15AnchoredAtom1115 chi) ∨
      (Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom1110 chi)) ∨
      ((Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom1111 chi) ∨
      (Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom1146 chi))))) ∨
      (((((Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom1191 chi) ∨
      (Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom1356 chi)) ∨
      ((¬Fin15AnchoredAtom3567 chi ∧
      Fin15AnchoredAtom1110 chi ∧
      Fin15AnchoredAtom1111 chi ∧
      Fin15AnchoredAtom1146 chi ∧
      Fin15AnchoredAtom1191 chi ∧
      Fin15AnchoredAtom1356 chi) ∨
      (Fin15AnchoredAtom3568 chi ∧
      ¬Fin15AnchoredAtom1110 chi))) ∨
      (((Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom1110 chi) ∨
      (Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom1113 chi)) ∨
      ((Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom1148 chi) ∨
      (Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom1193 chi)))) ∨
      ((((Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom1358 chi) ∨
      (¬Fin15AnchoredAtom3569 chi ∧
      Fin15AnchoredAtom1110 chi ∧
      Fin15AnchoredAtom1113 chi ∧
      Fin15AnchoredAtom1148 chi ∧
      Fin15AnchoredAtom1193 chi ∧
      Fin15AnchoredAtom1358 chi)) ∨
      ((Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom1110 chi) ∨
      (Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom1114 chi))) ∨
      (((Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom1149 chi) ∨
      (Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom1194 chi)) ∨
      ((Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom1359 chi) ∨
      (¬Fin15AnchoredAtom3570 chi ∧
      Fin15AnchoredAtom1110 chi ∧
      Fin15AnchoredAtom1114 chi ∧
      Fin15AnchoredAtom1149 chi ∧
      Fin15AnchoredAtom1194 chi ∧
      Fin15AnchoredAtom1359 chi)))))) ∨
      ((((((Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom1110 chi) ∨
      (Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom1115 chi)) ∨
      ((Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom1150 chi) ∨
      (Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom1195 chi))) ∨
      (((Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom1360 chi) ∨
      (¬Fin15AnchoredAtom3571 chi ∧
      Fin15AnchoredAtom1110 chi ∧
      Fin15AnchoredAtom1115 chi ∧
      Fin15AnchoredAtom1150 chi ∧
      Fin15AnchoredAtom1195 chi ∧
      Fin15AnchoredAtom1360 chi)) ∨
      ((Fin15AnchoredAtom3572 chi ∧
      ¬Fin15AnchoredAtom1111 chi) ∨
      (Fin15AnchoredAtom3572 chi ∧
      ¬Fin15AnchoredAtom1112 chi)))) ∨
      ((((Fin15AnchoredAtom3572 chi ∧
      ¬Fin15AnchoredAtom1151 chi) ∨
      (Fin15AnchoredAtom3572 chi ∧
      ¬Fin15AnchoredAtom1196 chi)) ∨
      ((Fin15AnchoredAtom3572 chi ∧
      ¬Fin15AnchoredAtom1361 chi) ∨
      (¬Fin15AnchoredAtom3572 chi ∧
      Fin15AnchoredAtom1111 chi ∧
      Fin15AnchoredAtom1112 chi ∧
      Fin15AnchoredAtom1151 chi ∧
      Fin15AnchoredAtom1196 chi ∧
      Fin15AnchoredAtom1361 chi))) ∨
      (((Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom1111 chi) ∨
      (Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom1113 chi)) ∨
      ((Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom1152 chi) ∨
      (Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom1197 chi))))) ∨
      (((((Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom1362 chi) ∨
      (¬Fin15AnchoredAtom3573 chi ∧
      Fin15AnchoredAtom1111 chi ∧
      Fin15AnchoredAtom1113 chi ∧
      Fin15AnchoredAtom1152 chi ∧
      Fin15AnchoredAtom1197 chi ∧
      Fin15AnchoredAtom1362 chi)) ∨
      ((Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom1111 chi) ∨
      (Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom1114 chi))) ∨
      (((Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom1153 chi) ∨
      (Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom1198 chi)) ∨
      ((Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom1363 chi) ∨
      (¬Fin15AnchoredAtom3574 chi ∧
      Fin15AnchoredAtom1111 chi ∧
      Fin15AnchoredAtom1114 chi ∧
      Fin15AnchoredAtom1153 chi ∧
      Fin15AnchoredAtom1198 chi ∧
      Fin15AnchoredAtom1363 chi)))) ∨
      ((((Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom1111 chi) ∨
      (Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom1115 chi)) ∨
      ((Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom1154 chi) ∨
      (Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom1199 chi))) ∨
      (((Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom1364 chi) ∨
      (¬Fin15AnchoredAtom3575 chi ∧
      Fin15AnchoredAtom1111 chi ∧
      Fin15AnchoredAtom1115 chi ∧
      Fin15AnchoredAtom1154 chi ∧
      Fin15AnchoredAtom1199 chi ∧
      Fin15AnchoredAtom1364 chi)) ∨
      ((Fin15AnchoredAtom3576 chi ∧
      ¬Fin15AnchoredAtom1113 chi) ∨
      (Fin15AnchoredAtom3577 chi ∧
      ¬Fin15AnchoredAtom1112 chi)))))))))) := by
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
                exact fin15Anchored_clause23221 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23222 chi hbad
                ·
                  exact fin15Anchored_clause23223 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23224 chi hbad
                ·
                  exact fin15Anchored_clause23225 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23226 chi hbad
                ·
                  exact fin15Anchored_clause23227 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23228 chi hbad
                ·
                  exact fin15Anchored_clause23229 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23230 chi hbad
                ·
                  exact fin15Anchored_clause23231 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23232 chi hbad
                ·
                  exact fin15Anchored_clause23233 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23234 chi hbad
                ·
                  exact fin15Anchored_clause23235 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23236 chi hbad
                ·
                  exact fin15Anchored_clause23237 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23238 chi hbad
                ·
                  exact fin15Anchored_clause23239 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23240 chi hbad
                ·
                  exact fin15Anchored_clause23241 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23242 chi hbad
                ·
                  exact fin15Anchored_clause23243 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23244 chi hbad
                ·
                  exact fin15Anchored_clause23245 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23246 chi hbad
                ·
                  exact fin15Anchored_clause23247 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23248 chi hbad
                ·
                  exact fin15Anchored_clause23249 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23250 chi hbad
                ·
                  exact fin15Anchored_clause23251 chi hbad
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
                  exact fin15Anchored_clause23252 chi hbad
                ·
                  exact fin15Anchored_clause23253 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23254 chi hbad
                ·
                  exact fin15Anchored_clause23255 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23256 chi hbad
                ·
                  exact fin15Anchored_clause23257 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23258 chi hbad
                ·
                  exact fin15Anchored_clause23259 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23260 chi hbad
                ·
                  exact fin15Anchored_clause23261 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23262 chi hbad
                ·
                  exact fin15Anchored_clause23263 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23264 chi hbad
                ·
                  exact fin15Anchored_clause23265 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23266 chi hbad
                ·
                  exact fin15Anchored_clause23267 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23268 chi hbad
                ·
                  exact fin15Anchored_clause23269 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23270 chi hbad
                ·
                  exact fin15Anchored_clause23271 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23272 chi hbad
                ·
                  exact fin15Anchored_clause23273 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23274 chi hbad
                ·
                  exact fin15Anchored_clause23275 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23276 chi hbad
                ·
                  exact fin15Anchored_clause23277 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23278 chi hbad
                ·
                  exact fin15Anchored_clause23279 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23280 chi hbad
                ·
                  exact fin15Anchored_clause23281 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23282 chi hbad
                ·
                  exact fin15Anchored_clause23283 chi hbad
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
                exact fin15Anchored_clause23284 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23285 chi hbad
                ·
                  exact fin15Anchored_clause23286 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23287 chi hbad
                ·
                  exact fin15Anchored_clause23288 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23289 chi hbad
                ·
                  exact fin15Anchored_clause23290 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23291 chi hbad
                ·
                  exact fin15Anchored_clause23292 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23293 chi hbad
                ·
                  exact fin15Anchored_clause23294 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23295 chi hbad
                ·
                  exact fin15Anchored_clause23296 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23297 chi hbad
                ·
                  exact fin15Anchored_clause23298 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23299 chi hbad
                ·
                  exact fin15Anchored_clause23300 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23301 chi hbad
                ·
                  exact fin15Anchored_clause23302 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23303 chi hbad
                ·
                  exact fin15Anchored_clause23304 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23305 chi hbad
                ·
                  exact fin15Anchored_clause23306 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23307 chi hbad
                ·
                  exact fin15Anchored_clause23308 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23309 chi hbad
                ·
                  exact fin15Anchored_clause23310 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23311 chi hbad
                ·
                  exact fin15Anchored_clause23312 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23313 chi hbad
                ·
                  exact fin15Anchored_clause23314 chi hbad
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
                  exact fin15Anchored_clause23315 chi hbad
                ·
                  exact fin15Anchored_clause23316 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23317 chi hbad
                ·
                  exact fin15Anchored_clause23318 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23319 chi hbad
                ·
                  exact fin15Anchored_clause23320 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23321 chi hbad
                ·
                  exact fin15Anchored_clause23322 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23323 chi hbad
                ·
                  exact fin15Anchored_clause23324 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23325 chi hbad
                ·
                  exact fin15Anchored_clause23326 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23327 chi hbad
                ·
                  exact fin15Anchored_clause23328 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23329 chi hbad
                ·
                  exact fin15Anchored_clause23330 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23331 chi hbad
                ·
                  exact fin15Anchored_clause23332 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23333 chi hbad
                ·
                  exact fin15Anchored_clause23334 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23335 chi hbad
                ·
                  exact fin15Anchored_clause23336 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23337 chi hbad
                ·
                  exact fin15Anchored_clause23338 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23339 chi hbad
                ·
                  exact fin15Anchored_clause23340 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23341 chi hbad
                ·
                  exact fin15Anchored_clause23342 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23343 chi hbad
                ·
                  exact fin15Anchored_clause23344 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23345 chi hbad
                ·
                  exact fin15Anchored_clause23346 chi hbad
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
                exact fin15Anchored_clause23347 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23348 chi hbad
                ·
                  exact fin15Anchored_clause23349 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23350 chi hbad
                ·
                  exact fin15Anchored_clause23351 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23352 chi hbad
                ·
                  exact fin15Anchored_clause23353 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23354 chi hbad
                ·
                  exact fin15Anchored_clause23355 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23356 chi hbad
                ·
                  exact fin15Anchored_clause23357 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23358 chi hbad
                ·
                  exact fin15Anchored_clause23359 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23360 chi hbad
                ·
                  exact fin15Anchored_clause23361 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23362 chi hbad
                ·
                  exact fin15Anchored_clause23363 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23364 chi hbad
                ·
                  exact fin15Anchored_clause23365 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23366 chi hbad
                ·
                  exact fin15Anchored_clause23367 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23368 chi hbad
                ·
                  exact fin15Anchored_clause23369 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23370 chi hbad
                ·
                  exact fin15Anchored_clause23371 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23372 chi hbad
                ·
                  exact fin15Anchored_clause23373 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23374 chi hbad
                ·
                  exact fin15Anchored_clause23375 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23376 chi hbad
                ·
                  exact fin15Anchored_clause23377 chi hbad
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
                  exact fin15Anchored_clause23378 chi hbad
                ·
                  exact fin15Anchored_clause23379 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23380 chi hbad
                ·
                  exact fin15Anchored_clause23381 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23382 chi hbad
                ·
                  exact fin15Anchored_clause23383 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23384 chi hbad
                ·
                  exact fin15Anchored_clause23385 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23386 chi hbad
                ·
                  exact fin15Anchored_clause23387 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23388 chi hbad
                ·
                  exact fin15Anchored_clause23389 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23390 chi hbad
                ·
                  exact fin15Anchored_clause23391 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23392 chi hbad
                ·
                  exact fin15Anchored_clause23393 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23394 chi hbad
                ·
                  exact fin15Anchored_clause23395 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23396 chi hbad
                ·
                  exact fin15Anchored_clause23397 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23398 chi hbad
                ·
                  exact fin15Anchored_clause23399 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23400 chi hbad
                ·
                  exact fin15Anchored_clause23401 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23402 chi hbad
                ·
                  exact fin15Anchored_clause23403 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23404 chi hbad
                ·
                  exact fin15Anchored_clause23405 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23406 chi hbad
                ·
                  exact fin15Anchored_clause23407 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23408 chi hbad
                ·
                  exact fin15Anchored_clause23409 chi hbad
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
                exact fin15Anchored_clause23410 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23411 chi hbad
                ·
                  exact fin15Anchored_clause23412 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23413 chi hbad
                ·
                  exact fin15Anchored_clause23414 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23415 chi hbad
                ·
                  exact fin15Anchored_clause23416 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23417 chi hbad
                ·
                  exact fin15Anchored_clause23418 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23419 chi hbad
                ·
                  exact fin15Anchored_clause23420 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23421 chi hbad
                ·
                  exact fin15Anchored_clause23422 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23423 chi hbad
                ·
                  exact fin15Anchored_clause23424 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23425 chi hbad
                ·
                  exact fin15Anchored_clause23426 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23427 chi hbad
                ·
                  exact fin15Anchored_clause23428 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23429 chi hbad
                ·
                  exact fin15Anchored_clause23430 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23431 chi hbad
                ·
                  exact fin15Anchored_clause23432 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23433 chi hbad
                ·
                  exact fin15Anchored_clause23434 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23435 chi hbad
                ·
                  exact fin15Anchored_clause23436 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23437 chi hbad
                ·
                  exact fin15Anchored_clause23438 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23439 chi hbad
                ·
                  exact fin15Anchored_clause23440 chi hbad
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
                  exact fin15Anchored_clause23441 chi hbad
                ·
                  exact fin15Anchored_clause23442 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23443 chi hbad
                ·
                  exact fin15Anchored_clause23444 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23445 chi hbad
                ·
                  exact fin15Anchored_clause23446 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23447 chi hbad
                ·
                  exact fin15Anchored_clause23448 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23449 chi hbad
                ·
                  exact fin15Anchored_clause23450 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23451 chi hbad
                ·
                  exact fin15Anchored_clause23452 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23453 chi hbad
                ·
                  exact fin15Anchored_clause23454 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23455 chi hbad
                ·
                  exact fin15Anchored_clause23456 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23457 chi hbad
                ·
                  exact fin15Anchored_clause23458 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23459 chi hbad
                ·
                  exact fin15Anchored_clause23460 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23461 chi hbad
                ·
                  exact fin15Anchored_clause23462 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23463 chi hbad
                ·
                  exact fin15Anchored_clause23464 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23465 chi hbad
                ·
                  exact fin15Anchored_clause23466 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23467 chi hbad
                ·
                  exact fin15Anchored_clause23468 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23469 chi hbad
                ·
                  exact fin15Anchored_clause23470 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23471 chi hbad
                ·
                  exact fin15Anchored_clause23472 chi hbad

end ErdosSzekeres

end
