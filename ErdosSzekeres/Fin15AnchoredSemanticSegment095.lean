module

public import ErdosSzekeres.Fin15AnchoredClauseChunk187
public import ErdosSzekeres.Fin15AnchoredClauseChunk188
public import ErdosSzekeres.Fin15AnchoredClauseChunk189

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 095. -/

theorem fin15Anchored_rejectSemanticSegment095
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom1179 chi) ∨
      ((Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom1215 chi) ∨
      (Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom1500 chi))) ∨
      (((¬Fin15AnchoredAtom3711 chi ∧
      Fin15AnchoredAtom1162 chi ∧
      Fin15AnchoredAtom1164 chi ∧
      Fin15AnchoredAtom1179 chi ∧
      Fin15AnchoredAtom1215 chi ∧
      Fin15AnchoredAtom1500 chi) ∨
      (Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom1162 chi)) ∨
      ((Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom1165 chi) ∨
      (Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom1180 chi)))) ∨
      ((((Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom1216 chi) ∨
      (Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom1501 chi)) ∨
      ((¬Fin15AnchoredAtom3712 chi ∧
      Fin15AnchoredAtom1162 chi ∧
      Fin15AnchoredAtom1165 chi ∧
      Fin15AnchoredAtom1180 chi ∧
      Fin15AnchoredAtom1216 chi ∧
      Fin15AnchoredAtom1501 chi) ∨
      (Fin15AnchoredAtom3713 chi ∧
      ¬Fin15AnchoredAtom1502 chi))) ∨
      (((Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom1162 chi) ∨
      (Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom1167 chi)) ∨
      ((Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom1182 chi) ∨
      (Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom1218 chi))))) ∨
      (((((Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom1503 chi) ∨
      (¬Fin15AnchoredAtom3714 chi ∧
      Fin15AnchoredAtom1162 chi ∧
      Fin15AnchoredAtom1167 chi ∧
      Fin15AnchoredAtom1182 chi ∧
      Fin15AnchoredAtom1218 chi ∧
      Fin15AnchoredAtom1503 chi)) ∨
      ((Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom1162 chi) ∨
      (Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom1168 chi))) ∨
      (((Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom1183 chi) ∨
      (Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom1219 chi)) ∨
      ((Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom1504 chi) ∨
      (¬Fin15AnchoredAtom3715 chi ∧
      Fin15AnchoredAtom1162 chi ∧
      Fin15AnchoredAtom1168 chi ∧
      Fin15AnchoredAtom1183 chi ∧
      Fin15AnchoredAtom1219 chi ∧
      Fin15AnchoredAtom1504 chi)))) ∨
      ((((Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom1162 chi) ∨
      (Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom1169 chi)) ∨
      ((Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom1184 chi) ∨
      (Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom1220 chi))) ∨
      (((Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom1505 chi) ∨
      (¬Fin15AnchoredAtom3716 chi ∧
      Fin15AnchoredAtom1162 chi ∧
      Fin15AnchoredAtom1169 chi ∧
      Fin15AnchoredAtom1184 chi ∧
      Fin15AnchoredAtom1220 chi ∧
      Fin15AnchoredAtom1505 chi)) ∨
      ((Fin15AnchoredAtom3721 chi ∧
      ¬Fin15AnchoredAtom1168 chi) ∨
      (Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom1164 chi)))))) ∨
      ((((((Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom1165 chi) ∨
      (Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom1191 chi)) ∨
      ((Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom1227 chi) ∨
      (Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom1512 chi))) ∨
      (((¬Fin15AnchoredAtom3723 chi ∧
      Fin15AnchoredAtom1164 chi ∧
      Fin15AnchoredAtom1165 chi ∧
      Fin15AnchoredAtom1191 chi ∧
      Fin15AnchoredAtom1227 chi ∧
      Fin15AnchoredAtom1512 chi) ∨
      (Fin15AnchoredAtom3724 chi ∧
      ¬Fin15AnchoredAtom1164 chi)) ∨
      ((Fin15AnchoredAtom3724 chi ∧
      ¬Fin15AnchoredAtom1513 chi) ∨
      (¬Fin15AnchoredAtom3724 chi ∧
      Fin15AnchoredAtom1164 chi ∧
      Fin15AnchoredAtom1166 chi ∧
      Fin15AnchoredAtom1192 chi ∧
      Fin15AnchoredAtom1228 chi ∧
      Fin15AnchoredAtom1513 chi)))) ∨
      ((((Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom1164 chi) ∨
      (Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom1167 chi)) ∨
      ((Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom1193 chi) ∨
      (Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom1229 chi))) ∨
      (((Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom1514 chi) ∨
      (¬Fin15AnchoredAtom3725 chi ∧
      Fin15AnchoredAtom1164 chi ∧
      Fin15AnchoredAtom1167 chi ∧
      Fin15AnchoredAtom1193 chi ∧
      Fin15AnchoredAtom1229 chi ∧
      Fin15AnchoredAtom1514 chi)) ∨
      ((Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom1164 chi) ∨
      (Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom1168 chi))))) ∨
      (((((Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom1194 chi) ∨
      (Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom1230 chi)) ∨
      ((Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom1515 chi) ∨
      (¬Fin15AnchoredAtom3726 chi ∧
      Fin15AnchoredAtom1164 chi ∧
      Fin15AnchoredAtom1168 chi ∧
      Fin15AnchoredAtom1194 chi ∧
      Fin15AnchoredAtom1230 chi ∧
      Fin15AnchoredAtom1515 chi))) ∨
      (((Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom1164 chi) ∨
      (Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom1169 chi)) ∨
      ((Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom1195 chi) ∨
      (Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom1231 chi)))) ∨
      ((((Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom1516 chi) ∨
      (¬Fin15AnchoredAtom3727 chi ∧
      Fin15AnchoredAtom1164 chi ∧
      Fin15AnchoredAtom1169 chi ∧
      Fin15AnchoredAtom1195 chi ∧
      Fin15AnchoredAtom1231 chi ∧
      Fin15AnchoredAtom1516 chi)) ∨
      ((Fin15AnchoredAtom3728 chi ∧
      ¬Fin15AnchoredAtom1165 chi) ∨
      (Fin15AnchoredAtom3728 chi ∧
      ¬Fin15AnchoredAtom1232 chi))) ∨
      (((Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom1165 chi) ∨
      (Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom1167 chi)) ∨
      ((Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom1197 chi) ∨
      (Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom1233 chi))))))) ∨
      ((((((Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom1518 chi) ∨
      ((¬Fin15AnchoredAtom3729 chi ∧
      Fin15AnchoredAtom1165 chi ∧
      Fin15AnchoredAtom1167 chi ∧
      Fin15AnchoredAtom1197 chi ∧
      Fin15AnchoredAtom1233 chi ∧
      Fin15AnchoredAtom1518 chi) ∨
      (Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom1165 chi))) ∨
      (((Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom1168 chi) ∨
      (Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom1198 chi)) ∨
      ((Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom1234 chi) ∨
      (Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom1519 chi)))) ∨
      ((((¬Fin15AnchoredAtom3730 chi ∧
      Fin15AnchoredAtom1165 chi ∧
      Fin15AnchoredAtom1168 chi ∧
      Fin15AnchoredAtom1198 chi ∧
      Fin15AnchoredAtom1234 chi ∧
      Fin15AnchoredAtom1519 chi) ∨
      (Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom1165 chi)) ∨
      ((Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom1169 chi) ∨
      (Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom1199 chi))) ∨
      (((Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom1235 chi) ∨
      (Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom1520 chi)) ∨
      ((¬Fin15AnchoredAtom3731 chi ∧
      Fin15AnchoredAtom1165 chi ∧
      Fin15AnchoredAtom1169 chi ∧
      Fin15AnchoredAtom1199 chi ∧
      Fin15AnchoredAtom1235 chi ∧
      Fin15AnchoredAtom1520 chi) ∨
      (Fin15AnchoredAtom3732 chi ∧
      ¬Fin15AnchoredAtom1167 chi))))) ∨
      (((((Fin15AnchoredAtom3733 chi ∧
      ¬Fin15AnchoredAtom1168 chi) ∨
      (Fin15AnchoredAtom3734 chi ∧
      ¬Fin15AnchoredAtom1169 chi)) ∨
      ((Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom1167 chi) ∨
      (Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom1168 chi))) ∨
      (((Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom1203 chi) ∨
      (Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom1239 chi)) ∨
      ((Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom1524 chi) ∨
      (¬Fin15AnchoredAtom3735 chi ∧
      Fin15AnchoredAtom1167 chi ∧
      Fin15AnchoredAtom1168 chi ∧
      Fin15AnchoredAtom1203 chi ∧
      Fin15AnchoredAtom1239 chi ∧
      Fin15AnchoredAtom1524 chi)))) ∨
      ((((Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom1167 chi) ∨
      (Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom1169 chi)) ∨
      ((Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom1204 chi) ∨
      (Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom1240 chi))) ∨
      (((Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom1525 chi) ∨
      (¬Fin15AnchoredAtom3736 chi ∧
      Fin15AnchoredAtom1167 chi ∧
      Fin15AnchoredAtom1169 chi ∧
      Fin15AnchoredAtom1204 chi ∧
      Fin15AnchoredAtom1240 chi ∧
      Fin15AnchoredAtom1525 chi)) ∨
      ((Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom1168 chi) ∨
      (Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom1169 chi)))))) ∨
      ((((((Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom1205 chi) ∨
      (Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom1241 chi)) ∨
      ((Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom1526 chi) ∨
      (¬Fin15AnchoredAtom3737 chi ∧
      Fin15AnchoredAtom1168 chi ∧
      Fin15AnchoredAtom1169 chi ∧
      Fin15AnchoredAtom1205 chi ∧
      Fin15AnchoredAtom1241 chi ∧
      Fin15AnchoredAtom1526 chi))) ∨
      (((Fin15AnchoredAtom3738 chi ∧
      ¬Fin15AnchoredAtom1170 chi) ∨
      (Fin15AnchoredAtom3738 chi ∧
      ¬Fin15AnchoredAtom1242 chi)) ∨
      ((Fin15AnchoredAtom3738 chi ∧
      ¬Fin15AnchoredAtom1527 chi) ∨
      (¬Fin15AnchoredAtom3738 chi ∧
      Fin15AnchoredAtom1170 chi ∧
      Fin15AnchoredAtom1171 chi ∧
      Fin15AnchoredAtom1178 chi ∧
      Fin15AnchoredAtom1242 chi ∧
      Fin15AnchoredAtom1527 chi)))) ∨
      ((((Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom1170 chi) ∨
      (Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom1172 chi)) ∨
      ((Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom1179 chi) ∨
      (Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom1243 chi))) ∨
      (((Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom1528 chi) ∨
      (¬Fin15AnchoredAtom3739 chi ∧
      Fin15AnchoredAtom1170 chi ∧
      Fin15AnchoredAtom1172 chi ∧
      Fin15AnchoredAtom1179 chi ∧
      Fin15AnchoredAtom1243 chi ∧
      Fin15AnchoredAtom1528 chi)) ∨
      ((Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom1170 chi) ∨
      (Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom1173 chi))))) ∨
      (((((Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom1180 chi) ∨
      (Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom1244 chi)) ∨
      ((Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom1529 chi) ∨
      (¬Fin15AnchoredAtom3740 chi ∧
      Fin15AnchoredAtom1170 chi ∧
      Fin15AnchoredAtom1173 chi ∧
      Fin15AnchoredAtom1180 chi ∧
      Fin15AnchoredAtom1244 chi ∧
      Fin15AnchoredAtom1529 chi))) ∨
      (((Fin15AnchoredAtom3741 chi ∧
      ¬Fin15AnchoredAtom1170 chi) ∨
      (Fin15AnchoredAtom3741 chi ∧
      ¬Fin15AnchoredAtom1245 chi)) ∨
      ((Fin15AnchoredAtom3741 chi ∧
      ¬Fin15AnchoredAtom1530 chi) ∨
      (¬Fin15AnchoredAtom3741 chi ∧
      Fin15AnchoredAtom1170 chi ∧
      Fin15AnchoredAtom1174 chi ∧
      Fin15AnchoredAtom1181 chi ∧
      Fin15AnchoredAtom1245 chi ∧
      Fin15AnchoredAtom1530 chi)))) ∨
      ((((Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom1170 chi) ∨
      (Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom1175 chi)) ∨
      ((Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom1182 chi) ∨
      (Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom1246 chi))) ∨
      (((Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom1531 chi) ∨
      (¬Fin15AnchoredAtom3742 chi ∧
      Fin15AnchoredAtom1170 chi ∧
      Fin15AnchoredAtom1175 chi ∧
      Fin15AnchoredAtom1182 chi ∧
      Fin15AnchoredAtom1246 chi ∧
      Fin15AnchoredAtom1531 chi)) ∨
      ((Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom1170 chi) ∨
      (Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom1176 chi)))))))) ∨
      (((((((Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom1183 chi) ∨
      ((Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom1247 chi) ∨
      (Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom1532 chi))) ∨
      (((¬Fin15AnchoredAtom3743 chi ∧
      Fin15AnchoredAtom1170 chi ∧
      Fin15AnchoredAtom1176 chi ∧
      Fin15AnchoredAtom1183 chi ∧
      Fin15AnchoredAtom1247 chi ∧
      Fin15AnchoredAtom1532 chi) ∨
      (Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom1170 chi)) ∨
      ((Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom1177 chi) ∨
      (Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom1184 chi)))) ∨
      ((((Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom1248 chi) ∨
      (Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom1533 chi)) ∨
      ((¬Fin15AnchoredAtom3744 chi ∧
      Fin15AnchoredAtom1170 chi ∧
      Fin15AnchoredAtom1177 chi ∧
      Fin15AnchoredAtom1184 chi ∧
      Fin15AnchoredAtom1248 chi ∧
      Fin15AnchoredAtom1533 chi) ∨
      (Fin15AnchoredAtom3745 chi ∧
      ¬Fin15AnchoredAtom1172 chi))) ∨
      (((Fin15AnchoredAtom3745 chi ∧
      ¬Fin15AnchoredAtom1249 chi) ∨
      (¬Fin15AnchoredAtom3745 chi ∧
      Fin15AnchoredAtom1171 chi ∧
      Fin15AnchoredAtom1172 chi ∧
      Fin15AnchoredAtom1185 chi ∧
      Fin15AnchoredAtom1249 chi ∧
      Fin15AnchoredAtom1534 chi)) ∨
      ((Fin15AnchoredAtom3746 chi ∧
      ¬Fin15AnchoredAtom1173 chi) ∨
      (Fin15AnchoredAtom3748 chi ∧
      ¬Fin15AnchoredAtom1171 chi))))) ∨
      (((((Fin15AnchoredAtom3749 chi ∧
      ¬Fin15AnchoredAtom1171 chi) ∨
      (Fin15AnchoredAtom3749 chi ∧
      ¬Fin15AnchoredAtom1253 chi)) ∨
      ((Fin15AnchoredAtom3750 chi ∧
      ¬Fin15AnchoredAtom1177 chi) ∨
      (Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom1172 chi))) ∨
      (((Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom1173 chi) ∨
      (Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom1191 chi)) ∨
      ((Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom1255 chi) ∨
      (Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom1540 chi)))) ∨
      ((((¬Fin15AnchoredAtom3751 chi ∧
      Fin15AnchoredAtom1172 chi ∧
      Fin15AnchoredAtom1173 chi ∧
      Fin15AnchoredAtom1191 chi ∧
      Fin15AnchoredAtom1255 chi ∧
      Fin15AnchoredAtom1540 chi) ∨
      (Fin15AnchoredAtom3752 chi ∧
      ¬Fin15AnchoredAtom1172 chi)) ∨
      ((Fin15AnchoredAtom3752 chi ∧
      ¬Fin15AnchoredAtom1541 chi) ∨
      (¬Fin15AnchoredAtom3752 chi ∧
      Fin15AnchoredAtom1172 chi ∧
      Fin15AnchoredAtom1174 chi ∧
      Fin15AnchoredAtom1192 chi ∧
      Fin15AnchoredAtom1256 chi ∧
      Fin15AnchoredAtom1541 chi))) ∨
      (((Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom1172 chi) ∨
      (Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom1175 chi)) ∨
      ((Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom1193 chi) ∨
      (Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom1257 chi)))))) ∨
      ((((((Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom1542 chi) ∨
      (¬Fin15AnchoredAtom3753 chi ∧
      Fin15AnchoredAtom1172 chi ∧
      Fin15AnchoredAtom1175 chi ∧
      Fin15AnchoredAtom1193 chi ∧
      Fin15AnchoredAtom1257 chi ∧
      Fin15AnchoredAtom1542 chi)) ∨
      ((Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom1172 chi) ∨
      (Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom1176 chi))) ∨
      (((Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom1194 chi) ∨
      (Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom1258 chi)) ∨
      ((Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom1543 chi) ∨
      (¬Fin15AnchoredAtom3754 chi ∧
      Fin15AnchoredAtom1172 chi ∧
      Fin15AnchoredAtom1176 chi ∧
      Fin15AnchoredAtom1194 chi ∧
      Fin15AnchoredAtom1258 chi ∧
      Fin15AnchoredAtom1543 chi)))) ∨
      ((((Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom1172 chi) ∨
      (Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom1177 chi)) ∨
      ((Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom1195 chi) ∨
      (Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom1259 chi))) ∨
      (((Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom1544 chi) ∨
      (¬Fin15AnchoredAtom3755 chi ∧
      Fin15AnchoredAtom1172 chi ∧
      Fin15AnchoredAtom1177 chi ∧
      Fin15AnchoredAtom1195 chi ∧
      Fin15AnchoredAtom1259 chi ∧
      Fin15AnchoredAtom1544 chi)) ∨
      ((Fin15AnchoredAtom3756 chi ∧
      ¬Fin15AnchoredAtom1173 chi) ∨
      (Fin15AnchoredAtom3756 chi ∧
      ¬Fin15AnchoredAtom1196 chi))))) ∨
      (((((Fin15AnchoredAtom3756 chi ∧
      ¬Fin15AnchoredAtom1260 chi) ∨
      (Fin15AnchoredAtom3756 chi ∧
      ¬Fin15AnchoredAtom1545 chi)) ∨
      ((¬Fin15AnchoredAtom3756 chi ∧
      Fin15AnchoredAtom1173 chi ∧
      Fin15AnchoredAtom1174 chi ∧
      Fin15AnchoredAtom1196 chi ∧
      Fin15AnchoredAtom1260 chi ∧
      Fin15AnchoredAtom1545 chi) ∨
      (Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom1173 chi))) ∨
      (((Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom1175 chi) ∨
      (Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom1197 chi)) ∨
      ((Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom1261 chi) ∨
      (Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom1546 chi)))) ∨
      ((((¬Fin15AnchoredAtom3757 chi ∧
      Fin15AnchoredAtom1173 chi ∧
      Fin15AnchoredAtom1175 chi ∧
      Fin15AnchoredAtom1197 chi ∧
      Fin15AnchoredAtom1261 chi ∧
      Fin15AnchoredAtom1546 chi) ∨
      (Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom1173 chi)) ∨
      ((Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom1176 chi) ∨
      (Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom1198 chi))) ∨
      (((Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom1262 chi) ∨
      (Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom1547 chi)) ∨
      ((¬Fin15AnchoredAtom3758 chi ∧
      Fin15AnchoredAtom1173 chi ∧
      Fin15AnchoredAtom1176 chi ∧
      Fin15AnchoredAtom1198 chi ∧
      Fin15AnchoredAtom1262 chi ∧
      Fin15AnchoredAtom1547 chi) ∨
      (Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom1173 chi))))))) ∨
      (((((((Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom1177 chi) ∨
      (Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom1199 chi)) ∨
      ((Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom1263 chi) ∨
      (Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom1548 chi))) ∨
      (((¬Fin15AnchoredAtom3759 chi ∧
      Fin15AnchoredAtom1173 chi ∧
      Fin15AnchoredAtom1177 chi ∧
      Fin15AnchoredAtom1199 chi ∧
      Fin15AnchoredAtom1263 chi ∧
      Fin15AnchoredAtom1548 chi) ∨
      (Fin15AnchoredAtom3760 chi ∧
      ¬Fin15AnchoredAtom1174 chi)) ∨
      ((Fin15AnchoredAtom3760 chi ∧
      ¬Fin15AnchoredAtom1175 chi) ∨
      (Fin15AnchoredAtom3760 chi ∧
      ¬Fin15AnchoredAtom1200 chi)))) ∨
      ((((Fin15AnchoredAtom3760 chi ∧
      ¬Fin15AnchoredAtom1264 chi) ∨
      (Fin15AnchoredAtom3760 chi ∧
      ¬Fin15AnchoredAtom1549 chi)) ∨
      ((¬Fin15AnchoredAtom3760 chi ∧
      Fin15AnchoredAtom1174 chi ∧
      Fin15AnchoredAtom1175 chi ∧
      Fin15AnchoredAtom1200 chi ∧
      Fin15AnchoredAtom1264 chi ∧
      Fin15AnchoredAtom1549 chi) ∨
      (Fin15AnchoredAtom3761 chi ∧
      ¬Fin15AnchoredAtom1550 chi))) ∨
      (((Fin15AnchoredAtom3762 chi ∧
      ¬Fin15AnchoredAtom1177 chi) ∨
      (Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom1175 chi)) ∨
      ((Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom1176 chi) ∨
      (Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom1203 chi))))) ∨
      (((((Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom1267 chi) ∨
      (Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom1552 chi)) ∨
      ((¬Fin15AnchoredAtom3763 chi ∧
      Fin15AnchoredAtom1175 chi ∧
      Fin15AnchoredAtom1176 chi ∧
      Fin15AnchoredAtom1203 chi ∧
      Fin15AnchoredAtom1267 chi ∧
      Fin15AnchoredAtom1552 chi) ∨
      (Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom1175 chi))) ∨
      (((Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom1177 chi) ∨
      (Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom1204 chi)) ∨
      ((Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom1268 chi) ∨
      (Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom1553 chi)))) ∨
      ((((¬Fin15AnchoredAtom3764 chi ∧
      Fin15AnchoredAtom1175 chi ∧
      Fin15AnchoredAtom1177 chi ∧
      Fin15AnchoredAtom1204 chi ∧
      Fin15AnchoredAtom1268 chi ∧
      Fin15AnchoredAtom1553 chi) ∨
      (Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom1176 chi)) ∨
      ((Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom1177 chi) ∨
      (Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom1205 chi))) ∨
      (((Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom1269 chi) ∨
      (Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom1554 chi)) ∨
      ((¬Fin15AnchoredAtom3765 chi ∧
      Fin15AnchoredAtom1176 chi ∧
      Fin15AnchoredAtom1177 chi ∧
      Fin15AnchoredAtom1205 chi ∧
      Fin15AnchoredAtom1269 chi ∧
      Fin15AnchoredAtom1554 chi) ∨
      (Fin15AnchoredAtom3766 chi ∧
      ¬Fin15AnchoredAtom1178 chi)))))) ∨
      ((((((Fin15AnchoredAtom3766 chi ∧
      ¬Fin15AnchoredAtom1179 chi) ∨
      (Fin15AnchoredAtom3766 chi ∧
      ¬Fin15AnchoredAtom1270 chi)) ∨
      ((Fin15AnchoredAtom3766 chi ∧
      ¬Fin15AnchoredAtom1555 chi) ∨
      (¬Fin15AnchoredAtom3766 chi ∧
      Fin15AnchoredAtom1178 chi ∧
      Fin15AnchoredAtom1179 chi ∧
      Fin15AnchoredAtom1185 chi ∧
      Fin15AnchoredAtom1270 chi ∧
      Fin15AnchoredAtom1555 chi))) ∨
      (((Fin15AnchoredAtom3767 chi ∧
      ¬Fin15AnchoredAtom1180 chi) ∨
      (¬Fin15AnchoredAtom3767 chi ∧
      Fin15AnchoredAtom1178 chi ∧
      Fin15AnchoredAtom1180 chi ∧
      Fin15AnchoredAtom1186 chi ∧
      Fin15AnchoredAtom1271 chi ∧
      Fin15AnchoredAtom1556 chi)) ∨
      ((Fin15AnchoredAtom3769 chi ∧
      ¬Fin15AnchoredAtom1182 chi) ∨
      (Fin15AnchoredAtom3771 chi ∧
      ¬Fin15AnchoredAtom1184 chi)))) ∨
      ((((Fin15AnchoredAtom3771 chi ∧
      ¬Fin15AnchoredAtom1190 chi) ∨
      (Fin15AnchoredAtom3771 chi ∧
      ¬Fin15AnchoredAtom1560 chi)) ∨
      ((Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom1179 chi) ∨
      (Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom1180 chi))) ∨
      (((Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom1191 chi) ∨
      (Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom1276 chi)) ∨
      ((Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom1561 chi) ∨
      (¬Fin15AnchoredAtom3772 chi ∧
      Fin15AnchoredAtom1179 chi ∧
      Fin15AnchoredAtom1180 chi ∧
      Fin15AnchoredAtom1191 chi ∧
      Fin15AnchoredAtom1276 chi ∧
      Fin15AnchoredAtom1561 chi))))) ∨
      (((((Fin15AnchoredAtom3773 chi ∧
      ¬Fin15AnchoredAtom1179 chi) ∨
      (Fin15AnchoredAtom3773 chi ∧
      ¬Fin15AnchoredAtom1562 chi)) ∨
      ((¬Fin15AnchoredAtom3773 chi ∧
      Fin15AnchoredAtom1179 chi ∧
      Fin15AnchoredAtom1181 chi ∧
      Fin15AnchoredAtom1192 chi ∧
      Fin15AnchoredAtom1277 chi ∧
      Fin15AnchoredAtom1562 chi) ∨
      (Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom1179 chi))) ∨
      (((Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom1182 chi) ∨
      (Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom1193 chi)) ∨
      ((Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom1278 chi) ∨
      (Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom1563 chi)))) ∨
      ((((¬Fin15AnchoredAtom3774 chi ∧
      Fin15AnchoredAtom1179 chi ∧
      Fin15AnchoredAtom1182 chi ∧
      Fin15AnchoredAtom1193 chi ∧
      Fin15AnchoredAtom1278 chi ∧
      Fin15AnchoredAtom1563 chi) ∨
      (Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom1179 chi)) ∨
      ((Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom1183 chi) ∨
      (Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom1194 chi))) ∨
      (((Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom1279 chi) ∨
      (Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom1564 chi)) ∨
      ((¬Fin15AnchoredAtom3775 chi ∧
      Fin15AnchoredAtom1179 chi ∧
      Fin15AnchoredAtom1183 chi ∧
      Fin15AnchoredAtom1194 chi ∧
      Fin15AnchoredAtom1279 chi ∧
      Fin15AnchoredAtom1564 chi) ∨
      (Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom1179 chi)))))))))) := by
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
                exact fin15Anchored_clause23978 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23979 chi hbad
                ·
                  exact fin15Anchored_clause23980 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23981 chi hbad
                ·
                  exact fin15Anchored_clause23982 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23983 chi hbad
                ·
                  exact fin15Anchored_clause23984 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23985 chi hbad
                ·
                  exact fin15Anchored_clause23986 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23987 chi hbad
                ·
                  exact fin15Anchored_clause23988 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23989 chi hbad
                ·
                  exact fin15Anchored_clause23990 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23991 chi hbad
                ·
                  exact fin15Anchored_clause23992 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23993 chi hbad
                ·
                  exact fin15Anchored_clause23994 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23995 chi hbad
                ·
                  exact fin15Anchored_clause23996 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23997 chi hbad
                ·
                  exact fin15Anchored_clause23998 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23999 chi hbad
                ·
                  exact fin15Anchored_clause24000 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24001 chi hbad
                ·
                  exact fin15Anchored_clause24002 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24003 chi hbad
                ·
                  exact fin15Anchored_clause24004 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24005 chi hbad
                ·
                  exact fin15Anchored_clause24006 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24007 chi hbad
                ·
                  exact fin15Anchored_clause24008 chi hbad
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
                  exact fin15Anchored_clause24009 chi hbad
                ·
                  exact fin15Anchored_clause24010 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24011 chi hbad
                ·
                  exact fin15Anchored_clause24012 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24013 chi hbad
                ·
                  exact fin15Anchored_clause24014 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24015 chi hbad
                ·
                  exact fin15Anchored_clause24016 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24017 chi hbad
                ·
                  exact fin15Anchored_clause24018 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24019 chi hbad
                ·
                  exact fin15Anchored_clause24020 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24021 chi hbad
                ·
                  exact fin15Anchored_clause24022 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24023 chi hbad
                ·
                  exact fin15Anchored_clause24024 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24025 chi hbad
                ·
                  exact fin15Anchored_clause24026 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24027 chi hbad
                ·
                  exact fin15Anchored_clause24028 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24029 chi hbad
                ·
                  exact fin15Anchored_clause24030 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24031 chi hbad
                ·
                  exact fin15Anchored_clause24032 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24033 chi hbad
                ·
                  exact fin15Anchored_clause24034 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24035 chi hbad
                ·
                  exact fin15Anchored_clause24036 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24037 chi hbad
                ·
                  exact fin15Anchored_clause24038 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24039 chi hbad
                ·
                  exact fin15Anchored_clause24040 chi hbad
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
                exact fin15Anchored_clause24041 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24042 chi hbad
                ·
                  exact fin15Anchored_clause24043 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24044 chi hbad
                ·
                  exact fin15Anchored_clause24045 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24046 chi hbad
                ·
                  exact fin15Anchored_clause24047 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24048 chi hbad
                ·
                  exact fin15Anchored_clause24049 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24050 chi hbad
                ·
                  exact fin15Anchored_clause24051 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24052 chi hbad
                ·
                  exact fin15Anchored_clause24053 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24054 chi hbad
                ·
                  exact fin15Anchored_clause24055 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24056 chi hbad
                ·
                  exact fin15Anchored_clause24057 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24058 chi hbad
                ·
                  exact fin15Anchored_clause24059 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24060 chi hbad
                ·
                  exact fin15Anchored_clause24061 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24062 chi hbad
                ·
                  exact fin15Anchored_clause24063 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24064 chi hbad
                ·
                  exact fin15Anchored_clause24065 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24066 chi hbad
                ·
                  exact fin15Anchored_clause24067 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24068 chi hbad
                ·
                  exact fin15Anchored_clause24069 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24070 chi hbad
                ·
                  exact fin15Anchored_clause24071 chi hbad
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
                  exact fin15Anchored_clause24072 chi hbad
                ·
                  exact fin15Anchored_clause24073 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24074 chi hbad
                ·
                  exact fin15Anchored_clause24075 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24076 chi hbad
                ·
                  exact fin15Anchored_clause24077 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24078 chi hbad
                ·
                  exact fin15Anchored_clause24079 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24080 chi hbad
                ·
                  exact fin15Anchored_clause24081 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24082 chi hbad
                ·
                  exact fin15Anchored_clause24083 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24084 chi hbad
                ·
                  exact fin15Anchored_clause24085 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24086 chi hbad
                ·
                  exact fin15Anchored_clause24087 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24088 chi hbad
                ·
                  exact fin15Anchored_clause24089 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24090 chi hbad
                ·
                  exact fin15Anchored_clause24091 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24092 chi hbad
                ·
                  exact fin15Anchored_clause24093 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24094 chi hbad
                ·
                  exact fin15Anchored_clause24095 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24096 chi hbad
                ·
                  exact fin15Anchored_clause24097 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24098 chi hbad
                ·
                  exact fin15Anchored_clause24099 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24100 chi hbad
                ·
                  exact fin15Anchored_clause24101 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24102 chi hbad
                ·
                  exact fin15Anchored_clause24103 chi hbad
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
                exact fin15Anchored_clause24104 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24105 chi hbad
                ·
                  exact fin15Anchored_clause24106 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24107 chi hbad
                ·
                  exact fin15Anchored_clause24108 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24109 chi hbad
                ·
                  exact fin15Anchored_clause24110 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24111 chi hbad
                ·
                  exact fin15Anchored_clause24112 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24113 chi hbad
                ·
                  exact fin15Anchored_clause24114 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24115 chi hbad
                ·
                  exact fin15Anchored_clause24116 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24117 chi hbad
                ·
                  exact fin15Anchored_clause24118 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24119 chi hbad
                ·
                  exact fin15Anchored_clause24120 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24121 chi hbad
                ·
                  exact fin15Anchored_clause24122 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24123 chi hbad
                ·
                  exact fin15Anchored_clause24124 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24125 chi hbad
                ·
                  exact fin15Anchored_clause24126 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24127 chi hbad
                ·
                  exact fin15Anchored_clause24128 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24129 chi hbad
                ·
                  exact fin15Anchored_clause24130 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24131 chi hbad
                ·
                  exact fin15Anchored_clause24132 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24133 chi hbad
                ·
                  exact fin15Anchored_clause24134 chi hbad
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
                  exact fin15Anchored_clause24135 chi hbad
                ·
                  exact fin15Anchored_clause24136 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24137 chi hbad
                ·
                  exact fin15Anchored_clause24138 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24139 chi hbad
                ·
                  exact fin15Anchored_clause24140 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24141 chi hbad
                ·
                  exact fin15Anchored_clause24142 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24143 chi hbad
                ·
                  exact fin15Anchored_clause24144 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24145 chi hbad
                ·
                  exact fin15Anchored_clause24146 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24147 chi hbad
                ·
                  exact fin15Anchored_clause24148 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24149 chi hbad
                ·
                  exact fin15Anchored_clause24150 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24151 chi hbad
                ·
                  exact fin15Anchored_clause24152 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24153 chi hbad
                ·
                  exact fin15Anchored_clause24154 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24155 chi hbad
                ·
                  exact fin15Anchored_clause24156 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24157 chi hbad
                ·
                  exact fin15Anchored_clause24158 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24159 chi hbad
                ·
                  exact fin15Anchored_clause24160 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24161 chi hbad
                ·
                  exact fin15Anchored_clause24162 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24163 chi hbad
                ·
                  exact fin15Anchored_clause24164 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24165 chi hbad
                ·
                  exact fin15Anchored_clause24166 chi hbad
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
                  exact fin15Anchored_clause24167 chi hbad
                ·
                  exact fin15Anchored_clause24168 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24169 chi hbad
                ·
                  exact fin15Anchored_clause24170 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24171 chi hbad
                ·
                  exact fin15Anchored_clause24172 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24173 chi hbad
                ·
                  exact fin15Anchored_clause24174 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24175 chi hbad
                ·
                  exact fin15Anchored_clause24176 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24177 chi hbad
                ·
                  exact fin15Anchored_clause24178 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24179 chi hbad
                ·
                  exact fin15Anchored_clause24180 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24181 chi hbad
                ·
                  exact fin15Anchored_clause24182 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24183 chi hbad
                ·
                  exact fin15Anchored_clause24184 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24185 chi hbad
                ·
                  exact fin15Anchored_clause24186 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24187 chi hbad
                ·
                  exact fin15Anchored_clause24188 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24189 chi hbad
                ·
                  exact fin15Anchored_clause24190 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24191 chi hbad
                ·
                  exact fin15Anchored_clause24192 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24193 chi hbad
                ·
                  exact fin15Anchored_clause24194 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24195 chi hbad
                ·
                  exact fin15Anchored_clause24196 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24197 chi hbad
                ·
                  exact fin15Anchored_clause24198 chi hbad
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
                  exact fin15Anchored_clause24199 chi hbad
                ·
                  exact fin15Anchored_clause24200 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24201 chi hbad
                ·
                  exact fin15Anchored_clause24202 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24203 chi hbad
                ·
                  exact fin15Anchored_clause24204 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24205 chi hbad
                ·
                  exact fin15Anchored_clause24206 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24207 chi hbad
                ·
                  exact fin15Anchored_clause24208 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24209 chi hbad
                ·
                  exact fin15Anchored_clause24210 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24211 chi hbad
                ·
                  exact fin15Anchored_clause24212 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24213 chi hbad
                ·
                  exact fin15Anchored_clause24214 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24215 chi hbad
                ·
                  exact fin15Anchored_clause24216 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24217 chi hbad
                ·
                  exact fin15Anchored_clause24218 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24219 chi hbad
                ·
                  exact fin15Anchored_clause24220 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24221 chi hbad
                ·
                  exact fin15Anchored_clause24222 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24223 chi hbad
                ·
                  exact fin15Anchored_clause24224 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24225 chi hbad
                ·
                  exact fin15Anchored_clause24226 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24227 chi hbad
                ·
                  exact fin15Anchored_clause24228 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24229 chi hbad
                ·
                  exact fin15Anchored_clause24230 chi hbad

end ErdosSzekeres

end
