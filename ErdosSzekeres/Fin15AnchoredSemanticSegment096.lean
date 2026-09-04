module

public import ErdosSzekeres.Fin15AnchoredClauseChunk189
public import ErdosSzekeres.Fin15AnchoredClauseChunk190
public import ErdosSzekeres.Fin15AnchoredClauseChunk191

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 096. -/

theorem fin15Anchored_rejectSemanticSegment096
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom1184 chi) ∨
      ((Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom1195 chi) ∨
      (Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom1280 chi))) ∨
      (((Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom1565 chi) ∨
      (¬Fin15AnchoredAtom3776 chi ∧
      Fin15AnchoredAtom1179 chi ∧
      Fin15AnchoredAtom1184 chi ∧
      Fin15AnchoredAtom1195 chi ∧
      Fin15AnchoredAtom1280 chi ∧
      Fin15AnchoredAtom1565 chi)) ∨
      ((Fin15AnchoredAtom3777 chi ∧
      ¬Fin15AnchoredAtom1180 chi) ∨
      (Fin15AnchoredAtom3777 chi ∧
      ¬Fin15AnchoredAtom1181 chi)))) ∨
      ((((Fin15AnchoredAtom3777 chi ∧
      ¬Fin15AnchoredAtom1281 chi) ∨
      (Fin15AnchoredAtom3777 chi ∧
      ¬Fin15AnchoredAtom1566 chi)) ∨
      ((Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom1180 chi) ∨
      (Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom1182 chi))) ∨
      (((Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom1197 chi) ∨
      (Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom1282 chi)) ∨
      ((Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom1567 chi) ∨
      (¬Fin15AnchoredAtom3778 chi ∧
      Fin15AnchoredAtom1180 chi ∧
      Fin15AnchoredAtom1182 chi ∧
      Fin15AnchoredAtom1197 chi ∧
      Fin15AnchoredAtom1282 chi ∧
      Fin15AnchoredAtom1567 chi))))) ∨
      (((((Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom1180 chi) ∨
      (Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom1183 chi)) ∨
      ((Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom1198 chi) ∨
      (Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom1283 chi))) ∨
      (((Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom1568 chi) ∨
      (¬Fin15AnchoredAtom3779 chi ∧
      Fin15AnchoredAtom1180 chi ∧
      Fin15AnchoredAtom1183 chi ∧
      Fin15AnchoredAtom1198 chi ∧
      Fin15AnchoredAtom1283 chi ∧
      Fin15AnchoredAtom1568 chi)) ∨
      ((Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom1180 chi) ∨
      (Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom1184 chi)))) ∨
      ((((Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom1199 chi) ∨
      (Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom1284 chi)) ∨
      ((Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom1569 chi) ∨
      (¬Fin15AnchoredAtom3780 chi ∧
      Fin15AnchoredAtom1180 chi ∧
      Fin15AnchoredAtom1184 chi ∧
      Fin15AnchoredAtom1199 chi ∧
      Fin15AnchoredAtom1284 chi ∧
      Fin15AnchoredAtom1569 chi))) ∨
      (((Fin15AnchoredAtom3781 chi ∧
      ¬Fin15AnchoredAtom1182 chi) ∨
      (Fin15AnchoredAtom3781 chi ∧
      ¬Fin15AnchoredAtom1200 chi)) ∨
      ((Fin15AnchoredAtom3781 chi ∧
      ¬Fin15AnchoredAtom1570 chi) ∨
      (¬Fin15AnchoredAtom3781 chi ∧
      Fin15AnchoredAtom1181 chi ∧
      Fin15AnchoredAtom1182 chi ∧
      Fin15AnchoredAtom1200 chi ∧
      Fin15AnchoredAtom1285 chi ∧
      Fin15AnchoredAtom1570 chi)))))) ∨
      ((((((Fin15AnchoredAtom3782 chi ∧
      ¬Fin15AnchoredAtom1183 chi) ∨
      (Fin15AnchoredAtom3783 chi ∧
      ¬Fin15AnchoredAtom1184 chi)) ∨
      ((Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom1182 chi) ∨
      (Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom1183 chi))) ∨
      (((Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom1203 chi) ∨
      (Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom1288 chi)) ∨
      ((Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom1573 chi) ∨
      (¬Fin15AnchoredAtom3784 chi ∧
      Fin15AnchoredAtom1182 chi ∧
      Fin15AnchoredAtom1183 chi ∧
      Fin15AnchoredAtom1203 chi ∧
      Fin15AnchoredAtom1288 chi ∧
      Fin15AnchoredAtom1573 chi)))) ∨
      ((((Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom1182 chi) ∨
      (Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom1184 chi)) ∨
      ((Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom1204 chi) ∨
      (Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom1289 chi))) ∨
      (((Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom1574 chi) ∨
      (¬Fin15AnchoredAtom3785 chi ∧
      Fin15AnchoredAtom1182 chi ∧
      Fin15AnchoredAtom1184 chi ∧
      Fin15AnchoredAtom1204 chi ∧
      Fin15AnchoredAtom1289 chi ∧
      Fin15AnchoredAtom1574 chi)) ∨
      ((Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom1183 chi) ∨
      (Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom1184 chi))))) ∨
      (((((Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom1205 chi) ∨
      (Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom1290 chi)) ∨
      ((Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom1575 chi) ∨
      (¬Fin15AnchoredAtom3786 chi ∧
      Fin15AnchoredAtom1183 chi ∧
      Fin15AnchoredAtom1184 chi ∧
      Fin15AnchoredAtom1205 chi ∧
      Fin15AnchoredAtom1290 chi ∧
      Fin15AnchoredAtom1575 chi))) ∨
      (((Fin15AnchoredAtom3787 chi ∧
      ¬Fin15AnchoredAtom1576 chi) ∨
      (¬Fin15AnchoredAtom3787 chi ∧
      Fin15AnchoredAtom1185 chi ∧
      Fin15AnchoredAtom1186 chi ∧
      Fin15AnchoredAtom1191 chi ∧
      Fin15AnchoredAtom1291 chi ∧
      Fin15AnchoredAtom1576 chi)) ∨
      ((Fin15AnchoredAtom3789 chi ∧
      ¬Fin15AnchoredAtom1188 chi) ∨
      (Fin15AnchoredAtom3789 chi ∧
      ¬Fin15AnchoredAtom1578 chi)))) ∨
      ((((¬Fin15AnchoredAtom3789 chi ∧
      Fin15AnchoredAtom1185 chi ∧
      Fin15AnchoredAtom1188 chi ∧
      Fin15AnchoredAtom1193 chi ∧
      Fin15AnchoredAtom1293 chi ∧
      Fin15AnchoredAtom1578 chi) ∨
      (Fin15AnchoredAtom3791 chi ∧
      ¬Fin15AnchoredAtom1195 chi)) ∨
      ((Fin15AnchoredAtom3793 chi ∧
      ¬Fin15AnchoredAtom1197 chi) ∨
      (Fin15AnchoredAtom3793 chi ∧
      ¬Fin15AnchoredAtom1582 chi))) ∨
      (((¬Fin15AnchoredAtom3793 chi ∧
      Fin15AnchoredAtom1186 chi ∧
      Fin15AnchoredAtom1188 chi ∧
      Fin15AnchoredAtom1197 chi ∧
      Fin15AnchoredAtom1297 chi ∧
      Fin15AnchoredAtom1582 chi) ∨
      (Fin15AnchoredAtom3794 chi ∧
      ¬Fin15AnchoredAtom1198 chi)) ∨
      ((¬Fin15AnchoredAtom3794 chi ∧
      Fin15AnchoredAtom1186 chi ∧
      Fin15AnchoredAtom1189 chi ∧
      Fin15AnchoredAtom1198 chi ∧
      Fin15AnchoredAtom1298 chi ∧
      Fin15AnchoredAtom1583 chi) ∨
      (Fin15AnchoredAtom3795 chi ∧
      ¬Fin15AnchoredAtom1199 chi))))))) ∨
      ((((((Fin15AnchoredAtom3799 chi ∧
      ¬Fin15AnchoredAtom1188 chi) ∨
      ((¬Fin15AnchoredAtom3799 chi ∧
      Fin15AnchoredAtom1188 chi ∧
      Fin15AnchoredAtom1189 chi ∧
      Fin15AnchoredAtom1203 chi ∧
      Fin15AnchoredAtom1303 chi ∧
      Fin15AnchoredAtom1588 chi) ∨
      (Fin15AnchoredAtom3800 chi ∧
      ¬Fin15AnchoredAtom1190 chi))) ∨
      (((Fin15AnchoredAtom3800 chi ∧
      ¬Fin15AnchoredAtom1204 chi) ∨
      (Fin15AnchoredAtom3800 chi ∧
      ¬Fin15AnchoredAtom1304 chi)) ∨
      ((Fin15AnchoredAtom3801 chi ∧
      ¬Fin15AnchoredAtom1590 chi) ∨
      (Fin15AnchoredAtom3802 chi ∧
      ¬Fin15AnchoredAtom1191 chi)))) ∨
      ((((Fin15AnchoredAtom3802 chi ∧
      ¬Fin15AnchoredAtom1306 chi) ∨
      (Fin15AnchoredAtom3802 chi ∧
      ¬Fin15AnchoredAtom1591 chi)) ∨
      ((Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom1191 chi) ∨
      (Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom1193 chi))) ∨
      (((Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom1197 chi) ∨
      (Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom1307 chi)) ∨
      ((Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom1592 chi) ∨
      (¬Fin15AnchoredAtom3803 chi ∧
      Fin15AnchoredAtom1191 chi ∧
      Fin15AnchoredAtom1193 chi ∧
      Fin15AnchoredAtom1197 chi ∧
      Fin15AnchoredAtom1307 chi ∧
      Fin15AnchoredAtom1592 chi))))) ∨
      (((((Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom1191 chi) ∨
      (Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom1194 chi)) ∨
      ((Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom1198 chi) ∨
      (Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom1308 chi))) ∨
      (((Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom1593 chi) ∨
      (¬Fin15AnchoredAtom3804 chi ∧
      Fin15AnchoredAtom1191 chi ∧
      Fin15AnchoredAtom1194 chi ∧
      Fin15AnchoredAtom1198 chi ∧
      Fin15AnchoredAtom1308 chi ∧
      Fin15AnchoredAtom1593 chi)) ∨
      ((Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom1191 chi) ∨
      (Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom1195 chi)))) ∨
      ((((Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom1199 chi) ∨
      (Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom1309 chi)) ∨
      ((Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom1594 chi) ∨
      (¬Fin15AnchoredAtom3805 chi ∧
      Fin15AnchoredAtom1191 chi ∧
      Fin15AnchoredAtom1195 chi ∧
      Fin15AnchoredAtom1199 chi ∧
      Fin15AnchoredAtom1309 chi ∧
      Fin15AnchoredAtom1594 chi))) ∨
      (((Fin15AnchoredAtom3806 chi ∧
      ¬Fin15AnchoredAtom1192 chi) ∨
      (Fin15AnchoredAtom3806 chi ∧
      ¬Fin15AnchoredAtom1193 chi)) ∨
      ((Fin15AnchoredAtom3806 chi ∧
      ¬Fin15AnchoredAtom1200 chi) ∨
      (Fin15AnchoredAtom3806 chi ∧
      ¬Fin15AnchoredAtom1310 chi)))))) ∨
      ((((((Fin15AnchoredAtom3806 chi ∧
      ¬Fin15AnchoredAtom1595 chi) ∨
      (Fin15AnchoredAtom3807 chi ∧
      ¬Fin15AnchoredAtom1194 chi)) ∨
      ((Fin15AnchoredAtom3807 chi ∧
      ¬Fin15AnchoredAtom1596 chi) ∨
      (Fin15AnchoredAtom3808 chi ∧
      ¬Fin15AnchoredAtom1195 chi))) ∨
      (((Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom1193 chi) ∨
      (Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom1194 chi)) ∨
      ((Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom1203 chi) ∨
      (Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom1313 chi)))) ∨
      ((((Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom1598 chi) ∨
      (¬Fin15AnchoredAtom3809 chi ∧
      Fin15AnchoredAtom1193 chi ∧
      Fin15AnchoredAtom1194 chi ∧
      Fin15AnchoredAtom1203 chi ∧
      Fin15AnchoredAtom1313 chi ∧
      Fin15AnchoredAtom1598 chi)) ∨
      ((Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom1193 chi) ∨
      (Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom1195 chi))) ∨
      (((Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom1204 chi) ∨
      (Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom1314 chi)) ∨
      ((Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom1599 chi) ∨
      (¬Fin15AnchoredAtom3810 chi ∧
      Fin15AnchoredAtom1193 chi ∧
      Fin15AnchoredAtom1195 chi ∧
      Fin15AnchoredAtom1204 chi ∧
      Fin15AnchoredAtom1314 chi ∧
      Fin15AnchoredAtom1599 chi))))) ∨
      (((((Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom1194 chi) ∨
      (Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom1195 chi)) ∨
      ((Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom1205 chi) ∨
      (Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom1315 chi))) ∨
      (((Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom1600 chi) ∨
      (¬Fin15AnchoredAtom3811 chi ∧
      Fin15AnchoredAtom1194 chi ∧
      Fin15AnchoredAtom1195 chi ∧
      Fin15AnchoredAtom1205 chi ∧
      Fin15AnchoredAtom1315 chi ∧
      Fin15AnchoredAtom1600 chi)) ∨
      ((Fin15AnchoredAtom3812 chi ∧
      ¬Fin15AnchoredAtom1197 chi) ∨
      (Fin15AnchoredAtom3812 chi ∧
      ¬Fin15AnchoredAtom1316 chi)))) ∨
      ((((Fin15AnchoredAtom3812 chi ∧
      ¬Fin15AnchoredAtom1601 chi) ∨
      (Fin15AnchoredAtom3813 chi ∧
      ¬Fin15AnchoredAtom1198 chi)) ∨
      ((Fin15AnchoredAtom3813 chi ∧
      ¬Fin15AnchoredAtom1602 chi) ∨
      (Fin15AnchoredAtom3814 chi ∧
      ¬Fin15AnchoredAtom1199 chi))) ∨
      (((Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom1197 chi) ∨
      (Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom1198 chi)) ∨
      ((Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom1203 chi) ∨
      (Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom1319 chi)))))))) ∨
      (((((((Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom1604 chi) ∨
      ((¬Fin15AnchoredAtom3815 chi ∧
      Fin15AnchoredAtom1197 chi ∧
      Fin15AnchoredAtom1198 chi ∧
      Fin15AnchoredAtom1203 chi ∧
      Fin15AnchoredAtom1319 chi ∧
      Fin15AnchoredAtom1604 chi) ∨
      (Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom1197 chi))) ∨
      (((Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom1199 chi) ∨
      (Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom1204 chi)) ∨
      ((Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom1320 chi) ∨
      (Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom1605 chi)))) ∨
      ((((¬Fin15AnchoredAtom3816 chi ∧
      Fin15AnchoredAtom1197 chi ∧
      Fin15AnchoredAtom1199 chi ∧
      Fin15AnchoredAtom1204 chi ∧
      Fin15AnchoredAtom1320 chi ∧
      Fin15AnchoredAtom1605 chi) ∨
      (Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom1198 chi)) ∨
      ((Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom1199 chi) ∨
      (Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom1205 chi))) ∨
      (((Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom1321 chi) ∨
      (Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom1606 chi)) ∨
      ((¬Fin15AnchoredAtom3817 chi ∧
      Fin15AnchoredAtom1198 chi ∧
      Fin15AnchoredAtom1199 chi ∧
      Fin15AnchoredAtom1205 chi ∧
      Fin15AnchoredAtom1321 chi ∧
      Fin15AnchoredAtom1606 chi) ∨
      (Fin15AnchoredAtom3818 chi ∧
      ¬Fin15AnchoredAtom1203 chi))))) ∨
      (((((Fin15AnchoredAtom3818 chi ∧
      ¬Fin15AnchoredAtom1322 chi) ∨
      (¬Fin15AnchoredAtom3818 chi ∧
      Fin15AnchoredAtom1200 chi ∧
      Fin15AnchoredAtom1201 chi ∧
      Fin15AnchoredAtom1203 chi ∧
      Fin15AnchoredAtom1322 chi ∧
      Fin15AnchoredAtom1607 chi)) ∨
      ((Fin15AnchoredAtom3819 chi ∧
      ¬Fin15AnchoredAtom1204 chi) ∨
      (Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom1203 chi))) ∨
      (((Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom1204 chi) ∨
      (Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom1205 chi)) ∨
      ((Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom1325 chi) ∨
      (Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom1610 chi)))) ∨
      ((((¬Fin15AnchoredAtom3821 chi ∧
      Fin15AnchoredAtom1203 chi ∧
      Fin15AnchoredAtom1204 chi ∧
      Fin15AnchoredAtom1205 chi ∧
      Fin15AnchoredAtom1325 chi ∧
      Fin15AnchoredAtom1610 chi) ∨
      (Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom1206 chi)) ∨
      ((Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom1208 chi) ∨
      (Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom1215 chi))) ∨
      (((Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom1243 chi) ∨
      (Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom1612 chi)) ∨
      ((¬Fin15AnchoredAtom3823 chi ∧
      Fin15AnchoredAtom1206 chi ∧
      Fin15AnchoredAtom1208 chi ∧
      Fin15AnchoredAtom1215 chi ∧
      Fin15AnchoredAtom1243 chi ∧
      Fin15AnchoredAtom1612 chi) ∨
      (Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom1206 chi)))))) ∨
      ((((((Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom1209 chi) ∨
      (Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom1216 chi)) ∨
      ((Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom1244 chi) ∨
      (Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom1613 chi))) ∨
      (((¬Fin15AnchoredAtom3824 chi ∧
      Fin15AnchoredAtom1206 chi ∧
      Fin15AnchoredAtom1209 chi ∧
      Fin15AnchoredAtom1216 chi ∧
      Fin15AnchoredAtom1244 chi ∧
      Fin15AnchoredAtom1613 chi) ∨
      (Fin15AnchoredAtom3825 chi ∧
      ¬Fin15AnchoredAtom1206 chi)) ∨
      ((Fin15AnchoredAtom3825 chi ∧
      ¬Fin15AnchoredAtom1210 chi) ∨
      (Fin15AnchoredAtom3825 chi ∧
      ¬Fin15AnchoredAtom1217 chi)))) ∨
      ((((Fin15AnchoredAtom3825 chi ∧
      ¬Fin15AnchoredAtom1245 chi) ∨
      (Fin15AnchoredAtom3825 chi ∧
      ¬Fin15AnchoredAtom1614 chi)) ∨
      ((¬Fin15AnchoredAtom3825 chi ∧
      Fin15AnchoredAtom1206 chi ∧
      Fin15AnchoredAtom1210 chi ∧
      Fin15AnchoredAtom1217 chi ∧
      Fin15AnchoredAtom1245 chi ∧
      Fin15AnchoredAtom1614 chi) ∨
      (Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom1206 chi))) ∨
      (((Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom1211 chi) ∨
      (Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom1218 chi)) ∨
      ((Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom1246 chi) ∨
      (Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom1615 chi))))) ∨
      (((((¬Fin15AnchoredAtom3826 chi ∧
      Fin15AnchoredAtom1206 chi ∧
      Fin15AnchoredAtom1211 chi ∧
      Fin15AnchoredAtom1218 chi ∧
      Fin15AnchoredAtom1246 chi ∧
      Fin15AnchoredAtom1615 chi) ∨
      (Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom1206 chi)) ∨
      ((Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom1212 chi) ∨
      (Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom1219 chi))) ∨
      (((Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom1247 chi) ∨
      (Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom1616 chi)) ∨
      ((¬Fin15AnchoredAtom3827 chi ∧
      Fin15AnchoredAtom1206 chi ∧
      Fin15AnchoredAtom1212 chi ∧
      Fin15AnchoredAtom1219 chi ∧
      Fin15AnchoredAtom1247 chi ∧
      Fin15AnchoredAtom1616 chi) ∨
      (Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom1206 chi)))) ∨
      ((((Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom1213 chi) ∨
      (Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom1220 chi)) ∨
      ((Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom1248 chi) ∨
      (Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom1617 chi))) ∨
      (((¬Fin15AnchoredAtom3828 chi ∧
      Fin15AnchoredAtom1206 chi ∧
      Fin15AnchoredAtom1213 chi ∧
      Fin15AnchoredAtom1220 chi ∧
      Fin15AnchoredAtom1248 chi ∧
      Fin15AnchoredAtom1617 chi) ∨
      (Fin15AnchoredAtom3830 chi ∧
      ¬Fin15AnchoredAtom1222 chi)) ∨
      ((¬Fin15AnchoredAtom3830 chi ∧
      Fin15AnchoredAtom1207 chi ∧
      Fin15AnchoredAtom1209 chi ∧
      Fin15AnchoredAtom1222 chi ∧
      Fin15AnchoredAtom1250 chi ∧
      Fin15AnchoredAtom1619 chi) ∨
      (Fin15AnchoredAtom3833 chi ∧
      ¬Fin15AnchoredAtom1622 chi))))))) ∨
      ((((((Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom1208 chi) ∨
      ((Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom1209 chi) ∨
      (Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom1227 chi))) ∨
      (((Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom1255 chi) ∨
      (Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom1624 chi)) ∨
      ((¬Fin15AnchoredAtom3835 chi ∧
      Fin15AnchoredAtom1208 chi ∧
      Fin15AnchoredAtom1209 chi ∧
      Fin15AnchoredAtom1227 chi ∧
      Fin15AnchoredAtom1255 chi ∧
      Fin15AnchoredAtom1624 chi) ∨
      (Fin15AnchoredAtom3836 chi ∧
      ¬Fin15AnchoredAtom1208 chi)))) ∨
      ((((Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom1208 chi) ∨
      (Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom1211 chi)) ∨
      ((Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom1229 chi) ∨
      (Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom1257 chi))) ∨
      (((Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom1626 chi) ∨
      (¬Fin15AnchoredAtom3837 chi ∧
      Fin15AnchoredAtom1208 chi ∧
      Fin15AnchoredAtom1211 chi ∧
      Fin15AnchoredAtom1229 chi ∧
      Fin15AnchoredAtom1257 chi ∧
      Fin15AnchoredAtom1626 chi)) ∨
      ((Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom1208 chi) ∨
      (Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom1212 chi))))) ∨
      (((((Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom1230 chi) ∨
      (Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom1258 chi)) ∨
      ((Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom1627 chi) ∨
      (¬Fin15AnchoredAtom3838 chi ∧
      Fin15AnchoredAtom1208 chi ∧
      Fin15AnchoredAtom1212 chi ∧
      Fin15AnchoredAtom1230 chi ∧
      Fin15AnchoredAtom1258 chi ∧
      Fin15AnchoredAtom1627 chi))) ∨
      (((Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom1208 chi) ∨
      (Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom1213 chi)) ∨
      ((Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom1231 chi) ∨
      (Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom1259 chi)))) ∨
      ((((Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom1628 chi) ∨
      (¬Fin15AnchoredAtom3839 chi ∧
      Fin15AnchoredAtom1208 chi ∧
      Fin15AnchoredAtom1213 chi ∧
      Fin15AnchoredAtom1231 chi ∧
      Fin15AnchoredAtom1259 chi ∧
      Fin15AnchoredAtom1628 chi)) ∨
      ((Fin15AnchoredAtom3840 chi ∧
      ¬Fin15AnchoredAtom1209 chi) ∨
      (Fin15AnchoredAtom3840 chi ∧
      ¬Fin15AnchoredAtom1210 chi))) ∨
      (((Fin15AnchoredAtom3840 chi ∧
      ¬Fin15AnchoredAtom1232 chi) ∨
      (Fin15AnchoredAtom3840 chi ∧
      ¬Fin15AnchoredAtom1260 chi)) ∨
      ((Fin15AnchoredAtom3840 chi ∧
      ¬Fin15AnchoredAtom1629 chi) ∨
      (¬Fin15AnchoredAtom3840 chi ∧
      Fin15AnchoredAtom1209 chi ∧
      Fin15AnchoredAtom1210 chi ∧
      Fin15AnchoredAtom1232 chi ∧
      Fin15AnchoredAtom1260 chi ∧
      Fin15AnchoredAtom1629 chi)))))) ∨
      ((((((Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom1209 chi) ∨
      (Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom1211 chi)) ∨
      ((Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom1233 chi) ∨
      (Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom1261 chi))) ∨
      (((Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom1630 chi) ∨
      (¬Fin15AnchoredAtom3841 chi ∧
      Fin15AnchoredAtom1209 chi ∧
      Fin15AnchoredAtom1211 chi ∧
      Fin15AnchoredAtom1233 chi ∧
      Fin15AnchoredAtom1261 chi ∧
      Fin15AnchoredAtom1630 chi)) ∨
      ((Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom1209 chi) ∨
      (Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom1212 chi)))) ∨
      ((((Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom1234 chi) ∨
      (Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom1262 chi)) ∨
      ((Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom1631 chi) ∨
      (¬Fin15AnchoredAtom3842 chi ∧
      Fin15AnchoredAtom1209 chi ∧
      Fin15AnchoredAtom1212 chi ∧
      Fin15AnchoredAtom1234 chi ∧
      Fin15AnchoredAtom1262 chi ∧
      Fin15AnchoredAtom1631 chi))) ∨
      (((Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom1209 chi) ∨
      (Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom1213 chi)) ∨
      ((Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom1235 chi) ∨
      (Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom1263 chi))))) ∨
      (((((Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom1632 chi) ∨
      (¬Fin15AnchoredAtom3843 chi ∧
      Fin15AnchoredAtom1209 chi ∧
      Fin15AnchoredAtom1213 chi ∧
      Fin15AnchoredAtom1235 chi ∧
      Fin15AnchoredAtom1263 chi ∧
      Fin15AnchoredAtom1632 chi)) ∨
      ((Fin15AnchoredAtom3844 chi ∧
      ¬Fin15AnchoredAtom1211 chi) ∨
      (Fin15AnchoredAtom3844 chi ∧
      ¬Fin15AnchoredAtom1264 chi))) ∨
      (((Fin15AnchoredAtom3844 chi ∧
      ¬Fin15AnchoredAtom1633 chi) ∨
      (¬Fin15AnchoredAtom3844 chi ∧
      Fin15AnchoredAtom1210 chi ∧
      Fin15AnchoredAtom1211 chi ∧
      Fin15AnchoredAtom1236 chi ∧
      Fin15AnchoredAtom1264 chi ∧
      Fin15AnchoredAtom1633 chi)) ∨
      ((Fin15AnchoredAtom3845 chi ∧
      ¬Fin15AnchoredAtom1212 chi) ∨
      (Fin15AnchoredAtom3846 chi ∧
      ¬Fin15AnchoredAtom1213 chi)))) ∨
      ((((Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom1211 chi) ∨
      (Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom1212 chi)) ∨
      ((Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom1239 chi) ∨
      (Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom1267 chi))) ∨
      (((Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom1636 chi) ∨
      (¬Fin15AnchoredAtom3847 chi ∧
      Fin15AnchoredAtom1211 chi ∧
      Fin15AnchoredAtom1212 chi ∧
      Fin15AnchoredAtom1239 chi ∧
      Fin15AnchoredAtom1267 chi ∧
      Fin15AnchoredAtom1636 chi)) ∨
      ((Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom1211 chi) ∨
      (Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom1213 chi)))))))))) := by
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
                exact fin15Anchored_clause24231 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24232 chi hbad
                ·
                  exact fin15Anchored_clause24233 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24234 chi hbad
                ·
                  exact fin15Anchored_clause24235 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24236 chi hbad
                ·
                  exact fin15Anchored_clause24237 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24238 chi hbad
                ·
                  exact fin15Anchored_clause24239 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24240 chi hbad
                ·
                  exact fin15Anchored_clause24241 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24242 chi hbad
                ·
                  exact fin15Anchored_clause24243 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24244 chi hbad
                ·
                  exact fin15Anchored_clause24245 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24246 chi hbad
                ·
                  exact fin15Anchored_clause24247 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24248 chi hbad
                ·
                  exact fin15Anchored_clause24249 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24250 chi hbad
                ·
                  exact fin15Anchored_clause24251 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24252 chi hbad
                ·
                  exact fin15Anchored_clause24253 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24254 chi hbad
                ·
                  exact fin15Anchored_clause24255 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24256 chi hbad
                ·
                  exact fin15Anchored_clause24257 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24258 chi hbad
                ·
                  exact fin15Anchored_clause24259 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24260 chi hbad
                ·
                  exact fin15Anchored_clause24261 chi hbad
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
                  exact fin15Anchored_clause24262 chi hbad
                ·
                  exact fin15Anchored_clause24263 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24264 chi hbad
                ·
                  exact fin15Anchored_clause24265 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24266 chi hbad
                ·
                  exact fin15Anchored_clause24267 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24268 chi hbad
                ·
                  exact fin15Anchored_clause24269 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24270 chi hbad
                ·
                  exact fin15Anchored_clause24271 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24272 chi hbad
                ·
                  exact fin15Anchored_clause24273 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24274 chi hbad
                ·
                  exact fin15Anchored_clause24275 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24276 chi hbad
                ·
                  exact fin15Anchored_clause24277 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24278 chi hbad
                ·
                  exact fin15Anchored_clause24279 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24280 chi hbad
                ·
                  exact fin15Anchored_clause24281 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24282 chi hbad
                ·
                  exact fin15Anchored_clause24283 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24284 chi hbad
                ·
                  exact fin15Anchored_clause24285 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24286 chi hbad
                ·
                  exact fin15Anchored_clause24287 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24288 chi hbad
                ·
                  exact fin15Anchored_clause24289 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24290 chi hbad
                ·
                  exact fin15Anchored_clause24291 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24292 chi hbad
                ·
                  exact fin15Anchored_clause24293 chi hbad
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
                exact fin15Anchored_clause24294 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24295 chi hbad
                ·
                  exact fin15Anchored_clause24296 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24297 chi hbad
                ·
                  exact fin15Anchored_clause24298 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24299 chi hbad
                ·
                  exact fin15Anchored_clause24300 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24301 chi hbad
                ·
                  exact fin15Anchored_clause24302 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24303 chi hbad
                ·
                  exact fin15Anchored_clause24304 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24305 chi hbad
                ·
                  exact fin15Anchored_clause24306 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24307 chi hbad
                ·
                  exact fin15Anchored_clause24308 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24309 chi hbad
                ·
                  exact fin15Anchored_clause24310 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24311 chi hbad
                ·
                  exact fin15Anchored_clause24312 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24313 chi hbad
                ·
                  exact fin15Anchored_clause24314 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24315 chi hbad
                ·
                  exact fin15Anchored_clause24316 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24317 chi hbad
                ·
                  exact fin15Anchored_clause24318 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24319 chi hbad
                ·
                  exact fin15Anchored_clause24320 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24321 chi hbad
                ·
                  exact fin15Anchored_clause24322 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24323 chi hbad
                ·
                  exact fin15Anchored_clause24324 chi hbad
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
                  exact fin15Anchored_clause24325 chi hbad
                ·
                  exact fin15Anchored_clause24326 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24327 chi hbad
                ·
                  exact fin15Anchored_clause24328 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24329 chi hbad
                ·
                  exact fin15Anchored_clause24330 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24331 chi hbad
                ·
                  exact fin15Anchored_clause24332 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24333 chi hbad
                ·
                  exact fin15Anchored_clause24334 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24335 chi hbad
                ·
                  exact fin15Anchored_clause24336 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24337 chi hbad
                ·
                  exact fin15Anchored_clause24338 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24339 chi hbad
                ·
                  exact fin15Anchored_clause24340 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24341 chi hbad
                ·
                  exact fin15Anchored_clause24342 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24343 chi hbad
                ·
                  exact fin15Anchored_clause24344 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24345 chi hbad
                ·
                  exact fin15Anchored_clause24346 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24347 chi hbad
                ·
                  exact fin15Anchored_clause24348 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24349 chi hbad
                ·
                  exact fin15Anchored_clause24350 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24351 chi hbad
                ·
                  exact fin15Anchored_clause24352 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24353 chi hbad
                ·
                  exact fin15Anchored_clause24354 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24355 chi hbad
                ·
                  exact fin15Anchored_clause24356 chi hbad
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
                exact fin15Anchored_clause24357 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24358 chi hbad
                ·
                  exact fin15Anchored_clause24359 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24360 chi hbad
                ·
                  exact fin15Anchored_clause24361 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24362 chi hbad
                ·
                  exact fin15Anchored_clause24363 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24364 chi hbad
                ·
                  exact fin15Anchored_clause24365 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24366 chi hbad
                ·
                  exact fin15Anchored_clause24367 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24368 chi hbad
                ·
                  exact fin15Anchored_clause24369 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24370 chi hbad
                ·
                  exact fin15Anchored_clause24371 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24372 chi hbad
                ·
                  exact fin15Anchored_clause24373 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24374 chi hbad
                ·
                  exact fin15Anchored_clause24375 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24376 chi hbad
                ·
                  exact fin15Anchored_clause24377 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24378 chi hbad
                ·
                  exact fin15Anchored_clause24379 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24380 chi hbad
                ·
                  exact fin15Anchored_clause24381 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24382 chi hbad
                ·
                  exact fin15Anchored_clause24383 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24384 chi hbad
                ·
                  exact fin15Anchored_clause24385 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24386 chi hbad
                ·
                  exact fin15Anchored_clause24387 chi hbad
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
                  exact fin15Anchored_clause24388 chi hbad
                ·
                  exact fin15Anchored_clause24389 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24390 chi hbad
                ·
                  exact fin15Anchored_clause24391 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24392 chi hbad
                ·
                  exact fin15Anchored_clause24393 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24394 chi hbad
                ·
                  exact fin15Anchored_clause24395 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24396 chi hbad
                ·
                  exact fin15Anchored_clause24397 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24398 chi hbad
                ·
                  exact fin15Anchored_clause24399 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24400 chi hbad
                ·
                  exact fin15Anchored_clause24401 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24402 chi hbad
                ·
                  exact fin15Anchored_clause24403 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24404 chi hbad
                ·
                  exact fin15Anchored_clause24405 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24406 chi hbad
                ·
                  exact fin15Anchored_clause24407 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24408 chi hbad
                ·
                  exact fin15Anchored_clause24409 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24410 chi hbad
                ·
                  exact fin15Anchored_clause24411 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24412 chi hbad
                ·
                  exact fin15Anchored_clause24413 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24414 chi hbad
                ·
                  exact fin15Anchored_clause24415 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24416 chi hbad
                ·
                  exact fin15Anchored_clause24417 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24418 chi hbad
                ·
                  exact fin15Anchored_clause24419 chi hbad
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
                exact fin15Anchored_clause24420 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24421 chi hbad
                ·
                  exact fin15Anchored_clause24422 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24423 chi hbad
                ·
                  exact fin15Anchored_clause24424 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24425 chi hbad
                ·
                  exact fin15Anchored_clause24426 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24427 chi hbad
                ·
                  exact fin15Anchored_clause24428 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24429 chi hbad
                ·
                  exact fin15Anchored_clause24430 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24431 chi hbad
                ·
                  exact fin15Anchored_clause24432 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24433 chi hbad
                ·
                  exact fin15Anchored_clause24434 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24435 chi hbad
                ·
                  exact fin15Anchored_clause24436 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24437 chi hbad
                ·
                  exact fin15Anchored_clause24438 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24439 chi hbad
                ·
                  exact fin15Anchored_clause24440 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24441 chi hbad
                ·
                  exact fin15Anchored_clause24442 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24443 chi hbad
                ·
                  exact fin15Anchored_clause24444 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24445 chi hbad
                ·
                  exact fin15Anchored_clause24446 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24447 chi hbad
                ·
                  exact fin15Anchored_clause24448 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24449 chi hbad
                ·
                  exact fin15Anchored_clause24450 chi hbad
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
                  exact fin15Anchored_clause24451 chi hbad
                ·
                  exact fin15Anchored_clause24452 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24453 chi hbad
                ·
                  exact fin15Anchored_clause24454 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24455 chi hbad
                ·
                  exact fin15Anchored_clause24456 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24457 chi hbad
                ·
                  exact fin15Anchored_clause24458 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24459 chi hbad
                ·
                  exact fin15Anchored_clause24460 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24461 chi hbad
                ·
                  exact fin15Anchored_clause24462 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24463 chi hbad
                ·
                  exact fin15Anchored_clause24464 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24465 chi hbad
                ·
                  exact fin15Anchored_clause24466 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24467 chi hbad
                ·
                  exact fin15Anchored_clause24468 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24469 chi hbad
                ·
                  exact fin15Anchored_clause24470 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24471 chi hbad
                ·
                  exact fin15Anchored_clause24472 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24473 chi hbad
                ·
                  exact fin15Anchored_clause24474 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24475 chi hbad
                ·
                  exact fin15Anchored_clause24476 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24477 chi hbad
                ·
                  exact fin15Anchored_clause24478 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24479 chi hbad
                ·
                  exact fin15Anchored_clause24480 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24481 chi hbad
                ·
                  exact fin15Anchored_clause24482 chi hbad

end ErdosSzekeres

end
