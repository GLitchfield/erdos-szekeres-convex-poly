module

public import ErdosSzekeres.Fin15AnchoredClauseChunk191
public import ErdosSzekeres.Fin15AnchoredClauseChunk192
public import ErdosSzekeres.Fin15AnchoredClauseChunk193

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 097. -/

theorem fin15Anchored_rejectSemanticSegment097
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom1240 chi) ∨
      ((Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom1268 chi) ∨
      (Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom1637 chi))) ∨
      (((¬Fin15AnchoredAtom3848 chi ∧
      Fin15AnchoredAtom1211 chi ∧
      Fin15AnchoredAtom1213 chi ∧
      Fin15AnchoredAtom1240 chi ∧
      Fin15AnchoredAtom1268 chi ∧
      Fin15AnchoredAtom1637 chi) ∨
      (Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom1212 chi)) ∨
      ((Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom1213 chi) ∨
      (Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom1241 chi)))) ∨
      ((((Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom1269 chi) ∨
      (Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom1638 chi)) ∨
      ((¬Fin15AnchoredAtom3849 chi ∧
      Fin15AnchoredAtom1212 chi ∧
      Fin15AnchoredAtom1213 chi ∧
      Fin15AnchoredAtom1241 chi ∧
      Fin15AnchoredAtom1269 chi ∧
      Fin15AnchoredAtom1638 chi) ∨
      (Fin15AnchoredAtom3851 chi ∧
      ¬Fin15AnchoredAtom1214 chi))) ∨
      (((Fin15AnchoredAtom3854 chi ∧
      ¬Fin15AnchoredAtom1214 chi) ∨
      (Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom1215 chi)) ∨
      ((Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom1216 chi) ∨
      (Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom1227 chi))))) ∨
      (((((Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom1276 chi) ∨
      (Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom1645 chi)) ∨
      ((¬Fin15AnchoredAtom3856 chi ∧
      Fin15AnchoredAtom1215 chi ∧
      Fin15AnchoredAtom1216 chi ∧
      Fin15AnchoredAtom1227 chi ∧
      Fin15AnchoredAtom1276 chi ∧
      Fin15AnchoredAtom1645 chi) ∨
      (Fin15AnchoredAtom3857 chi ∧
      ¬Fin15AnchoredAtom1215 chi))) ∨
      (((Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom1215 chi) ∨
      (Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom1218 chi)) ∨
      ((Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom1229 chi) ∨
      (Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom1278 chi)))) ∨
      ((((Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom1647 chi) ∨
      (¬Fin15AnchoredAtom3858 chi ∧
      Fin15AnchoredAtom1215 chi ∧
      Fin15AnchoredAtom1218 chi ∧
      Fin15AnchoredAtom1229 chi ∧
      Fin15AnchoredAtom1278 chi ∧
      Fin15AnchoredAtom1647 chi)) ∨
      ((Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom1215 chi) ∨
      (Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom1219 chi))) ∨
      (((Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom1230 chi) ∨
      (Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom1279 chi)) ∨
      ((Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom1648 chi) ∨
      (¬Fin15AnchoredAtom3859 chi ∧
      Fin15AnchoredAtom1215 chi ∧
      Fin15AnchoredAtom1219 chi ∧
      Fin15AnchoredAtom1230 chi ∧
      Fin15AnchoredAtom1279 chi ∧
      Fin15AnchoredAtom1648 chi)))))) ∨
      ((((((Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom1215 chi) ∨
      (Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom1220 chi)) ∨
      ((Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom1231 chi) ∨
      (Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom1280 chi))) ∨
      (((Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom1649 chi) ∨
      (¬Fin15AnchoredAtom3860 chi ∧
      Fin15AnchoredAtom1215 chi ∧
      Fin15AnchoredAtom1220 chi ∧
      Fin15AnchoredAtom1231 chi ∧
      Fin15AnchoredAtom1280 chi ∧
      Fin15AnchoredAtom1649 chi)) ∨
      ((Fin15AnchoredAtom3861 chi ∧
      ¬Fin15AnchoredAtom1216 chi) ∨
      (Fin15AnchoredAtom3861 chi ∧
      ¬Fin15AnchoredAtom1217 chi)))) ∨
      ((((Fin15AnchoredAtom3861 chi ∧
      ¬Fin15AnchoredAtom1281 chi) ∨
      (Fin15AnchoredAtom3861 chi ∧
      ¬Fin15AnchoredAtom1650 chi)) ∨
      ((¬Fin15AnchoredAtom3861 chi ∧
      Fin15AnchoredAtom1216 chi ∧
      Fin15AnchoredAtom1217 chi ∧
      Fin15AnchoredAtom1232 chi ∧
      Fin15AnchoredAtom1281 chi ∧
      Fin15AnchoredAtom1650 chi) ∨
      (Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom1216 chi))) ∨
      (((Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom1218 chi) ∨
      (Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom1233 chi)) ∨
      ((Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom1282 chi) ∨
      (Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom1651 chi))))) ∨
      (((((¬Fin15AnchoredAtom3862 chi ∧
      Fin15AnchoredAtom1216 chi ∧
      Fin15AnchoredAtom1218 chi ∧
      Fin15AnchoredAtom1233 chi ∧
      Fin15AnchoredAtom1282 chi ∧
      Fin15AnchoredAtom1651 chi) ∨
      (Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom1216 chi)) ∨
      ((Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom1219 chi) ∨
      (Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom1234 chi))) ∨
      (((Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom1283 chi) ∨
      (Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom1652 chi)) ∨
      ((¬Fin15AnchoredAtom3863 chi ∧
      Fin15AnchoredAtom1216 chi ∧
      Fin15AnchoredAtom1219 chi ∧
      Fin15AnchoredAtom1234 chi ∧
      Fin15AnchoredAtom1283 chi ∧
      Fin15AnchoredAtom1652 chi) ∨
      (Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom1216 chi)))) ∨
      ((((Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom1220 chi) ∨
      (Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom1235 chi)) ∨
      ((Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom1284 chi) ∨
      (Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom1653 chi))) ∨
      (((¬Fin15AnchoredAtom3864 chi ∧
      Fin15AnchoredAtom1216 chi ∧
      Fin15AnchoredAtom1220 chi ∧
      Fin15AnchoredAtom1235 chi ∧
      Fin15AnchoredAtom1284 chi ∧
      Fin15AnchoredAtom1653 chi) ∨
      (Fin15AnchoredAtom3865 chi ∧
      ¬Fin15AnchoredAtom1218 chi)) ∨
      ((Fin15AnchoredAtom3865 chi ∧
      ¬Fin15AnchoredAtom1285 chi) ∨
      (Fin15AnchoredAtom3865 chi ∧
      ¬Fin15AnchoredAtom1654 chi))))))) ∨
      ((((((Fin15AnchoredAtom3866 chi ∧
      ¬Fin15AnchoredAtom1219 chi) ∨
      ((Fin15AnchoredAtom3867 chi ∧
      ¬Fin15AnchoredAtom1220 chi) ∨
      (Fin15AnchoredAtom3867 chi ∧
      ¬Fin15AnchoredAtom1656 chi))) ∨
      (((Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom1218 chi) ∨
      (Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom1219 chi)) ∨
      ((Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom1239 chi) ∨
      (Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom1288 chi)))) ∨
      ((((Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom1657 chi) ∨
      (¬Fin15AnchoredAtom3868 chi ∧
      Fin15AnchoredAtom1218 chi ∧
      Fin15AnchoredAtom1219 chi ∧
      Fin15AnchoredAtom1239 chi ∧
      Fin15AnchoredAtom1288 chi ∧
      Fin15AnchoredAtom1657 chi)) ∨
      ((Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom1218 chi) ∨
      (Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom1220 chi))) ∨
      (((Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom1240 chi) ∨
      (Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom1289 chi)) ∨
      ((Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom1658 chi) ∨
      (¬Fin15AnchoredAtom3869 chi ∧
      Fin15AnchoredAtom1218 chi ∧
      Fin15AnchoredAtom1220 chi ∧
      Fin15AnchoredAtom1240 chi ∧
      Fin15AnchoredAtom1289 chi ∧
      Fin15AnchoredAtom1658 chi))))) ∨
      (((((Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom1219 chi) ∨
      (Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom1220 chi)) ∨
      ((Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom1241 chi) ∨
      (Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom1290 chi))) ∨
      (((Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom1659 chi) ∨
      (¬Fin15AnchoredAtom3870 chi ∧
      Fin15AnchoredAtom1219 chi ∧
      Fin15AnchoredAtom1220 chi ∧
      Fin15AnchoredAtom1241 chi ∧
      Fin15AnchoredAtom1290 chi ∧
      Fin15AnchoredAtom1659 chi)) ∨
      ((Fin15AnchoredAtom3877 chi ∧
      ¬Fin15AnchoredAtom1222 chi) ∨
      (Fin15AnchoredAtom3877 chi ∧
      ¬Fin15AnchoredAtom1297 chi)))) ∨
      ((((Fin15AnchoredAtom3878 chi ∧
      ¬Fin15AnchoredAtom1222 chi) ∨
      (Fin15AnchoredAtom3878 chi ∧
      ¬Fin15AnchoredAtom1234 chi)) ∨
      ((Fin15AnchoredAtom3878 chi ∧
      ¬Fin15AnchoredAtom1298 chi) ∨
      (Fin15AnchoredAtom3883 chi ∧
      ¬Fin15AnchoredAtom1672 chi))) ∨
      (((Fin15AnchoredAtom3886 chi ∧
      ¬Fin15AnchoredAtom1227 chi) ∨
      (Fin15AnchoredAtom3886 chi ∧
      ¬Fin15AnchoredAtom1306 chi)) ∨
      ((Fin15AnchoredAtom3886 chi ∧
      ¬Fin15AnchoredAtom1675 chi) ∨
      (Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom1227 chi)))))) ∨
      ((((((Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom1229 chi) ∨
      (Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom1233 chi)) ∨
      ((Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom1307 chi) ∨
      (Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom1676 chi))) ∨
      (((¬Fin15AnchoredAtom3887 chi ∧
      Fin15AnchoredAtom1227 chi ∧
      Fin15AnchoredAtom1229 chi ∧
      Fin15AnchoredAtom1233 chi ∧
      Fin15AnchoredAtom1307 chi ∧
      Fin15AnchoredAtom1676 chi) ∨
      (Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom1227 chi)) ∨
      ((Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom1230 chi) ∨
      (Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom1234 chi)))) ∨
      ((((Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom1308 chi) ∨
      (Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom1677 chi)) ∨
      ((¬Fin15AnchoredAtom3888 chi ∧
      Fin15AnchoredAtom1227 chi ∧
      Fin15AnchoredAtom1230 chi ∧
      Fin15AnchoredAtom1234 chi ∧
      Fin15AnchoredAtom1308 chi ∧
      Fin15AnchoredAtom1677 chi) ∨
      (Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom1227 chi))) ∨
      (((Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom1231 chi) ∨
      (Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom1235 chi)) ∨
      ((Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom1309 chi) ∨
      (Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom1678 chi))))) ∨
      (((((¬Fin15AnchoredAtom3889 chi ∧
      Fin15AnchoredAtom1227 chi ∧
      Fin15AnchoredAtom1231 chi ∧
      Fin15AnchoredAtom1235 chi ∧
      Fin15AnchoredAtom1309 chi ∧
      Fin15AnchoredAtom1678 chi) ∨
      (Fin15AnchoredAtom3890 chi ∧
      ¬Fin15AnchoredAtom1229 chi)) ∨
      ((Fin15AnchoredAtom3890 chi ∧
      ¬Fin15AnchoredAtom1310 chi) ∨
      (Fin15AnchoredAtom3890 chi ∧
      ¬Fin15AnchoredAtom1679 chi))) ∨
      (((Fin15AnchoredAtom3891 chi ∧
      ¬Fin15AnchoredAtom1230 chi) ∨
      (Fin15AnchoredAtom3891 chi ∧
      ¬Fin15AnchoredAtom1680 chi)) ∨
      ((Fin15AnchoredAtom3892 chi ∧
      ¬Fin15AnchoredAtom1312 chi) ∨
      (Fin15AnchoredAtom3892 chi ∧
      ¬Fin15AnchoredAtom1681 chi)))) ∨
      ((((Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom1229 chi) ∨
      (Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom1230 chi)) ∨
      ((Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom1239 chi) ∨
      (Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom1313 chi))) ∨
      (((Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom1682 chi) ∨
      (¬Fin15AnchoredAtom3893 chi ∧
      Fin15AnchoredAtom1229 chi ∧
      Fin15AnchoredAtom1230 chi ∧
      Fin15AnchoredAtom1239 chi ∧
      Fin15AnchoredAtom1313 chi ∧
      Fin15AnchoredAtom1682 chi)) ∨
      ((Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom1229 chi) ∨
      (Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom1231 chi)))))))) ∨
      (((((((Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom1240 chi) ∨
      ((Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom1314 chi) ∨
      (Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom1683 chi))) ∨
      (((¬Fin15AnchoredAtom3894 chi ∧
      Fin15AnchoredAtom1229 chi ∧
      Fin15AnchoredAtom1231 chi ∧
      Fin15AnchoredAtom1240 chi ∧
      Fin15AnchoredAtom1314 chi ∧
      Fin15AnchoredAtom1683 chi) ∨
      (Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom1230 chi)) ∨
      ((Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom1231 chi) ∨
      (Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom1241 chi)))) ∨
      ((((Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom1315 chi) ∨
      (Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom1684 chi)) ∨
      ((¬Fin15AnchoredAtom3895 chi ∧
      Fin15AnchoredAtom1230 chi ∧
      Fin15AnchoredAtom1231 chi ∧
      Fin15AnchoredAtom1241 chi ∧
      Fin15AnchoredAtom1315 chi ∧
      Fin15AnchoredAtom1684 chi) ∨
      (Fin15AnchoredAtom3896 chi ∧
      ¬Fin15AnchoredAtom1316 chi))) ∨
      (((Fin15AnchoredAtom3896 chi ∧
      ¬Fin15AnchoredAtom1685 chi) ∨
      (¬Fin15AnchoredAtom3896 chi ∧
      Fin15AnchoredAtom1232 chi ∧
      Fin15AnchoredAtom1233 chi ∧
      Fin15AnchoredAtom1236 chi ∧
      Fin15AnchoredAtom1316 chi ∧
      Fin15AnchoredAtom1685 chi)) ∨
      ((Fin15AnchoredAtom3897 chi ∧
      ¬Fin15AnchoredAtom1234 chi) ∨
      (Fin15AnchoredAtom3897 chi ∧
      ¬Fin15AnchoredAtom1686 chi))))) ∨
      (((((¬Fin15AnchoredAtom3897 chi ∧
      Fin15AnchoredAtom1232 chi ∧
      Fin15AnchoredAtom1234 chi ∧
      Fin15AnchoredAtom1237 chi ∧
      Fin15AnchoredAtom1317 chi ∧
      Fin15AnchoredAtom1686 chi) ∨
      (Fin15AnchoredAtom3898 chi ∧
      ¬Fin15AnchoredAtom1687 chi)) ∨
      ((Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom1233 chi) ∨
      (Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom1234 chi))) ∨
      (((Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom1239 chi) ∨
      (Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom1319 chi)) ∨
      ((Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom1688 chi) ∨
      (¬Fin15AnchoredAtom3899 chi ∧
      Fin15AnchoredAtom1233 chi ∧
      Fin15AnchoredAtom1234 chi ∧
      Fin15AnchoredAtom1239 chi ∧
      Fin15AnchoredAtom1319 chi ∧
      Fin15AnchoredAtom1688 chi)))) ∨
      ((((Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom1233 chi) ∨
      (Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom1235 chi)) ∨
      ((Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom1240 chi) ∨
      (Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom1320 chi))) ∨
      (((Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom1689 chi) ∨
      (¬Fin15AnchoredAtom3900 chi ∧
      Fin15AnchoredAtom1233 chi ∧
      Fin15AnchoredAtom1235 chi ∧
      Fin15AnchoredAtom1240 chi ∧
      Fin15AnchoredAtom1320 chi ∧
      Fin15AnchoredAtom1689 chi)) ∨
      ((Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom1234 chi) ∨
      (Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom1235 chi)))))) ∨
      ((((((Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom1241 chi) ∨
      (Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom1321 chi)) ∨
      ((Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom1690 chi) ∨
      (¬Fin15AnchoredAtom3901 chi ∧
      Fin15AnchoredAtom1234 chi ∧
      Fin15AnchoredAtom1235 chi ∧
      Fin15AnchoredAtom1241 chi ∧
      Fin15AnchoredAtom1321 chi ∧
      Fin15AnchoredAtom1690 chi))) ∨
      (((Fin15AnchoredAtom3902 chi ∧
      ¬Fin15AnchoredAtom1239 chi) ∨
      (Fin15AnchoredAtom3902 chi ∧
      ¬Fin15AnchoredAtom1322 chi)) ∨
      ((Fin15AnchoredAtom3903 chi ∧
      ¬Fin15AnchoredAtom1692 chi) ∨
      (Fin15AnchoredAtom3904 chi ∧
      ¬Fin15AnchoredAtom1241 chi)))) ∨
      ((((Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom1239 chi) ∨
      (Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom1240 chi)) ∨
      ((Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom1241 chi) ∨
      (Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom1325 chi))) ∨
      (((Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom1694 chi) ∨
      (¬Fin15AnchoredAtom3905 chi ∧
      Fin15AnchoredAtom1239 chi ∧
      Fin15AnchoredAtom1240 chi ∧
      Fin15AnchoredAtom1241 chi ∧
      Fin15AnchoredAtom1325 chi ∧
      Fin15AnchoredAtom1694 chi)) ∨
      ((Fin15AnchoredAtom3906 chi ∧
      ¬Fin15AnchoredAtom1270 chi) ∨
      (Fin15AnchoredAtom3906 chi ∧
      ¬Fin15AnchoredAtom1695 chi))))) ∨
      (((((¬Fin15AnchoredAtom3906 chi ∧
      Fin15AnchoredAtom1242 chi ∧
      Fin15AnchoredAtom1243 chi ∧
      Fin15AnchoredAtom1249 chi ∧
      Fin15AnchoredAtom1270 chi ∧
      Fin15AnchoredAtom1695 chi) ∨
      (Fin15AnchoredAtom3907 chi ∧
      ¬Fin15AnchoredAtom1271 chi)) ∨
      ((Fin15AnchoredAtom3907 chi ∧
      ¬Fin15AnchoredAtom1696 chi) ∨
      (Fin15AnchoredAtom3911 chi ∧
      ¬Fin15AnchoredAtom1248 chi))) ∨
      (((Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom1243 chi) ∨
      (Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom1244 chi)) ∨
      ((Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom1255 chi) ∨
      (Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom1276 chi)))) ∨
      ((((Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom1701 chi) ∨
      (¬Fin15AnchoredAtom3912 chi ∧
      Fin15AnchoredAtom1243 chi ∧
      Fin15AnchoredAtom1244 chi ∧
      Fin15AnchoredAtom1255 chi ∧
      Fin15AnchoredAtom1276 chi ∧
      Fin15AnchoredAtom1701 chi)) ∨
      ((Fin15AnchoredAtom3913 chi ∧
      ¬Fin15AnchoredAtom1243 chi) ∨
      (Fin15AnchoredAtom3913 chi ∧
      ¬Fin15AnchoredAtom1256 chi))) ∨
      (((Fin15AnchoredAtom3913 chi ∧
      ¬Fin15AnchoredAtom1277 chi) ∨
      (Fin15AnchoredAtom3913 chi ∧
      ¬Fin15AnchoredAtom1702 chi)) ∨
      ((¬Fin15AnchoredAtom3913 chi ∧
      Fin15AnchoredAtom1243 chi ∧
      Fin15AnchoredAtom1245 chi ∧
      Fin15AnchoredAtom1256 chi ∧
      Fin15AnchoredAtom1277 chi ∧
      Fin15AnchoredAtom1702 chi) ∨
      (Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom1243 chi))))))) ∨
      ((((((Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom1246 chi) ∨
      ((Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom1257 chi) ∨
      (Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom1278 chi))) ∨
      (((Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom1703 chi) ∨
      (¬Fin15AnchoredAtom3914 chi ∧
      Fin15AnchoredAtom1243 chi ∧
      Fin15AnchoredAtom1246 chi ∧
      Fin15AnchoredAtom1257 chi ∧
      Fin15AnchoredAtom1278 chi ∧
      Fin15AnchoredAtom1703 chi)) ∨
      ((Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom1243 chi) ∨
      (Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom1247 chi)))) ∨
      ((((Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom1258 chi) ∨
      (Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom1279 chi)) ∨
      ((Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom1704 chi) ∨
      (¬Fin15AnchoredAtom3915 chi ∧
      Fin15AnchoredAtom1243 chi ∧
      Fin15AnchoredAtom1247 chi ∧
      Fin15AnchoredAtom1258 chi ∧
      Fin15AnchoredAtom1279 chi ∧
      Fin15AnchoredAtom1704 chi))) ∨
      (((Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom1243 chi) ∨
      (Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom1248 chi)) ∨
      ((Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom1259 chi) ∨
      (Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom1280 chi))))) ∨
      (((((Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom1705 chi) ∨
      (¬Fin15AnchoredAtom3916 chi ∧
      Fin15AnchoredAtom1243 chi ∧
      Fin15AnchoredAtom1248 chi ∧
      Fin15AnchoredAtom1259 chi ∧
      Fin15AnchoredAtom1280 chi ∧
      Fin15AnchoredAtom1705 chi)) ∨
      ((Fin15AnchoredAtom3917 chi ∧
      ¬Fin15AnchoredAtom1244 chi) ∨
      (Fin15AnchoredAtom3917 chi ∧
      ¬Fin15AnchoredAtom1260 chi))) ∨
      (((Fin15AnchoredAtom3917 chi ∧
      ¬Fin15AnchoredAtom1281 chi) ∨
      (Fin15AnchoredAtom3917 chi ∧
      ¬Fin15AnchoredAtom1706 chi)) ∨
      ((¬Fin15AnchoredAtom3917 chi ∧
      Fin15AnchoredAtom1244 chi ∧
      Fin15AnchoredAtom1245 chi ∧
      Fin15AnchoredAtom1260 chi ∧
      Fin15AnchoredAtom1281 chi ∧
      Fin15AnchoredAtom1706 chi) ∨
      (Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom1244 chi)))) ∨
      ((((Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom1246 chi) ∨
      (Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom1261 chi)) ∨
      ((Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom1282 chi) ∨
      (Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom1707 chi))) ∨
      (((¬Fin15AnchoredAtom3918 chi ∧
      Fin15AnchoredAtom1244 chi ∧
      Fin15AnchoredAtom1246 chi ∧
      Fin15AnchoredAtom1261 chi ∧
      Fin15AnchoredAtom1282 chi ∧
      Fin15AnchoredAtom1707 chi) ∨
      (Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom1244 chi)) ∨
      ((Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom1247 chi) ∨
      (Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom1262 chi)))))) ∨
      ((((((Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom1283 chi) ∨
      (Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom1708 chi)) ∨
      ((¬Fin15AnchoredAtom3919 chi ∧
      Fin15AnchoredAtom1244 chi ∧
      Fin15AnchoredAtom1247 chi ∧
      Fin15AnchoredAtom1262 chi ∧
      Fin15AnchoredAtom1283 chi ∧
      Fin15AnchoredAtom1708 chi) ∨
      (Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom1244 chi))) ∨
      (((Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom1248 chi) ∨
      (Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom1263 chi)) ∨
      ((Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom1284 chi) ∨
      (Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom1709 chi)))) ∨
      ((((¬Fin15AnchoredAtom3920 chi ∧
      Fin15AnchoredAtom1244 chi ∧
      Fin15AnchoredAtom1248 chi ∧
      Fin15AnchoredAtom1263 chi ∧
      Fin15AnchoredAtom1284 chi ∧
      Fin15AnchoredAtom1709 chi) ∨
      (Fin15AnchoredAtom3921 chi ∧
      ¬Fin15AnchoredAtom1246 chi)) ∨
      ((Fin15AnchoredAtom3921 chi ∧
      ¬Fin15AnchoredAtom1264 chi) ∨
      (Fin15AnchoredAtom3921 chi ∧
      ¬Fin15AnchoredAtom1285 chi))) ∨
      (((Fin15AnchoredAtom3921 chi ∧
      ¬Fin15AnchoredAtom1710 chi) ∨
      (Fin15AnchoredAtom3922 chi ∧
      ¬Fin15AnchoredAtom1247 chi)) ∨
      ((Fin15AnchoredAtom3922 chi ∧
      ¬Fin15AnchoredAtom1286 chi) ∨
      (¬Fin15AnchoredAtom3922 chi ∧
      Fin15AnchoredAtom1245 chi ∧
      Fin15AnchoredAtom1247 chi ∧
      Fin15AnchoredAtom1265 chi ∧
      Fin15AnchoredAtom1286 chi ∧
      Fin15AnchoredAtom1711 chi))))) ∨
      (((((Fin15AnchoredAtom3923 chi ∧
      ¬Fin15AnchoredAtom1248 chi) ∨
      (Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom1246 chi)) ∨
      ((Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom1247 chi) ∨
      (Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom1267 chi))) ∨
      (((Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom1288 chi) ∨
      (Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom1713 chi)) ∨
      ((¬Fin15AnchoredAtom3924 chi ∧
      Fin15AnchoredAtom1246 chi ∧
      Fin15AnchoredAtom1247 chi ∧
      Fin15AnchoredAtom1267 chi ∧
      Fin15AnchoredAtom1288 chi ∧
      Fin15AnchoredAtom1713 chi) ∨
      (Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom1246 chi)))) ∨
      ((((Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom1248 chi) ∨
      (Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom1268 chi)) ∨
      ((Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom1289 chi) ∨
      (Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom1714 chi))) ∨
      (((¬Fin15AnchoredAtom3925 chi ∧
      Fin15AnchoredAtom1246 chi ∧
      Fin15AnchoredAtom1248 chi ∧
      Fin15AnchoredAtom1268 chi ∧
      Fin15AnchoredAtom1289 chi ∧
      Fin15AnchoredAtom1714 chi) ∨
      (Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom1247 chi)) ∨
      ((Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom1248 chi) ∨
      (Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom1269 chi)))))))))) := by
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
                exact fin15Anchored_clause24483 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24484 chi hbad
                ·
                  exact fin15Anchored_clause24485 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24486 chi hbad
                ·
                  exact fin15Anchored_clause24487 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24488 chi hbad
                ·
                  exact fin15Anchored_clause24489 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24490 chi hbad
                ·
                  exact fin15Anchored_clause24491 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24492 chi hbad
                ·
                  exact fin15Anchored_clause24493 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24494 chi hbad
                ·
                  exact fin15Anchored_clause24495 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24496 chi hbad
                ·
                  exact fin15Anchored_clause24497 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24498 chi hbad
                ·
                  exact fin15Anchored_clause24499 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24500 chi hbad
                ·
                  exact fin15Anchored_clause24501 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24502 chi hbad
                ·
                  exact fin15Anchored_clause24503 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24504 chi hbad
                ·
                  exact fin15Anchored_clause24505 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24506 chi hbad
                ·
                  exact fin15Anchored_clause24507 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24508 chi hbad
                ·
                  exact fin15Anchored_clause24509 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24510 chi hbad
                ·
                  exact fin15Anchored_clause24511 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24512 chi hbad
                ·
                  exact fin15Anchored_clause24513 chi hbad
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
                  exact fin15Anchored_clause24514 chi hbad
                ·
                  exact fin15Anchored_clause24515 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24516 chi hbad
                ·
                  exact fin15Anchored_clause24517 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24518 chi hbad
                ·
                  exact fin15Anchored_clause24519 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24520 chi hbad
                ·
                  exact fin15Anchored_clause24521 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24522 chi hbad
                ·
                  exact fin15Anchored_clause24523 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24524 chi hbad
                ·
                  exact fin15Anchored_clause24525 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24526 chi hbad
                ·
                  exact fin15Anchored_clause24527 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24528 chi hbad
                ·
                  exact fin15Anchored_clause24529 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24530 chi hbad
                ·
                  exact fin15Anchored_clause24531 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24532 chi hbad
                ·
                  exact fin15Anchored_clause24533 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24534 chi hbad
                ·
                  exact fin15Anchored_clause24535 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24536 chi hbad
                ·
                  exact fin15Anchored_clause24537 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24538 chi hbad
                ·
                  exact fin15Anchored_clause24539 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24540 chi hbad
                ·
                  exact fin15Anchored_clause24541 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24542 chi hbad
                ·
                  exact fin15Anchored_clause24543 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24544 chi hbad
                ·
                  exact fin15Anchored_clause24545 chi hbad
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
                exact fin15Anchored_clause24546 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24547 chi hbad
                ·
                  exact fin15Anchored_clause24548 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24549 chi hbad
                ·
                  exact fin15Anchored_clause24550 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24551 chi hbad
                ·
                  exact fin15Anchored_clause24552 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24553 chi hbad
                ·
                  exact fin15Anchored_clause24554 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24555 chi hbad
                ·
                  exact fin15Anchored_clause24556 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24557 chi hbad
                ·
                  exact fin15Anchored_clause24558 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24559 chi hbad
                ·
                  exact fin15Anchored_clause24560 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24561 chi hbad
                ·
                  exact fin15Anchored_clause24562 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24563 chi hbad
                ·
                  exact fin15Anchored_clause24564 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24565 chi hbad
                ·
                  exact fin15Anchored_clause24566 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24567 chi hbad
                ·
                  exact fin15Anchored_clause24568 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24569 chi hbad
                ·
                  exact fin15Anchored_clause24570 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24571 chi hbad
                ·
                  exact fin15Anchored_clause24572 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24573 chi hbad
                ·
                  exact fin15Anchored_clause24574 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24575 chi hbad
                ·
                  exact fin15Anchored_clause24576 chi hbad
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
                  exact fin15Anchored_clause24577 chi hbad
                ·
                  exact fin15Anchored_clause24578 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24579 chi hbad
                ·
                  exact fin15Anchored_clause24580 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24581 chi hbad
                ·
                  exact fin15Anchored_clause24582 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24583 chi hbad
                ·
                  exact fin15Anchored_clause24584 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24585 chi hbad
                ·
                  exact fin15Anchored_clause24586 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24587 chi hbad
                ·
                  exact fin15Anchored_clause24588 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24589 chi hbad
                ·
                  exact fin15Anchored_clause24590 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24591 chi hbad
                ·
                  exact fin15Anchored_clause24592 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24593 chi hbad
                ·
                  exact fin15Anchored_clause24594 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24595 chi hbad
                ·
                  exact fin15Anchored_clause24596 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24597 chi hbad
                ·
                  exact fin15Anchored_clause24598 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24599 chi hbad
                ·
                  exact fin15Anchored_clause24600 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24601 chi hbad
                ·
                  exact fin15Anchored_clause24602 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24603 chi hbad
                ·
                  exact fin15Anchored_clause24604 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24605 chi hbad
                ·
                  exact fin15Anchored_clause24606 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24607 chi hbad
                ·
                  exact fin15Anchored_clause24608 chi hbad
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
                exact fin15Anchored_clause24609 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24610 chi hbad
                ·
                  exact fin15Anchored_clause24611 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24612 chi hbad
                ·
                  exact fin15Anchored_clause24613 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24614 chi hbad
                ·
                  exact fin15Anchored_clause24615 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24616 chi hbad
                ·
                  exact fin15Anchored_clause24617 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24618 chi hbad
                ·
                  exact fin15Anchored_clause24619 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24620 chi hbad
                ·
                  exact fin15Anchored_clause24621 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24622 chi hbad
                ·
                  exact fin15Anchored_clause24623 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24624 chi hbad
                ·
                  exact fin15Anchored_clause24625 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24626 chi hbad
                ·
                  exact fin15Anchored_clause24627 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24628 chi hbad
                ·
                  exact fin15Anchored_clause24629 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24630 chi hbad
                ·
                  exact fin15Anchored_clause24631 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24632 chi hbad
                ·
                  exact fin15Anchored_clause24633 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24634 chi hbad
                ·
                  exact fin15Anchored_clause24635 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24636 chi hbad
                ·
                  exact fin15Anchored_clause24637 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24638 chi hbad
                ·
                  exact fin15Anchored_clause24639 chi hbad
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
                  exact fin15Anchored_clause24640 chi hbad
                ·
                  exact fin15Anchored_clause24641 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24642 chi hbad
                ·
                  exact fin15Anchored_clause24643 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24644 chi hbad
                ·
                  exact fin15Anchored_clause24645 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24646 chi hbad
                ·
                  exact fin15Anchored_clause24647 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24648 chi hbad
                ·
                  exact fin15Anchored_clause24649 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24650 chi hbad
                ·
                  exact fin15Anchored_clause24651 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24652 chi hbad
                ·
                  exact fin15Anchored_clause24653 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24654 chi hbad
                ·
                  exact fin15Anchored_clause24655 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24656 chi hbad
                ·
                  exact fin15Anchored_clause24657 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24658 chi hbad
                ·
                  exact fin15Anchored_clause24659 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24660 chi hbad
                ·
                  exact fin15Anchored_clause24661 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24662 chi hbad
                ·
                  exact fin15Anchored_clause24663 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24664 chi hbad
                ·
                  exact fin15Anchored_clause24665 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24666 chi hbad
                ·
                  exact fin15Anchored_clause24667 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24668 chi hbad
                ·
                  exact fin15Anchored_clause24669 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24670 chi hbad
                ·
                  exact fin15Anchored_clause24671 chi hbad
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
                exact fin15Anchored_clause24672 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24673 chi hbad
                ·
                  exact fin15Anchored_clause24674 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24675 chi hbad
                ·
                  exact fin15Anchored_clause24676 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24677 chi hbad
                ·
                  exact fin15Anchored_clause24678 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24679 chi hbad
                ·
                  exact fin15Anchored_clause24680 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24681 chi hbad
                ·
                  exact fin15Anchored_clause24682 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24683 chi hbad
                ·
                  exact fin15Anchored_clause24684 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24685 chi hbad
                ·
                  exact fin15Anchored_clause24686 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24687 chi hbad
                ·
                  exact fin15Anchored_clause24688 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24689 chi hbad
                ·
                  exact fin15Anchored_clause24690 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24691 chi hbad
                ·
                  exact fin15Anchored_clause24692 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24693 chi hbad
                ·
                  exact fin15Anchored_clause24694 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24695 chi hbad
                ·
                  exact fin15Anchored_clause24696 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24697 chi hbad
                ·
                  exact fin15Anchored_clause24698 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24699 chi hbad
                ·
                  exact fin15Anchored_clause24700 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24701 chi hbad
                ·
                  exact fin15Anchored_clause24702 chi hbad
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
                  exact fin15Anchored_clause24703 chi hbad
                ·
                  exact fin15Anchored_clause24704 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24705 chi hbad
                ·
                  exact fin15Anchored_clause24706 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24707 chi hbad
                ·
                  exact fin15Anchored_clause24708 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24709 chi hbad
                ·
                  exact fin15Anchored_clause24710 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24711 chi hbad
                ·
                  exact fin15Anchored_clause24712 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24713 chi hbad
                ·
                  exact fin15Anchored_clause24714 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24715 chi hbad
                ·
                  exact fin15Anchored_clause24716 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24717 chi hbad
                ·
                  exact fin15Anchored_clause24718 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24719 chi hbad
                ·
                  exact fin15Anchored_clause24720 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24721 chi hbad
                ·
                  exact fin15Anchored_clause24722 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24723 chi hbad
                ·
                  exact fin15Anchored_clause24724 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24725 chi hbad
                ·
                  exact fin15Anchored_clause24726 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24727 chi hbad
                ·
                  exact fin15Anchored_clause24728 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24729 chi hbad
                ·
                  exact fin15Anchored_clause24730 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24731 chi hbad
                ·
                  exact fin15Anchored_clause24732 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24733 chi hbad
                ·
                  exact fin15Anchored_clause24734 chi hbad

end ErdosSzekeres

end
