module

public import ErdosSzekeres.Fin15AnchoredClauseChunk193
public import ErdosSzekeres.Fin15AnchoredClauseChunk194
public import ErdosSzekeres.Fin15AnchoredClauseChunk195

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 098. -/

theorem fin15Anchored_rejectSemanticSegment098
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom1290 chi) ∨
      ((Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom1715 chi) ∨
      (¬Fin15AnchoredAtom3926 chi ∧
      Fin15AnchoredAtom1247 chi ∧
      Fin15AnchoredAtom1248 chi ∧
      Fin15AnchoredAtom1269 chi ∧
      Fin15AnchoredAtom1290 chi ∧
      Fin15AnchoredAtom1715 chi))) ∨
      (((Fin15AnchoredAtom3927 chi ∧
      ¬Fin15AnchoredAtom1255 chi) ∨
      (Fin15AnchoredAtom3933 chi ∧
      ¬Fin15AnchoredAtom1297 chi)) ∨
      ((Fin15AnchoredAtom3934 chi ∧
      ¬Fin15AnchoredAtom1298 chi) ∨
      (Fin15AnchoredAtom3935 chi ∧
      ¬Fin15AnchoredAtom1263 chi)))) ∨
      ((((Fin15AnchoredAtom3939 chi ∧
      ¬Fin15AnchoredAtom1267 chi) ∨
      (Fin15AnchoredAtom3940 chi ∧
      ¬Fin15AnchoredAtom1268 chi)) ∨
      ((Fin15AnchoredAtom3941 chi ∧
      ¬Fin15AnchoredAtom1269 chi) ∨
      (Fin15AnchoredAtom3942 chi ∧
      ¬Fin15AnchoredAtom1255 chi))) ∨
      (((Fin15AnchoredAtom3942 chi ∧
      ¬Fin15AnchoredAtom1256 chi) ∨
      (Fin15AnchoredAtom3942 chi ∧
      ¬Fin15AnchoredAtom1260 chi)) ∨
      ((Fin15AnchoredAtom3942 chi ∧
      ¬Fin15AnchoredAtom1306 chi) ∨
      (Fin15AnchoredAtom3942 chi ∧
      ¬Fin15AnchoredAtom1731 chi))))) ∨
      (((((¬Fin15AnchoredAtom3942 chi ∧
      Fin15AnchoredAtom1255 chi ∧
      Fin15AnchoredAtom1256 chi ∧
      Fin15AnchoredAtom1260 chi ∧
      Fin15AnchoredAtom1306 chi ∧
      Fin15AnchoredAtom1731 chi) ∨
      (Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom1255 chi)) ∨
      ((Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom1257 chi) ∨
      (Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom1261 chi))) ∨
      (((Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom1307 chi) ∨
      (Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom1732 chi)) ∨
      ((¬Fin15AnchoredAtom3943 chi ∧
      Fin15AnchoredAtom1255 chi ∧
      Fin15AnchoredAtom1257 chi ∧
      Fin15AnchoredAtom1261 chi ∧
      Fin15AnchoredAtom1307 chi ∧
      Fin15AnchoredAtom1732 chi) ∨
      (Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom1255 chi)))) ∨
      ((((Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom1258 chi) ∨
      (Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom1262 chi)) ∨
      ((Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom1308 chi) ∨
      (Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom1733 chi))) ∨
      (((¬Fin15AnchoredAtom3944 chi ∧
      Fin15AnchoredAtom1255 chi ∧
      Fin15AnchoredAtom1258 chi ∧
      Fin15AnchoredAtom1262 chi ∧
      Fin15AnchoredAtom1308 chi ∧
      Fin15AnchoredAtom1733 chi) ∨
      (Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom1255 chi)) ∨
      ((Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom1259 chi) ∨
      (Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom1263 chi)))))) ∨
      ((((((Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom1309 chi) ∨
      (Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom1734 chi)) ∨
      ((¬Fin15AnchoredAtom3945 chi ∧
      Fin15AnchoredAtom1255 chi ∧
      Fin15AnchoredAtom1259 chi ∧
      Fin15AnchoredAtom1263 chi ∧
      Fin15AnchoredAtom1309 chi ∧
      Fin15AnchoredAtom1734 chi) ∨
      (Fin15AnchoredAtom3946 chi ∧
      ¬Fin15AnchoredAtom1256 chi))) ∨
      (((Fin15AnchoredAtom3946 chi ∧
      ¬Fin15AnchoredAtom1257 chi) ∨
      (Fin15AnchoredAtom3946 chi ∧
      ¬Fin15AnchoredAtom1735 chi)) ∨
      ((¬Fin15AnchoredAtom3946 chi ∧
      Fin15AnchoredAtom1256 chi ∧
      Fin15AnchoredAtom1257 chi ∧
      Fin15AnchoredAtom1264 chi ∧
      Fin15AnchoredAtom1310 chi ∧
      Fin15AnchoredAtom1735 chi) ∨
      (Fin15AnchoredAtom3947 chi ∧
      ¬Fin15AnchoredAtom1256 chi)))) ∨
      ((((Fin15AnchoredAtom3947 chi ∧
      ¬Fin15AnchoredAtom1258 chi) ∨
      (Fin15AnchoredAtom3947 chi ∧
      ¬Fin15AnchoredAtom1311 chi)) ∨
      ((Fin15AnchoredAtom3947 chi ∧
      ¬Fin15AnchoredAtom1736 chi) ∨
      (¬Fin15AnchoredAtom3947 chi ∧
      Fin15AnchoredAtom1256 chi ∧
      Fin15AnchoredAtom1258 chi ∧
      Fin15AnchoredAtom1265 chi ∧
      Fin15AnchoredAtom1311 chi ∧
      Fin15AnchoredAtom1736 chi))) ∨
      (((Fin15AnchoredAtom3948 chi ∧
      ¬Fin15AnchoredAtom1256 chi) ∨
      (Fin15AnchoredAtom3948 chi ∧
      ¬Fin15AnchoredAtom1266 chi)) ∨
      ((Fin15AnchoredAtom3948 chi ∧
      ¬Fin15AnchoredAtom1312 chi) ∨
      (Fin15AnchoredAtom3948 chi ∧
      ¬Fin15AnchoredAtom1737 chi))))) ∨
      (((((¬Fin15AnchoredAtom3948 chi ∧
      Fin15AnchoredAtom1256 chi ∧
      Fin15AnchoredAtom1259 chi ∧
      Fin15AnchoredAtom1266 chi ∧
      Fin15AnchoredAtom1312 chi ∧
      Fin15AnchoredAtom1737 chi) ∨
      (Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom1257 chi)) ∨
      ((Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom1258 chi) ∨
      (Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom1267 chi))) ∨
      (((Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom1313 chi) ∨
      (Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom1738 chi)) ∨
      ((¬Fin15AnchoredAtom3949 chi ∧
      Fin15AnchoredAtom1257 chi ∧
      Fin15AnchoredAtom1258 chi ∧
      Fin15AnchoredAtom1267 chi ∧
      Fin15AnchoredAtom1313 chi ∧
      Fin15AnchoredAtom1738 chi) ∨
      (Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom1257 chi)))) ∨
      ((((Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom1259 chi) ∨
      (Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom1268 chi)) ∨
      ((Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom1314 chi) ∨
      (Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom1739 chi))) ∨
      (((¬Fin15AnchoredAtom3950 chi ∧
      Fin15AnchoredAtom1257 chi ∧
      Fin15AnchoredAtom1259 chi ∧
      Fin15AnchoredAtom1268 chi ∧
      Fin15AnchoredAtom1314 chi ∧
      Fin15AnchoredAtom1739 chi) ∨
      (Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom1258 chi)) ∨
      ((Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom1259 chi) ∨
      (Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom1269 chi))))))) ∨
      ((((((Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom1315 chi) ∨
      ((Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom1740 chi) ∨
      (¬Fin15AnchoredAtom3951 chi ∧
      Fin15AnchoredAtom1258 chi ∧
      Fin15AnchoredAtom1259 chi ∧
      Fin15AnchoredAtom1269 chi ∧
      Fin15AnchoredAtom1315 chi ∧
      Fin15AnchoredAtom1740 chi))) ∨
      (((Fin15AnchoredAtom3952 chi ∧
      ¬Fin15AnchoredAtom1260 chi) ∨
      (Fin15AnchoredAtom3952 chi ∧
      ¬Fin15AnchoredAtom1261 chi)) ∨
      ((Fin15AnchoredAtom3952 chi ∧
      ¬Fin15AnchoredAtom1264 chi) ∨
      (Fin15AnchoredAtom3952 chi ∧
      ¬Fin15AnchoredAtom1316 chi)))) ∨
      ((((Fin15AnchoredAtom3952 chi ∧
      ¬Fin15AnchoredAtom1741 chi) ∨
      (¬Fin15AnchoredAtom3952 chi ∧
      Fin15AnchoredAtom1260 chi ∧
      Fin15AnchoredAtom1261 chi ∧
      Fin15AnchoredAtom1264 chi ∧
      Fin15AnchoredAtom1316 chi ∧
      Fin15AnchoredAtom1741 chi)) ∨
      ((Fin15AnchoredAtom3953 chi ∧
      ¬Fin15AnchoredAtom1262 chi) ∨
      (Fin15AnchoredAtom3953 chi ∧
      ¬Fin15AnchoredAtom1265 chi))) ∨
      (((Fin15AnchoredAtom3953 chi ∧
      ¬Fin15AnchoredAtom1317 chi) ∨
      (¬Fin15AnchoredAtom3953 chi ∧
      Fin15AnchoredAtom1260 chi ∧
      Fin15AnchoredAtom1262 chi ∧
      Fin15AnchoredAtom1265 chi ∧
      Fin15AnchoredAtom1317 chi ∧
      Fin15AnchoredAtom1742 chi)) ∨
      ((Fin15AnchoredAtom3954 chi ∧
      ¬Fin15AnchoredAtom1263 chi) ∨
      (Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom1261 chi))))) ∨
      (((((Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom1262 chi) ∨
      (Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom1267 chi)) ∨
      ((Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom1319 chi) ∨
      (Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom1744 chi))) ∨
      (((¬Fin15AnchoredAtom3955 chi ∧
      Fin15AnchoredAtom1261 chi ∧
      Fin15AnchoredAtom1262 chi ∧
      Fin15AnchoredAtom1267 chi ∧
      Fin15AnchoredAtom1319 chi ∧
      Fin15AnchoredAtom1744 chi) ∨
      (Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom1261 chi)) ∨
      ((Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom1263 chi) ∨
      (Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom1268 chi)))) ∨
      ((((Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom1320 chi) ∨
      (Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom1745 chi)) ∨
      ((¬Fin15AnchoredAtom3956 chi ∧
      Fin15AnchoredAtom1261 chi ∧
      Fin15AnchoredAtom1263 chi ∧
      Fin15AnchoredAtom1268 chi ∧
      Fin15AnchoredAtom1320 chi ∧
      Fin15AnchoredAtom1745 chi) ∨
      (Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom1262 chi))) ∨
      (((Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom1263 chi) ∨
      (Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom1269 chi)) ∨
      ((Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom1321 chi) ∨
      (Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom1746 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom3957 chi ∧
      Fin15AnchoredAtom1262 chi ∧
      Fin15AnchoredAtom1263 chi ∧
      Fin15AnchoredAtom1269 chi ∧
      Fin15AnchoredAtom1321 chi ∧
      Fin15AnchoredAtom1746 chi) ∨
      (Fin15AnchoredAtom3958 chi ∧
      ¬Fin15AnchoredAtom1267 chi)) ∨
      ((Fin15AnchoredAtom3958 chi ∧
      ¬Fin15AnchoredAtom1322 chi) ∨
      (Fin15AnchoredAtom3958 chi ∧
      ¬Fin15AnchoredAtom1747 chi))) ∨
      (((¬Fin15AnchoredAtom3958 chi ∧
      Fin15AnchoredAtom1264 chi ∧
      Fin15AnchoredAtom1265 chi ∧
      Fin15AnchoredAtom1267 chi ∧
      Fin15AnchoredAtom1322 chi ∧
      Fin15AnchoredAtom1747 chi) ∨
      (Fin15AnchoredAtom3959 chi ∧
      ¬Fin15AnchoredAtom1323 chi)) ∨
      ((Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom1267 chi) ∨
      (Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom1268 chi)))) ∨
      ((((Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom1269 chi) ∨
      (Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom1325 chi)) ∨
      ((Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom1750 chi) ∨
      (¬Fin15AnchoredAtom3961 chi ∧
      Fin15AnchoredAtom1267 chi ∧
      Fin15AnchoredAtom1268 chi ∧
      Fin15AnchoredAtom1269 chi ∧
      Fin15AnchoredAtom1325 chi ∧
      Fin15AnchoredAtom1750 chi))) ∨
      (((Fin15AnchoredAtom3962 chi ∧
      ¬Fin15AnchoredAtom1276 chi) ∨
      (Fin15AnchoredAtom3964 chi ∧
      ¬Fin15AnchoredAtom1270 chi)) ∨
      ((Fin15AnchoredAtom3966 chi ∧
      ¬Fin15AnchoredAtom1280 chi) ∨
      (Fin15AnchoredAtom3969 chi ∧
      ¬Fin15AnchoredAtom1758 chi))))) ∨
      (((((Fin15AnchoredAtom3975 chi ∧
      ¬Fin15AnchoredAtom1273 chi) ∨
      (Fin15AnchoredAtom3975 chi ∧
      ¬Fin15AnchoredAtom1304 chi)) ∨
      ((Fin15AnchoredAtom3977 chi ∧
      ¬Fin15AnchoredAtom1276 chi) ∨
      (Fin15AnchoredAtom3977 chi ∧
      ¬Fin15AnchoredAtom1306 chi))) ∨
      (((Fin15AnchoredAtom3977 chi ∧
      ¬Fin15AnchoredAtom1766 chi) ∨
      (¬Fin15AnchoredAtom3977 chi ∧
      Fin15AnchoredAtom1276 chi ∧
      Fin15AnchoredAtom1277 chi ∧
      Fin15AnchoredAtom1281 chi ∧
      Fin15AnchoredAtom1306 chi ∧
      Fin15AnchoredAtom1766 chi)) ∨
      ((Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom1276 chi) ∨
      (Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom1278 chi)))) ∨
      ((((Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom1282 chi) ∨
      (Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom1307 chi)) ∨
      ((Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom1767 chi) ∨
      (¬Fin15AnchoredAtom3978 chi ∧
      Fin15AnchoredAtom1276 chi ∧
      Fin15AnchoredAtom1278 chi ∧
      Fin15AnchoredAtom1282 chi ∧
      Fin15AnchoredAtom1307 chi ∧
      Fin15AnchoredAtom1767 chi))) ∨
      (((Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom1276 chi) ∨
      (Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom1279 chi)) ∨
      ((Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom1283 chi) ∨
      (Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom1308 chi)))))))) ∨
      (((((((Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom1768 chi) ∨
      ((¬Fin15AnchoredAtom3979 chi ∧
      Fin15AnchoredAtom1276 chi ∧
      Fin15AnchoredAtom1279 chi ∧
      Fin15AnchoredAtom1283 chi ∧
      Fin15AnchoredAtom1308 chi ∧
      Fin15AnchoredAtom1768 chi) ∨
      (Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom1276 chi))) ∨
      (((Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom1280 chi) ∨
      (Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom1284 chi)) ∨
      ((Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom1309 chi) ∨
      (Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom1769 chi)))) ∨
      ((((¬Fin15AnchoredAtom3980 chi ∧
      Fin15AnchoredAtom1276 chi ∧
      Fin15AnchoredAtom1280 chi ∧
      Fin15AnchoredAtom1284 chi ∧
      Fin15AnchoredAtom1309 chi ∧
      Fin15AnchoredAtom1769 chi) ∨
      (Fin15AnchoredAtom3981 chi ∧
      ¬Fin15AnchoredAtom1278 chi)) ∨
      ((Fin15AnchoredAtom3981 chi ∧
      ¬Fin15AnchoredAtom1310 chi) ∨
      (Fin15AnchoredAtom3981 chi ∧
      ¬Fin15AnchoredAtom1770 chi))) ∨
      (((¬Fin15AnchoredAtom3981 chi ∧
      Fin15AnchoredAtom1277 chi ∧
      Fin15AnchoredAtom1278 chi ∧
      Fin15AnchoredAtom1285 chi ∧
      Fin15AnchoredAtom1310 chi ∧
      Fin15AnchoredAtom1770 chi) ∨
      (Fin15AnchoredAtom3982 chi ∧
      ¬Fin15AnchoredAtom1279 chi)) ∨
      ((Fin15AnchoredAtom3982 chi ∧
      ¬Fin15AnchoredAtom1311 chi) ∨
      (Fin15AnchoredAtom3983 chi ∧
      ¬Fin15AnchoredAtom1280 chi))))) ∨
      (((((Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom1278 chi) ∨
      (Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom1279 chi)) ∨
      ((Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom1288 chi) ∨
      (Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom1313 chi))) ∨
      (((Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom1773 chi) ∨
      (¬Fin15AnchoredAtom3984 chi ∧
      Fin15AnchoredAtom1278 chi ∧
      Fin15AnchoredAtom1279 chi ∧
      Fin15AnchoredAtom1288 chi ∧
      Fin15AnchoredAtom1313 chi ∧
      Fin15AnchoredAtom1773 chi)) ∨
      ((Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom1278 chi) ∨
      (Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom1280 chi)))) ∨
      ((((Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom1289 chi) ∨
      (Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom1314 chi)) ∨
      ((Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom1774 chi) ∨
      (¬Fin15AnchoredAtom3985 chi ∧
      Fin15AnchoredAtom1278 chi ∧
      Fin15AnchoredAtom1280 chi ∧
      Fin15AnchoredAtom1289 chi ∧
      Fin15AnchoredAtom1314 chi ∧
      Fin15AnchoredAtom1774 chi))) ∨
      (((Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom1279 chi) ∨
      (Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom1280 chi)) ∨
      ((Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom1290 chi) ∨
      (Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom1315 chi)))))) ∨
      ((((((Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom1775 chi) ∨
      (¬Fin15AnchoredAtom3986 chi ∧
      Fin15AnchoredAtom1279 chi ∧
      Fin15AnchoredAtom1280 chi ∧
      Fin15AnchoredAtom1290 chi ∧
      Fin15AnchoredAtom1315 chi ∧
      Fin15AnchoredAtom1775 chi)) ∨
      ((Fin15AnchoredAtom3987 chi ∧
      ¬Fin15AnchoredAtom1282 chi) ∨
      (Fin15AnchoredAtom3987 chi ∧
      ¬Fin15AnchoredAtom1316 chi))) ∨
      (((Fin15AnchoredAtom3987 chi ∧
      ¬Fin15AnchoredAtom1776 chi) ∨
      (¬Fin15AnchoredAtom3987 chi ∧
      Fin15AnchoredAtom1281 chi ∧
      Fin15AnchoredAtom1282 chi ∧
      Fin15AnchoredAtom1285 chi ∧
      Fin15AnchoredAtom1316 chi ∧
      Fin15AnchoredAtom1776 chi)) ∨
      ((Fin15AnchoredAtom3988 chi ∧
      ¬Fin15AnchoredAtom1281 chi) ∨
      (Fin15AnchoredAtom3988 chi ∧
      ¬Fin15AnchoredAtom1777 chi)))) ∨
      ((((¬Fin15AnchoredAtom3988 chi ∧
      Fin15AnchoredAtom1281 chi ∧
      Fin15AnchoredAtom1283 chi ∧
      Fin15AnchoredAtom1286 chi ∧
      Fin15AnchoredAtom1317 chi ∧
      Fin15AnchoredAtom1777 chi) ∨
      (Fin15AnchoredAtom3989 chi ∧
      ¬Fin15AnchoredAtom1281 chi)) ∨
      ((Fin15AnchoredAtom3989 chi ∧
      ¬Fin15AnchoredAtom1284 chi) ∨
      (Fin15AnchoredAtom3989 chi ∧
      ¬Fin15AnchoredAtom1287 chi))) ∨
      (((Fin15AnchoredAtom3989 chi ∧
      ¬Fin15AnchoredAtom1318 chi) ∨
      (Fin15AnchoredAtom3989 chi ∧
      ¬Fin15AnchoredAtom1778 chi)) ∨
      ((Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom1282 chi) ∨
      (Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom1283 chi))))) ∨
      (((((Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom1288 chi) ∨
      (Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom1319 chi)) ∨
      ((Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom1779 chi) ∨
      (¬Fin15AnchoredAtom3990 chi ∧
      Fin15AnchoredAtom1282 chi ∧
      Fin15AnchoredAtom1283 chi ∧
      Fin15AnchoredAtom1288 chi ∧
      Fin15AnchoredAtom1319 chi ∧
      Fin15AnchoredAtom1779 chi))) ∨
      (((Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom1282 chi) ∨
      (Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom1284 chi)) ∨
      ((Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom1289 chi) ∨
      (Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom1320 chi)))) ∨
      ((((Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom1780 chi) ∨
      (¬Fin15AnchoredAtom3991 chi ∧
      Fin15AnchoredAtom1282 chi ∧
      Fin15AnchoredAtom1284 chi ∧
      Fin15AnchoredAtom1289 chi ∧
      Fin15AnchoredAtom1320 chi ∧
      Fin15AnchoredAtom1780 chi)) ∨
      ((Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom1283 chi) ∨
      (Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom1284 chi))) ∨
      (((Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom1290 chi) ∨
      (Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom1321 chi)) ∨
      ((Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom1781 chi) ∨
      (¬Fin15AnchoredAtom3992 chi ∧
      Fin15AnchoredAtom1283 chi ∧
      Fin15AnchoredAtom1284 chi ∧
      Fin15AnchoredAtom1290 chi ∧
      Fin15AnchoredAtom1321 chi ∧
      Fin15AnchoredAtom1781 chi))))))) ∨
      ((((((Fin15AnchoredAtom3993 chi ∧
      ¬Fin15AnchoredAtom1288 chi) ∨
      ((Fin15AnchoredAtom3993 chi ∧
      ¬Fin15AnchoredAtom1322 chi) ∨
      (Fin15AnchoredAtom3994 chi ∧
      ¬Fin15AnchoredAtom1289 chi))) ∨
      (((Fin15AnchoredAtom3994 chi ∧
      ¬Fin15AnchoredAtom1323 chi) ∨
      (Fin15AnchoredAtom3995 chi ∧
      ¬Fin15AnchoredAtom1286 chi)) ∨
      ((Fin15AnchoredAtom3995 chi ∧
      ¬Fin15AnchoredAtom1287 chi) ∨
      (¬Fin15AnchoredAtom3995 chi ∧
      Fin15AnchoredAtom1286 chi ∧
      Fin15AnchoredAtom1287 chi ∧
      Fin15AnchoredAtom1290 chi ∧
      Fin15AnchoredAtom1324 chi ∧
      Fin15AnchoredAtom1784 chi)))) ∨
      ((((Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom1288 chi) ∨
      (Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom1289 chi)) ∨
      ((Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom1290 chi) ∨
      (Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom1325 chi))) ∨
      (((Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom1785 chi) ∨
      (¬Fin15AnchoredAtom3996 chi ∧
      Fin15AnchoredAtom1288 chi ∧
      Fin15AnchoredAtom1289 chi ∧
      Fin15AnchoredAtom1290 chi ∧
      Fin15AnchoredAtom1325 chi ∧
      Fin15AnchoredAtom1785 chi)) ∨
      ((Fin15AnchoredAtom3998 chi ∧
      ¬Fin15AnchoredAtom1787 chi) ∨
      (¬Fin15AnchoredAtom3998 chi ∧
      Fin15AnchoredAtom1291 chi ∧
      Fin15AnchoredAtom1293 chi ∧
      Fin15AnchoredAtom1297 chi ∧
      Fin15AnchoredAtom1307 chi ∧
      Fin15AnchoredAtom1787 chi))))) ∨
      (((((Fin15AnchoredAtom4005 chi ∧
      ¬Fin15AnchoredAtom1314 chi) ∨
      (Fin15AnchoredAtom4010 chi ∧
      ¬Fin15AnchoredAtom1297 chi)) ∨
      ((Fin15AnchoredAtom4010 chi ∧
      ¬Fin15AnchoredAtom1319 chi) ∨
      (¬Fin15AnchoredAtom4010 chi ∧
      Fin15AnchoredAtom1297 chi ∧
      Fin15AnchoredAtom1298 chi ∧
      Fin15AnchoredAtom1303 chi ∧
      Fin15AnchoredAtom1319 chi ∧
      Fin15AnchoredAtom1799 chi))) ∨
      (((Fin15AnchoredAtom4011 chi ∧
      ¬Fin15AnchoredAtom1320 chi) ∨
      (Fin15AnchoredAtom4012 chi ∧
      ¬Fin15AnchoredAtom1321 chi)) ∨
      ((Fin15AnchoredAtom4016 chi ∧
      ¬Fin15AnchoredAtom1325 chi) ∨
      (Fin15AnchoredAtom4017 chi ∧
      ¬Fin15AnchoredAtom1306 chi)))) ∨
      ((((Fin15AnchoredAtom4017 chi ∧
      ¬Fin15AnchoredAtom1307 chi) ∨
      (Fin15AnchoredAtom4017 chi ∧
      ¬Fin15AnchoredAtom1806 chi)) ∨
      ((¬Fin15AnchoredAtom4017 chi ∧
      Fin15AnchoredAtom1306 chi ∧
      Fin15AnchoredAtom1307 chi ∧
      Fin15AnchoredAtom1310 chi ∧
      Fin15AnchoredAtom1316 chi ∧
      Fin15AnchoredAtom1806 chi) ∨
      (Fin15AnchoredAtom4018 chi ∧
      ¬Fin15AnchoredAtom1306 chi))) ∨
      (((Fin15AnchoredAtom4018 chi ∧
      ¬Fin15AnchoredAtom1308 chi) ∨
      (Fin15AnchoredAtom4019 chi ∧
      ¬Fin15AnchoredAtom1309 chi)) ∨
      ((Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom1307 chi) ∨
      (Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom1308 chi)))))) ∨
      ((((((Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom1313 chi) ∨
      (Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom1319 chi)) ∨
      ((Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom1809 chi) ∨
      (¬Fin15AnchoredAtom4020 chi ∧
      Fin15AnchoredAtom1307 chi ∧
      Fin15AnchoredAtom1308 chi ∧
      Fin15AnchoredAtom1313 chi ∧
      Fin15AnchoredAtom1319 chi ∧
      Fin15AnchoredAtom1809 chi))) ∨
      (((Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom1307 chi) ∨
      (Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom1309 chi)) ∨
      ((Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom1314 chi) ∨
      (Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom1320 chi)))) ∨
      ((((Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom1810 chi) ∨
      (¬Fin15AnchoredAtom4021 chi ∧
      Fin15AnchoredAtom1307 chi ∧
      Fin15AnchoredAtom1309 chi ∧
      Fin15AnchoredAtom1314 chi ∧
      Fin15AnchoredAtom1320 chi ∧
      Fin15AnchoredAtom1810 chi)) ∨
      ((Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom1308 chi) ∨
      (Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom1309 chi))) ∨
      (((Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom1315 chi) ∨
      (Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom1321 chi)) ∨
      ((Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom1811 chi) ∨
      (¬Fin15AnchoredAtom4022 chi ∧
      Fin15AnchoredAtom1308 chi ∧
      Fin15AnchoredAtom1309 chi ∧
      Fin15AnchoredAtom1315 chi ∧
      Fin15AnchoredAtom1321 chi ∧
      Fin15AnchoredAtom1811 chi))))) ∨
      (((((Fin15AnchoredAtom4023 chi ∧
      ¬Fin15AnchoredAtom1310 chi) ∨
      (Fin15AnchoredAtom4023 chi ∧
      ¬Fin15AnchoredAtom1311 chi)) ∨
      ((Fin15AnchoredAtom4023 chi ∧
      ¬Fin15AnchoredAtom1313 chi) ∨
      (Fin15AnchoredAtom4023 chi ∧
      ¬Fin15AnchoredAtom1322 chi))) ∨
      (((Fin15AnchoredAtom4023 chi ∧
      ¬Fin15AnchoredAtom1812 chi) ∨
      (Fin15AnchoredAtom4024 chi ∧
      ¬Fin15AnchoredAtom1314 chi)) ∨
      ((Fin15AnchoredAtom4025 chi ∧
      ¬Fin15AnchoredAtom1312 chi) ∨
      (Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom1313 chi)))) ∨
      ((((Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom1314 chi) ∨
      (Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom1315 chi)) ∨
      ((Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom1325 chi) ∨
      (Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom1815 chi))) ∨
      (((¬Fin15AnchoredAtom4026 chi ∧
      Fin15AnchoredAtom1313 chi ∧
      Fin15AnchoredAtom1314 chi ∧
      Fin15AnchoredAtom1315 chi ∧
      Fin15AnchoredAtom1325 chi ∧
      Fin15AnchoredAtom1815 chi) ∨
      (Fin15AnchoredAtom4027 chi ∧
      ¬Fin15AnchoredAtom1319 chi)) ∨
      ((Fin15AnchoredAtom4027 chi ∧
      ¬Fin15AnchoredAtom1322 chi) ∨
      (¬Fin15AnchoredAtom4027 chi ∧
      Fin15AnchoredAtom1316 chi ∧
      Fin15AnchoredAtom1317 chi ∧
      Fin15AnchoredAtom1319 chi ∧
      Fin15AnchoredAtom1322 chi ∧
      Fin15AnchoredAtom1816 chi)))))))))) := by
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
                exact fin15Anchored_clause24735 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24736 chi hbad
                ·
                  exact fin15Anchored_clause24737 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24738 chi hbad
                ·
                  exact fin15Anchored_clause24739 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24740 chi hbad
                ·
                  exact fin15Anchored_clause24741 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24742 chi hbad
                ·
                  exact fin15Anchored_clause24743 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24744 chi hbad
                ·
                  exact fin15Anchored_clause24745 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24746 chi hbad
                ·
                  exact fin15Anchored_clause24747 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24748 chi hbad
                ·
                  exact fin15Anchored_clause24749 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24750 chi hbad
                ·
                  exact fin15Anchored_clause24751 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24752 chi hbad
                ·
                  exact fin15Anchored_clause24753 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24754 chi hbad
                ·
                  exact fin15Anchored_clause24755 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24756 chi hbad
                ·
                  exact fin15Anchored_clause24757 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24758 chi hbad
                ·
                  exact fin15Anchored_clause24759 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24760 chi hbad
                ·
                  exact fin15Anchored_clause24761 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24762 chi hbad
                ·
                  exact fin15Anchored_clause24763 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24764 chi hbad
                ·
                  exact fin15Anchored_clause24765 chi hbad
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
                  exact fin15Anchored_clause24766 chi hbad
                ·
                  exact fin15Anchored_clause24767 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24768 chi hbad
                ·
                  exact fin15Anchored_clause24769 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24770 chi hbad
                ·
                  exact fin15Anchored_clause24771 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24772 chi hbad
                ·
                  exact fin15Anchored_clause24773 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24774 chi hbad
                ·
                  exact fin15Anchored_clause24775 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24776 chi hbad
                ·
                  exact fin15Anchored_clause24777 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24778 chi hbad
                ·
                  exact fin15Anchored_clause24779 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24780 chi hbad
                ·
                  exact fin15Anchored_clause24781 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24782 chi hbad
                ·
                  exact fin15Anchored_clause24783 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24784 chi hbad
                ·
                  exact fin15Anchored_clause24785 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24786 chi hbad
                ·
                  exact fin15Anchored_clause24787 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24788 chi hbad
                ·
                  exact fin15Anchored_clause24789 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24790 chi hbad
                ·
                  exact fin15Anchored_clause24791 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24792 chi hbad
                ·
                  exact fin15Anchored_clause24793 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24794 chi hbad
                ·
                  exact fin15Anchored_clause24795 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24796 chi hbad
                ·
                  exact fin15Anchored_clause24797 chi hbad
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
                exact fin15Anchored_clause24798 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24799 chi hbad
                ·
                  exact fin15Anchored_clause24800 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24801 chi hbad
                ·
                  exact fin15Anchored_clause24802 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24803 chi hbad
                ·
                  exact fin15Anchored_clause24804 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24805 chi hbad
                ·
                  exact fin15Anchored_clause24806 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24807 chi hbad
                ·
                  exact fin15Anchored_clause24808 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24809 chi hbad
                ·
                  exact fin15Anchored_clause24810 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24811 chi hbad
                ·
                  exact fin15Anchored_clause24812 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24813 chi hbad
                ·
                  exact fin15Anchored_clause24814 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24815 chi hbad
                ·
                  exact fin15Anchored_clause24816 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24817 chi hbad
                ·
                  exact fin15Anchored_clause24818 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24819 chi hbad
                ·
                  exact fin15Anchored_clause24820 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24821 chi hbad
                ·
                  exact fin15Anchored_clause24822 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24823 chi hbad
                ·
                  exact fin15Anchored_clause24824 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24825 chi hbad
                ·
                  exact fin15Anchored_clause24826 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24827 chi hbad
                ·
                  exact fin15Anchored_clause24828 chi hbad
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
                  exact fin15Anchored_clause24829 chi hbad
                ·
                  exact fin15Anchored_clause24830 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24831 chi hbad
                ·
                  exact fin15Anchored_clause24832 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24833 chi hbad
                ·
                  exact fin15Anchored_clause24834 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24835 chi hbad
                ·
                  exact fin15Anchored_clause24836 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24837 chi hbad
                ·
                  exact fin15Anchored_clause24838 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24839 chi hbad
                ·
                  exact fin15Anchored_clause24840 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24841 chi hbad
                ·
                  exact fin15Anchored_clause24842 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24843 chi hbad
                ·
                  exact fin15Anchored_clause24844 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24845 chi hbad
                ·
                  exact fin15Anchored_clause24846 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24847 chi hbad
                ·
                  exact fin15Anchored_clause24848 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24849 chi hbad
                ·
                  exact fin15Anchored_clause24850 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24851 chi hbad
                ·
                  exact fin15Anchored_clause24852 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24853 chi hbad
                ·
                  exact fin15Anchored_clause24854 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24855 chi hbad
                ·
                  exact fin15Anchored_clause24856 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24857 chi hbad
                ·
                  exact fin15Anchored_clause24858 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24859 chi hbad
                ·
                  exact fin15Anchored_clause24860 chi hbad
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
                exact fin15Anchored_clause24861 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24862 chi hbad
                ·
                  exact fin15Anchored_clause24863 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24864 chi hbad
                ·
                  exact fin15Anchored_clause24865 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24866 chi hbad
                ·
                  exact fin15Anchored_clause24867 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24868 chi hbad
                ·
                  exact fin15Anchored_clause24869 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24870 chi hbad
                ·
                  exact fin15Anchored_clause24871 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24872 chi hbad
                ·
                  exact fin15Anchored_clause24873 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24874 chi hbad
                ·
                  exact fin15Anchored_clause24875 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24876 chi hbad
                ·
                  exact fin15Anchored_clause24877 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24878 chi hbad
                ·
                  exact fin15Anchored_clause24879 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24880 chi hbad
                ·
                  exact fin15Anchored_clause24881 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24882 chi hbad
                ·
                  exact fin15Anchored_clause24883 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24884 chi hbad
                ·
                  exact fin15Anchored_clause24885 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24886 chi hbad
                ·
                  exact fin15Anchored_clause24887 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24888 chi hbad
                ·
                  exact fin15Anchored_clause24889 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24890 chi hbad
                ·
                  exact fin15Anchored_clause24891 chi hbad
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
                  exact fin15Anchored_clause24892 chi hbad
                ·
                  exact fin15Anchored_clause24893 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24894 chi hbad
                ·
                  exact fin15Anchored_clause24895 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24896 chi hbad
                ·
                  exact fin15Anchored_clause24897 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24898 chi hbad
                ·
                  exact fin15Anchored_clause24899 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24900 chi hbad
                ·
                  exact fin15Anchored_clause24901 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24902 chi hbad
                ·
                  exact fin15Anchored_clause24903 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24904 chi hbad
                ·
                  exact fin15Anchored_clause24905 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24906 chi hbad
                ·
                  exact fin15Anchored_clause24907 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24908 chi hbad
                ·
                  exact fin15Anchored_clause24909 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24910 chi hbad
                ·
                  exact fin15Anchored_clause24911 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24912 chi hbad
                ·
                  exact fin15Anchored_clause24913 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24914 chi hbad
                ·
                  exact fin15Anchored_clause24915 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24916 chi hbad
                ·
                  exact fin15Anchored_clause24917 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24918 chi hbad
                ·
                  exact fin15Anchored_clause24919 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24920 chi hbad
                ·
                  exact fin15Anchored_clause24921 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24922 chi hbad
                ·
                  exact fin15Anchored_clause24923 chi hbad
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
                exact fin15Anchored_clause24924 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24925 chi hbad
                ·
                  exact fin15Anchored_clause24926 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24927 chi hbad
                ·
                  exact fin15Anchored_clause24928 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24929 chi hbad
                ·
                  exact fin15Anchored_clause24930 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24931 chi hbad
                ·
                  exact fin15Anchored_clause24932 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24933 chi hbad
                ·
                  exact fin15Anchored_clause24934 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24935 chi hbad
                ·
                  exact fin15Anchored_clause24936 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24937 chi hbad
                ·
                  exact fin15Anchored_clause24938 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24939 chi hbad
                ·
                  exact fin15Anchored_clause24940 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24941 chi hbad
                ·
                  exact fin15Anchored_clause24942 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24943 chi hbad
                ·
                  exact fin15Anchored_clause24944 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24945 chi hbad
                ·
                  exact fin15Anchored_clause24946 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24947 chi hbad
                ·
                  exact fin15Anchored_clause24948 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24949 chi hbad
                ·
                  exact fin15Anchored_clause24950 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24951 chi hbad
                ·
                  exact fin15Anchored_clause24952 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24953 chi hbad
                ·
                  exact fin15Anchored_clause24954 chi hbad
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
                  exact fin15Anchored_clause24955 chi hbad
                ·
                  exact fin15Anchored_clause24956 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24957 chi hbad
                ·
                  exact fin15Anchored_clause24958 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24959 chi hbad
                ·
                  exact fin15Anchored_clause24960 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24961 chi hbad
                ·
                  exact fin15Anchored_clause24962 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24963 chi hbad
                ·
                  exact fin15Anchored_clause24964 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24965 chi hbad
                ·
                  exact fin15Anchored_clause24966 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24967 chi hbad
                ·
                  exact fin15Anchored_clause24968 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24969 chi hbad
                ·
                  exact fin15Anchored_clause24970 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24971 chi hbad
                ·
                  exact fin15Anchored_clause24972 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24973 chi hbad
                ·
                  exact fin15Anchored_clause24974 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24975 chi hbad
                ·
                  exact fin15Anchored_clause24976 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24977 chi hbad
                ·
                  exact fin15Anchored_clause24978 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24979 chi hbad
                ·
                  exact fin15Anchored_clause24980 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24981 chi hbad
                ·
                  exact fin15Anchored_clause24982 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24983 chi hbad
                ·
                  exact fin15Anchored_clause24984 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause24985 chi hbad
                ·
                  exact fin15Anchored_clause24986 chi hbad

end ErdosSzekeres

end
