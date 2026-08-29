module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk095
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk096

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 124. -/

theorem predecessorHalfFin13_rejectSemanticSegment124
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((¬PredecessorHalfFin13Atom1204 chi ∧
      ¬PredecessorHalfFin13Atom1205 chi ∧
      ¬PredecessorHalfFin13Atom1206 chi ∧
      ¬PredecessorHalfFin13Atom1216 chi ∧
      ¬PredecessorHalfFin13Atom1217 chi ∧
      ¬PredecessorHalfFin13Atom1221 chi ∧
      ¬PredecessorHalfFin13Atom1237 chi ∧
      ¬PredecessorHalfFin13Atom1238 chi ∧
      ¬PredecessorHalfFin13Atom1242 chi ∧
      ¬PredecessorHalfFin13Atom1267 chi ∧
      ¬PredecessorHalfFin13Atom1377 chi ∧
      ¬PredecessorHalfFin13Atom1378 chi ∧
      ¬PredecessorHalfFin13Atom1382 chi ∧
      ¬PredecessorHalfFin13Atom1407 chi ∧
      ¬PredecessorHalfFin13Atom1442 chi ∧
      ¬PredecessorHalfFin13Atom1917 chi ∧
      ¬PredecessorHalfFin13Atom1918 chi ∧
      ¬PredecessorHalfFin13Atom1922 chi ∧
      ¬PredecessorHalfFin13Atom1947 chi ∧
      ¬PredecessorHalfFin13Atom1982 chi ∧
      ¬PredecessorHalfFin13Atom2178 chi) ∨
      ((¬PredecessorHalfFin13Atom1204 chi ∧
      ¬PredecessorHalfFin13Atom1205 chi ∧
      ¬PredecessorHalfFin13Atom1207 chi ∧
      ¬PredecessorHalfFin13Atom1216 chi ∧
      ¬PredecessorHalfFin13Atom1218 chi ∧
      ¬PredecessorHalfFin13Atom1222 chi ∧
      ¬PredecessorHalfFin13Atom1237 chi ∧
      ¬PredecessorHalfFin13Atom1239 chi ∧
      ¬PredecessorHalfFin13Atom1243 chi ∧
      ¬PredecessorHalfFin13Atom1268 chi ∧
      ¬PredecessorHalfFin13Atom1377 chi ∧
      ¬PredecessorHalfFin13Atom1379 chi ∧
      ¬PredecessorHalfFin13Atom1383 chi ∧
      ¬PredecessorHalfFin13Atom1408 chi ∧
      ¬PredecessorHalfFin13Atom1443 chi ∧
      ¬PredecessorHalfFin13Atom1917 chi ∧
      ¬PredecessorHalfFin13Atom1919 chi ∧
      ¬PredecessorHalfFin13Atom1923 chi ∧
      ¬PredecessorHalfFin13Atom1948 chi ∧
      ¬PredecessorHalfFin13Atom1983 chi ∧
      ¬PredecessorHalfFin13Atom2179 chi) ∨
      (¬PredecessorHalfFin13Atom1204 chi ∧
      ¬PredecessorHalfFin13Atom1205 chi ∧
      ¬PredecessorHalfFin13Atom1209 chi ∧
      ¬PredecessorHalfFin13Atom1216 chi ∧
      ¬PredecessorHalfFin13Atom1220 chi ∧
      ¬PredecessorHalfFin13Atom1224 chi ∧
      ¬PredecessorHalfFin13Atom1237 chi ∧
      ¬PredecessorHalfFin13Atom1241 chi ∧
      ¬PredecessorHalfFin13Atom1245 chi ∧
      ¬PredecessorHalfFin13Atom1270 chi ∧
      ¬PredecessorHalfFin13Atom1377 chi ∧
      ¬PredecessorHalfFin13Atom1381 chi ∧
      ¬PredecessorHalfFin13Atom1385 chi ∧
      ¬PredecessorHalfFin13Atom1410 chi ∧
      ¬PredecessorHalfFin13Atom1445 chi ∧
      ¬PredecessorHalfFin13Atom1917 chi ∧
      ¬PredecessorHalfFin13Atom1921 chi ∧
      ¬PredecessorHalfFin13Atom1925 chi ∧
      ¬PredecessorHalfFin13Atom1950 chi ∧
      ¬PredecessorHalfFin13Atom1985 chi ∧
      ¬PredecessorHalfFin13Atom2181 chi))) ∨
      ((¬PredecessorHalfFin13Atom1204 chi ∧
      ¬PredecessorHalfFin13Atom1206 chi ∧
      ¬PredecessorHalfFin13Atom1207 chi ∧
      ¬PredecessorHalfFin13Atom1217 chi ∧
      ¬PredecessorHalfFin13Atom1218 chi ∧
      ¬PredecessorHalfFin13Atom1225 chi ∧
      ¬PredecessorHalfFin13Atom1238 chi ∧
      ¬PredecessorHalfFin13Atom1239 chi ∧
      ¬PredecessorHalfFin13Atom1246 chi ∧
      ¬PredecessorHalfFin13Atom1271 chi ∧
      ¬PredecessorHalfFin13Atom1378 chi ∧
      ¬PredecessorHalfFin13Atom1379 chi ∧
      ¬PredecessorHalfFin13Atom1386 chi ∧
      ¬PredecessorHalfFin13Atom1411 chi ∧
      ¬PredecessorHalfFin13Atom1446 chi ∧
      ¬PredecessorHalfFin13Atom1918 chi ∧
      ¬PredecessorHalfFin13Atom1919 chi ∧
      ¬PredecessorHalfFin13Atom1926 chi ∧
      ¬PredecessorHalfFin13Atom1951 chi ∧
      ¬PredecessorHalfFin13Atom1986 chi ∧
      ¬PredecessorHalfFin13Atom2182 chi) ∨
      ((¬PredecessorHalfFin13Atom1204 chi ∧
      ¬PredecessorHalfFin13Atom1206 chi ∧
      ¬PredecessorHalfFin13Atom1209 chi ∧
      ¬PredecessorHalfFin13Atom1217 chi ∧
      ¬PredecessorHalfFin13Atom1220 chi ∧
      ¬PredecessorHalfFin13Atom1227 chi ∧
      ¬PredecessorHalfFin13Atom1238 chi ∧
      ¬PredecessorHalfFin13Atom1241 chi ∧
      ¬PredecessorHalfFin13Atom1248 chi ∧
      ¬PredecessorHalfFin13Atom1273 chi ∧
      ¬PredecessorHalfFin13Atom1378 chi ∧
      ¬PredecessorHalfFin13Atom1381 chi ∧
      ¬PredecessorHalfFin13Atom1388 chi ∧
      ¬PredecessorHalfFin13Atom1413 chi ∧
      ¬PredecessorHalfFin13Atom1448 chi ∧
      ¬PredecessorHalfFin13Atom1918 chi ∧
      ¬PredecessorHalfFin13Atom1921 chi ∧
      ¬PredecessorHalfFin13Atom1928 chi ∧
      ¬PredecessorHalfFin13Atom1953 chi ∧
      ¬PredecessorHalfFin13Atom1988 chi ∧
      ¬PredecessorHalfFin13Atom2184 chi) ∨
      (¬PredecessorHalfFin13Atom1204 chi ∧
      ¬PredecessorHalfFin13Atom1207 chi ∧
      ¬PredecessorHalfFin13Atom1209 chi ∧
      ¬PredecessorHalfFin13Atom1218 chi ∧
      ¬PredecessorHalfFin13Atom1220 chi ∧
      ¬PredecessorHalfFin13Atom1229 chi ∧
      ¬PredecessorHalfFin13Atom1239 chi ∧
      ¬PredecessorHalfFin13Atom1241 chi ∧
      ¬PredecessorHalfFin13Atom1250 chi ∧
      ¬PredecessorHalfFin13Atom1275 chi ∧
      ¬PredecessorHalfFin13Atom1379 chi ∧
      ¬PredecessorHalfFin13Atom1381 chi ∧
      ¬PredecessorHalfFin13Atom1390 chi ∧
      ¬PredecessorHalfFin13Atom1415 chi ∧
      ¬PredecessorHalfFin13Atom1450 chi ∧
      ¬PredecessorHalfFin13Atom1919 chi ∧
      ¬PredecessorHalfFin13Atom1921 chi ∧
      ¬PredecessorHalfFin13Atom1930 chi ∧
      ¬PredecessorHalfFin13Atom1955 chi ∧
      ¬PredecessorHalfFin13Atom1990 chi ∧
      ¬PredecessorHalfFin13Atom2186 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1205 chi ∧
      ¬PredecessorHalfFin13Atom1206 chi ∧
      ¬PredecessorHalfFin13Atom1207 chi ∧
      ¬PredecessorHalfFin13Atom1221 chi ∧
      ¬PredecessorHalfFin13Atom1222 chi ∧
      ¬PredecessorHalfFin13Atom1225 chi ∧
      ¬PredecessorHalfFin13Atom1242 chi ∧
      ¬PredecessorHalfFin13Atom1243 chi ∧
      ¬PredecessorHalfFin13Atom1246 chi ∧
      ¬PredecessorHalfFin13Atom1277 chi ∧
      ¬PredecessorHalfFin13Atom1382 chi ∧
      ¬PredecessorHalfFin13Atom1383 chi ∧
      ¬PredecessorHalfFin13Atom1386 chi ∧
      ¬PredecessorHalfFin13Atom1417 chi ∧
      ¬PredecessorHalfFin13Atom1452 chi ∧
      ¬PredecessorHalfFin13Atom1922 chi ∧
      ¬PredecessorHalfFin13Atom1923 chi ∧
      ¬PredecessorHalfFin13Atom1926 chi ∧
      ¬PredecessorHalfFin13Atom1957 chi ∧
      ¬PredecessorHalfFin13Atom1992 chi ∧
      ¬PredecessorHalfFin13Atom2188 chi) ∨
      ((¬PredecessorHalfFin13Atom1205 chi ∧
      ¬PredecessorHalfFin13Atom1206 chi ∧
      ¬PredecessorHalfFin13Atom1209 chi ∧
      ¬PredecessorHalfFin13Atom1221 chi ∧
      ¬PredecessorHalfFin13Atom1224 chi ∧
      ¬PredecessorHalfFin13Atom1227 chi ∧
      ¬PredecessorHalfFin13Atom1242 chi ∧
      ¬PredecessorHalfFin13Atom1245 chi ∧
      ¬PredecessorHalfFin13Atom1248 chi ∧
      ¬PredecessorHalfFin13Atom1279 chi ∧
      ¬PredecessorHalfFin13Atom1382 chi ∧
      ¬PredecessorHalfFin13Atom1385 chi ∧
      ¬PredecessorHalfFin13Atom1388 chi ∧
      ¬PredecessorHalfFin13Atom1419 chi ∧
      ¬PredecessorHalfFin13Atom1454 chi ∧
      ¬PredecessorHalfFin13Atom1922 chi ∧
      ¬PredecessorHalfFin13Atom1925 chi ∧
      ¬PredecessorHalfFin13Atom1928 chi ∧
      ¬PredecessorHalfFin13Atom1959 chi ∧
      ¬PredecessorHalfFin13Atom1994 chi ∧
      ¬PredecessorHalfFin13Atom2190 chi) ∨
      (¬PredecessorHalfFin13Atom1205 chi ∧
      ¬PredecessorHalfFin13Atom1207 chi ∧
      ¬PredecessorHalfFin13Atom1209 chi ∧
      ¬PredecessorHalfFin13Atom1222 chi ∧
      ¬PredecessorHalfFin13Atom1224 chi ∧
      ¬PredecessorHalfFin13Atom1229 chi ∧
      ¬PredecessorHalfFin13Atom1243 chi ∧
      ¬PredecessorHalfFin13Atom1245 chi ∧
      ¬PredecessorHalfFin13Atom1250 chi ∧
      ¬PredecessorHalfFin13Atom1281 chi ∧
      ¬PredecessorHalfFin13Atom1383 chi ∧
      ¬PredecessorHalfFin13Atom1385 chi ∧
      ¬PredecessorHalfFin13Atom1390 chi ∧
      ¬PredecessorHalfFin13Atom1421 chi ∧
      ¬PredecessorHalfFin13Atom1456 chi ∧
      ¬PredecessorHalfFin13Atom1923 chi ∧
      ¬PredecessorHalfFin13Atom1925 chi ∧
      ¬PredecessorHalfFin13Atom1930 chi ∧
      ¬PredecessorHalfFin13Atom1961 chi ∧
      ¬PredecessorHalfFin13Atom1996 chi ∧
      ¬PredecessorHalfFin13Atom2192 chi))) ∨
      ((¬PredecessorHalfFin13Atom1206 chi ∧
      ¬PredecessorHalfFin13Atom1207 chi ∧
      ¬PredecessorHalfFin13Atom1209 chi ∧
      ¬PredecessorHalfFin13Atom1225 chi ∧
      ¬PredecessorHalfFin13Atom1227 chi ∧
      ¬PredecessorHalfFin13Atom1229 chi ∧
      ¬PredecessorHalfFin13Atom1246 chi ∧
      ¬PredecessorHalfFin13Atom1248 chi ∧
      ¬PredecessorHalfFin13Atom1250 chi ∧
      ¬PredecessorHalfFin13Atom1284 chi ∧
      ¬PredecessorHalfFin13Atom1386 chi ∧
      ¬PredecessorHalfFin13Atom1388 chi ∧
      ¬PredecessorHalfFin13Atom1390 chi ∧
      ¬PredecessorHalfFin13Atom1424 chi ∧
      ¬PredecessorHalfFin13Atom1459 chi ∧
      ¬PredecessorHalfFin13Atom1926 chi ∧
      ¬PredecessorHalfFin13Atom1928 chi ∧
      ¬PredecessorHalfFin13Atom1930 chi ∧
      ¬PredecessorHalfFin13Atom1964 chi ∧
      ¬PredecessorHalfFin13Atom1999 chi ∧
      ¬PredecessorHalfFin13Atom2195 chi) ∨
      ((¬PredecessorHalfFin13Atom1210 chi ∧
      ¬PredecessorHalfFin13Atom1211 chi ∧
      ¬PredecessorHalfFin13Atom1212 chi ∧
      ¬PredecessorHalfFin13Atom1216 chi ∧
      ¬PredecessorHalfFin13Atom1217 chi ∧
      ¬PredecessorHalfFin13Atom1221 chi ∧
      ¬PredecessorHalfFin13Atom1252 chi ∧
      ¬PredecessorHalfFin13Atom1253 chi ∧
      ¬PredecessorHalfFin13Atom1257 chi ∧
      ¬PredecessorHalfFin13Atom1267 chi ∧
      ¬PredecessorHalfFin13Atom1392 chi ∧
      ¬PredecessorHalfFin13Atom1393 chi ∧
      ¬PredecessorHalfFin13Atom1397 chi ∧
      ¬PredecessorHalfFin13Atom1407 chi ∧
      ¬PredecessorHalfFin13Atom1462 chi ∧
      ¬PredecessorHalfFin13Atom1932 chi ∧
      ¬PredecessorHalfFin13Atom1933 chi ∧
      ¬PredecessorHalfFin13Atom1937 chi ∧
      ¬PredecessorHalfFin13Atom1947 chi ∧
      ¬PredecessorHalfFin13Atom2002 chi ∧
      ¬PredecessorHalfFin13Atom2198 chi) ∨
      (¬PredecessorHalfFin13Atom1210 chi ∧
      ¬PredecessorHalfFin13Atom1211 chi ∧
      ¬PredecessorHalfFin13Atom1213 chi ∧
      ¬PredecessorHalfFin13Atom1216 chi ∧
      ¬PredecessorHalfFin13Atom1218 chi ∧
      ¬PredecessorHalfFin13Atom1222 chi ∧
      ¬PredecessorHalfFin13Atom1252 chi ∧
      ¬PredecessorHalfFin13Atom1254 chi ∧
      ¬PredecessorHalfFin13Atom1258 chi ∧
      ¬PredecessorHalfFin13Atom1268 chi ∧
      ¬PredecessorHalfFin13Atom1392 chi ∧
      ¬PredecessorHalfFin13Atom1394 chi ∧
      ¬PredecessorHalfFin13Atom1398 chi ∧
      ¬PredecessorHalfFin13Atom1408 chi ∧
      ¬PredecessorHalfFin13Atom1463 chi ∧
      ¬PredecessorHalfFin13Atom1932 chi ∧
      ¬PredecessorHalfFin13Atom1934 chi ∧
      ¬PredecessorHalfFin13Atom1938 chi ∧
      ¬PredecessorHalfFin13Atom1948 chi ∧
      ¬PredecessorHalfFin13Atom2003 chi ∧
      ¬PredecessorHalfFin13Atom2199 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom1210 chi ∧
      ¬PredecessorHalfFin13Atom1211 chi ∧
      ¬PredecessorHalfFin13Atom1215 chi ∧
      ¬PredecessorHalfFin13Atom1216 chi ∧
      ¬PredecessorHalfFin13Atom1220 chi ∧
      ¬PredecessorHalfFin13Atom1224 chi ∧
      ¬PredecessorHalfFin13Atom1252 chi ∧
      ¬PredecessorHalfFin13Atom1256 chi ∧
      ¬PredecessorHalfFin13Atom1260 chi ∧
      ¬PredecessorHalfFin13Atom1270 chi ∧
      ¬PredecessorHalfFin13Atom1392 chi ∧
      ¬PredecessorHalfFin13Atom1396 chi ∧
      ¬PredecessorHalfFin13Atom1400 chi ∧
      ¬PredecessorHalfFin13Atom1410 chi ∧
      ¬PredecessorHalfFin13Atom1465 chi ∧
      ¬PredecessorHalfFin13Atom1932 chi ∧
      ¬PredecessorHalfFin13Atom1936 chi ∧
      ¬PredecessorHalfFin13Atom1940 chi ∧
      ¬PredecessorHalfFin13Atom1950 chi ∧
      ¬PredecessorHalfFin13Atom2005 chi ∧
      ¬PredecessorHalfFin13Atom2201 chi) ∨
      ((¬PredecessorHalfFin13Atom1210 chi ∧
      ¬PredecessorHalfFin13Atom1212 chi ∧
      ¬PredecessorHalfFin13Atom1213 chi ∧
      ¬PredecessorHalfFin13Atom1217 chi ∧
      ¬PredecessorHalfFin13Atom1218 chi ∧
      ¬PredecessorHalfFin13Atom1225 chi ∧
      ¬PredecessorHalfFin13Atom1253 chi ∧
      ¬PredecessorHalfFin13Atom1254 chi ∧
      ¬PredecessorHalfFin13Atom1261 chi ∧
      ¬PredecessorHalfFin13Atom1271 chi ∧
      ¬PredecessorHalfFin13Atom1393 chi ∧
      ¬PredecessorHalfFin13Atom1394 chi ∧
      ¬PredecessorHalfFin13Atom1401 chi ∧
      ¬PredecessorHalfFin13Atom1411 chi ∧
      ¬PredecessorHalfFin13Atom1466 chi ∧
      ¬PredecessorHalfFin13Atom1933 chi ∧
      ¬PredecessorHalfFin13Atom1934 chi ∧
      ¬PredecessorHalfFin13Atom1941 chi ∧
      ¬PredecessorHalfFin13Atom1951 chi ∧
      ¬PredecessorHalfFin13Atom2006 chi ∧
      ¬PredecessorHalfFin13Atom2202 chi) ∨
      (¬PredecessorHalfFin13Atom1210 chi ∧
      ¬PredecessorHalfFin13Atom1212 chi ∧
      ¬PredecessorHalfFin13Atom1215 chi ∧
      ¬PredecessorHalfFin13Atom1217 chi ∧
      ¬PredecessorHalfFin13Atom1220 chi ∧
      ¬PredecessorHalfFin13Atom1227 chi ∧
      ¬PredecessorHalfFin13Atom1253 chi ∧
      ¬PredecessorHalfFin13Atom1256 chi ∧
      ¬PredecessorHalfFin13Atom1263 chi ∧
      ¬PredecessorHalfFin13Atom1273 chi ∧
      ¬PredecessorHalfFin13Atom1393 chi ∧
      ¬PredecessorHalfFin13Atom1396 chi ∧
      ¬PredecessorHalfFin13Atom1403 chi ∧
      ¬PredecessorHalfFin13Atom1413 chi ∧
      ¬PredecessorHalfFin13Atom1468 chi ∧
      ¬PredecessorHalfFin13Atom1933 chi ∧
      ¬PredecessorHalfFin13Atom1936 chi ∧
      ¬PredecessorHalfFin13Atom1943 chi ∧
      ¬PredecessorHalfFin13Atom1953 chi ∧
      ¬PredecessorHalfFin13Atom2008 chi ∧
      ¬PredecessorHalfFin13Atom2204 chi))) ∨
      ((¬PredecessorHalfFin13Atom1210 chi ∧
      ¬PredecessorHalfFin13Atom1213 chi ∧
      ¬PredecessorHalfFin13Atom1215 chi ∧
      ¬PredecessorHalfFin13Atom1218 chi ∧
      ¬PredecessorHalfFin13Atom1220 chi ∧
      ¬PredecessorHalfFin13Atom1229 chi ∧
      ¬PredecessorHalfFin13Atom1254 chi ∧
      ¬PredecessorHalfFin13Atom1256 chi ∧
      ¬PredecessorHalfFin13Atom1265 chi ∧
      ¬PredecessorHalfFin13Atom1275 chi ∧
      ¬PredecessorHalfFin13Atom1394 chi ∧
      ¬PredecessorHalfFin13Atom1396 chi ∧
      ¬PredecessorHalfFin13Atom1405 chi ∧
      ¬PredecessorHalfFin13Atom1415 chi ∧
      ¬PredecessorHalfFin13Atom1470 chi ∧
      ¬PredecessorHalfFin13Atom1934 chi ∧
      ¬PredecessorHalfFin13Atom1936 chi ∧
      ¬PredecessorHalfFin13Atom1945 chi ∧
      ¬PredecessorHalfFin13Atom1955 chi ∧
      ¬PredecessorHalfFin13Atom2010 chi ∧
      ¬PredecessorHalfFin13Atom2206 chi) ∨
      ((¬PredecessorHalfFin13Atom1211 chi ∧
      ¬PredecessorHalfFin13Atom1212 chi ∧
      ¬PredecessorHalfFin13Atom1213 chi ∧
      ¬PredecessorHalfFin13Atom1221 chi ∧
      ¬PredecessorHalfFin13Atom1222 chi ∧
      ¬PredecessorHalfFin13Atom1225 chi ∧
      ¬PredecessorHalfFin13Atom1257 chi ∧
      ¬PredecessorHalfFin13Atom1258 chi ∧
      ¬PredecessorHalfFin13Atom1261 chi ∧
      ¬PredecessorHalfFin13Atom1277 chi ∧
      ¬PredecessorHalfFin13Atom1397 chi ∧
      ¬PredecessorHalfFin13Atom1398 chi ∧
      ¬PredecessorHalfFin13Atom1401 chi ∧
      ¬PredecessorHalfFin13Atom1417 chi ∧
      ¬PredecessorHalfFin13Atom1472 chi ∧
      ¬PredecessorHalfFin13Atom1937 chi ∧
      ¬PredecessorHalfFin13Atom1938 chi ∧
      ¬PredecessorHalfFin13Atom1941 chi ∧
      ¬PredecessorHalfFin13Atom1957 chi ∧
      ¬PredecessorHalfFin13Atom2012 chi ∧
      ¬PredecessorHalfFin13Atom2208 chi) ∨
      (¬PredecessorHalfFin13Atom1211 chi ∧
      ¬PredecessorHalfFin13Atom1212 chi ∧
      ¬PredecessorHalfFin13Atom1215 chi ∧
      ¬PredecessorHalfFin13Atom1221 chi ∧
      ¬PredecessorHalfFin13Atom1224 chi ∧
      ¬PredecessorHalfFin13Atom1227 chi ∧
      ¬PredecessorHalfFin13Atom1257 chi ∧
      ¬PredecessorHalfFin13Atom1260 chi ∧
      ¬PredecessorHalfFin13Atom1263 chi ∧
      ¬PredecessorHalfFin13Atom1279 chi ∧
      ¬PredecessorHalfFin13Atom1397 chi ∧
      ¬PredecessorHalfFin13Atom1400 chi ∧
      ¬PredecessorHalfFin13Atom1403 chi ∧
      ¬PredecessorHalfFin13Atom1419 chi ∧
      ¬PredecessorHalfFin13Atom1474 chi ∧
      ¬PredecessorHalfFin13Atom1937 chi ∧
      ¬PredecessorHalfFin13Atom1940 chi ∧
      ¬PredecessorHalfFin13Atom1943 chi ∧
      ¬PredecessorHalfFin13Atom1959 chi ∧
      ¬PredecessorHalfFin13Atom2014 chi ∧
      ¬PredecessorHalfFin13Atom2210 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1211 chi ∧
      ¬PredecessorHalfFin13Atom1213 chi ∧
      ¬PredecessorHalfFin13Atom1215 chi ∧
      ¬PredecessorHalfFin13Atom1222 chi ∧
      ¬PredecessorHalfFin13Atom1224 chi ∧
      ¬PredecessorHalfFin13Atom1229 chi ∧
      ¬PredecessorHalfFin13Atom1258 chi ∧
      ¬PredecessorHalfFin13Atom1260 chi ∧
      ¬PredecessorHalfFin13Atom1265 chi ∧
      ¬PredecessorHalfFin13Atom1281 chi ∧
      ¬PredecessorHalfFin13Atom1398 chi ∧
      ¬PredecessorHalfFin13Atom1400 chi ∧
      ¬PredecessorHalfFin13Atom1405 chi ∧
      ¬PredecessorHalfFin13Atom1421 chi ∧
      ¬PredecessorHalfFin13Atom1476 chi ∧
      ¬PredecessorHalfFin13Atom1938 chi ∧
      ¬PredecessorHalfFin13Atom1940 chi ∧
      ¬PredecessorHalfFin13Atom1945 chi ∧
      ¬PredecessorHalfFin13Atom1961 chi ∧
      ¬PredecessorHalfFin13Atom2016 chi ∧
      ¬PredecessorHalfFin13Atom2212 chi) ∨
      ((¬PredecessorHalfFin13Atom1212 chi ∧
      ¬PredecessorHalfFin13Atom1213 chi ∧
      ¬PredecessorHalfFin13Atom1215 chi ∧
      ¬PredecessorHalfFin13Atom1225 chi ∧
      ¬PredecessorHalfFin13Atom1227 chi ∧
      ¬PredecessorHalfFin13Atom1229 chi ∧
      ¬PredecessorHalfFin13Atom1261 chi ∧
      ¬PredecessorHalfFin13Atom1263 chi ∧
      ¬PredecessorHalfFin13Atom1265 chi ∧
      ¬PredecessorHalfFin13Atom1284 chi ∧
      ¬PredecessorHalfFin13Atom1401 chi ∧
      ¬PredecessorHalfFin13Atom1403 chi ∧
      ¬PredecessorHalfFin13Atom1405 chi ∧
      ¬PredecessorHalfFin13Atom1424 chi ∧
      ¬PredecessorHalfFin13Atom1479 chi ∧
      ¬PredecessorHalfFin13Atom1941 chi ∧
      ¬PredecessorHalfFin13Atom1943 chi ∧
      ¬PredecessorHalfFin13Atom1945 chi ∧
      ¬PredecessorHalfFin13Atom1964 chi ∧
      ¬PredecessorHalfFin13Atom2019 chi ∧
      ¬PredecessorHalfFin13Atom2215 chi) ∨
      (¬PredecessorHalfFin13Atom1216 chi ∧
      ¬PredecessorHalfFin13Atom1217 chi ∧
      ¬PredecessorHalfFin13Atom1218 chi ∧
      ¬PredecessorHalfFin13Atom1221 chi ∧
      ¬PredecessorHalfFin13Atom1222 chi ∧
      ¬PredecessorHalfFin13Atom1225 chi ∧
      ¬PredecessorHalfFin13Atom1267 chi ∧
      ¬PredecessorHalfFin13Atom1268 chi ∧
      ¬PredecessorHalfFin13Atom1271 chi ∧
      ¬PredecessorHalfFin13Atom1277 chi ∧
      ¬PredecessorHalfFin13Atom1407 chi ∧
      ¬PredecessorHalfFin13Atom1408 chi ∧
      ¬PredecessorHalfFin13Atom1411 chi ∧
      ¬PredecessorHalfFin13Atom1417 chi ∧
      ¬PredecessorHalfFin13Atom1482 chi ∧
      ¬PredecessorHalfFin13Atom1947 chi ∧
      ¬PredecessorHalfFin13Atom1948 chi ∧
      ¬PredecessorHalfFin13Atom1951 chi ∧
      ¬PredecessorHalfFin13Atom1957 chi ∧
      ¬PredecessorHalfFin13Atom2022 chi ∧
      ¬PredecessorHalfFin13Atom2218 chi))) ∨
      ((¬PredecessorHalfFin13Atom1216 chi ∧
      ¬PredecessorHalfFin13Atom1217 chi ∧
      ¬PredecessorHalfFin13Atom1220 chi ∧
      ¬PredecessorHalfFin13Atom1221 chi ∧
      ¬PredecessorHalfFin13Atom1224 chi ∧
      ¬PredecessorHalfFin13Atom1227 chi ∧
      ¬PredecessorHalfFin13Atom1267 chi ∧
      ¬PredecessorHalfFin13Atom1270 chi ∧
      ¬PredecessorHalfFin13Atom1273 chi ∧
      ¬PredecessorHalfFin13Atom1279 chi ∧
      ¬PredecessorHalfFin13Atom1407 chi ∧
      ¬PredecessorHalfFin13Atom1410 chi ∧
      ¬PredecessorHalfFin13Atom1413 chi ∧
      ¬PredecessorHalfFin13Atom1419 chi ∧
      ¬PredecessorHalfFin13Atom1484 chi ∧
      ¬PredecessorHalfFin13Atom1947 chi ∧
      ¬PredecessorHalfFin13Atom1950 chi ∧
      ¬PredecessorHalfFin13Atom1953 chi ∧
      ¬PredecessorHalfFin13Atom1959 chi ∧
      ¬PredecessorHalfFin13Atom2024 chi ∧
      ¬PredecessorHalfFin13Atom2220 chi) ∨
      ((¬PredecessorHalfFin13Atom1216 chi ∧
      ¬PredecessorHalfFin13Atom1218 chi ∧
      ¬PredecessorHalfFin13Atom1220 chi ∧
      ¬PredecessorHalfFin13Atom1222 chi ∧
      ¬PredecessorHalfFin13Atom1224 chi ∧
      ¬PredecessorHalfFin13Atom1229 chi ∧
      ¬PredecessorHalfFin13Atom1268 chi ∧
      ¬PredecessorHalfFin13Atom1270 chi ∧
      ¬PredecessorHalfFin13Atom1275 chi ∧
      ¬PredecessorHalfFin13Atom1281 chi ∧
      ¬PredecessorHalfFin13Atom1408 chi ∧
      ¬PredecessorHalfFin13Atom1410 chi ∧
      ¬PredecessorHalfFin13Atom1415 chi ∧
      ¬PredecessorHalfFin13Atom1421 chi ∧
      ¬PredecessorHalfFin13Atom1486 chi ∧
      ¬PredecessorHalfFin13Atom1948 chi ∧
      ¬PredecessorHalfFin13Atom1950 chi ∧
      ¬PredecessorHalfFin13Atom1955 chi ∧
      ¬PredecessorHalfFin13Atom1961 chi ∧
      ¬PredecessorHalfFin13Atom2026 chi ∧
      ¬PredecessorHalfFin13Atom2222 chi) ∨
      (¬PredecessorHalfFin13Atom1217 chi ∧
      ¬PredecessorHalfFin13Atom1218 chi ∧
      ¬PredecessorHalfFin13Atom1220 chi ∧
      ¬PredecessorHalfFin13Atom1225 chi ∧
      ¬PredecessorHalfFin13Atom1227 chi ∧
      ¬PredecessorHalfFin13Atom1229 chi ∧
      ¬PredecessorHalfFin13Atom1271 chi ∧
      ¬PredecessorHalfFin13Atom1273 chi ∧
      ¬PredecessorHalfFin13Atom1275 chi ∧
      ¬PredecessorHalfFin13Atom1284 chi ∧
      ¬PredecessorHalfFin13Atom1411 chi ∧
      ¬PredecessorHalfFin13Atom1413 chi ∧
      ¬PredecessorHalfFin13Atom1415 chi ∧
      ¬PredecessorHalfFin13Atom1424 chi ∧
      ¬PredecessorHalfFin13Atom1489 chi ∧
      ¬PredecessorHalfFin13Atom1951 chi ∧
      ¬PredecessorHalfFin13Atom1953 chi ∧
      ¬PredecessorHalfFin13Atom1955 chi ∧
      ¬PredecessorHalfFin13Atom1964 chi ∧
      ¬PredecessorHalfFin13Atom2029 chi ∧
      ¬PredecessorHalfFin13Atom2225 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom1221 chi ∧
      ¬PredecessorHalfFin13Atom1222 chi ∧
      ¬PredecessorHalfFin13Atom1224 chi ∧
      ¬PredecessorHalfFin13Atom1225 chi ∧
      ¬PredecessorHalfFin13Atom1227 chi ∧
      ¬PredecessorHalfFin13Atom1229 chi ∧
      ¬PredecessorHalfFin13Atom1277 chi ∧
      ¬PredecessorHalfFin13Atom1279 chi ∧
      ¬PredecessorHalfFin13Atom1281 chi ∧
      ¬PredecessorHalfFin13Atom1284 chi ∧
      ¬PredecessorHalfFin13Atom1417 chi ∧
      ¬PredecessorHalfFin13Atom1419 chi ∧
      ¬PredecessorHalfFin13Atom1421 chi ∧
      ¬PredecessorHalfFin13Atom1424 chi ∧
      ¬PredecessorHalfFin13Atom1493 chi ∧
      ¬PredecessorHalfFin13Atom1957 chi ∧
      ¬PredecessorHalfFin13Atom1959 chi ∧
      ¬PredecessorHalfFin13Atom1961 chi ∧
      ¬PredecessorHalfFin13Atom1964 chi ∧
      ¬PredecessorHalfFin13Atom2033 chi ∧
      ¬PredecessorHalfFin13Atom2229 chi) ∨
      ((¬PredecessorHalfFin13Atom1231 chi ∧
      ¬PredecessorHalfFin13Atom1232 chi ∧
      ¬PredecessorHalfFin13Atom1233 chi ∧
      ¬PredecessorHalfFin13Atom1237 chi ∧
      ¬PredecessorHalfFin13Atom1238 chi ∧
      ¬PredecessorHalfFin13Atom1242 chi ∧
      ¬PredecessorHalfFin13Atom1252 chi ∧
      ¬PredecessorHalfFin13Atom1253 chi ∧
      ¬PredecessorHalfFin13Atom1257 chi ∧
      ¬PredecessorHalfFin13Atom1267 chi ∧
      ¬PredecessorHalfFin13Atom1427 chi ∧
      ¬PredecessorHalfFin13Atom1428 chi ∧
      ¬PredecessorHalfFin13Atom1432 chi ∧
      ¬PredecessorHalfFin13Atom1442 chi ∧
      ¬PredecessorHalfFin13Atom1462 chi ∧
      ¬PredecessorHalfFin13Atom1967 chi ∧
      ¬PredecessorHalfFin13Atom1968 chi ∧
      ¬PredecessorHalfFin13Atom1972 chi ∧
      ¬PredecessorHalfFin13Atom1982 chi ∧
      ¬PredecessorHalfFin13Atom2002 chi ∧
      ¬PredecessorHalfFin13Atom2233 chi) ∨
      (¬PredecessorHalfFin13Atom1231 chi ∧
      ¬PredecessorHalfFin13Atom1232 chi ∧
      ¬PredecessorHalfFin13Atom1234 chi ∧
      ¬PredecessorHalfFin13Atom1237 chi ∧
      ¬PredecessorHalfFin13Atom1239 chi ∧
      ¬PredecessorHalfFin13Atom1243 chi ∧
      ¬PredecessorHalfFin13Atom1252 chi ∧
      ¬PredecessorHalfFin13Atom1254 chi ∧
      ¬PredecessorHalfFin13Atom1258 chi ∧
      ¬PredecessorHalfFin13Atom1268 chi ∧
      ¬PredecessorHalfFin13Atom1427 chi ∧
      ¬PredecessorHalfFin13Atom1429 chi ∧
      ¬PredecessorHalfFin13Atom1433 chi ∧
      ¬PredecessorHalfFin13Atom1443 chi ∧
      ¬PredecessorHalfFin13Atom1463 chi ∧
      ¬PredecessorHalfFin13Atom1967 chi ∧
      ¬PredecessorHalfFin13Atom1969 chi ∧
      ¬PredecessorHalfFin13Atom1973 chi ∧
      ¬PredecessorHalfFin13Atom1983 chi ∧
      ¬PredecessorHalfFin13Atom2003 chi ∧
      ¬PredecessorHalfFin13Atom2234 chi))) ∨
      ((¬PredecessorHalfFin13Atom1231 chi ∧
      ¬PredecessorHalfFin13Atom1232 chi ∧
      ¬PredecessorHalfFin13Atom1236 chi ∧
      ¬PredecessorHalfFin13Atom1237 chi ∧
      ¬PredecessorHalfFin13Atom1241 chi ∧
      ¬PredecessorHalfFin13Atom1245 chi ∧
      ¬PredecessorHalfFin13Atom1252 chi ∧
      ¬PredecessorHalfFin13Atom1256 chi ∧
      ¬PredecessorHalfFin13Atom1260 chi ∧
      ¬PredecessorHalfFin13Atom1270 chi ∧
      ¬PredecessorHalfFin13Atom1427 chi ∧
      ¬PredecessorHalfFin13Atom1431 chi ∧
      ¬PredecessorHalfFin13Atom1435 chi ∧
      ¬PredecessorHalfFin13Atom1445 chi ∧
      ¬PredecessorHalfFin13Atom1465 chi ∧
      ¬PredecessorHalfFin13Atom1967 chi ∧
      ¬PredecessorHalfFin13Atom1971 chi ∧
      ¬PredecessorHalfFin13Atom1975 chi ∧
      ¬PredecessorHalfFin13Atom1985 chi ∧
      ¬PredecessorHalfFin13Atom2005 chi ∧
      ¬PredecessorHalfFin13Atom2236 chi) ∨
      ((¬PredecessorHalfFin13Atom1231 chi ∧
      ¬PredecessorHalfFin13Atom1233 chi ∧
      ¬PredecessorHalfFin13Atom1234 chi ∧
      ¬PredecessorHalfFin13Atom1238 chi ∧
      ¬PredecessorHalfFin13Atom1239 chi ∧
      ¬PredecessorHalfFin13Atom1246 chi ∧
      ¬PredecessorHalfFin13Atom1253 chi ∧
      ¬PredecessorHalfFin13Atom1254 chi ∧
      ¬PredecessorHalfFin13Atom1261 chi ∧
      ¬PredecessorHalfFin13Atom1271 chi ∧
      ¬PredecessorHalfFin13Atom1428 chi ∧
      ¬PredecessorHalfFin13Atom1429 chi ∧
      ¬PredecessorHalfFin13Atom1436 chi ∧
      ¬PredecessorHalfFin13Atom1446 chi ∧
      ¬PredecessorHalfFin13Atom1466 chi ∧
      ¬PredecessorHalfFin13Atom1968 chi ∧
      ¬PredecessorHalfFin13Atom1969 chi ∧
      ¬PredecessorHalfFin13Atom1976 chi ∧
      ¬PredecessorHalfFin13Atom1986 chi ∧
      ¬PredecessorHalfFin13Atom2006 chi ∧
      ¬PredecessorHalfFin13Atom2237 chi) ∨
      (¬PredecessorHalfFin13Atom1231 chi ∧
      ¬PredecessorHalfFin13Atom1233 chi ∧
      ¬PredecessorHalfFin13Atom1236 chi ∧
      ¬PredecessorHalfFin13Atom1238 chi ∧
      ¬PredecessorHalfFin13Atom1241 chi ∧
      ¬PredecessorHalfFin13Atom1248 chi ∧
      ¬PredecessorHalfFin13Atom1253 chi ∧
      ¬PredecessorHalfFin13Atom1256 chi ∧
      ¬PredecessorHalfFin13Atom1263 chi ∧
      ¬PredecessorHalfFin13Atom1273 chi ∧
      ¬PredecessorHalfFin13Atom1428 chi ∧
      ¬PredecessorHalfFin13Atom1431 chi ∧
      ¬PredecessorHalfFin13Atom1438 chi ∧
      ¬PredecessorHalfFin13Atom1448 chi ∧
      ¬PredecessorHalfFin13Atom1468 chi ∧
      ¬PredecessorHalfFin13Atom1968 chi ∧
      ¬PredecessorHalfFin13Atom1971 chi ∧
      ¬PredecessorHalfFin13Atom1978 chi ∧
      ¬PredecessorHalfFin13Atom1988 chi ∧
      ¬PredecessorHalfFin13Atom2008 chi ∧
      ¬PredecessorHalfFin13Atom2239 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1231 chi ∧
      ¬PredecessorHalfFin13Atom1234 chi ∧
      ¬PredecessorHalfFin13Atom1236 chi ∧
      ¬PredecessorHalfFin13Atom1239 chi ∧
      ¬PredecessorHalfFin13Atom1241 chi ∧
      ¬PredecessorHalfFin13Atom1250 chi ∧
      ¬PredecessorHalfFin13Atom1254 chi ∧
      ¬PredecessorHalfFin13Atom1256 chi ∧
      ¬PredecessorHalfFin13Atom1265 chi ∧
      ¬PredecessorHalfFin13Atom1275 chi ∧
      ¬PredecessorHalfFin13Atom1429 chi ∧
      ¬PredecessorHalfFin13Atom1431 chi ∧
      ¬PredecessorHalfFin13Atom1440 chi ∧
      ¬PredecessorHalfFin13Atom1450 chi ∧
      ¬PredecessorHalfFin13Atom1470 chi ∧
      ¬PredecessorHalfFin13Atom1969 chi ∧
      ¬PredecessorHalfFin13Atom1971 chi ∧
      ¬PredecessorHalfFin13Atom1980 chi ∧
      ¬PredecessorHalfFin13Atom1990 chi ∧
      ¬PredecessorHalfFin13Atom2010 chi ∧
      ¬PredecessorHalfFin13Atom2241 chi) ∨
      ((¬PredecessorHalfFin13Atom1232 chi ∧
      ¬PredecessorHalfFin13Atom1233 chi ∧
      ¬PredecessorHalfFin13Atom1234 chi ∧
      ¬PredecessorHalfFin13Atom1242 chi ∧
      ¬PredecessorHalfFin13Atom1243 chi ∧
      ¬PredecessorHalfFin13Atom1246 chi ∧
      ¬PredecessorHalfFin13Atom1257 chi ∧
      ¬PredecessorHalfFin13Atom1258 chi ∧
      ¬PredecessorHalfFin13Atom1261 chi ∧
      ¬PredecessorHalfFin13Atom1277 chi ∧
      ¬PredecessorHalfFin13Atom1432 chi ∧
      ¬PredecessorHalfFin13Atom1433 chi ∧
      ¬PredecessorHalfFin13Atom1436 chi ∧
      ¬PredecessorHalfFin13Atom1452 chi ∧
      ¬PredecessorHalfFin13Atom1472 chi ∧
      ¬PredecessorHalfFin13Atom1972 chi ∧
      ¬PredecessorHalfFin13Atom1973 chi ∧
      ¬PredecessorHalfFin13Atom1976 chi ∧
      ¬PredecessorHalfFin13Atom1992 chi ∧
      ¬PredecessorHalfFin13Atom2012 chi ∧
      ¬PredecessorHalfFin13Atom2243 chi) ∨
      (¬PredecessorHalfFin13Atom1232 chi ∧
      ¬PredecessorHalfFin13Atom1233 chi ∧
      ¬PredecessorHalfFin13Atom1236 chi ∧
      ¬PredecessorHalfFin13Atom1242 chi ∧
      ¬PredecessorHalfFin13Atom1245 chi ∧
      ¬PredecessorHalfFin13Atom1248 chi ∧
      ¬PredecessorHalfFin13Atom1257 chi ∧
      ¬PredecessorHalfFin13Atom1260 chi ∧
      ¬PredecessorHalfFin13Atom1263 chi ∧
      ¬PredecessorHalfFin13Atom1279 chi ∧
      ¬PredecessorHalfFin13Atom1432 chi ∧
      ¬PredecessorHalfFin13Atom1435 chi ∧
      ¬PredecessorHalfFin13Atom1438 chi ∧
      ¬PredecessorHalfFin13Atom1454 chi ∧
      ¬PredecessorHalfFin13Atom1474 chi ∧
      ¬PredecessorHalfFin13Atom1972 chi ∧
      ¬PredecessorHalfFin13Atom1975 chi ∧
      ¬PredecessorHalfFin13Atom1978 chi ∧
      ¬PredecessorHalfFin13Atom1994 chi ∧
      ¬PredecessorHalfFin13Atom2014 chi ∧
      ¬PredecessorHalfFin13Atom2245 chi))) ∨
      ((¬PredecessorHalfFin13Atom1232 chi ∧
      ¬PredecessorHalfFin13Atom1234 chi ∧
      ¬PredecessorHalfFin13Atom1236 chi ∧
      ¬PredecessorHalfFin13Atom1243 chi ∧
      ¬PredecessorHalfFin13Atom1245 chi ∧
      ¬PredecessorHalfFin13Atom1250 chi ∧
      ¬PredecessorHalfFin13Atom1258 chi ∧
      ¬PredecessorHalfFin13Atom1260 chi ∧
      ¬PredecessorHalfFin13Atom1265 chi ∧
      ¬PredecessorHalfFin13Atom1281 chi ∧
      ¬PredecessorHalfFin13Atom1433 chi ∧
      ¬PredecessorHalfFin13Atom1435 chi ∧
      ¬PredecessorHalfFin13Atom1440 chi ∧
      ¬PredecessorHalfFin13Atom1456 chi ∧
      ¬PredecessorHalfFin13Atom1476 chi ∧
      ¬PredecessorHalfFin13Atom1973 chi ∧
      ¬PredecessorHalfFin13Atom1975 chi ∧
      ¬PredecessorHalfFin13Atom1980 chi ∧
      ¬PredecessorHalfFin13Atom1996 chi ∧
      ¬PredecessorHalfFin13Atom2016 chi ∧
      ¬PredecessorHalfFin13Atom2247 chi) ∨
      ((¬PredecessorHalfFin13Atom1233 chi ∧
      ¬PredecessorHalfFin13Atom1234 chi ∧
      ¬PredecessorHalfFin13Atom1236 chi ∧
      ¬PredecessorHalfFin13Atom1246 chi ∧
      ¬PredecessorHalfFin13Atom1248 chi ∧
      ¬PredecessorHalfFin13Atom1250 chi ∧
      ¬PredecessorHalfFin13Atom1261 chi ∧
      ¬PredecessorHalfFin13Atom1263 chi ∧
      ¬PredecessorHalfFin13Atom1265 chi ∧
      ¬PredecessorHalfFin13Atom1284 chi ∧
      ¬PredecessorHalfFin13Atom1436 chi ∧
      ¬PredecessorHalfFin13Atom1438 chi ∧
      ¬PredecessorHalfFin13Atom1440 chi ∧
      ¬PredecessorHalfFin13Atom1459 chi ∧
      ¬PredecessorHalfFin13Atom1479 chi ∧
      ¬PredecessorHalfFin13Atom1976 chi ∧
      ¬PredecessorHalfFin13Atom1978 chi ∧
      ¬PredecessorHalfFin13Atom1980 chi ∧
      ¬PredecessorHalfFin13Atom1999 chi ∧
      ¬PredecessorHalfFin13Atom2019 chi ∧
      ¬PredecessorHalfFin13Atom2250 chi) ∨
      (¬PredecessorHalfFin13Atom1237 chi ∧
      ¬PredecessorHalfFin13Atom1238 chi ∧
      ¬PredecessorHalfFin13Atom1239 chi ∧
      ¬PredecessorHalfFin13Atom1242 chi ∧
      ¬PredecessorHalfFin13Atom1243 chi ∧
      ¬PredecessorHalfFin13Atom1246 chi ∧
      ¬PredecessorHalfFin13Atom1267 chi ∧
      ¬PredecessorHalfFin13Atom1268 chi ∧
      ¬PredecessorHalfFin13Atom1271 chi ∧
      ¬PredecessorHalfFin13Atom1277 chi ∧
      ¬PredecessorHalfFin13Atom1442 chi ∧
      ¬PredecessorHalfFin13Atom1443 chi ∧
      ¬PredecessorHalfFin13Atom1446 chi ∧
      ¬PredecessorHalfFin13Atom1452 chi ∧
      ¬PredecessorHalfFin13Atom1482 chi ∧
      ¬PredecessorHalfFin13Atom1982 chi ∧
      ¬PredecessorHalfFin13Atom1983 chi ∧
      ¬PredecessorHalfFin13Atom1986 chi ∧
      ¬PredecessorHalfFin13Atom1992 chi ∧
      ¬PredecessorHalfFin13Atom2022 chi ∧
      ¬PredecessorHalfFin13Atom2253 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom1237 chi ∧
      ¬PredecessorHalfFin13Atom1238 chi ∧
      ¬PredecessorHalfFin13Atom1241 chi ∧
      ¬PredecessorHalfFin13Atom1242 chi ∧
      ¬PredecessorHalfFin13Atom1245 chi ∧
      ¬PredecessorHalfFin13Atom1248 chi ∧
      ¬PredecessorHalfFin13Atom1267 chi ∧
      ¬PredecessorHalfFin13Atom1270 chi ∧
      ¬PredecessorHalfFin13Atom1273 chi ∧
      ¬PredecessorHalfFin13Atom1279 chi ∧
      ¬PredecessorHalfFin13Atom1442 chi ∧
      ¬PredecessorHalfFin13Atom1445 chi ∧
      ¬PredecessorHalfFin13Atom1448 chi ∧
      ¬PredecessorHalfFin13Atom1454 chi ∧
      ¬PredecessorHalfFin13Atom1484 chi ∧
      ¬PredecessorHalfFin13Atom1982 chi ∧
      ¬PredecessorHalfFin13Atom1985 chi ∧
      ¬PredecessorHalfFin13Atom1988 chi ∧
      ¬PredecessorHalfFin13Atom1994 chi ∧
      ¬PredecessorHalfFin13Atom2024 chi ∧
      ¬PredecessorHalfFin13Atom2255 chi) ∨
      ((¬PredecessorHalfFin13Atom1237 chi ∧
      ¬PredecessorHalfFin13Atom1239 chi ∧
      ¬PredecessorHalfFin13Atom1241 chi ∧
      ¬PredecessorHalfFin13Atom1243 chi ∧
      ¬PredecessorHalfFin13Atom1245 chi ∧
      ¬PredecessorHalfFin13Atom1250 chi ∧
      ¬PredecessorHalfFin13Atom1268 chi ∧
      ¬PredecessorHalfFin13Atom1270 chi ∧
      ¬PredecessorHalfFin13Atom1275 chi ∧
      ¬PredecessorHalfFin13Atom1281 chi ∧
      ¬PredecessorHalfFin13Atom1443 chi ∧
      ¬PredecessorHalfFin13Atom1445 chi ∧
      ¬PredecessorHalfFin13Atom1450 chi ∧
      ¬PredecessorHalfFin13Atom1456 chi ∧
      ¬PredecessorHalfFin13Atom1486 chi ∧
      ¬PredecessorHalfFin13Atom1983 chi ∧
      ¬PredecessorHalfFin13Atom1985 chi ∧
      ¬PredecessorHalfFin13Atom1990 chi ∧
      ¬PredecessorHalfFin13Atom1996 chi ∧
      ¬PredecessorHalfFin13Atom2026 chi ∧
      ¬PredecessorHalfFin13Atom2257 chi) ∨
      (¬PredecessorHalfFin13Atom1238 chi ∧
      ¬PredecessorHalfFin13Atom1239 chi ∧
      ¬PredecessorHalfFin13Atom1241 chi ∧
      ¬PredecessorHalfFin13Atom1246 chi ∧
      ¬PredecessorHalfFin13Atom1248 chi ∧
      ¬PredecessorHalfFin13Atom1250 chi ∧
      ¬PredecessorHalfFin13Atom1271 chi ∧
      ¬PredecessorHalfFin13Atom1273 chi ∧
      ¬PredecessorHalfFin13Atom1275 chi ∧
      ¬PredecessorHalfFin13Atom1284 chi ∧
      ¬PredecessorHalfFin13Atom1446 chi ∧
      ¬PredecessorHalfFin13Atom1448 chi ∧
      ¬PredecessorHalfFin13Atom1450 chi ∧
      ¬PredecessorHalfFin13Atom1459 chi ∧
      ¬PredecessorHalfFin13Atom1489 chi ∧
      ¬PredecessorHalfFin13Atom1986 chi ∧
      ¬PredecessorHalfFin13Atom1988 chi ∧
      ¬PredecessorHalfFin13Atom1990 chi ∧
      ¬PredecessorHalfFin13Atom1999 chi ∧
      ¬PredecessorHalfFin13Atom2029 chi ∧
      ¬PredecessorHalfFin13Atom2260 chi))) ∨
      ((¬PredecessorHalfFin13Atom1242 chi ∧
      ¬PredecessorHalfFin13Atom1243 chi ∧
      ¬PredecessorHalfFin13Atom1245 chi ∧
      ¬PredecessorHalfFin13Atom1246 chi ∧
      ¬PredecessorHalfFin13Atom1248 chi ∧
      ¬PredecessorHalfFin13Atom1250 chi ∧
      ¬PredecessorHalfFin13Atom1277 chi ∧
      ¬PredecessorHalfFin13Atom1279 chi ∧
      ¬PredecessorHalfFin13Atom1281 chi ∧
      ¬PredecessorHalfFin13Atom1284 chi ∧
      ¬PredecessorHalfFin13Atom1452 chi ∧
      ¬PredecessorHalfFin13Atom1454 chi ∧
      ¬PredecessorHalfFin13Atom1456 chi ∧
      ¬PredecessorHalfFin13Atom1459 chi ∧
      ¬PredecessorHalfFin13Atom1493 chi ∧
      ¬PredecessorHalfFin13Atom1992 chi ∧
      ¬PredecessorHalfFin13Atom1994 chi ∧
      ¬PredecessorHalfFin13Atom1996 chi ∧
      ¬PredecessorHalfFin13Atom1999 chi ∧
      ¬PredecessorHalfFin13Atom2033 chi ∧
      ¬PredecessorHalfFin13Atom2264 chi) ∨
      ((¬PredecessorHalfFin13Atom1252 chi ∧
      ¬PredecessorHalfFin13Atom1253 chi ∧
      ¬PredecessorHalfFin13Atom1254 chi ∧
      ¬PredecessorHalfFin13Atom1257 chi ∧
      ¬PredecessorHalfFin13Atom1258 chi ∧
      ¬PredecessorHalfFin13Atom1261 chi ∧
      ¬PredecessorHalfFin13Atom1267 chi ∧
      ¬PredecessorHalfFin13Atom1268 chi ∧
      ¬PredecessorHalfFin13Atom1271 chi ∧
      ¬PredecessorHalfFin13Atom1277 chi ∧
      ¬PredecessorHalfFin13Atom1462 chi ∧
      ¬PredecessorHalfFin13Atom1463 chi ∧
      ¬PredecessorHalfFin13Atom1466 chi ∧
      ¬PredecessorHalfFin13Atom1472 chi ∧
      ¬PredecessorHalfFin13Atom1482 chi ∧
      ¬PredecessorHalfFin13Atom2002 chi ∧
      ¬PredecessorHalfFin13Atom2003 chi ∧
      ¬PredecessorHalfFin13Atom2006 chi ∧
      ¬PredecessorHalfFin13Atom2012 chi ∧
      ¬PredecessorHalfFin13Atom2022 chi ∧
      ¬PredecessorHalfFin13Atom2268 chi) ∨
      (¬PredecessorHalfFin13Atom1252 chi ∧
      ¬PredecessorHalfFin13Atom1253 chi ∧
      ¬PredecessorHalfFin13Atom1256 chi ∧
      ¬PredecessorHalfFin13Atom1257 chi ∧
      ¬PredecessorHalfFin13Atom1260 chi ∧
      ¬PredecessorHalfFin13Atom1263 chi ∧
      ¬PredecessorHalfFin13Atom1267 chi ∧
      ¬PredecessorHalfFin13Atom1270 chi ∧
      ¬PredecessorHalfFin13Atom1273 chi ∧
      ¬PredecessorHalfFin13Atom1279 chi ∧
      ¬PredecessorHalfFin13Atom1462 chi ∧
      ¬PredecessorHalfFin13Atom1465 chi ∧
      ¬PredecessorHalfFin13Atom1468 chi ∧
      ¬PredecessorHalfFin13Atom1474 chi ∧
      ¬PredecessorHalfFin13Atom1484 chi ∧
      ¬PredecessorHalfFin13Atom2002 chi ∧
      ¬PredecessorHalfFin13Atom2005 chi ∧
      ¬PredecessorHalfFin13Atom2008 chi ∧
      ¬PredecessorHalfFin13Atom2014 chi ∧
      ¬PredecessorHalfFin13Atom2024 chi ∧
      ¬PredecessorHalfFin13Atom2270 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1252 chi ∧
      ¬PredecessorHalfFin13Atom1254 chi ∧
      ¬PredecessorHalfFin13Atom1256 chi ∧
      ¬PredecessorHalfFin13Atom1258 chi ∧
      ¬PredecessorHalfFin13Atom1260 chi ∧
      ¬PredecessorHalfFin13Atom1265 chi ∧
      ¬PredecessorHalfFin13Atom1268 chi ∧
      ¬PredecessorHalfFin13Atom1270 chi ∧
      ¬PredecessorHalfFin13Atom1275 chi ∧
      ¬PredecessorHalfFin13Atom1281 chi ∧
      ¬PredecessorHalfFin13Atom1463 chi ∧
      ¬PredecessorHalfFin13Atom1465 chi ∧
      ¬PredecessorHalfFin13Atom1470 chi ∧
      ¬PredecessorHalfFin13Atom1476 chi ∧
      ¬PredecessorHalfFin13Atom1486 chi ∧
      ¬PredecessorHalfFin13Atom2003 chi ∧
      ¬PredecessorHalfFin13Atom2005 chi ∧
      ¬PredecessorHalfFin13Atom2010 chi ∧
      ¬PredecessorHalfFin13Atom2016 chi ∧
      ¬PredecessorHalfFin13Atom2026 chi ∧
      ¬PredecessorHalfFin13Atom2272 chi) ∨
      ((¬PredecessorHalfFin13Atom1253 chi ∧
      ¬PredecessorHalfFin13Atom1254 chi ∧
      ¬PredecessorHalfFin13Atom1256 chi ∧
      ¬PredecessorHalfFin13Atom1261 chi ∧
      ¬PredecessorHalfFin13Atom1263 chi ∧
      ¬PredecessorHalfFin13Atom1265 chi ∧
      ¬PredecessorHalfFin13Atom1271 chi ∧
      ¬PredecessorHalfFin13Atom1273 chi ∧
      ¬PredecessorHalfFin13Atom1275 chi ∧
      ¬PredecessorHalfFin13Atom1284 chi ∧
      ¬PredecessorHalfFin13Atom1466 chi ∧
      ¬PredecessorHalfFin13Atom1468 chi ∧
      ¬PredecessorHalfFin13Atom1470 chi ∧
      ¬PredecessorHalfFin13Atom1479 chi ∧
      ¬PredecessorHalfFin13Atom1489 chi ∧
      ¬PredecessorHalfFin13Atom2006 chi ∧
      ¬PredecessorHalfFin13Atom2008 chi ∧
      ¬PredecessorHalfFin13Atom2010 chi ∧
      ¬PredecessorHalfFin13Atom2019 chi ∧
      ¬PredecessorHalfFin13Atom2029 chi ∧
      ¬PredecessorHalfFin13Atom2275 chi) ∨
      (¬PredecessorHalfFin13Atom1257 chi ∧
      ¬PredecessorHalfFin13Atom1258 chi ∧
      ¬PredecessorHalfFin13Atom1260 chi ∧
      ¬PredecessorHalfFin13Atom1261 chi ∧
      ¬PredecessorHalfFin13Atom1263 chi ∧
      ¬PredecessorHalfFin13Atom1265 chi ∧
      ¬PredecessorHalfFin13Atom1277 chi ∧
      ¬PredecessorHalfFin13Atom1279 chi ∧
      ¬PredecessorHalfFin13Atom1281 chi ∧
      ¬PredecessorHalfFin13Atom1284 chi ∧
      ¬PredecessorHalfFin13Atom1472 chi ∧
      ¬PredecessorHalfFin13Atom1474 chi ∧
      ¬PredecessorHalfFin13Atom1476 chi ∧
      ¬PredecessorHalfFin13Atom1479 chi ∧
      ¬PredecessorHalfFin13Atom1493 chi ∧
      ¬PredecessorHalfFin13Atom2012 chi ∧
      ¬PredecessorHalfFin13Atom2014 chi ∧
      ¬PredecessorHalfFin13Atom2016 chi ∧
      ¬PredecessorHalfFin13Atom2019 chi ∧
      ¬PredecessorHalfFin13Atom2033 chi ∧
      ¬PredecessorHalfFin13Atom2279 chi))) ∨
      (((¬PredecessorHalfFin13Atom1267 chi ∧
      ¬PredecessorHalfFin13Atom1268 chi ∧
      ¬PredecessorHalfFin13Atom1270 chi ∧
      ¬PredecessorHalfFin13Atom1271 chi ∧
      ¬PredecessorHalfFin13Atom1273 chi ∧
      ¬PredecessorHalfFin13Atom1275 chi ∧
      ¬PredecessorHalfFin13Atom1277 chi ∧
      ¬PredecessorHalfFin13Atom1279 chi ∧
      ¬PredecessorHalfFin13Atom1281 chi ∧
      ¬PredecessorHalfFin13Atom1284 chi ∧
      ¬PredecessorHalfFin13Atom1482 chi ∧
      ¬PredecessorHalfFin13Atom1484 chi ∧
      ¬PredecessorHalfFin13Atom1486 chi ∧
      ¬PredecessorHalfFin13Atom1489 chi ∧
      ¬PredecessorHalfFin13Atom1493 chi ∧
      ¬PredecessorHalfFin13Atom2022 chi ∧
      ¬PredecessorHalfFin13Atom2024 chi ∧
      ¬PredecessorHalfFin13Atom2026 chi ∧
      ¬PredecessorHalfFin13Atom2029 chi ∧
      ¬PredecessorHalfFin13Atom2033 chi ∧
      ¬PredecessorHalfFin13Atom2284 chi) ∨
      (¬PredecessorHalfFin13Atom1287 chi ∧
      ¬PredecessorHalfFin13Atom1288 chi ∧
      ¬PredecessorHalfFin13Atom1289 chi ∧
      ¬PredecessorHalfFin13Atom1294 chi ∧
      ¬PredecessorHalfFin13Atom1295 chi ∧
      ¬PredecessorHalfFin13Atom1300 chi ∧
      ¬PredecessorHalfFin13Atom1315 chi ∧
      ¬PredecessorHalfFin13Atom1316 chi ∧
      ¬PredecessorHalfFin13Atom1321 chi ∧
      ¬PredecessorHalfFin13Atom1336 chi ∧
      ¬PredecessorHalfFin13Atom1371 chi ∧
      ¬PredecessorHalfFin13Atom1372 chi ∧
      ¬PredecessorHalfFin13Atom1377 chi ∧
      ¬PredecessorHalfFin13Atom1392 chi ∧
      ¬PredecessorHalfFin13Atom1427 chi ∧
      ¬PredecessorHalfFin13Atom2037 chi ∧
      ¬PredecessorHalfFin13Atom2038 chi ∧
      ¬PredecessorHalfFin13Atom2043 chi ∧
      ¬PredecessorHalfFin13Atom2058 chi ∧
      ¬PredecessorHalfFin13Atom2093 chi ∧
      ¬PredecessorHalfFin13Atom2163 chi)) ∨
      ((¬PredecessorHalfFin13Atom1287 chi ∧
      ¬PredecessorHalfFin13Atom1288 chi ∧
      ¬PredecessorHalfFin13Atom1290 chi ∧
      ¬PredecessorHalfFin13Atom1294 chi ∧
      ¬PredecessorHalfFin13Atom1296 chi ∧
      ¬PredecessorHalfFin13Atom1301 chi ∧
      ¬PredecessorHalfFin13Atom1315 chi ∧
      ¬PredecessorHalfFin13Atom1317 chi ∧
      ¬PredecessorHalfFin13Atom1322 chi ∧
      ¬PredecessorHalfFin13Atom1337 chi ∧
      ¬PredecessorHalfFin13Atom1371 chi ∧
      ¬PredecessorHalfFin13Atom1373 chi ∧
      ¬PredecessorHalfFin13Atom1378 chi ∧
      ¬PredecessorHalfFin13Atom1393 chi ∧
      ¬PredecessorHalfFin13Atom1428 chi ∧
      ¬PredecessorHalfFin13Atom2037 chi ∧
      ¬PredecessorHalfFin13Atom2039 chi ∧
      ¬PredecessorHalfFin13Atom2044 chi ∧
      ¬PredecessorHalfFin13Atom2059 chi ∧
      ¬PredecessorHalfFin13Atom2094 chi ∧
      ¬PredecessorHalfFin13Atom2164 chi) ∨
      (¬PredecessorHalfFin13Atom1287 chi ∧
      ¬PredecessorHalfFin13Atom1288 chi ∧
      ¬PredecessorHalfFin13Atom1291 chi ∧
      ¬PredecessorHalfFin13Atom1294 chi ∧
      ¬PredecessorHalfFin13Atom1297 chi ∧
      ¬PredecessorHalfFin13Atom1302 chi ∧
      ¬PredecessorHalfFin13Atom1315 chi ∧
      ¬PredecessorHalfFin13Atom1318 chi ∧
      ¬PredecessorHalfFin13Atom1323 chi ∧
      ¬PredecessorHalfFin13Atom1338 chi ∧
      ¬PredecessorHalfFin13Atom1371 chi ∧
      ¬PredecessorHalfFin13Atom1374 chi ∧
      ¬PredecessorHalfFin13Atom1379 chi ∧
      ¬PredecessorHalfFin13Atom1394 chi ∧
      ¬PredecessorHalfFin13Atom1429 chi ∧
      ¬PredecessorHalfFin13Atom2037 chi ∧
      ¬PredecessorHalfFin13Atom2040 chi ∧
      ¬PredecessorHalfFin13Atom2045 chi ∧
      ¬PredecessorHalfFin13Atom2060 chi ∧
      ¬PredecessorHalfFin13Atom2095 chi ∧
      ¬PredecessorHalfFin13Atom2165 chi))))))) ∨
      ((((((¬PredecessorHalfFin13Atom1287 chi ∧
      ¬PredecessorHalfFin13Atom1288 chi ∧
      ¬PredecessorHalfFin13Atom1293 chi ∧
      ¬PredecessorHalfFin13Atom1294 chi ∧
      ¬PredecessorHalfFin13Atom1299 chi ∧
      ¬PredecessorHalfFin13Atom1304 chi ∧
      ¬PredecessorHalfFin13Atom1315 chi ∧
      ¬PredecessorHalfFin13Atom1320 chi ∧
      ¬PredecessorHalfFin13Atom1325 chi ∧
      ¬PredecessorHalfFin13Atom1340 chi ∧
      ¬PredecessorHalfFin13Atom1371 chi ∧
      ¬PredecessorHalfFin13Atom1376 chi ∧
      ¬PredecessorHalfFin13Atom1381 chi ∧
      ¬PredecessorHalfFin13Atom1396 chi ∧
      ¬PredecessorHalfFin13Atom1431 chi ∧
      ¬PredecessorHalfFin13Atom2037 chi ∧
      ¬PredecessorHalfFin13Atom2042 chi ∧
      ¬PredecessorHalfFin13Atom2047 chi ∧
      ¬PredecessorHalfFin13Atom2062 chi ∧
      ¬PredecessorHalfFin13Atom2097 chi ∧
      ¬PredecessorHalfFin13Atom2167 chi) ∨
      ((¬PredecessorHalfFin13Atom1287 chi ∧
      ¬PredecessorHalfFin13Atom1289 chi ∧
      ¬PredecessorHalfFin13Atom1290 chi ∧
      ¬PredecessorHalfFin13Atom1295 chi ∧
      ¬PredecessorHalfFin13Atom1296 chi ∧
      ¬PredecessorHalfFin13Atom1305 chi ∧
      ¬PredecessorHalfFin13Atom1316 chi ∧
      ¬PredecessorHalfFin13Atom1317 chi ∧
      ¬PredecessorHalfFin13Atom1326 chi ∧
      ¬PredecessorHalfFin13Atom1341 chi ∧
      ¬PredecessorHalfFin13Atom1372 chi ∧
      ¬PredecessorHalfFin13Atom1373 chi ∧
      ¬PredecessorHalfFin13Atom1382 chi ∧
      ¬PredecessorHalfFin13Atom1397 chi ∧
      ¬PredecessorHalfFin13Atom1432 chi ∧
      ¬PredecessorHalfFin13Atom2038 chi ∧
      ¬PredecessorHalfFin13Atom2039 chi ∧
      ¬PredecessorHalfFin13Atom2048 chi ∧
      ¬PredecessorHalfFin13Atom2063 chi ∧
      ¬PredecessorHalfFin13Atom2098 chi ∧
      ¬PredecessorHalfFin13Atom2168 chi) ∨
      (¬PredecessorHalfFin13Atom1287 chi ∧
      ¬PredecessorHalfFin13Atom1289 chi ∧
      ¬PredecessorHalfFin13Atom1291 chi ∧
      ¬PredecessorHalfFin13Atom1295 chi ∧
      ¬PredecessorHalfFin13Atom1297 chi ∧
      ¬PredecessorHalfFin13Atom1306 chi ∧
      ¬PredecessorHalfFin13Atom1316 chi ∧
      ¬PredecessorHalfFin13Atom1318 chi ∧
      ¬PredecessorHalfFin13Atom1327 chi ∧
      ¬PredecessorHalfFin13Atom1342 chi ∧
      ¬PredecessorHalfFin13Atom1372 chi ∧
      ¬PredecessorHalfFin13Atom1374 chi ∧
      ¬PredecessorHalfFin13Atom1383 chi ∧
      ¬PredecessorHalfFin13Atom1398 chi ∧
      ¬PredecessorHalfFin13Atom1433 chi ∧
      ¬PredecessorHalfFin13Atom2038 chi ∧
      ¬PredecessorHalfFin13Atom2040 chi ∧
      ¬PredecessorHalfFin13Atom2049 chi ∧
      ¬PredecessorHalfFin13Atom2064 chi ∧
      ¬PredecessorHalfFin13Atom2099 chi ∧
      ¬PredecessorHalfFin13Atom2169 chi))) ∨
      ((¬PredecessorHalfFin13Atom1287 chi ∧
      ¬PredecessorHalfFin13Atom1289 chi ∧
      ¬PredecessorHalfFin13Atom1293 chi ∧
      ¬PredecessorHalfFin13Atom1295 chi ∧
      ¬PredecessorHalfFin13Atom1299 chi ∧
      ¬PredecessorHalfFin13Atom1308 chi ∧
      ¬PredecessorHalfFin13Atom1316 chi ∧
      ¬PredecessorHalfFin13Atom1320 chi ∧
      ¬PredecessorHalfFin13Atom1329 chi ∧
      ¬PredecessorHalfFin13Atom1344 chi ∧
      ¬PredecessorHalfFin13Atom1372 chi ∧
      ¬PredecessorHalfFin13Atom1376 chi ∧
      ¬PredecessorHalfFin13Atom1385 chi ∧
      ¬PredecessorHalfFin13Atom1400 chi ∧
      ¬PredecessorHalfFin13Atom1435 chi ∧
      ¬PredecessorHalfFin13Atom2038 chi ∧
      ¬PredecessorHalfFin13Atom2042 chi ∧
      ¬PredecessorHalfFin13Atom2051 chi ∧
      ¬PredecessorHalfFin13Atom2066 chi ∧
      ¬PredecessorHalfFin13Atom2101 chi ∧
      ¬PredecessorHalfFin13Atom2171 chi) ∨
      ((¬PredecessorHalfFin13Atom1287 chi ∧
      ¬PredecessorHalfFin13Atom1290 chi ∧
      ¬PredecessorHalfFin13Atom1291 chi ∧
      ¬PredecessorHalfFin13Atom1296 chi ∧
      ¬PredecessorHalfFin13Atom1297 chi ∧
      ¬PredecessorHalfFin13Atom1309 chi ∧
      ¬PredecessorHalfFin13Atom1317 chi ∧
      ¬PredecessorHalfFin13Atom1318 chi ∧
      ¬PredecessorHalfFin13Atom1330 chi ∧
      ¬PredecessorHalfFin13Atom1345 chi ∧
      ¬PredecessorHalfFin13Atom1373 chi ∧
      ¬PredecessorHalfFin13Atom1374 chi ∧
      ¬PredecessorHalfFin13Atom1386 chi ∧
      ¬PredecessorHalfFin13Atom1401 chi ∧
      ¬PredecessorHalfFin13Atom1436 chi ∧
      ¬PredecessorHalfFin13Atom2039 chi ∧
      ¬PredecessorHalfFin13Atom2040 chi ∧
      ¬PredecessorHalfFin13Atom2052 chi ∧
      ¬PredecessorHalfFin13Atom2067 chi ∧
      ¬PredecessorHalfFin13Atom2102 chi ∧
      ¬PredecessorHalfFin13Atom2172 chi) ∨
      (¬PredecessorHalfFin13Atom1287 chi ∧
      ¬PredecessorHalfFin13Atom1290 chi ∧
      ¬PredecessorHalfFin13Atom1293 chi ∧
      ¬PredecessorHalfFin13Atom1296 chi ∧
      ¬PredecessorHalfFin13Atom1299 chi ∧
      ¬PredecessorHalfFin13Atom1311 chi ∧
      ¬PredecessorHalfFin13Atom1317 chi ∧
      ¬PredecessorHalfFin13Atom1320 chi ∧
      ¬PredecessorHalfFin13Atom1332 chi ∧
      ¬PredecessorHalfFin13Atom1347 chi ∧
      ¬PredecessorHalfFin13Atom1373 chi ∧
      ¬PredecessorHalfFin13Atom1376 chi ∧
      ¬PredecessorHalfFin13Atom1388 chi ∧
      ¬PredecessorHalfFin13Atom1403 chi ∧
      ¬PredecessorHalfFin13Atom1438 chi ∧
      ¬PredecessorHalfFin13Atom2039 chi ∧
      ¬PredecessorHalfFin13Atom2042 chi ∧
      ¬PredecessorHalfFin13Atom2054 chi ∧
      ¬PredecessorHalfFin13Atom2069 chi ∧
      ¬PredecessorHalfFin13Atom2104 chi ∧
      ¬PredecessorHalfFin13Atom2174 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1287 chi ∧
      ¬PredecessorHalfFin13Atom1291 chi ∧
      ¬PredecessorHalfFin13Atom1293 chi ∧
      ¬PredecessorHalfFin13Atom1297 chi ∧
      ¬PredecessorHalfFin13Atom1299 chi ∧
      ¬PredecessorHalfFin13Atom1313 chi ∧
      ¬PredecessorHalfFin13Atom1318 chi ∧
      ¬PredecessorHalfFin13Atom1320 chi ∧
      ¬PredecessorHalfFin13Atom1334 chi ∧
      ¬PredecessorHalfFin13Atom1349 chi ∧
      ¬PredecessorHalfFin13Atom1374 chi ∧
      ¬PredecessorHalfFin13Atom1376 chi ∧
      ¬PredecessorHalfFin13Atom1390 chi ∧
      ¬PredecessorHalfFin13Atom1405 chi ∧
      ¬PredecessorHalfFin13Atom1440 chi ∧
      ¬PredecessorHalfFin13Atom2040 chi ∧
      ¬PredecessorHalfFin13Atom2042 chi ∧
      ¬PredecessorHalfFin13Atom2056 chi ∧
      ¬PredecessorHalfFin13Atom2071 chi ∧
      ¬PredecessorHalfFin13Atom2106 chi ∧
      ¬PredecessorHalfFin13Atom2176 chi) ∨
      ((¬PredecessorHalfFin13Atom1288 chi ∧
      ¬PredecessorHalfFin13Atom1289 chi ∧
      ¬PredecessorHalfFin13Atom1290 chi ∧
      ¬PredecessorHalfFin13Atom1300 chi ∧
      ¬PredecessorHalfFin13Atom1301 chi ∧
      ¬PredecessorHalfFin13Atom1305 chi ∧
      ¬PredecessorHalfFin13Atom1321 chi ∧
      ¬PredecessorHalfFin13Atom1322 chi ∧
      ¬PredecessorHalfFin13Atom1326 chi ∧
      ¬PredecessorHalfFin13Atom1351 chi ∧
      ¬PredecessorHalfFin13Atom1377 chi ∧
      ¬PredecessorHalfFin13Atom1378 chi ∧
      ¬PredecessorHalfFin13Atom1382 chi ∧
      ¬PredecessorHalfFin13Atom1407 chi ∧
      ¬PredecessorHalfFin13Atom1442 chi ∧
      ¬PredecessorHalfFin13Atom2043 chi ∧
      ¬PredecessorHalfFin13Atom2044 chi ∧
      ¬PredecessorHalfFin13Atom2048 chi ∧
      ¬PredecessorHalfFin13Atom2073 chi ∧
      ¬PredecessorHalfFin13Atom2108 chi ∧
      ¬PredecessorHalfFin13Atom2178 chi) ∨
      (¬PredecessorHalfFin13Atom1288 chi ∧
      ¬PredecessorHalfFin13Atom1289 chi ∧
      ¬PredecessorHalfFin13Atom1291 chi ∧
      ¬PredecessorHalfFin13Atom1300 chi ∧
      ¬PredecessorHalfFin13Atom1302 chi ∧
      ¬PredecessorHalfFin13Atom1306 chi ∧
      ¬PredecessorHalfFin13Atom1321 chi ∧
      ¬PredecessorHalfFin13Atom1323 chi ∧
      ¬PredecessorHalfFin13Atom1327 chi ∧
      ¬PredecessorHalfFin13Atom1352 chi ∧
      ¬PredecessorHalfFin13Atom1377 chi ∧
      ¬PredecessorHalfFin13Atom1379 chi ∧
      ¬PredecessorHalfFin13Atom1383 chi ∧
      ¬PredecessorHalfFin13Atom1408 chi ∧
      ¬PredecessorHalfFin13Atom1443 chi ∧
      ¬PredecessorHalfFin13Atom2043 chi ∧
      ¬PredecessorHalfFin13Atom2045 chi ∧
      ¬PredecessorHalfFin13Atom2049 chi ∧
      ¬PredecessorHalfFin13Atom2074 chi ∧
      ¬PredecessorHalfFin13Atom2109 chi ∧
      ¬PredecessorHalfFin13Atom2179 chi))) ∨
      ((¬PredecessorHalfFin13Atom1288 chi ∧
      ¬PredecessorHalfFin13Atom1289 chi ∧
      ¬PredecessorHalfFin13Atom1293 chi ∧
      ¬PredecessorHalfFin13Atom1300 chi ∧
      ¬PredecessorHalfFin13Atom1304 chi ∧
      ¬PredecessorHalfFin13Atom1308 chi ∧
      ¬PredecessorHalfFin13Atom1321 chi ∧
      ¬PredecessorHalfFin13Atom1325 chi ∧
      ¬PredecessorHalfFin13Atom1329 chi ∧
      ¬PredecessorHalfFin13Atom1354 chi ∧
      ¬PredecessorHalfFin13Atom1377 chi ∧
      ¬PredecessorHalfFin13Atom1381 chi ∧
      ¬PredecessorHalfFin13Atom1385 chi ∧
      ¬PredecessorHalfFin13Atom1410 chi ∧
      ¬PredecessorHalfFin13Atom1445 chi ∧
      ¬PredecessorHalfFin13Atom2043 chi ∧
      ¬PredecessorHalfFin13Atom2047 chi ∧
      ¬PredecessorHalfFin13Atom2051 chi ∧
      ¬PredecessorHalfFin13Atom2076 chi ∧
      ¬PredecessorHalfFin13Atom2111 chi ∧
      ¬PredecessorHalfFin13Atom2181 chi) ∨
      ((¬PredecessorHalfFin13Atom1288 chi ∧
      ¬PredecessorHalfFin13Atom1290 chi ∧
      ¬PredecessorHalfFin13Atom1291 chi ∧
      ¬PredecessorHalfFin13Atom1301 chi ∧
      ¬PredecessorHalfFin13Atom1302 chi ∧
      ¬PredecessorHalfFin13Atom1309 chi ∧
      ¬PredecessorHalfFin13Atom1322 chi ∧
      ¬PredecessorHalfFin13Atom1323 chi ∧
      ¬PredecessorHalfFin13Atom1330 chi ∧
      ¬PredecessorHalfFin13Atom1355 chi ∧
      ¬PredecessorHalfFin13Atom1378 chi ∧
      ¬PredecessorHalfFin13Atom1379 chi ∧
      ¬PredecessorHalfFin13Atom1386 chi ∧
      ¬PredecessorHalfFin13Atom1411 chi ∧
      ¬PredecessorHalfFin13Atom1446 chi ∧
      ¬PredecessorHalfFin13Atom2044 chi ∧
      ¬PredecessorHalfFin13Atom2045 chi ∧
      ¬PredecessorHalfFin13Atom2052 chi ∧
      ¬PredecessorHalfFin13Atom2077 chi ∧
      ¬PredecessorHalfFin13Atom2112 chi ∧
      ¬PredecessorHalfFin13Atom2182 chi) ∨
      (¬PredecessorHalfFin13Atom1288 chi ∧
      ¬PredecessorHalfFin13Atom1290 chi ∧
      ¬PredecessorHalfFin13Atom1293 chi ∧
      ¬PredecessorHalfFin13Atom1301 chi ∧
      ¬PredecessorHalfFin13Atom1304 chi ∧
      ¬PredecessorHalfFin13Atom1311 chi ∧
      ¬PredecessorHalfFin13Atom1322 chi ∧
      ¬PredecessorHalfFin13Atom1325 chi ∧
      ¬PredecessorHalfFin13Atom1332 chi ∧
      ¬PredecessorHalfFin13Atom1357 chi ∧
      ¬PredecessorHalfFin13Atom1378 chi ∧
      ¬PredecessorHalfFin13Atom1381 chi ∧
      ¬PredecessorHalfFin13Atom1388 chi ∧
      ¬PredecessorHalfFin13Atom1413 chi ∧
      ¬PredecessorHalfFin13Atom1448 chi ∧
      ¬PredecessorHalfFin13Atom2044 chi ∧
      ¬PredecessorHalfFin13Atom2047 chi ∧
      ¬PredecessorHalfFin13Atom2054 chi ∧
      ¬PredecessorHalfFin13Atom2079 chi ∧
      ¬PredecessorHalfFin13Atom2114 chi ∧
      ¬PredecessorHalfFin13Atom2184 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom1288 chi ∧
      ¬PredecessorHalfFin13Atom1291 chi ∧
      ¬PredecessorHalfFin13Atom1293 chi ∧
      ¬PredecessorHalfFin13Atom1302 chi ∧
      ¬PredecessorHalfFin13Atom1304 chi ∧
      ¬PredecessorHalfFin13Atom1313 chi ∧
      ¬PredecessorHalfFin13Atom1323 chi ∧
      ¬PredecessorHalfFin13Atom1325 chi ∧
      ¬PredecessorHalfFin13Atom1334 chi ∧
      ¬PredecessorHalfFin13Atom1359 chi ∧
      ¬PredecessorHalfFin13Atom1379 chi ∧
      ¬PredecessorHalfFin13Atom1381 chi ∧
      ¬PredecessorHalfFin13Atom1390 chi ∧
      ¬PredecessorHalfFin13Atom1415 chi ∧
      ¬PredecessorHalfFin13Atom1450 chi ∧
      ¬PredecessorHalfFin13Atom2045 chi ∧
      ¬PredecessorHalfFin13Atom2047 chi ∧
      ¬PredecessorHalfFin13Atom2056 chi ∧
      ¬PredecessorHalfFin13Atom2081 chi ∧
      ¬PredecessorHalfFin13Atom2116 chi ∧
      ¬PredecessorHalfFin13Atom2186 chi) ∨
      ((¬PredecessorHalfFin13Atom1289 chi ∧
      ¬PredecessorHalfFin13Atom1290 chi ∧
      ¬PredecessorHalfFin13Atom1291 chi ∧
      ¬PredecessorHalfFin13Atom1305 chi ∧
      ¬PredecessorHalfFin13Atom1306 chi ∧
      ¬PredecessorHalfFin13Atom1309 chi ∧
      ¬PredecessorHalfFin13Atom1326 chi ∧
      ¬PredecessorHalfFin13Atom1327 chi ∧
      ¬PredecessorHalfFin13Atom1330 chi ∧
      ¬PredecessorHalfFin13Atom1361 chi ∧
      ¬PredecessorHalfFin13Atom1382 chi ∧
      ¬PredecessorHalfFin13Atom1383 chi ∧
      ¬PredecessorHalfFin13Atom1386 chi ∧
      ¬PredecessorHalfFin13Atom1417 chi ∧
      ¬PredecessorHalfFin13Atom1452 chi ∧
      ¬PredecessorHalfFin13Atom2048 chi ∧
      ¬PredecessorHalfFin13Atom2049 chi ∧
      ¬PredecessorHalfFin13Atom2052 chi ∧
      ¬PredecessorHalfFin13Atom2083 chi ∧
      ¬PredecessorHalfFin13Atom2118 chi ∧
      ¬PredecessorHalfFin13Atom2188 chi) ∨
      (¬PredecessorHalfFin13Atom1289 chi ∧
      ¬PredecessorHalfFin13Atom1290 chi ∧
      ¬PredecessorHalfFin13Atom1293 chi ∧
      ¬PredecessorHalfFin13Atom1305 chi ∧
      ¬PredecessorHalfFin13Atom1308 chi ∧
      ¬PredecessorHalfFin13Atom1311 chi ∧
      ¬PredecessorHalfFin13Atom1326 chi ∧
      ¬PredecessorHalfFin13Atom1329 chi ∧
      ¬PredecessorHalfFin13Atom1332 chi ∧
      ¬PredecessorHalfFin13Atom1363 chi ∧
      ¬PredecessorHalfFin13Atom1382 chi ∧
      ¬PredecessorHalfFin13Atom1385 chi ∧
      ¬PredecessorHalfFin13Atom1388 chi ∧
      ¬PredecessorHalfFin13Atom1419 chi ∧
      ¬PredecessorHalfFin13Atom1454 chi ∧
      ¬PredecessorHalfFin13Atom2048 chi ∧
      ¬PredecessorHalfFin13Atom2051 chi ∧
      ¬PredecessorHalfFin13Atom2054 chi ∧
      ¬PredecessorHalfFin13Atom2085 chi ∧
      ¬PredecessorHalfFin13Atom2120 chi ∧
      ¬PredecessorHalfFin13Atom2190 chi))) ∨
      ((¬PredecessorHalfFin13Atom1289 chi ∧
      ¬PredecessorHalfFin13Atom1291 chi ∧
      ¬PredecessorHalfFin13Atom1293 chi ∧
      ¬PredecessorHalfFin13Atom1306 chi ∧
      ¬PredecessorHalfFin13Atom1308 chi ∧
      ¬PredecessorHalfFin13Atom1313 chi ∧
      ¬PredecessorHalfFin13Atom1327 chi ∧
      ¬PredecessorHalfFin13Atom1329 chi ∧
      ¬PredecessorHalfFin13Atom1334 chi ∧
      ¬PredecessorHalfFin13Atom1365 chi ∧
      ¬PredecessorHalfFin13Atom1383 chi ∧
      ¬PredecessorHalfFin13Atom1385 chi ∧
      ¬PredecessorHalfFin13Atom1390 chi ∧
      ¬PredecessorHalfFin13Atom1421 chi ∧
      ¬PredecessorHalfFin13Atom1456 chi ∧
      ¬PredecessorHalfFin13Atom2049 chi ∧
      ¬PredecessorHalfFin13Atom2051 chi ∧
      ¬PredecessorHalfFin13Atom2056 chi ∧
      ¬PredecessorHalfFin13Atom2087 chi ∧
      ¬PredecessorHalfFin13Atom2122 chi ∧
      ¬PredecessorHalfFin13Atom2192 chi) ∨
      ((¬PredecessorHalfFin13Atom1290 chi ∧
      ¬PredecessorHalfFin13Atom1291 chi ∧
      ¬PredecessorHalfFin13Atom1293 chi ∧
      ¬PredecessorHalfFin13Atom1309 chi ∧
      ¬PredecessorHalfFin13Atom1311 chi ∧
      ¬PredecessorHalfFin13Atom1313 chi ∧
      ¬PredecessorHalfFin13Atom1330 chi ∧
      ¬PredecessorHalfFin13Atom1332 chi ∧
      ¬PredecessorHalfFin13Atom1334 chi ∧
      ¬PredecessorHalfFin13Atom1368 chi ∧
      ¬PredecessorHalfFin13Atom1386 chi ∧
      ¬PredecessorHalfFin13Atom1388 chi ∧
      ¬PredecessorHalfFin13Atom1390 chi ∧
      ¬PredecessorHalfFin13Atom1424 chi ∧
      ¬PredecessorHalfFin13Atom1459 chi ∧
      ¬PredecessorHalfFin13Atom2052 chi ∧
      ¬PredecessorHalfFin13Atom2054 chi ∧
      ¬PredecessorHalfFin13Atom2056 chi ∧
      ¬PredecessorHalfFin13Atom2090 chi ∧
      ¬PredecessorHalfFin13Atom2125 chi ∧
      ¬PredecessorHalfFin13Atom2195 chi) ∨
      (¬PredecessorHalfFin13Atom1294 chi ∧
      ¬PredecessorHalfFin13Atom1295 chi ∧
      ¬PredecessorHalfFin13Atom1296 chi ∧
      ¬PredecessorHalfFin13Atom1300 chi ∧
      ¬PredecessorHalfFin13Atom1301 chi ∧
      ¬PredecessorHalfFin13Atom1305 chi ∧
      ¬PredecessorHalfFin13Atom1336 chi ∧
      ¬PredecessorHalfFin13Atom1337 chi ∧
      ¬PredecessorHalfFin13Atom1341 chi ∧
      ¬PredecessorHalfFin13Atom1351 chi ∧
      ¬PredecessorHalfFin13Atom1392 chi ∧
      ¬PredecessorHalfFin13Atom1393 chi ∧
      ¬PredecessorHalfFin13Atom1397 chi ∧
      ¬PredecessorHalfFin13Atom1407 chi ∧
      ¬PredecessorHalfFin13Atom1462 chi ∧
      ¬PredecessorHalfFin13Atom2058 chi ∧
      ¬PredecessorHalfFin13Atom2059 chi ∧
      ¬PredecessorHalfFin13Atom2063 chi ∧
      ¬PredecessorHalfFin13Atom2073 chi ∧
      ¬PredecessorHalfFin13Atom2128 chi ∧
      ¬PredecessorHalfFin13Atom2198 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1294 chi ∧
      ¬PredecessorHalfFin13Atom1295 chi ∧
      ¬PredecessorHalfFin13Atom1297 chi ∧
      ¬PredecessorHalfFin13Atom1300 chi ∧
      ¬PredecessorHalfFin13Atom1302 chi ∧
      ¬PredecessorHalfFin13Atom1306 chi ∧
      ¬PredecessorHalfFin13Atom1336 chi ∧
      ¬PredecessorHalfFin13Atom1338 chi ∧
      ¬PredecessorHalfFin13Atom1342 chi ∧
      ¬PredecessorHalfFin13Atom1352 chi ∧
      ¬PredecessorHalfFin13Atom1392 chi ∧
      ¬PredecessorHalfFin13Atom1394 chi ∧
      ¬PredecessorHalfFin13Atom1398 chi ∧
      ¬PredecessorHalfFin13Atom1408 chi ∧
      ¬PredecessorHalfFin13Atom1463 chi ∧
      ¬PredecessorHalfFin13Atom2058 chi ∧
      ¬PredecessorHalfFin13Atom2060 chi ∧
      ¬PredecessorHalfFin13Atom2064 chi ∧
      ¬PredecessorHalfFin13Atom2074 chi ∧
      ¬PredecessorHalfFin13Atom2129 chi ∧
      ¬PredecessorHalfFin13Atom2199 chi) ∨
      ((¬PredecessorHalfFin13Atom1294 chi ∧
      ¬PredecessorHalfFin13Atom1295 chi ∧
      ¬PredecessorHalfFin13Atom1299 chi ∧
      ¬PredecessorHalfFin13Atom1300 chi ∧
      ¬PredecessorHalfFin13Atom1304 chi ∧
      ¬PredecessorHalfFin13Atom1308 chi ∧
      ¬PredecessorHalfFin13Atom1336 chi ∧
      ¬PredecessorHalfFin13Atom1340 chi ∧
      ¬PredecessorHalfFin13Atom1344 chi ∧
      ¬PredecessorHalfFin13Atom1354 chi ∧
      ¬PredecessorHalfFin13Atom1392 chi ∧
      ¬PredecessorHalfFin13Atom1396 chi ∧
      ¬PredecessorHalfFin13Atom1400 chi ∧
      ¬PredecessorHalfFin13Atom1410 chi ∧
      ¬PredecessorHalfFin13Atom1465 chi ∧
      ¬PredecessorHalfFin13Atom2058 chi ∧
      ¬PredecessorHalfFin13Atom2062 chi ∧
      ¬PredecessorHalfFin13Atom2066 chi ∧
      ¬PredecessorHalfFin13Atom2076 chi ∧
      ¬PredecessorHalfFin13Atom2131 chi ∧
      ¬PredecessorHalfFin13Atom2201 chi) ∨
      (¬PredecessorHalfFin13Atom1294 chi ∧
      ¬PredecessorHalfFin13Atom1296 chi ∧
      ¬PredecessorHalfFin13Atom1297 chi ∧
      ¬PredecessorHalfFin13Atom1301 chi ∧
      ¬PredecessorHalfFin13Atom1302 chi ∧
      ¬PredecessorHalfFin13Atom1309 chi ∧
      ¬PredecessorHalfFin13Atom1337 chi ∧
      ¬PredecessorHalfFin13Atom1338 chi ∧
      ¬PredecessorHalfFin13Atom1345 chi ∧
      ¬PredecessorHalfFin13Atom1355 chi ∧
      ¬PredecessorHalfFin13Atom1393 chi ∧
      ¬PredecessorHalfFin13Atom1394 chi ∧
      ¬PredecessorHalfFin13Atom1401 chi ∧
      ¬PredecessorHalfFin13Atom1411 chi ∧
      ¬PredecessorHalfFin13Atom1466 chi ∧
      ¬PredecessorHalfFin13Atom2059 chi ∧
      ¬PredecessorHalfFin13Atom2060 chi ∧
      ¬PredecessorHalfFin13Atom2067 chi ∧
      ¬PredecessorHalfFin13Atom2077 chi ∧
      ¬PredecessorHalfFin13Atom2132 chi ∧
      ¬PredecessorHalfFin13Atom2202 chi))) ∨
      ((¬PredecessorHalfFin13Atom1294 chi ∧
      ¬PredecessorHalfFin13Atom1296 chi ∧
      ¬PredecessorHalfFin13Atom1299 chi ∧
      ¬PredecessorHalfFin13Atom1301 chi ∧
      ¬PredecessorHalfFin13Atom1304 chi ∧
      ¬PredecessorHalfFin13Atom1311 chi ∧
      ¬PredecessorHalfFin13Atom1337 chi ∧
      ¬PredecessorHalfFin13Atom1340 chi ∧
      ¬PredecessorHalfFin13Atom1347 chi ∧
      ¬PredecessorHalfFin13Atom1357 chi ∧
      ¬PredecessorHalfFin13Atom1393 chi ∧
      ¬PredecessorHalfFin13Atom1396 chi ∧
      ¬PredecessorHalfFin13Atom1403 chi ∧
      ¬PredecessorHalfFin13Atom1413 chi ∧
      ¬PredecessorHalfFin13Atom1468 chi ∧
      ¬PredecessorHalfFin13Atom2059 chi ∧
      ¬PredecessorHalfFin13Atom2062 chi ∧
      ¬PredecessorHalfFin13Atom2069 chi ∧
      ¬PredecessorHalfFin13Atom2079 chi ∧
      ¬PredecessorHalfFin13Atom2134 chi ∧
      ¬PredecessorHalfFin13Atom2204 chi) ∨
      ((¬PredecessorHalfFin13Atom1294 chi ∧
      ¬PredecessorHalfFin13Atom1297 chi ∧
      ¬PredecessorHalfFin13Atom1299 chi ∧
      ¬PredecessorHalfFin13Atom1302 chi ∧
      ¬PredecessorHalfFin13Atom1304 chi ∧
      ¬PredecessorHalfFin13Atom1313 chi ∧
      ¬PredecessorHalfFin13Atom1338 chi ∧
      ¬PredecessorHalfFin13Atom1340 chi ∧
      ¬PredecessorHalfFin13Atom1349 chi ∧
      ¬PredecessorHalfFin13Atom1359 chi ∧
      ¬PredecessorHalfFin13Atom1394 chi ∧
      ¬PredecessorHalfFin13Atom1396 chi ∧
      ¬PredecessorHalfFin13Atom1405 chi ∧
      ¬PredecessorHalfFin13Atom1415 chi ∧
      ¬PredecessorHalfFin13Atom1470 chi ∧
      ¬PredecessorHalfFin13Atom2060 chi ∧
      ¬PredecessorHalfFin13Atom2062 chi ∧
      ¬PredecessorHalfFin13Atom2071 chi ∧
      ¬PredecessorHalfFin13Atom2081 chi ∧
      ¬PredecessorHalfFin13Atom2136 chi ∧
      ¬PredecessorHalfFin13Atom2206 chi) ∨
      (¬PredecessorHalfFin13Atom1295 chi ∧
      ¬PredecessorHalfFin13Atom1296 chi ∧
      ¬PredecessorHalfFin13Atom1297 chi ∧
      ¬PredecessorHalfFin13Atom1305 chi ∧
      ¬PredecessorHalfFin13Atom1306 chi ∧
      ¬PredecessorHalfFin13Atom1309 chi ∧
      ¬PredecessorHalfFin13Atom1341 chi ∧
      ¬PredecessorHalfFin13Atom1342 chi ∧
      ¬PredecessorHalfFin13Atom1345 chi ∧
      ¬PredecessorHalfFin13Atom1361 chi ∧
      ¬PredecessorHalfFin13Atom1397 chi ∧
      ¬PredecessorHalfFin13Atom1398 chi ∧
      ¬PredecessorHalfFin13Atom1401 chi ∧
      ¬PredecessorHalfFin13Atom1417 chi ∧
      ¬PredecessorHalfFin13Atom1472 chi ∧
      ¬PredecessorHalfFin13Atom2063 chi ∧
      ¬PredecessorHalfFin13Atom2064 chi ∧
      ¬PredecessorHalfFin13Atom2067 chi ∧
      ¬PredecessorHalfFin13Atom2083 chi ∧
      ¬PredecessorHalfFin13Atom2138 chi ∧
      ¬PredecessorHalfFin13Atom2208 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom1295 chi ∧
      ¬PredecessorHalfFin13Atom1296 chi ∧
      ¬PredecessorHalfFin13Atom1299 chi ∧
      ¬PredecessorHalfFin13Atom1305 chi ∧
      ¬PredecessorHalfFin13Atom1308 chi ∧
      ¬PredecessorHalfFin13Atom1311 chi ∧
      ¬PredecessorHalfFin13Atom1341 chi ∧
      ¬PredecessorHalfFin13Atom1344 chi ∧
      ¬PredecessorHalfFin13Atom1347 chi ∧
      ¬PredecessorHalfFin13Atom1363 chi ∧
      ¬PredecessorHalfFin13Atom1397 chi ∧
      ¬PredecessorHalfFin13Atom1400 chi ∧
      ¬PredecessorHalfFin13Atom1403 chi ∧
      ¬PredecessorHalfFin13Atom1419 chi ∧
      ¬PredecessorHalfFin13Atom1474 chi ∧
      ¬PredecessorHalfFin13Atom2063 chi ∧
      ¬PredecessorHalfFin13Atom2066 chi ∧
      ¬PredecessorHalfFin13Atom2069 chi ∧
      ¬PredecessorHalfFin13Atom2085 chi ∧
      ¬PredecessorHalfFin13Atom2140 chi ∧
      ¬PredecessorHalfFin13Atom2210 chi) ∨
      ((¬PredecessorHalfFin13Atom1295 chi ∧
      ¬PredecessorHalfFin13Atom1297 chi ∧
      ¬PredecessorHalfFin13Atom1299 chi ∧
      ¬PredecessorHalfFin13Atom1306 chi ∧
      ¬PredecessorHalfFin13Atom1308 chi ∧
      ¬PredecessorHalfFin13Atom1313 chi ∧
      ¬PredecessorHalfFin13Atom1342 chi ∧
      ¬PredecessorHalfFin13Atom1344 chi ∧
      ¬PredecessorHalfFin13Atom1349 chi ∧
      ¬PredecessorHalfFin13Atom1365 chi ∧
      ¬PredecessorHalfFin13Atom1398 chi ∧
      ¬PredecessorHalfFin13Atom1400 chi ∧
      ¬PredecessorHalfFin13Atom1405 chi ∧
      ¬PredecessorHalfFin13Atom1421 chi ∧
      ¬PredecessorHalfFin13Atom1476 chi ∧
      ¬PredecessorHalfFin13Atom2064 chi ∧
      ¬PredecessorHalfFin13Atom2066 chi ∧
      ¬PredecessorHalfFin13Atom2071 chi ∧
      ¬PredecessorHalfFin13Atom2087 chi ∧
      ¬PredecessorHalfFin13Atom2142 chi ∧
      ¬PredecessorHalfFin13Atom2212 chi) ∨
      (¬PredecessorHalfFin13Atom1296 chi ∧
      ¬PredecessorHalfFin13Atom1297 chi ∧
      ¬PredecessorHalfFin13Atom1299 chi ∧
      ¬PredecessorHalfFin13Atom1309 chi ∧
      ¬PredecessorHalfFin13Atom1311 chi ∧
      ¬PredecessorHalfFin13Atom1313 chi ∧
      ¬PredecessorHalfFin13Atom1345 chi ∧
      ¬PredecessorHalfFin13Atom1347 chi ∧
      ¬PredecessorHalfFin13Atom1349 chi ∧
      ¬PredecessorHalfFin13Atom1368 chi ∧
      ¬PredecessorHalfFin13Atom1401 chi ∧
      ¬PredecessorHalfFin13Atom1403 chi ∧
      ¬PredecessorHalfFin13Atom1405 chi ∧
      ¬PredecessorHalfFin13Atom1424 chi ∧
      ¬PredecessorHalfFin13Atom1479 chi ∧
      ¬PredecessorHalfFin13Atom2067 chi ∧
      ¬PredecessorHalfFin13Atom2069 chi ∧
      ¬PredecessorHalfFin13Atom2071 chi ∧
      ¬PredecessorHalfFin13Atom2090 chi ∧
      ¬PredecessorHalfFin13Atom2145 chi ∧
      ¬PredecessorHalfFin13Atom2215 chi))) ∨
      ((¬PredecessorHalfFin13Atom1300 chi ∧
      ¬PredecessorHalfFin13Atom1301 chi ∧
      ¬PredecessorHalfFin13Atom1302 chi ∧
      ¬PredecessorHalfFin13Atom1305 chi ∧
      ¬PredecessorHalfFin13Atom1306 chi ∧
      ¬PredecessorHalfFin13Atom1309 chi ∧
      ¬PredecessorHalfFin13Atom1351 chi ∧
      ¬PredecessorHalfFin13Atom1352 chi ∧
      ¬PredecessorHalfFin13Atom1355 chi ∧
      ¬PredecessorHalfFin13Atom1361 chi ∧
      ¬PredecessorHalfFin13Atom1407 chi ∧
      ¬PredecessorHalfFin13Atom1408 chi ∧
      ¬PredecessorHalfFin13Atom1411 chi ∧
      ¬PredecessorHalfFin13Atom1417 chi ∧
      ¬PredecessorHalfFin13Atom1482 chi ∧
      ¬PredecessorHalfFin13Atom2073 chi ∧
      ¬PredecessorHalfFin13Atom2074 chi ∧
      ¬PredecessorHalfFin13Atom2077 chi ∧
      ¬PredecessorHalfFin13Atom2083 chi ∧
      ¬PredecessorHalfFin13Atom2148 chi ∧
      ¬PredecessorHalfFin13Atom2218 chi) ∨
      ((¬PredecessorHalfFin13Atom1300 chi ∧
      ¬PredecessorHalfFin13Atom1301 chi ∧
      ¬PredecessorHalfFin13Atom1304 chi ∧
      ¬PredecessorHalfFin13Atom1305 chi ∧
      ¬PredecessorHalfFin13Atom1308 chi ∧
      ¬PredecessorHalfFin13Atom1311 chi ∧
      ¬PredecessorHalfFin13Atom1351 chi ∧
      ¬PredecessorHalfFin13Atom1354 chi ∧
      ¬PredecessorHalfFin13Atom1357 chi ∧
      ¬PredecessorHalfFin13Atom1363 chi ∧
      ¬PredecessorHalfFin13Atom1407 chi ∧
      ¬PredecessorHalfFin13Atom1410 chi ∧
      ¬PredecessorHalfFin13Atom1413 chi ∧
      ¬PredecessorHalfFin13Atom1419 chi ∧
      ¬PredecessorHalfFin13Atom1484 chi ∧
      ¬PredecessorHalfFin13Atom2073 chi ∧
      ¬PredecessorHalfFin13Atom2076 chi ∧
      ¬PredecessorHalfFin13Atom2079 chi ∧
      ¬PredecessorHalfFin13Atom2085 chi ∧
      ¬PredecessorHalfFin13Atom2150 chi ∧
      ¬PredecessorHalfFin13Atom2220 chi) ∨
      (¬PredecessorHalfFin13Atom1300 chi ∧
      ¬PredecessorHalfFin13Atom1302 chi ∧
      ¬PredecessorHalfFin13Atom1304 chi ∧
      ¬PredecessorHalfFin13Atom1306 chi ∧
      ¬PredecessorHalfFin13Atom1308 chi ∧
      ¬PredecessorHalfFin13Atom1313 chi ∧
      ¬PredecessorHalfFin13Atom1352 chi ∧
      ¬PredecessorHalfFin13Atom1354 chi ∧
      ¬PredecessorHalfFin13Atom1359 chi ∧
      ¬PredecessorHalfFin13Atom1365 chi ∧
      ¬PredecessorHalfFin13Atom1408 chi ∧
      ¬PredecessorHalfFin13Atom1410 chi ∧
      ¬PredecessorHalfFin13Atom1415 chi ∧
      ¬PredecessorHalfFin13Atom1421 chi ∧
      ¬PredecessorHalfFin13Atom1486 chi ∧
      ¬PredecessorHalfFin13Atom2074 chi ∧
      ¬PredecessorHalfFin13Atom2076 chi ∧
      ¬PredecessorHalfFin13Atom2081 chi ∧
      ¬PredecessorHalfFin13Atom2087 chi ∧
      ¬PredecessorHalfFin13Atom2152 chi ∧
      ¬PredecessorHalfFin13Atom2222 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1301 chi ∧
      ¬PredecessorHalfFin13Atom1302 chi ∧
      ¬PredecessorHalfFin13Atom1304 chi ∧
      ¬PredecessorHalfFin13Atom1309 chi ∧
      ¬PredecessorHalfFin13Atom1311 chi ∧
      ¬PredecessorHalfFin13Atom1313 chi ∧
      ¬PredecessorHalfFin13Atom1355 chi ∧
      ¬PredecessorHalfFin13Atom1357 chi ∧
      ¬PredecessorHalfFin13Atom1359 chi ∧
      ¬PredecessorHalfFin13Atom1368 chi ∧
      ¬PredecessorHalfFin13Atom1411 chi ∧
      ¬PredecessorHalfFin13Atom1413 chi ∧
      ¬PredecessorHalfFin13Atom1415 chi ∧
      ¬PredecessorHalfFin13Atom1424 chi ∧
      ¬PredecessorHalfFin13Atom1489 chi ∧
      ¬PredecessorHalfFin13Atom2077 chi ∧
      ¬PredecessorHalfFin13Atom2079 chi ∧
      ¬PredecessorHalfFin13Atom2081 chi ∧
      ¬PredecessorHalfFin13Atom2090 chi ∧
      ¬PredecessorHalfFin13Atom2155 chi ∧
      ¬PredecessorHalfFin13Atom2225 chi) ∨
      ((¬PredecessorHalfFin13Atom1305 chi ∧
      ¬PredecessorHalfFin13Atom1306 chi ∧
      ¬PredecessorHalfFin13Atom1308 chi ∧
      ¬PredecessorHalfFin13Atom1309 chi ∧
      ¬PredecessorHalfFin13Atom1311 chi ∧
      ¬PredecessorHalfFin13Atom1313 chi ∧
      ¬PredecessorHalfFin13Atom1361 chi ∧
      ¬PredecessorHalfFin13Atom1363 chi ∧
      ¬PredecessorHalfFin13Atom1365 chi ∧
      ¬PredecessorHalfFin13Atom1368 chi ∧
      ¬PredecessorHalfFin13Atom1417 chi ∧
      ¬PredecessorHalfFin13Atom1419 chi ∧
      ¬PredecessorHalfFin13Atom1421 chi ∧
      ¬PredecessorHalfFin13Atom1424 chi ∧
      ¬PredecessorHalfFin13Atom1493 chi ∧
      ¬PredecessorHalfFin13Atom2083 chi ∧
      ¬PredecessorHalfFin13Atom2085 chi ∧
      ¬PredecessorHalfFin13Atom2087 chi ∧
      ¬PredecessorHalfFin13Atom2090 chi ∧
      ¬PredecessorHalfFin13Atom2159 chi ∧
      ¬PredecessorHalfFin13Atom2229 chi) ∨
      (¬PredecessorHalfFin13Atom1315 chi ∧
      ¬PredecessorHalfFin13Atom1316 chi ∧
      ¬PredecessorHalfFin13Atom1317 chi ∧
      ¬PredecessorHalfFin13Atom1321 chi ∧
      ¬PredecessorHalfFin13Atom1322 chi ∧
      ¬PredecessorHalfFin13Atom1326 chi ∧
      ¬PredecessorHalfFin13Atom1336 chi ∧
      ¬PredecessorHalfFin13Atom1337 chi ∧
      ¬PredecessorHalfFin13Atom1341 chi ∧
      ¬PredecessorHalfFin13Atom1351 chi ∧
      ¬PredecessorHalfFin13Atom1427 chi ∧
      ¬PredecessorHalfFin13Atom1428 chi ∧
      ¬PredecessorHalfFin13Atom1432 chi ∧
      ¬PredecessorHalfFin13Atom1442 chi ∧
      ¬PredecessorHalfFin13Atom1462 chi ∧
      ¬PredecessorHalfFin13Atom2093 chi ∧
      ¬PredecessorHalfFin13Atom2094 chi ∧
      ¬PredecessorHalfFin13Atom2098 chi ∧
      ¬PredecessorHalfFin13Atom2108 chi ∧
      ¬PredecessorHalfFin13Atom2128 chi ∧
      ¬PredecessorHalfFin13Atom2233 chi))) ∨
      ((¬PredecessorHalfFin13Atom1315 chi ∧
      ¬PredecessorHalfFin13Atom1316 chi ∧
      ¬PredecessorHalfFin13Atom1318 chi ∧
      ¬PredecessorHalfFin13Atom1321 chi ∧
      ¬PredecessorHalfFin13Atom1323 chi ∧
      ¬PredecessorHalfFin13Atom1327 chi ∧
      ¬PredecessorHalfFin13Atom1336 chi ∧
      ¬PredecessorHalfFin13Atom1338 chi ∧
      ¬PredecessorHalfFin13Atom1342 chi ∧
      ¬PredecessorHalfFin13Atom1352 chi ∧
      ¬PredecessorHalfFin13Atom1427 chi ∧
      ¬PredecessorHalfFin13Atom1429 chi ∧
      ¬PredecessorHalfFin13Atom1433 chi ∧
      ¬PredecessorHalfFin13Atom1443 chi ∧
      ¬PredecessorHalfFin13Atom1463 chi ∧
      ¬PredecessorHalfFin13Atom2093 chi ∧
      ¬PredecessorHalfFin13Atom2095 chi ∧
      ¬PredecessorHalfFin13Atom2099 chi ∧
      ¬PredecessorHalfFin13Atom2109 chi ∧
      ¬PredecessorHalfFin13Atom2129 chi ∧
      ¬PredecessorHalfFin13Atom2234 chi) ∨
      ((¬PredecessorHalfFin13Atom1315 chi ∧
      ¬PredecessorHalfFin13Atom1316 chi ∧
      ¬PredecessorHalfFin13Atom1320 chi ∧
      ¬PredecessorHalfFin13Atom1321 chi ∧
      ¬PredecessorHalfFin13Atom1325 chi ∧
      ¬PredecessorHalfFin13Atom1329 chi ∧
      ¬PredecessorHalfFin13Atom1336 chi ∧
      ¬PredecessorHalfFin13Atom1340 chi ∧
      ¬PredecessorHalfFin13Atom1344 chi ∧
      ¬PredecessorHalfFin13Atom1354 chi ∧
      ¬PredecessorHalfFin13Atom1427 chi ∧
      ¬PredecessorHalfFin13Atom1431 chi ∧
      ¬PredecessorHalfFin13Atom1435 chi ∧
      ¬PredecessorHalfFin13Atom1445 chi ∧
      ¬PredecessorHalfFin13Atom1465 chi ∧
      ¬PredecessorHalfFin13Atom2093 chi ∧
      ¬PredecessorHalfFin13Atom2097 chi ∧
      ¬PredecessorHalfFin13Atom2101 chi ∧
      ¬PredecessorHalfFin13Atom2111 chi ∧
      ¬PredecessorHalfFin13Atom2131 chi ∧
      ¬PredecessorHalfFin13Atom2236 chi) ∨
      (¬PredecessorHalfFin13Atom1315 chi ∧
      ¬PredecessorHalfFin13Atom1317 chi ∧
      ¬PredecessorHalfFin13Atom1318 chi ∧
      ¬PredecessorHalfFin13Atom1322 chi ∧
      ¬PredecessorHalfFin13Atom1323 chi ∧
      ¬PredecessorHalfFin13Atom1330 chi ∧
      ¬PredecessorHalfFin13Atom1337 chi ∧
      ¬PredecessorHalfFin13Atom1338 chi ∧
      ¬PredecessorHalfFin13Atom1345 chi ∧
      ¬PredecessorHalfFin13Atom1355 chi ∧
      ¬PredecessorHalfFin13Atom1428 chi ∧
      ¬PredecessorHalfFin13Atom1429 chi ∧
      ¬PredecessorHalfFin13Atom1436 chi ∧
      ¬PredecessorHalfFin13Atom1446 chi ∧
      ¬PredecessorHalfFin13Atom1466 chi ∧
      ¬PredecessorHalfFin13Atom2094 chi ∧
      ¬PredecessorHalfFin13Atom2095 chi ∧
      ¬PredecessorHalfFin13Atom2102 chi ∧
      ¬PredecessorHalfFin13Atom2112 chi ∧
      ¬PredecessorHalfFin13Atom2132 chi ∧
      ¬PredecessorHalfFin13Atom2237 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom1315 chi ∧
      ¬PredecessorHalfFin13Atom1317 chi ∧
      ¬PredecessorHalfFin13Atom1320 chi ∧
      ¬PredecessorHalfFin13Atom1322 chi ∧
      ¬PredecessorHalfFin13Atom1325 chi ∧
      ¬PredecessorHalfFin13Atom1332 chi ∧
      ¬PredecessorHalfFin13Atom1337 chi ∧
      ¬PredecessorHalfFin13Atom1340 chi ∧
      ¬PredecessorHalfFin13Atom1347 chi ∧
      ¬PredecessorHalfFin13Atom1357 chi ∧
      ¬PredecessorHalfFin13Atom1428 chi ∧
      ¬PredecessorHalfFin13Atom1431 chi ∧
      ¬PredecessorHalfFin13Atom1438 chi ∧
      ¬PredecessorHalfFin13Atom1448 chi ∧
      ¬PredecessorHalfFin13Atom1468 chi ∧
      ¬PredecessorHalfFin13Atom2094 chi ∧
      ¬PredecessorHalfFin13Atom2097 chi ∧
      ¬PredecessorHalfFin13Atom2104 chi ∧
      ¬PredecessorHalfFin13Atom2114 chi ∧
      ¬PredecessorHalfFin13Atom2134 chi ∧
      ¬PredecessorHalfFin13Atom2239 chi) ∨
      ((¬PredecessorHalfFin13Atom1315 chi ∧
      ¬PredecessorHalfFin13Atom1318 chi ∧
      ¬PredecessorHalfFin13Atom1320 chi ∧
      ¬PredecessorHalfFin13Atom1323 chi ∧
      ¬PredecessorHalfFin13Atom1325 chi ∧
      ¬PredecessorHalfFin13Atom1334 chi ∧
      ¬PredecessorHalfFin13Atom1338 chi ∧
      ¬PredecessorHalfFin13Atom1340 chi ∧
      ¬PredecessorHalfFin13Atom1349 chi ∧
      ¬PredecessorHalfFin13Atom1359 chi ∧
      ¬PredecessorHalfFin13Atom1429 chi ∧
      ¬PredecessorHalfFin13Atom1431 chi ∧
      ¬PredecessorHalfFin13Atom1440 chi ∧
      ¬PredecessorHalfFin13Atom1450 chi ∧
      ¬PredecessorHalfFin13Atom1470 chi ∧
      ¬PredecessorHalfFin13Atom2095 chi ∧
      ¬PredecessorHalfFin13Atom2097 chi ∧
      ¬PredecessorHalfFin13Atom2106 chi ∧
      ¬PredecessorHalfFin13Atom2116 chi ∧
      ¬PredecessorHalfFin13Atom2136 chi ∧
      ¬PredecessorHalfFin13Atom2241 chi) ∨
      (¬PredecessorHalfFin13Atom1316 chi ∧
      ¬PredecessorHalfFin13Atom1317 chi ∧
      ¬PredecessorHalfFin13Atom1318 chi ∧
      ¬PredecessorHalfFin13Atom1326 chi ∧
      ¬PredecessorHalfFin13Atom1327 chi ∧
      ¬PredecessorHalfFin13Atom1330 chi ∧
      ¬PredecessorHalfFin13Atom1341 chi ∧
      ¬PredecessorHalfFin13Atom1342 chi ∧
      ¬PredecessorHalfFin13Atom1345 chi ∧
      ¬PredecessorHalfFin13Atom1361 chi ∧
      ¬PredecessorHalfFin13Atom1432 chi ∧
      ¬PredecessorHalfFin13Atom1433 chi ∧
      ¬PredecessorHalfFin13Atom1436 chi ∧
      ¬PredecessorHalfFin13Atom1452 chi ∧
      ¬PredecessorHalfFin13Atom1472 chi ∧
      ¬PredecessorHalfFin13Atom2098 chi ∧
      ¬PredecessorHalfFin13Atom2099 chi ∧
      ¬PredecessorHalfFin13Atom2102 chi ∧
      ¬PredecessorHalfFin13Atom2118 chi ∧
      ¬PredecessorHalfFin13Atom2138 chi ∧
      ¬PredecessorHalfFin13Atom2243 chi))) ∨
      ((¬PredecessorHalfFin13Atom1316 chi ∧
      ¬PredecessorHalfFin13Atom1317 chi ∧
      ¬PredecessorHalfFin13Atom1320 chi ∧
      ¬PredecessorHalfFin13Atom1326 chi ∧
      ¬PredecessorHalfFin13Atom1329 chi ∧
      ¬PredecessorHalfFin13Atom1332 chi ∧
      ¬PredecessorHalfFin13Atom1341 chi ∧
      ¬PredecessorHalfFin13Atom1344 chi ∧
      ¬PredecessorHalfFin13Atom1347 chi ∧
      ¬PredecessorHalfFin13Atom1363 chi ∧
      ¬PredecessorHalfFin13Atom1432 chi ∧
      ¬PredecessorHalfFin13Atom1435 chi ∧
      ¬PredecessorHalfFin13Atom1438 chi ∧
      ¬PredecessorHalfFin13Atom1454 chi ∧
      ¬PredecessorHalfFin13Atom1474 chi ∧
      ¬PredecessorHalfFin13Atom2098 chi ∧
      ¬PredecessorHalfFin13Atom2101 chi ∧
      ¬PredecessorHalfFin13Atom2104 chi ∧
      ¬PredecessorHalfFin13Atom2120 chi ∧
      ¬PredecessorHalfFin13Atom2140 chi ∧
      ¬PredecessorHalfFin13Atom2245 chi) ∨
      ((¬PredecessorHalfFin13Atom1316 chi ∧
      ¬PredecessorHalfFin13Atom1318 chi ∧
      ¬PredecessorHalfFin13Atom1320 chi ∧
      ¬PredecessorHalfFin13Atom1327 chi ∧
      ¬PredecessorHalfFin13Atom1329 chi ∧
      ¬PredecessorHalfFin13Atom1334 chi ∧
      ¬PredecessorHalfFin13Atom1342 chi ∧
      ¬PredecessorHalfFin13Atom1344 chi ∧
      ¬PredecessorHalfFin13Atom1349 chi ∧
      ¬PredecessorHalfFin13Atom1365 chi ∧
      ¬PredecessorHalfFin13Atom1433 chi ∧
      ¬PredecessorHalfFin13Atom1435 chi ∧
      ¬PredecessorHalfFin13Atom1440 chi ∧
      ¬PredecessorHalfFin13Atom1456 chi ∧
      ¬PredecessorHalfFin13Atom1476 chi ∧
      ¬PredecessorHalfFin13Atom2099 chi ∧
      ¬PredecessorHalfFin13Atom2101 chi ∧
      ¬PredecessorHalfFin13Atom2106 chi ∧
      ¬PredecessorHalfFin13Atom2122 chi ∧
      ¬PredecessorHalfFin13Atom2142 chi ∧
      ¬PredecessorHalfFin13Atom2247 chi) ∨
      (¬PredecessorHalfFin13Atom1317 chi ∧
      ¬PredecessorHalfFin13Atom1318 chi ∧
      ¬PredecessorHalfFin13Atom1320 chi ∧
      ¬PredecessorHalfFin13Atom1330 chi ∧
      ¬PredecessorHalfFin13Atom1332 chi ∧
      ¬PredecessorHalfFin13Atom1334 chi ∧
      ¬PredecessorHalfFin13Atom1345 chi ∧
      ¬PredecessorHalfFin13Atom1347 chi ∧
      ¬PredecessorHalfFin13Atom1349 chi ∧
      ¬PredecessorHalfFin13Atom1368 chi ∧
      ¬PredecessorHalfFin13Atom1436 chi ∧
      ¬PredecessorHalfFin13Atom1438 chi ∧
      ¬PredecessorHalfFin13Atom1440 chi ∧
      ¬PredecessorHalfFin13Atom1459 chi ∧
      ¬PredecessorHalfFin13Atom1479 chi ∧
      ¬PredecessorHalfFin13Atom2102 chi ∧
      ¬PredecessorHalfFin13Atom2104 chi ∧
      ¬PredecessorHalfFin13Atom2106 chi ∧
      ¬PredecessorHalfFin13Atom2125 chi ∧
      ¬PredecessorHalfFin13Atom2145 chi ∧
      ¬PredecessorHalfFin13Atom2250 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1321 chi ∧
      ¬PredecessorHalfFin13Atom1322 chi ∧
      ¬PredecessorHalfFin13Atom1323 chi ∧
      ¬PredecessorHalfFin13Atom1326 chi ∧
      ¬PredecessorHalfFin13Atom1327 chi ∧
      ¬PredecessorHalfFin13Atom1330 chi ∧
      ¬PredecessorHalfFin13Atom1351 chi ∧
      ¬PredecessorHalfFin13Atom1352 chi ∧
      ¬PredecessorHalfFin13Atom1355 chi ∧
      ¬PredecessorHalfFin13Atom1361 chi ∧
      ¬PredecessorHalfFin13Atom1442 chi ∧
      ¬PredecessorHalfFin13Atom1443 chi ∧
      ¬PredecessorHalfFin13Atom1446 chi ∧
      ¬PredecessorHalfFin13Atom1452 chi ∧
      ¬PredecessorHalfFin13Atom1482 chi ∧
      ¬PredecessorHalfFin13Atom2108 chi ∧
      ¬PredecessorHalfFin13Atom2109 chi ∧
      ¬PredecessorHalfFin13Atom2112 chi ∧
      ¬PredecessorHalfFin13Atom2118 chi ∧
      ¬PredecessorHalfFin13Atom2148 chi ∧
      ¬PredecessorHalfFin13Atom2253 chi) ∨
      ((¬PredecessorHalfFin13Atom1321 chi ∧
      ¬PredecessorHalfFin13Atom1322 chi ∧
      ¬PredecessorHalfFin13Atom1325 chi ∧
      ¬PredecessorHalfFin13Atom1326 chi ∧
      ¬PredecessorHalfFin13Atom1329 chi ∧
      ¬PredecessorHalfFin13Atom1332 chi ∧
      ¬PredecessorHalfFin13Atom1351 chi ∧
      ¬PredecessorHalfFin13Atom1354 chi ∧
      ¬PredecessorHalfFin13Atom1357 chi ∧
      ¬PredecessorHalfFin13Atom1363 chi ∧
      ¬PredecessorHalfFin13Atom1442 chi ∧
      ¬PredecessorHalfFin13Atom1445 chi ∧
      ¬PredecessorHalfFin13Atom1448 chi ∧
      ¬PredecessorHalfFin13Atom1454 chi ∧
      ¬PredecessorHalfFin13Atom1484 chi ∧
      ¬PredecessorHalfFin13Atom2108 chi ∧
      ¬PredecessorHalfFin13Atom2111 chi ∧
      ¬PredecessorHalfFin13Atom2114 chi ∧
      ¬PredecessorHalfFin13Atom2120 chi ∧
      ¬PredecessorHalfFin13Atom2150 chi ∧
      ¬PredecessorHalfFin13Atom2255 chi) ∨
      (¬PredecessorHalfFin13Atom1321 chi ∧
      ¬PredecessorHalfFin13Atom1323 chi ∧
      ¬PredecessorHalfFin13Atom1325 chi ∧
      ¬PredecessorHalfFin13Atom1327 chi ∧
      ¬PredecessorHalfFin13Atom1329 chi ∧
      ¬PredecessorHalfFin13Atom1334 chi ∧
      ¬PredecessorHalfFin13Atom1352 chi ∧
      ¬PredecessorHalfFin13Atom1354 chi ∧
      ¬PredecessorHalfFin13Atom1359 chi ∧
      ¬PredecessorHalfFin13Atom1365 chi ∧
      ¬PredecessorHalfFin13Atom1443 chi ∧
      ¬PredecessorHalfFin13Atom1445 chi ∧
      ¬PredecessorHalfFin13Atom1450 chi ∧
      ¬PredecessorHalfFin13Atom1456 chi ∧
      ¬PredecessorHalfFin13Atom1486 chi ∧
      ¬PredecessorHalfFin13Atom2109 chi ∧
      ¬PredecessorHalfFin13Atom2111 chi ∧
      ¬PredecessorHalfFin13Atom2116 chi ∧
      ¬PredecessorHalfFin13Atom2122 chi ∧
      ¬PredecessorHalfFin13Atom2152 chi ∧
      ¬PredecessorHalfFin13Atom2257 chi))) ∨
      (((¬PredecessorHalfFin13Atom1322 chi ∧
      ¬PredecessorHalfFin13Atom1323 chi ∧
      ¬PredecessorHalfFin13Atom1325 chi ∧
      ¬PredecessorHalfFin13Atom1330 chi ∧
      ¬PredecessorHalfFin13Atom1332 chi ∧
      ¬PredecessorHalfFin13Atom1334 chi ∧
      ¬PredecessorHalfFin13Atom1355 chi ∧
      ¬PredecessorHalfFin13Atom1357 chi ∧
      ¬PredecessorHalfFin13Atom1359 chi ∧
      ¬PredecessorHalfFin13Atom1368 chi ∧
      ¬PredecessorHalfFin13Atom1446 chi ∧
      ¬PredecessorHalfFin13Atom1448 chi ∧
      ¬PredecessorHalfFin13Atom1450 chi ∧
      ¬PredecessorHalfFin13Atom1459 chi ∧
      ¬PredecessorHalfFin13Atom1489 chi ∧
      ¬PredecessorHalfFin13Atom2112 chi ∧
      ¬PredecessorHalfFin13Atom2114 chi ∧
      ¬PredecessorHalfFin13Atom2116 chi ∧
      ¬PredecessorHalfFin13Atom2125 chi ∧
      ¬PredecessorHalfFin13Atom2155 chi ∧
      ¬PredecessorHalfFin13Atom2260 chi) ∨
      (¬PredecessorHalfFin13Atom1326 chi ∧
      ¬PredecessorHalfFin13Atom1327 chi ∧
      ¬PredecessorHalfFin13Atom1329 chi ∧
      ¬PredecessorHalfFin13Atom1330 chi ∧
      ¬PredecessorHalfFin13Atom1332 chi ∧
      ¬PredecessorHalfFin13Atom1334 chi ∧
      ¬PredecessorHalfFin13Atom1361 chi ∧
      ¬PredecessorHalfFin13Atom1363 chi ∧
      ¬PredecessorHalfFin13Atom1365 chi ∧
      ¬PredecessorHalfFin13Atom1368 chi ∧
      ¬PredecessorHalfFin13Atom1452 chi ∧
      ¬PredecessorHalfFin13Atom1454 chi ∧
      ¬PredecessorHalfFin13Atom1456 chi ∧
      ¬PredecessorHalfFin13Atom1459 chi ∧
      ¬PredecessorHalfFin13Atom1493 chi ∧
      ¬PredecessorHalfFin13Atom2118 chi ∧
      ¬PredecessorHalfFin13Atom2120 chi ∧
      ¬PredecessorHalfFin13Atom2122 chi ∧
      ¬PredecessorHalfFin13Atom2125 chi ∧
      ¬PredecessorHalfFin13Atom2159 chi ∧
      ¬PredecessorHalfFin13Atom2264 chi)) ∨
      ((¬PredecessorHalfFin13Atom1336 chi ∧
      ¬PredecessorHalfFin13Atom1337 chi ∧
      ¬PredecessorHalfFin13Atom1338 chi ∧
      ¬PredecessorHalfFin13Atom1341 chi ∧
      ¬PredecessorHalfFin13Atom1342 chi ∧
      ¬PredecessorHalfFin13Atom1345 chi ∧
      ¬PredecessorHalfFin13Atom1351 chi ∧
      ¬PredecessorHalfFin13Atom1352 chi ∧
      ¬PredecessorHalfFin13Atom1355 chi ∧
      ¬PredecessorHalfFin13Atom1361 chi ∧
      ¬PredecessorHalfFin13Atom1462 chi ∧
      ¬PredecessorHalfFin13Atom1463 chi ∧
      ¬PredecessorHalfFin13Atom1466 chi ∧
      ¬PredecessorHalfFin13Atom1472 chi ∧
      ¬PredecessorHalfFin13Atom1482 chi ∧
      ¬PredecessorHalfFin13Atom2128 chi ∧
      ¬PredecessorHalfFin13Atom2129 chi ∧
      ¬PredecessorHalfFin13Atom2132 chi ∧
      ¬PredecessorHalfFin13Atom2138 chi ∧
      ¬PredecessorHalfFin13Atom2148 chi ∧
      ¬PredecessorHalfFin13Atom2268 chi) ∨
      (¬PredecessorHalfFin13Atom1336 chi ∧
      ¬PredecessorHalfFin13Atom1337 chi ∧
      ¬PredecessorHalfFin13Atom1340 chi ∧
      ¬PredecessorHalfFin13Atom1341 chi ∧
      ¬PredecessorHalfFin13Atom1344 chi ∧
      ¬PredecessorHalfFin13Atom1347 chi ∧
      ¬PredecessorHalfFin13Atom1351 chi ∧
      ¬PredecessorHalfFin13Atom1354 chi ∧
      ¬PredecessorHalfFin13Atom1357 chi ∧
      ¬PredecessorHalfFin13Atom1363 chi ∧
      ¬PredecessorHalfFin13Atom1462 chi ∧
      ¬PredecessorHalfFin13Atom1465 chi ∧
      ¬PredecessorHalfFin13Atom1468 chi ∧
      ¬PredecessorHalfFin13Atom1474 chi ∧
      ¬PredecessorHalfFin13Atom1484 chi ∧
      ¬PredecessorHalfFin13Atom2128 chi ∧
      ¬PredecessorHalfFin13Atom2131 chi ∧
      ¬PredecessorHalfFin13Atom2134 chi ∧
      ¬PredecessorHalfFin13Atom2140 chi ∧
      ¬PredecessorHalfFin13Atom2150 chi ∧
      ¬PredecessorHalfFin13Atom2270 chi))))))))) := by
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
              exact predecessorHalfFin13_clause27202 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27203 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27205 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27206 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27208 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27210 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27212 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27214 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27216 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27219 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27222 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27223 chi hno hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27225 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27226 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27228 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27230 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27232 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27234 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27236 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27239 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27242 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27244 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27246 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27249 chi hno hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27253 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27257 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27258 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27260 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27261 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27263 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27265 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27267 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27269 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27271 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27274 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27277 chi hno hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27279 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27281 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27284 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27288 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27292 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27294 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27296 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27299 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27303 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27308 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27313 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27314 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27315 chi hno hbad
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
              exact predecessorHalfFin13_clause27317 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27318 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27319 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27321 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27322 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27324 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27326 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27328 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27329 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27331 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27332 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27334 chi hno hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27336 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27338 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27340 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27342 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27345 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27348 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27349 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27351 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27352 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27354 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27356 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27358 chi hno hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27360 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27362 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27365 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27368 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27370 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27372 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27375 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27379 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27383 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27384 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27386 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27387 chi hno hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27389 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27391 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27393 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27395 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27397 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27400 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27403 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27405 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27407 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27410 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27414 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27418 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27420 chi hno hbad

end ErdosSzekeres

end
