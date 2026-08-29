module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk096

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 125. -/

theorem predecessorHalfFin13_rejectSemanticSegment125
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((¬PredecessorHalfFin13Atom1336 chi ∧
      ¬PredecessorHalfFin13Atom1338 chi ∧
      ¬PredecessorHalfFin13Atom1340 chi ∧
      ¬PredecessorHalfFin13Atom1342 chi ∧
      ¬PredecessorHalfFin13Atom1344 chi ∧
      ¬PredecessorHalfFin13Atom1349 chi ∧
      ¬PredecessorHalfFin13Atom1352 chi ∧
      ¬PredecessorHalfFin13Atom1354 chi ∧
      ¬PredecessorHalfFin13Atom1359 chi ∧
      ¬PredecessorHalfFin13Atom1365 chi ∧
      ¬PredecessorHalfFin13Atom1463 chi ∧
      ¬PredecessorHalfFin13Atom1465 chi ∧
      ¬PredecessorHalfFin13Atom1470 chi ∧
      ¬PredecessorHalfFin13Atom1476 chi ∧
      ¬PredecessorHalfFin13Atom1486 chi ∧
      ¬PredecessorHalfFin13Atom2129 chi ∧
      ¬PredecessorHalfFin13Atom2131 chi ∧
      ¬PredecessorHalfFin13Atom2136 chi ∧
      ¬PredecessorHalfFin13Atom2142 chi ∧
      ¬PredecessorHalfFin13Atom2152 chi ∧
      ¬PredecessorHalfFin13Atom2272 chi) ∨
      ((¬PredecessorHalfFin13Atom1337 chi ∧
      ¬PredecessorHalfFin13Atom1338 chi ∧
      ¬PredecessorHalfFin13Atom1340 chi ∧
      ¬PredecessorHalfFin13Atom1345 chi ∧
      ¬PredecessorHalfFin13Atom1347 chi ∧
      ¬PredecessorHalfFin13Atom1349 chi ∧
      ¬PredecessorHalfFin13Atom1355 chi ∧
      ¬PredecessorHalfFin13Atom1357 chi ∧
      ¬PredecessorHalfFin13Atom1359 chi ∧
      ¬PredecessorHalfFin13Atom1368 chi ∧
      ¬PredecessorHalfFin13Atom1466 chi ∧
      ¬PredecessorHalfFin13Atom1468 chi ∧
      ¬PredecessorHalfFin13Atom1470 chi ∧
      ¬PredecessorHalfFin13Atom1479 chi ∧
      ¬PredecessorHalfFin13Atom1489 chi ∧
      ¬PredecessorHalfFin13Atom2132 chi ∧
      ¬PredecessorHalfFin13Atom2134 chi ∧
      ¬PredecessorHalfFin13Atom2136 chi ∧
      ¬PredecessorHalfFin13Atom2145 chi ∧
      ¬PredecessorHalfFin13Atom2155 chi ∧
      ¬PredecessorHalfFin13Atom2275 chi) ∨
      (¬PredecessorHalfFin13Atom1341 chi ∧
      ¬PredecessorHalfFin13Atom1342 chi ∧
      ¬PredecessorHalfFin13Atom1344 chi ∧
      ¬PredecessorHalfFin13Atom1345 chi ∧
      ¬PredecessorHalfFin13Atom1347 chi ∧
      ¬PredecessorHalfFin13Atom1349 chi ∧
      ¬PredecessorHalfFin13Atom1361 chi ∧
      ¬PredecessorHalfFin13Atom1363 chi ∧
      ¬PredecessorHalfFin13Atom1365 chi ∧
      ¬PredecessorHalfFin13Atom1368 chi ∧
      ¬PredecessorHalfFin13Atom1472 chi ∧
      ¬PredecessorHalfFin13Atom1474 chi ∧
      ¬PredecessorHalfFin13Atom1476 chi ∧
      ¬PredecessorHalfFin13Atom1479 chi ∧
      ¬PredecessorHalfFin13Atom1493 chi ∧
      ¬PredecessorHalfFin13Atom2138 chi ∧
      ¬PredecessorHalfFin13Atom2140 chi ∧
      ¬PredecessorHalfFin13Atom2142 chi ∧
      ¬PredecessorHalfFin13Atom2145 chi ∧
      ¬PredecessorHalfFin13Atom2159 chi ∧
      ¬PredecessorHalfFin13Atom2279 chi))) ∨
      ((¬PredecessorHalfFin13Atom1351 chi ∧
      ¬PredecessorHalfFin13Atom1352 chi ∧
      ¬PredecessorHalfFin13Atom1354 chi ∧
      ¬PredecessorHalfFin13Atom1355 chi ∧
      ¬PredecessorHalfFin13Atom1357 chi ∧
      ¬PredecessorHalfFin13Atom1359 chi ∧
      ¬PredecessorHalfFin13Atom1361 chi ∧
      ¬PredecessorHalfFin13Atom1363 chi ∧
      ¬PredecessorHalfFin13Atom1365 chi ∧
      ¬PredecessorHalfFin13Atom1368 chi ∧
      ¬PredecessorHalfFin13Atom1482 chi ∧
      ¬PredecessorHalfFin13Atom1484 chi ∧
      ¬PredecessorHalfFin13Atom1486 chi ∧
      ¬PredecessorHalfFin13Atom1489 chi ∧
      ¬PredecessorHalfFin13Atom1493 chi ∧
      ¬PredecessorHalfFin13Atom2148 chi ∧
      ¬PredecessorHalfFin13Atom2150 chi ∧
      ¬PredecessorHalfFin13Atom2152 chi ∧
      ¬PredecessorHalfFin13Atom2155 chi ∧
      ¬PredecessorHalfFin13Atom2159 chi ∧
      ¬PredecessorHalfFin13Atom2284 chi) ∨
      ((¬PredecessorHalfFin13Atom1371 chi ∧
      ¬PredecessorHalfFin13Atom1372 chi ∧
      ¬PredecessorHalfFin13Atom1373 chi ∧
      ¬PredecessorHalfFin13Atom1377 chi ∧
      ¬PredecessorHalfFin13Atom1378 chi ∧
      ¬PredecessorHalfFin13Atom1382 chi ∧
      ¬PredecessorHalfFin13Atom1392 chi ∧
      ¬PredecessorHalfFin13Atom1393 chi ∧
      ¬PredecessorHalfFin13Atom1397 chi ∧
      ¬PredecessorHalfFin13Atom1407 chi ∧
      ¬PredecessorHalfFin13Atom1427 chi ∧
      ¬PredecessorHalfFin13Atom1428 chi ∧
      ¬PredecessorHalfFin13Atom1432 chi ∧
      ¬PredecessorHalfFin13Atom1442 chi ∧
      ¬PredecessorHalfFin13Atom1462 chi ∧
      ¬PredecessorHalfFin13Atom2163 chi ∧
      ¬PredecessorHalfFin13Atom2164 chi ∧
      ¬PredecessorHalfFin13Atom2168 chi ∧
      ¬PredecessorHalfFin13Atom2178 chi ∧
      ¬PredecessorHalfFin13Atom2198 chi ∧
      ¬PredecessorHalfFin13Atom2233 chi) ∨
      (¬PredecessorHalfFin13Atom1371 chi ∧
      ¬PredecessorHalfFin13Atom1372 chi ∧
      ¬PredecessorHalfFin13Atom1374 chi ∧
      ¬PredecessorHalfFin13Atom1377 chi ∧
      ¬PredecessorHalfFin13Atom1379 chi ∧
      ¬PredecessorHalfFin13Atom1383 chi ∧
      ¬PredecessorHalfFin13Atom1392 chi ∧
      ¬PredecessorHalfFin13Atom1394 chi ∧
      ¬PredecessorHalfFin13Atom1398 chi ∧
      ¬PredecessorHalfFin13Atom1408 chi ∧
      ¬PredecessorHalfFin13Atom1427 chi ∧
      ¬PredecessorHalfFin13Atom1429 chi ∧
      ¬PredecessorHalfFin13Atom1433 chi ∧
      ¬PredecessorHalfFin13Atom1443 chi ∧
      ¬PredecessorHalfFin13Atom1463 chi ∧
      ¬PredecessorHalfFin13Atom2163 chi ∧
      ¬PredecessorHalfFin13Atom2165 chi ∧
      ¬PredecessorHalfFin13Atom2169 chi ∧
      ¬PredecessorHalfFin13Atom2179 chi ∧
      ¬PredecessorHalfFin13Atom2199 chi ∧
      ¬PredecessorHalfFin13Atom2234 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1371 chi ∧
      ¬PredecessorHalfFin13Atom1372 chi ∧
      ¬PredecessorHalfFin13Atom1376 chi ∧
      ¬PredecessorHalfFin13Atom1377 chi ∧
      ¬PredecessorHalfFin13Atom1381 chi ∧
      ¬PredecessorHalfFin13Atom1385 chi ∧
      ¬PredecessorHalfFin13Atom1392 chi ∧
      ¬PredecessorHalfFin13Atom1396 chi ∧
      ¬PredecessorHalfFin13Atom1400 chi ∧
      ¬PredecessorHalfFin13Atom1410 chi ∧
      ¬PredecessorHalfFin13Atom1427 chi ∧
      ¬PredecessorHalfFin13Atom1431 chi ∧
      ¬PredecessorHalfFin13Atom1435 chi ∧
      ¬PredecessorHalfFin13Atom1445 chi ∧
      ¬PredecessorHalfFin13Atom1465 chi ∧
      ¬PredecessorHalfFin13Atom2163 chi ∧
      ¬PredecessorHalfFin13Atom2167 chi ∧
      ¬PredecessorHalfFin13Atom2171 chi ∧
      ¬PredecessorHalfFin13Atom2181 chi ∧
      ¬PredecessorHalfFin13Atom2201 chi ∧
      ¬PredecessorHalfFin13Atom2236 chi) ∨
      ((¬PredecessorHalfFin13Atom1371 chi ∧
      ¬PredecessorHalfFin13Atom1373 chi ∧
      ¬PredecessorHalfFin13Atom1374 chi ∧
      ¬PredecessorHalfFin13Atom1378 chi ∧
      ¬PredecessorHalfFin13Atom1379 chi ∧
      ¬PredecessorHalfFin13Atom1386 chi ∧
      ¬PredecessorHalfFin13Atom1393 chi ∧
      ¬PredecessorHalfFin13Atom1394 chi ∧
      ¬PredecessorHalfFin13Atom1401 chi ∧
      ¬PredecessorHalfFin13Atom1411 chi ∧
      ¬PredecessorHalfFin13Atom1428 chi ∧
      ¬PredecessorHalfFin13Atom1429 chi ∧
      ¬PredecessorHalfFin13Atom1436 chi ∧
      ¬PredecessorHalfFin13Atom1446 chi ∧
      ¬PredecessorHalfFin13Atom1466 chi ∧
      ¬PredecessorHalfFin13Atom2164 chi ∧
      ¬PredecessorHalfFin13Atom2165 chi ∧
      ¬PredecessorHalfFin13Atom2172 chi ∧
      ¬PredecessorHalfFin13Atom2182 chi ∧
      ¬PredecessorHalfFin13Atom2202 chi ∧
      ¬PredecessorHalfFin13Atom2237 chi) ∨
      (¬PredecessorHalfFin13Atom1371 chi ∧
      ¬PredecessorHalfFin13Atom1373 chi ∧
      ¬PredecessorHalfFin13Atom1376 chi ∧
      ¬PredecessorHalfFin13Atom1378 chi ∧
      ¬PredecessorHalfFin13Atom1381 chi ∧
      ¬PredecessorHalfFin13Atom1388 chi ∧
      ¬PredecessorHalfFin13Atom1393 chi ∧
      ¬PredecessorHalfFin13Atom1396 chi ∧
      ¬PredecessorHalfFin13Atom1403 chi ∧
      ¬PredecessorHalfFin13Atom1413 chi ∧
      ¬PredecessorHalfFin13Atom1428 chi ∧
      ¬PredecessorHalfFin13Atom1431 chi ∧
      ¬PredecessorHalfFin13Atom1438 chi ∧
      ¬PredecessorHalfFin13Atom1448 chi ∧
      ¬PredecessorHalfFin13Atom1468 chi ∧
      ¬PredecessorHalfFin13Atom2164 chi ∧
      ¬PredecessorHalfFin13Atom2167 chi ∧
      ¬PredecessorHalfFin13Atom2174 chi ∧
      ¬PredecessorHalfFin13Atom2184 chi ∧
      ¬PredecessorHalfFin13Atom2204 chi ∧
      ¬PredecessorHalfFin13Atom2239 chi))) ∨
      ((¬PredecessorHalfFin13Atom1371 chi ∧
      ¬PredecessorHalfFin13Atom1374 chi ∧
      ¬PredecessorHalfFin13Atom1376 chi ∧
      ¬PredecessorHalfFin13Atom1379 chi ∧
      ¬PredecessorHalfFin13Atom1381 chi ∧
      ¬PredecessorHalfFin13Atom1390 chi ∧
      ¬PredecessorHalfFin13Atom1394 chi ∧
      ¬PredecessorHalfFin13Atom1396 chi ∧
      ¬PredecessorHalfFin13Atom1405 chi ∧
      ¬PredecessorHalfFin13Atom1415 chi ∧
      ¬PredecessorHalfFin13Atom1429 chi ∧
      ¬PredecessorHalfFin13Atom1431 chi ∧
      ¬PredecessorHalfFin13Atom1440 chi ∧
      ¬PredecessorHalfFin13Atom1450 chi ∧
      ¬PredecessorHalfFin13Atom1470 chi ∧
      ¬PredecessorHalfFin13Atom2165 chi ∧
      ¬PredecessorHalfFin13Atom2167 chi ∧
      ¬PredecessorHalfFin13Atom2176 chi ∧
      ¬PredecessorHalfFin13Atom2186 chi ∧
      ¬PredecessorHalfFin13Atom2206 chi ∧
      ¬PredecessorHalfFin13Atom2241 chi) ∨
      ((¬PredecessorHalfFin13Atom1372 chi ∧
      ¬PredecessorHalfFin13Atom1373 chi ∧
      ¬PredecessorHalfFin13Atom1374 chi ∧
      ¬PredecessorHalfFin13Atom1382 chi ∧
      ¬PredecessorHalfFin13Atom1383 chi ∧
      ¬PredecessorHalfFin13Atom1386 chi ∧
      ¬PredecessorHalfFin13Atom1397 chi ∧
      ¬PredecessorHalfFin13Atom1398 chi ∧
      ¬PredecessorHalfFin13Atom1401 chi ∧
      ¬PredecessorHalfFin13Atom1417 chi ∧
      ¬PredecessorHalfFin13Atom1432 chi ∧
      ¬PredecessorHalfFin13Atom1433 chi ∧
      ¬PredecessorHalfFin13Atom1436 chi ∧
      ¬PredecessorHalfFin13Atom1452 chi ∧
      ¬PredecessorHalfFin13Atom1472 chi ∧
      ¬PredecessorHalfFin13Atom2168 chi ∧
      ¬PredecessorHalfFin13Atom2169 chi ∧
      ¬PredecessorHalfFin13Atom2172 chi ∧
      ¬PredecessorHalfFin13Atom2188 chi ∧
      ¬PredecessorHalfFin13Atom2208 chi ∧
      ¬PredecessorHalfFin13Atom2243 chi) ∨
      (¬PredecessorHalfFin13Atom1372 chi ∧
      ¬PredecessorHalfFin13Atom1373 chi ∧
      ¬PredecessorHalfFin13Atom1376 chi ∧
      ¬PredecessorHalfFin13Atom1382 chi ∧
      ¬PredecessorHalfFin13Atom1385 chi ∧
      ¬PredecessorHalfFin13Atom1388 chi ∧
      ¬PredecessorHalfFin13Atom1397 chi ∧
      ¬PredecessorHalfFin13Atom1400 chi ∧
      ¬PredecessorHalfFin13Atom1403 chi ∧
      ¬PredecessorHalfFin13Atom1419 chi ∧
      ¬PredecessorHalfFin13Atom1432 chi ∧
      ¬PredecessorHalfFin13Atom1435 chi ∧
      ¬PredecessorHalfFin13Atom1438 chi ∧
      ¬PredecessorHalfFin13Atom1454 chi ∧
      ¬PredecessorHalfFin13Atom1474 chi ∧
      ¬PredecessorHalfFin13Atom2168 chi ∧
      ¬PredecessorHalfFin13Atom2171 chi ∧
      ¬PredecessorHalfFin13Atom2174 chi ∧
      ¬PredecessorHalfFin13Atom2190 chi ∧
      ¬PredecessorHalfFin13Atom2210 chi ∧
      ¬PredecessorHalfFin13Atom2245 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom1372 chi ∧
      ¬PredecessorHalfFin13Atom1374 chi ∧
      ¬PredecessorHalfFin13Atom1376 chi ∧
      ¬PredecessorHalfFin13Atom1383 chi ∧
      ¬PredecessorHalfFin13Atom1385 chi ∧
      ¬PredecessorHalfFin13Atom1390 chi ∧
      ¬PredecessorHalfFin13Atom1398 chi ∧
      ¬PredecessorHalfFin13Atom1400 chi ∧
      ¬PredecessorHalfFin13Atom1405 chi ∧
      ¬PredecessorHalfFin13Atom1421 chi ∧
      ¬PredecessorHalfFin13Atom1433 chi ∧
      ¬PredecessorHalfFin13Atom1435 chi ∧
      ¬PredecessorHalfFin13Atom1440 chi ∧
      ¬PredecessorHalfFin13Atom1456 chi ∧
      ¬PredecessorHalfFin13Atom1476 chi ∧
      ¬PredecessorHalfFin13Atom2169 chi ∧
      ¬PredecessorHalfFin13Atom2171 chi ∧
      ¬PredecessorHalfFin13Atom2176 chi ∧
      ¬PredecessorHalfFin13Atom2192 chi ∧
      ¬PredecessorHalfFin13Atom2212 chi ∧
      ¬PredecessorHalfFin13Atom2247 chi) ∨
      ((¬PredecessorHalfFin13Atom1373 chi ∧
      ¬PredecessorHalfFin13Atom1374 chi ∧
      ¬PredecessorHalfFin13Atom1376 chi ∧
      ¬PredecessorHalfFin13Atom1386 chi ∧
      ¬PredecessorHalfFin13Atom1388 chi ∧
      ¬PredecessorHalfFin13Atom1390 chi ∧
      ¬PredecessorHalfFin13Atom1401 chi ∧
      ¬PredecessorHalfFin13Atom1403 chi ∧
      ¬PredecessorHalfFin13Atom1405 chi ∧
      ¬PredecessorHalfFin13Atom1424 chi ∧
      ¬PredecessorHalfFin13Atom1436 chi ∧
      ¬PredecessorHalfFin13Atom1438 chi ∧
      ¬PredecessorHalfFin13Atom1440 chi ∧
      ¬PredecessorHalfFin13Atom1459 chi ∧
      ¬PredecessorHalfFin13Atom1479 chi ∧
      ¬PredecessorHalfFin13Atom2172 chi ∧
      ¬PredecessorHalfFin13Atom2174 chi ∧
      ¬PredecessorHalfFin13Atom2176 chi ∧
      ¬PredecessorHalfFin13Atom2195 chi ∧
      ¬PredecessorHalfFin13Atom2215 chi ∧
      ¬PredecessorHalfFin13Atom2250 chi) ∨
      (¬PredecessorHalfFin13Atom1377 chi ∧
      ¬PredecessorHalfFin13Atom1378 chi ∧
      ¬PredecessorHalfFin13Atom1379 chi ∧
      ¬PredecessorHalfFin13Atom1382 chi ∧
      ¬PredecessorHalfFin13Atom1383 chi ∧
      ¬PredecessorHalfFin13Atom1386 chi ∧
      ¬PredecessorHalfFin13Atom1407 chi ∧
      ¬PredecessorHalfFin13Atom1408 chi ∧
      ¬PredecessorHalfFin13Atom1411 chi ∧
      ¬PredecessorHalfFin13Atom1417 chi ∧
      ¬PredecessorHalfFin13Atom1442 chi ∧
      ¬PredecessorHalfFin13Atom1443 chi ∧
      ¬PredecessorHalfFin13Atom1446 chi ∧
      ¬PredecessorHalfFin13Atom1452 chi ∧
      ¬PredecessorHalfFin13Atom1482 chi ∧
      ¬PredecessorHalfFin13Atom2178 chi ∧
      ¬PredecessorHalfFin13Atom2179 chi ∧
      ¬PredecessorHalfFin13Atom2182 chi ∧
      ¬PredecessorHalfFin13Atom2188 chi ∧
      ¬PredecessorHalfFin13Atom2218 chi ∧
      ¬PredecessorHalfFin13Atom2253 chi))) ∨
      ((¬PredecessorHalfFin13Atom1377 chi ∧
      ¬PredecessorHalfFin13Atom1378 chi ∧
      ¬PredecessorHalfFin13Atom1381 chi ∧
      ¬PredecessorHalfFin13Atom1382 chi ∧
      ¬PredecessorHalfFin13Atom1385 chi ∧
      ¬PredecessorHalfFin13Atom1388 chi ∧
      ¬PredecessorHalfFin13Atom1407 chi ∧
      ¬PredecessorHalfFin13Atom1410 chi ∧
      ¬PredecessorHalfFin13Atom1413 chi ∧
      ¬PredecessorHalfFin13Atom1419 chi ∧
      ¬PredecessorHalfFin13Atom1442 chi ∧
      ¬PredecessorHalfFin13Atom1445 chi ∧
      ¬PredecessorHalfFin13Atom1448 chi ∧
      ¬PredecessorHalfFin13Atom1454 chi ∧
      ¬PredecessorHalfFin13Atom1484 chi ∧
      ¬PredecessorHalfFin13Atom2178 chi ∧
      ¬PredecessorHalfFin13Atom2181 chi ∧
      ¬PredecessorHalfFin13Atom2184 chi ∧
      ¬PredecessorHalfFin13Atom2190 chi ∧
      ¬PredecessorHalfFin13Atom2220 chi ∧
      ¬PredecessorHalfFin13Atom2255 chi) ∨
      ((¬PredecessorHalfFin13Atom1377 chi ∧
      ¬PredecessorHalfFin13Atom1379 chi ∧
      ¬PredecessorHalfFin13Atom1381 chi ∧
      ¬PredecessorHalfFin13Atom1383 chi ∧
      ¬PredecessorHalfFin13Atom1385 chi ∧
      ¬PredecessorHalfFin13Atom1390 chi ∧
      ¬PredecessorHalfFin13Atom1408 chi ∧
      ¬PredecessorHalfFin13Atom1410 chi ∧
      ¬PredecessorHalfFin13Atom1415 chi ∧
      ¬PredecessorHalfFin13Atom1421 chi ∧
      ¬PredecessorHalfFin13Atom1443 chi ∧
      ¬PredecessorHalfFin13Atom1445 chi ∧
      ¬PredecessorHalfFin13Atom1450 chi ∧
      ¬PredecessorHalfFin13Atom1456 chi ∧
      ¬PredecessorHalfFin13Atom1486 chi ∧
      ¬PredecessorHalfFin13Atom2179 chi ∧
      ¬PredecessorHalfFin13Atom2181 chi ∧
      ¬PredecessorHalfFin13Atom2186 chi ∧
      ¬PredecessorHalfFin13Atom2192 chi ∧
      ¬PredecessorHalfFin13Atom2222 chi ∧
      ¬PredecessorHalfFin13Atom2257 chi) ∨
      (¬PredecessorHalfFin13Atom1378 chi ∧
      ¬PredecessorHalfFin13Atom1379 chi ∧
      ¬PredecessorHalfFin13Atom1381 chi ∧
      ¬PredecessorHalfFin13Atom1386 chi ∧
      ¬PredecessorHalfFin13Atom1388 chi ∧
      ¬PredecessorHalfFin13Atom1390 chi ∧
      ¬PredecessorHalfFin13Atom1411 chi ∧
      ¬PredecessorHalfFin13Atom1413 chi ∧
      ¬PredecessorHalfFin13Atom1415 chi ∧
      ¬PredecessorHalfFin13Atom1424 chi ∧
      ¬PredecessorHalfFin13Atom1446 chi ∧
      ¬PredecessorHalfFin13Atom1448 chi ∧
      ¬PredecessorHalfFin13Atom1450 chi ∧
      ¬PredecessorHalfFin13Atom1459 chi ∧
      ¬PredecessorHalfFin13Atom1489 chi ∧
      ¬PredecessorHalfFin13Atom2182 chi ∧
      ¬PredecessorHalfFin13Atom2184 chi ∧
      ¬PredecessorHalfFin13Atom2186 chi ∧
      ¬PredecessorHalfFin13Atom2195 chi ∧
      ¬PredecessorHalfFin13Atom2225 chi ∧
      ¬PredecessorHalfFin13Atom2260 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1382 chi ∧
      ¬PredecessorHalfFin13Atom1383 chi ∧
      ¬PredecessorHalfFin13Atom1385 chi ∧
      ¬PredecessorHalfFin13Atom1386 chi ∧
      ¬PredecessorHalfFin13Atom1388 chi ∧
      ¬PredecessorHalfFin13Atom1390 chi ∧
      ¬PredecessorHalfFin13Atom1417 chi ∧
      ¬PredecessorHalfFin13Atom1419 chi ∧
      ¬PredecessorHalfFin13Atom1421 chi ∧
      ¬PredecessorHalfFin13Atom1424 chi ∧
      ¬PredecessorHalfFin13Atom1452 chi ∧
      ¬PredecessorHalfFin13Atom1454 chi ∧
      ¬PredecessorHalfFin13Atom1456 chi ∧
      ¬PredecessorHalfFin13Atom1459 chi ∧
      ¬PredecessorHalfFin13Atom1493 chi ∧
      ¬PredecessorHalfFin13Atom2188 chi ∧
      ¬PredecessorHalfFin13Atom2190 chi ∧
      ¬PredecessorHalfFin13Atom2192 chi ∧
      ¬PredecessorHalfFin13Atom2195 chi ∧
      ¬PredecessorHalfFin13Atom2229 chi ∧
      ¬PredecessorHalfFin13Atom2264 chi) ∨
      ((¬PredecessorHalfFin13Atom1392 chi ∧
      ¬PredecessorHalfFin13Atom1393 chi ∧
      ¬PredecessorHalfFin13Atom1394 chi ∧
      ¬PredecessorHalfFin13Atom1397 chi ∧
      ¬PredecessorHalfFin13Atom1398 chi ∧
      ¬PredecessorHalfFin13Atom1401 chi ∧
      ¬PredecessorHalfFin13Atom1407 chi ∧
      ¬PredecessorHalfFin13Atom1408 chi ∧
      ¬PredecessorHalfFin13Atom1411 chi ∧
      ¬PredecessorHalfFin13Atom1417 chi ∧
      ¬PredecessorHalfFin13Atom1462 chi ∧
      ¬PredecessorHalfFin13Atom1463 chi ∧
      ¬PredecessorHalfFin13Atom1466 chi ∧
      ¬PredecessorHalfFin13Atom1472 chi ∧
      ¬PredecessorHalfFin13Atom1482 chi ∧
      ¬PredecessorHalfFin13Atom2198 chi ∧
      ¬PredecessorHalfFin13Atom2199 chi ∧
      ¬PredecessorHalfFin13Atom2202 chi ∧
      ¬PredecessorHalfFin13Atom2208 chi ∧
      ¬PredecessorHalfFin13Atom2218 chi ∧
      ¬PredecessorHalfFin13Atom2268 chi) ∨
      (¬PredecessorHalfFin13Atom1392 chi ∧
      ¬PredecessorHalfFin13Atom1393 chi ∧
      ¬PredecessorHalfFin13Atom1396 chi ∧
      ¬PredecessorHalfFin13Atom1397 chi ∧
      ¬PredecessorHalfFin13Atom1400 chi ∧
      ¬PredecessorHalfFin13Atom1403 chi ∧
      ¬PredecessorHalfFin13Atom1407 chi ∧
      ¬PredecessorHalfFin13Atom1410 chi ∧
      ¬PredecessorHalfFin13Atom1413 chi ∧
      ¬PredecessorHalfFin13Atom1419 chi ∧
      ¬PredecessorHalfFin13Atom1462 chi ∧
      ¬PredecessorHalfFin13Atom1465 chi ∧
      ¬PredecessorHalfFin13Atom1468 chi ∧
      ¬PredecessorHalfFin13Atom1474 chi ∧
      ¬PredecessorHalfFin13Atom1484 chi ∧
      ¬PredecessorHalfFin13Atom2198 chi ∧
      ¬PredecessorHalfFin13Atom2201 chi ∧
      ¬PredecessorHalfFin13Atom2204 chi ∧
      ¬PredecessorHalfFin13Atom2210 chi ∧
      ¬PredecessorHalfFin13Atom2220 chi ∧
      ¬PredecessorHalfFin13Atom2270 chi))) ∨
      ((¬PredecessorHalfFin13Atom1392 chi ∧
      ¬PredecessorHalfFin13Atom1394 chi ∧
      ¬PredecessorHalfFin13Atom1396 chi ∧
      ¬PredecessorHalfFin13Atom1398 chi ∧
      ¬PredecessorHalfFin13Atom1400 chi ∧
      ¬PredecessorHalfFin13Atom1405 chi ∧
      ¬PredecessorHalfFin13Atom1408 chi ∧
      ¬PredecessorHalfFin13Atom1410 chi ∧
      ¬PredecessorHalfFin13Atom1415 chi ∧
      ¬PredecessorHalfFin13Atom1421 chi ∧
      ¬PredecessorHalfFin13Atom1463 chi ∧
      ¬PredecessorHalfFin13Atom1465 chi ∧
      ¬PredecessorHalfFin13Atom1470 chi ∧
      ¬PredecessorHalfFin13Atom1476 chi ∧
      ¬PredecessorHalfFin13Atom1486 chi ∧
      ¬PredecessorHalfFin13Atom2199 chi ∧
      ¬PredecessorHalfFin13Atom2201 chi ∧
      ¬PredecessorHalfFin13Atom2206 chi ∧
      ¬PredecessorHalfFin13Atom2212 chi ∧
      ¬PredecessorHalfFin13Atom2222 chi ∧
      ¬PredecessorHalfFin13Atom2272 chi) ∨
      ((¬PredecessorHalfFin13Atom1393 chi ∧
      ¬PredecessorHalfFin13Atom1394 chi ∧
      ¬PredecessorHalfFin13Atom1396 chi ∧
      ¬PredecessorHalfFin13Atom1401 chi ∧
      ¬PredecessorHalfFin13Atom1403 chi ∧
      ¬PredecessorHalfFin13Atom1405 chi ∧
      ¬PredecessorHalfFin13Atom1411 chi ∧
      ¬PredecessorHalfFin13Atom1413 chi ∧
      ¬PredecessorHalfFin13Atom1415 chi ∧
      ¬PredecessorHalfFin13Atom1424 chi ∧
      ¬PredecessorHalfFin13Atom1466 chi ∧
      ¬PredecessorHalfFin13Atom1468 chi ∧
      ¬PredecessorHalfFin13Atom1470 chi ∧
      ¬PredecessorHalfFin13Atom1479 chi ∧
      ¬PredecessorHalfFin13Atom1489 chi ∧
      ¬PredecessorHalfFin13Atom2202 chi ∧
      ¬PredecessorHalfFin13Atom2204 chi ∧
      ¬PredecessorHalfFin13Atom2206 chi ∧
      ¬PredecessorHalfFin13Atom2215 chi ∧
      ¬PredecessorHalfFin13Atom2225 chi ∧
      ¬PredecessorHalfFin13Atom2275 chi) ∨
      (¬PredecessorHalfFin13Atom1397 chi ∧
      ¬PredecessorHalfFin13Atom1398 chi ∧
      ¬PredecessorHalfFin13Atom1400 chi ∧
      ¬PredecessorHalfFin13Atom1401 chi ∧
      ¬PredecessorHalfFin13Atom1403 chi ∧
      ¬PredecessorHalfFin13Atom1405 chi ∧
      ¬PredecessorHalfFin13Atom1417 chi ∧
      ¬PredecessorHalfFin13Atom1419 chi ∧
      ¬PredecessorHalfFin13Atom1421 chi ∧
      ¬PredecessorHalfFin13Atom1424 chi ∧
      ¬PredecessorHalfFin13Atom1472 chi ∧
      ¬PredecessorHalfFin13Atom1474 chi ∧
      ¬PredecessorHalfFin13Atom1476 chi ∧
      ¬PredecessorHalfFin13Atom1479 chi ∧
      ¬PredecessorHalfFin13Atom1493 chi ∧
      ¬PredecessorHalfFin13Atom2208 chi ∧
      ¬PredecessorHalfFin13Atom2210 chi ∧
      ¬PredecessorHalfFin13Atom2212 chi ∧
      ¬PredecessorHalfFin13Atom2215 chi ∧
      ¬PredecessorHalfFin13Atom2229 chi ∧
      ¬PredecessorHalfFin13Atom2279 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom1407 chi ∧
      ¬PredecessorHalfFin13Atom1408 chi ∧
      ¬PredecessorHalfFin13Atom1410 chi ∧
      ¬PredecessorHalfFin13Atom1411 chi ∧
      ¬PredecessorHalfFin13Atom1413 chi ∧
      ¬PredecessorHalfFin13Atom1415 chi ∧
      ¬PredecessorHalfFin13Atom1417 chi ∧
      ¬PredecessorHalfFin13Atom1419 chi ∧
      ¬PredecessorHalfFin13Atom1421 chi ∧
      ¬PredecessorHalfFin13Atom1424 chi ∧
      ¬PredecessorHalfFin13Atom1482 chi ∧
      ¬PredecessorHalfFin13Atom1484 chi ∧
      ¬PredecessorHalfFin13Atom1486 chi ∧
      ¬PredecessorHalfFin13Atom1489 chi ∧
      ¬PredecessorHalfFin13Atom1493 chi ∧
      ¬PredecessorHalfFin13Atom2218 chi ∧
      ¬PredecessorHalfFin13Atom2220 chi ∧
      ¬PredecessorHalfFin13Atom2222 chi ∧
      ¬PredecessorHalfFin13Atom2225 chi ∧
      ¬PredecessorHalfFin13Atom2229 chi ∧
      ¬PredecessorHalfFin13Atom2284 chi) ∨
      ((¬PredecessorHalfFin13Atom1427 chi ∧
      ¬PredecessorHalfFin13Atom1428 chi ∧
      ¬PredecessorHalfFin13Atom1429 chi ∧
      ¬PredecessorHalfFin13Atom1432 chi ∧
      ¬PredecessorHalfFin13Atom1433 chi ∧
      ¬PredecessorHalfFin13Atom1436 chi ∧
      ¬PredecessorHalfFin13Atom1442 chi ∧
      ¬PredecessorHalfFin13Atom1443 chi ∧
      ¬PredecessorHalfFin13Atom1446 chi ∧
      ¬PredecessorHalfFin13Atom1452 chi ∧
      ¬PredecessorHalfFin13Atom1462 chi ∧
      ¬PredecessorHalfFin13Atom1463 chi ∧
      ¬PredecessorHalfFin13Atom1466 chi ∧
      ¬PredecessorHalfFin13Atom1472 chi ∧
      ¬PredecessorHalfFin13Atom1482 chi ∧
      ¬PredecessorHalfFin13Atom2233 chi ∧
      ¬PredecessorHalfFin13Atom2234 chi ∧
      ¬PredecessorHalfFin13Atom2237 chi ∧
      ¬PredecessorHalfFin13Atom2243 chi ∧
      ¬PredecessorHalfFin13Atom2253 chi ∧
      ¬PredecessorHalfFin13Atom2268 chi) ∨
      (¬PredecessorHalfFin13Atom1427 chi ∧
      ¬PredecessorHalfFin13Atom1428 chi ∧
      ¬PredecessorHalfFin13Atom1431 chi ∧
      ¬PredecessorHalfFin13Atom1432 chi ∧
      ¬PredecessorHalfFin13Atom1435 chi ∧
      ¬PredecessorHalfFin13Atom1438 chi ∧
      ¬PredecessorHalfFin13Atom1442 chi ∧
      ¬PredecessorHalfFin13Atom1445 chi ∧
      ¬PredecessorHalfFin13Atom1448 chi ∧
      ¬PredecessorHalfFin13Atom1454 chi ∧
      ¬PredecessorHalfFin13Atom1462 chi ∧
      ¬PredecessorHalfFin13Atom1465 chi ∧
      ¬PredecessorHalfFin13Atom1468 chi ∧
      ¬PredecessorHalfFin13Atom1474 chi ∧
      ¬PredecessorHalfFin13Atom1484 chi ∧
      ¬PredecessorHalfFin13Atom2233 chi ∧
      ¬PredecessorHalfFin13Atom2236 chi ∧
      ¬PredecessorHalfFin13Atom2239 chi ∧
      ¬PredecessorHalfFin13Atom2245 chi ∧
      ¬PredecessorHalfFin13Atom2255 chi ∧
      ¬PredecessorHalfFin13Atom2270 chi))) ∨
      ((¬PredecessorHalfFin13Atom1427 chi ∧
      ¬PredecessorHalfFin13Atom1429 chi ∧
      ¬PredecessorHalfFin13Atom1431 chi ∧
      ¬PredecessorHalfFin13Atom1433 chi ∧
      ¬PredecessorHalfFin13Atom1435 chi ∧
      ¬PredecessorHalfFin13Atom1440 chi ∧
      ¬PredecessorHalfFin13Atom1443 chi ∧
      ¬PredecessorHalfFin13Atom1445 chi ∧
      ¬PredecessorHalfFin13Atom1450 chi ∧
      ¬PredecessorHalfFin13Atom1456 chi ∧
      ¬PredecessorHalfFin13Atom1463 chi ∧
      ¬PredecessorHalfFin13Atom1465 chi ∧
      ¬PredecessorHalfFin13Atom1470 chi ∧
      ¬PredecessorHalfFin13Atom1476 chi ∧
      ¬PredecessorHalfFin13Atom1486 chi ∧
      ¬PredecessorHalfFin13Atom2234 chi ∧
      ¬PredecessorHalfFin13Atom2236 chi ∧
      ¬PredecessorHalfFin13Atom2241 chi ∧
      ¬PredecessorHalfFin13Atom2247 chi ∧
      ¬PredecessorHalfFin13Atom2257 chi ∧
      ¬PredecessorHalfFin13Atom2272 chi) ∨
      ((¬PredecessorHalfFin13Atom1428 chi ∧
      ¬PredecessorHalfFin13Atom1429 chi ∧
      ¬PredecessorHalfFin13Atom1431 chi ∧
      ¬PredecessorHalfFin13Atom1436 chi ∧
      ¬PredecessorHalfFin13Atom1438 chi ∧
      ¬PredecessorHalfFin13Atom1440 chi ∧
      ¬PredecessorHalfFin13Atom1446 chi ∧
      ¬PredecessorHalfFin13Atom1448 chi ∧
      ¬PredecessorHalfFin13Atom1450 chi ∧
      ¬PredecessorHalfFin13Atom1459 chi ∧
      ¬PredecessorHalfFin13Atom1466 chi ∧
      ¬PredecessorHalfFin13Atom1468 chi ∧
      ¬PredecessorHalfFin13Atom1470 chi ∧
      ¬PredecessorHalfFin13Atom1479 chi ∧
      ¬PredecessorHalfFin13Atom1489 chi ∧
      ¬PredecessorHalfFin13Atom2237 chi ∧
      ¬PredecessorHalfFin13Atom2239 chi ∧
      ¬PredecessorHalfFin13Atom2241 chi ∧
      ¬PredecessorHalfFin13Atom2250 chi ∧
      ¬PredecessorHalfFin13Atom2260 chi ∧
      ¬PredecessorHalfFin13Atom2275 chi) ∨
      (¬PredecessorHalfFin13Atom1432 chi ∧
      ¬PredecessorHalfFin13Atom1433 chi ∧
      ¬PredecessorHalfFin13Atom1435 chi ∧
      ¬PredecessorHalfFin13Atom1436 chi ∧
      ¬PredecessorHalfFin13Atom1438 chi ∧
      ¬PredecessorHalfFin13Atom1440 chi ∧
      ¬PredecessorHalfFin13Atom1452 chi ∧
      ¬PredecessorHalfFin13Atom1454 chi ∧
      ¬PredecessorHalfFin13Atom1456 chi ∧
      ¬PredecessorHalfFin13Atom1459 chi ∧
      ¬PredecessorHalfFin13Atom1472 chi ∧
      ¬PredecessorHalfFin13Atom1474 chi ∧
      ¬PredecessorHalfFin13Atom1476 chi ∧
      ¬PredecessorHalfFin13Atom1479 chi ∧
      ¬PredecessorHalfFin13Atom1493 chi ∧
      ¬PredecessorHalfFin13Atom2243 chi ∧
      ¬PredecessorHalfFin13Atom2245 chi ∧
      ¬PredecessorHalfFin13Atom2247 chi ∧
      ¬PredecessorHalfFin13Atom2250 chi ∧
      ¬PredecessorHalfFin13Atom2264 chi ∧
      ¬PredecessorHalfFin13Atom2279 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1442 chi ∧
      ¬PredecessorHalfFin13Atom1443 chi ∧
      ¬PredecessorHalfFin13Atom1445 chi ∧
      ¬PredecessorHalfFin13Atom1446 chi ∧
      ¬PredecessorHalfFin13Atom1448 chi ∧
      ¬PredecessorHalfFin13Atom1450 chi ∧
      ¬PredecessorHalfFin13Atom1452 chi ∧
      ¬PredecessorHalfFin13Atom1454 chi ∧
      ¬PredecessorHalfFin13Atom1456 chi ∧
      ¬PredecessorHalfFin13Atom1459 chi ∧
      ¬PredecessorHalfFin13Atom1482 chi ∧
      ¬PredecessorHalfFin13Atom1484 chi ∧
      ¬PredecessorHalfFin13Atom1486 chi ∧
      ¬PredecessorHalfFin13Atom1489 chi ∧
      ¬PredecessorHalfFin13Atom1493 chi ∧
      ¬PredecessorHalfFin13Atom2253 chi ∧
      ¬PredecessorHalfFin13Atom2255 chi ∧
      ¬PredecessorHalfFin13Atom2257 chi ∧
      ¬PredecessorHalfFin13Atom2260 chi ∧
      ¬PredecessorHalfFin13Atom2264 chi ∧
      ¬PredecessorHalfFin13Atom2284 chi) ∨
      ((¬PredecessorHalfFin13Atom1462 chi ∧
      ¬PredecessorHalfFin13Atom1463 chi ∧
      ¬PredecessorHalfFin13Atom1465 chi ∧
      ¬PredecessorHalfFin13Atom1466 chi ∧
      ¬PredecessorHalfFin13Atom1468 chi ∧
      ¬PredecessorHalfFin13Atom1470 chi ∧
      ¬PredecessorHalfFin13Atom1472 chi ∧
      ¬PredecessorHalfFin13Atom1474 chi ∧
      ¬PredecessorHalfFin13Atom1476 chi ∧
      ¬PredecessorHalfFin13Atom1479 chi ∧
      ¬PredecessorHalfFin13Atom1482 chi ∧
      ¬PredecessorHalfFin13Atom1484 chi ∧
      ¬PredecessorHalfFin13Atom1486 chi ∧
      ¬PredecessorHalfFin13Atom1489 chi ∧
      ¬PredecessorHalfFin13Atom1493 chi ∧
      ¬PredecessorHalfFin13Atom2268 chi ∧
      ¬PredecessorHalfFin13Atom2270 chi ∧
      ¬PredecessorHalfFin13Atom2272 chi ∧
      ¬PredecessorHalfFin13Atom2275 chi ∧
      ¬PredecessorHalfFin13Atom2279 chi ∧
      ¬PredecessorHalfFin13Atom2284 chi) ∨
      (¬PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom1861 chi ∧
      ¬PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom1911 chi ∧
      ¬PredecessorHalfFin13Atom1912 chi ∧
      ¬PredecessorHalfFin13Atom1917 chi ∧
      ¬PredecessorHalfFin13Atom1932 chi ∧
      ¬PredecessorHalfFin13Atom1967 chi ∧
      ¬PredecessorHalfFin13Atom2037 chi ∧
      ¬PredecessorHalfFin13Atom2038 chi ∧
      ¬PredecessorHalfFin13Atom2043 chi ∧
      ¬PredecessorHalfFin13Atom2058 chi ∧
      ¬PredecessorHalfFin13Atom2093 chi ∧
      ¬PredecessorHalfFin13Atom2163 chi))) ∨
      ((¬PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom1911 chi ∧
      ¬PredecessorHalfFin13Atom1913 chi ∧
      ¬PredecessorHalfFin13Atom1918 chi ∧
      ¬PredecessorHalfFin13Atom1933 chi ∧
      ¬PredecessorHalfFin13Atom1968 chi ∧
      ¬PredecessorHalfFin13Atom2037 chi ∧
      ¬PredecessorHalfFin13Atom2039 chi ∧
      ¬PredecessorHalfFin13Atom2044 chi ∧
      ¬PredecessorHalfFin13Atom2059 chi ∧
      ¬PredecessorHalfFin13Atom2094 chi ∧
      ¬PredecessorHalfFin13Atom2164 chi) ∨
      ((¬PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom1858 chi ∧
      ¬PredecessorHalfFin13Atom1863 chi ∧
      ¬PredecessorHalfFin13Atom1878 chi ∧
      ¬PredecessorHalfFin13Atom1911 chi ∧
      ¬PredecessorHalfFin13Atom1914 chi ∧
      ¬PredecessorHalfFin13Atom1919 chi ∧
      ¬PredecessorHalfFin13Atom1934 chi ∧
      ¬PredecessorHalfFin13Atom1969 chi ∧
      ¬PredecessorHalfFin13Atom2037 chi ∧
      ¬PredecessorHalfFin13Atom2040 chi ∧
      ¬PredecessorHalfFin13Atom2045 chi ∧
      ¬PredecessorHalfFin13Atom2060 chi ∧
      ¬PredecessorHalfFin13Atom2095 chi ∧
      ¬PredecessorHalfFin13Atom2165 chi) ∨
      (¬PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom1832 chi ∧
      ¬PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom1838 chi ∧
      ¬PredecessorHalfFin13Atom1843 chi ∧
      ¬PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom1859 chi ∧
      ¬PredecessorHalfFin13Atom1864 chi ∧
      ¬PredecessorHalfFin13Atom1879 chi ∧
      ¬PredecessorHalfFin13Atom1911 chi ∧
      ¬PredecessorHalfFin13Atom1915 chi ∧
      ¬PredecessorHalfFin13Atom1920 chi ∧
      ¬PredecessorHalfFin13Atom1935 chi ∧
      ¬PredecessorHalfFin13Atom1970 chi ∧
      ¬PredecessorHalfFin13Atom2037 chi ∧
      ¬PredecessorHalfFin13Atom2041 chi ∧
      ¬PredecessorHalfFin13Atom2046 chi ∧
      ¬PredecessorHalfFin13Atom2061 chi ∧
      ¬PredecessorHalfFin13Atom2096 chi ∧
      ¬PredecessorHalfFin13Atom2166 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom1839 chi ∧
      ¬PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom1860 chi ∧
      ¬PredecessorHalfFin13Atom1865 chi ∧
      ¬PredecessorHalfFin13Atom1880 chi ∧
      ¬PredecessorHalfFin13Atom1911 chi ∧
      ¬PredecessorHalfFin13Atom1916 chi ∧
      ¬PredecessorHalfFin13Atom1921 chi ∧
      ¬PredecessorHalfFin13Atom1936 chi ∧
      ¬PredecessorHalfFin13Atom1971 chi ∧
      ¬PredecessorHalfFin13Atom2037 chi ∧
      ¬PredecessorHalfFin13Atom2042 chi ∧
      ¬PredecessorHalfFin13Atom2047 chi ∧
      ¬PredecessorHalfFin13Atom2062 chi ∧
      ¬PredecessorHalfFin13Atom2097 chi ∧
      ¬PredecessorHalfFin13Atom2167 chi) ∨
      ((¬PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom1866 chi ∧
      ¬PredecessorHalfFin13Atom1881 chi ∧
      ¬PredecessorHalfFin13Atom1912 chi ∧
      ¬PredecessorHalfFin13Atom1913 chi ∧
      ¬PredecessorHalfFin13Atom1922 chi ∧
      ¬PredecessorHalfFin13Atom1937 chi ∧
      ¬PredecessorHalfFin13Atom1972 chi ∧
      ¬PredecessorHalfFin13Atom2038 chi ∧
      ¬PredecessorHalfFin13Atom2039 chi ∧
      ¬PredecessorHalfFin13Atom2048 chi ∧
      ¬PredecessorHalfFin13Atom2063 chi ∧
      ¬PredecessorHalfFin13Atom2098 chi ∧
      ¬PredecessorHalfFin13Atom2168 chi) ∨
      (¬PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom1858 chi ∧
      ¬PredecessorHalfFin13Atom1867 chi ∧
      ¬PredecessorHalfFin13Atom1882 chi ∧
      ¬PredecessorHalfFin13Atom1912 chi ∧
      ¬PredecessorHalfFin13Atom1914 chi ∧
      ¬PredecessorHalfFin13Atom1923 chi ∧
      ¬PredecessorHalfFin13Atom1938 chi ∧
      ¬PredecessorHalfFin13Atom1973 chi ∧
      ¬PredecessorHalfFin13Atom2038 chi ∧
      ¬PredecessorHalfFin13Atom2040 chi ∧
      ¬PredecessorHalfFin13Atom2049 chi ∧
      ¬PredecessorHalfFin13Atom2064 chi ∧
      ¬PredecessorHalfFin13Atom2099 chi ∧
      ¬PredecessorHalfFin13Atom2169 chi))) ∨
      ((¬PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom1832 chi ∧
      ¬PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom1838 chi ∧
      ¬PredecessorHalfFin13Atom1847 chi ∧
      ¬PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom1859 chi ∧
      ¬PredecessorHalfFin13Atom1868 chi ∧
      ¬PredecessorHalfFin13Atom1883 chi ∧
      ¬PredecessorHalfFin13Atom1912 chi ∧
      ¬PredecessorHalfFin13Atom1915 chi ∧
      ¬PredecessorHalfFin13Atom1924 chi ∧
      ¬PredecessorHalfFin13Atom1939 chi ∧
      ¬PredecessorHalfFin13Atom1974 chi ∧
      ¬PredecessorHalfFin13Atom2038 chi ∧
      ¬PredecessorHalfFin13Atom2041 chi ∧
      ¬PredecessorHalfFin13Atom2050 chi ∧
      ¬PredecessorHalfFin13Atom2065 chi ∧
      ¬PredecessorHalfFin13Atom2100 chi ∧
      ¬PredecessorHalfFin13Atom2170 chi) ∨
      ((¬PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom1839 chi ∧
      ¬PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom1860 chi ∧
      ¬PredecessorHalfFin13Atom1869 chi ∧
      ¬PredecessorHalfFin13Atom1884 chi ∧
      ¬PredecessorHalfFin13Atom1912 chi ∧
      ¬PredecessorHalfFin13Atom1916 chi ∧
      ¬PredecessorHalfFin13Atom1925 chi ∧
      ¬PredecessorHalfFin13Atom1940 chi ∧
      ¬PredecessorHalfFin13Atom1975 chi ∧
      ¬PredecessorHalfFin13Atom2038 chi ∧
      ¬PredecessorHalfFin13Atom2042 chi ∧
      ¬PredecessorHalfFin13Atom2051 chi ∧
      ¬PredecessorHalfFin13Atom2066 chi ∧
      ¬PredecessorHalfFin13Atom2101 chi ∧
      ¬PredecessorHalfFin13Atom2171 chi) ∨
      (¬PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom1858 chi ∧
      ¬PredecessorHalfFin13Atom1870 chi ∧
      ¬PredecessorHalfFin13Atom1885 chi ∧
      ¬PredecessorHalfFin13Atom1913 chi ∧
      ¬PredecessorHalfFin13Atom1914 chi ∧
      ¬PredecessorHalfFin13Atom1926 chi ∧
      ¬PredecessorHalfFin13Atom1941 chi ∧
      ¬PredecessorHalfFin13Atom1976 chi ∧
      ¬PredecessorHalfFin13Atom2039 chi ∧
      ¬PredecessorHalfFin13Atom2040 chi ∧
      ¬PredecessorHalfFin13Atom2052 chi ∧
      ¬PredecessorHalfFin13Atom2067 chi ∧
      ¬PredecessorHalfFin13Atom2102 chi ∧
      ¬PredecessorHalfFin13Atom2172 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom1832 chi ∧
      ¬PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom1838 chi ∧
      ¬PredecessorHalfFin13Atom1850 chi ∧
      ¬PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom1859 chi ∧
      ¬PredecessorHalfFin13Atom1871 chi ∧
      ¬PredecessorHalfFin13Atom1886 chi ∧
      ¬PredecessorHalfFin13Atom1913 chi ∧
      ¬PredecessorHalfFin13Atom1915 chi ∧
      ¬PredecessorHalfFin13Atom1927 chi ∧
      ¬PredecessorHalfFin13Atom1942 chi ∧
      ¬PredecessorHalfFin13Atom1977 chi ∧
      ¬PredecessorHalfFin13Atom2039 chi ∧
      ¬PredecessorHalfFin13Atom2041 chi ∧
      ¬PredecessorHalfFin13Atom2053 chi ∧
      ¬PredecessorHalfFin13Atom2068 chi ∧
      ¬PredecessorHalfFin13Atom2103 chi ∧
      ¬PredecessorHalfFin13Atom2173 chi) ∨
      ((¬PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom1839 chi ∧
      ¬PredecessorHalfFin13Atom1851 chi ∧
      ¬PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom1860 chi ∧
      ¬PredecessorHalfFin13Atom1872 chi ∧
      ¬PredecessorHalfFin13Atom1887 chi ∧
      ¬PredecessorHalfFin13Atom1913 chi ∧
      ¬PredecessorHalfFin13Atom1916 chi ∧
      ¬PredecessorHalfFin13Atom1928 chi ∧
      ¬PredecessorHalfFin13Atom1943 chi ∧
      ¬PredecessorHalfFin13Atom1978 chi ∧
      ¬PredecessorHalfFin13Atom2039 chi ∧
      ¬PredecessorHalfFin13Atom2042 chi ∧
      ¬PredecessorHalfFin13Atom2054 chi ∧
      ¬PredecessorHalfFin13Atom2069 chi ∧
      ¬PredecessorHalfFin13Atom2104 chi ∧
      ¬PredecessorHalfFin13Atom2174 chi) ∨
      (¬PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom1832 chi ∧
      ¬PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom1838 chi ∧
      ¬PredecessorHalfFin13Atom1852 chi ∧
      ¬PredecessorHalfFin13Atom1858 chi ∧
      ¬PredecessorHalfFin13Atom1859 chi ∧
      ¬PredecessorHalfFin13Atom1873 chi ∧
      ¬PredecessorHalfFin13Atom1888 chi ∧
      ¬PredecessorHalfFin13Atom1914 chi ∧
      ¬PredecessorHalfFin13Atom1915 chi ∧
      ¬PredecessorHalfFin13Atom1929 chi ∧
      ¬PredecessorHalfFin13Atom1944 chi ∧
      ¬PredecessorHalfFin13Atom1979 chi ∧
      ¬PredecessorHalfFin13Atom2040 chi ∧
      ¬PredecessorHalfFin13Atom2041 chi ∧
      ¬PredecessorHalfFin13Atom2055 chi ∧
      ¬PredecessorHalfFin13Atom2070 chi ∧
      ¬PredecessorHalfFin13Atom2105 chi ∧
      ¬PredecessorHalfFin13Atom2175 chi))) ∨
      (((¬PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom1839 chi ∧
      ¬PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom1858 chi ∧
      ¬PredecessorHalfFin13Atom1860 chi ∧
      ¬PredecessorHalfFin13Atom1874 chi ∧
      ¬PredecessorHalfFin13Atom1889 chi ∧
      ¬PredecessorHalfFin13Atom1914 chi ∧
      ¬PredecessorHalfFin13Atom1916 chi ∧
      ¬PredecessorHalfFin13Atom1930 chi ∧
      ¬PredecessorHalfFin13Atom1945 chi ∧
      ¬PredecessorHalfFin13Atom1980 chi ∧
      ¬PredecessorHalfFin13Atom2040 chi ∧
      ¬PredecessorHalfFin13Atom2042 chi ∧
      ¬PredecessorHalfFin13Atom2056 chi ∧
      ¬PredecessorHalfFin13Atom2071 chi ∧
      ¬PredecessorHalfFin13Atom2106 chi ∧
      ¬PredecessorHalfFin13Atom2176 chi) ∨
      (¬PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom1832 chi ∧
      ¬PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom1838 chi ∧
      ¬PredecessorHalfFin13Atom1839 chi ∧
      ¬PredecessorHalfFin13Atom1854 chi ∧
      ¬PredecessorHalfFin13Atom1859 chi ∧
      ¬PredecessorHalfFin13Atom1860 chi ∧
      ¬PredecessorHalfFin13Atom1875 chi ∧
      ¬PredecessorHalfFin13Atom1890 chi ∧
      ¬PredecessorHalfFin13Atom1915 chi ∧
      ¬PredecessorHalfFin13Atom1916 chi ∧
      ¬PredecessorHalfFin13Atom1931 chi ∧
      ¬PredecessorHalfFin13Atom1946 chi ∧
      ¬PredecessorHalfFin13Atom1981 chi ∧
      ¬PredecessorHalfFin13Atom2041 chi ∧
      ¬PredecessorHalfFin13Atom2042 chi ∧
      ¬PredecessorHalfFin13Atom2057 chi ∧
      ¬PredecessorHalfFin13Atom2072 chi ∧
      ¬PredecessorHalfFin13Atom2107 chi ∧
      ¬PredecessorHalfFin13Atom2177 chi)) ∨
      ((¬PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom1861 chi ∧
      ¬PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom1866 chi ∧
      ¬PredecessorHalfFin13Atom1891 chi ∧
      ¬PredecessorHalfFin13Atom1917 chi ∧
      ¬PredecessorHalfFin13Atom1918 chi ∧
      ¬PredecessorHalfFin13Atom1922 chi ∧
      ¬PredecessorHalfFin13Atom1947 chi ∧
      ¬PredecessorHalfFin13Atom1982 chi ∧
      ¬PredecessorHalfFin13Atom2043 chi ∧
      ¬PredecessorHalfFin13Atom2044 chi ∧
      ¬PredecessorHalfFin13Atom2048 chi ∧
      ¬PredecessorHalfFin13Atom2073 chi ∧
      ¬PredecessorHalfFin13Atom2108 chi ∧
      ¬PredecessorHalfFin13Atom2178 chi) ∨
      (¬PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom1861 chi ∧
      ¬PredecessorHalfFin13Atom1863 chi ∧
      ¬PredecessorHalfFin13Atom1867 chi ∧
      ¬PredecessorHalfFin13Atom1892 chi ∧
      ¬PredecessorHalfFin13Atom1917 chi ∧
      ¬PredecessorHalfFin13Atom1919 chi ∧
      ¬PredecessorHalfFin13Atom1923 chi ∧
      ¬PredecessorHalfFin13Atom1948 chi ∧
      ¬PredecessorHalfFin13Atom1983 chi ∧
      ¬PredecessorHalfFin13Atom2043 chi ∧
      ¬PredecessorHalfFin13Atom2045 chi ∧
      ¬PredecessorHalfFin13Atom2049 chi ∧
      ¬PredecessorHalfFin13Atom2074 chi ∧
      ¬PredecessorHalfFin13Atom2109 chi ∧
      ¬PredecessorHalfFin13Atom2179 chi))))))) ∨
      ((((((¬PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom1832 chi ∧
      ¬PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom1843 chi ∧
      ¬PredecessorHalfFin13Atom1847 chi ∧
      ¬PredecessorHalfFin13Atom1861 chi ∧
      ¬PredecessorHalfFin13Atom1864 chi ∧
      ¬PredecessorHalfFin13Atom1868 chi ∧
      ¬PredecessorHalfFin13Atom1893 chi ∧
      ¬PredecessorHalfFin13Atom1917 chi ∧
      ¬PredecessorHalfFin13Atom1920 chi ∧
      ¬PredecessorHalfFin13Atom1924 chi ∧
      ¬PredecessorHalfFin13Atom1949 chi ∧
      ¬PredecessorHalfFin13Atom1984 chi ∧
      ¬PredecessorHalfFin13Atom2043 chi ∧
      ¬PredecessorHalfFin13Atom2046 chi ∧
      ¬PredecessorHalfFin13Atom2050 chi ∧
      ¬PredecessorHalfFin13Atom2075 chi ∧
      ¬PredecessorHalfFin13Atom2110 chi ∧
      ¬PredecessorHalfFin13Atom2180 chi) ∨
      ((¬PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom1861 chi ∧
      ¬PredecessorHalfFin13Atom1865 chi ∧
      ¬PredecessorHalfFin13Atom1869 chi ∧
      ¬PredecessorHalfFin13Atom1894 chi ∧
      ¬PredecessorHalfFin13Atom1917 chi ∧
      ¬PredecessorHalfFin13Atom1921 chi ∧
      ¬PredecessorHalfFin13Atom1925 chi ∧
      ¬PredecessorHalfFin13Atom1950 chi ∧
      ¬PredecessorHalfFin13Atom1985 chi ∧
      ¬PredecessorHalfFin13Atom2043 chi ∧
      ¬PredecessorHalfFin13Atom2047 chi ∧
      ¬PredecessorHalfFin13Atom2051 chi ∧
      ¬PredecessorHalfFin13Atom2076 chi ∧
      ¬PredecessorHalfFin13Atom2111 chi ∧
      ¬PredecessorHalfFin13Atom2181 chi) ∨
      (¬PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom1863 chi ∧
      ¬PredecessorHalfFin13Atom1870 chi ∧
      ¬PredecessorHalfFin13Atom1895 chi ∧
      ¬PredecessorHalfFin13Atom1918 chi ∧
      ¬PredecessorHalfFin13Atom1919 chi ∧
      ¬PredecessorHalfFin13Atom1926 chi ∧
      ¬PredecessorHalfFin13Atom1951 chi ∧
      ¬PredecessorHalfFin13Atom1986 chi ∧
      ¬PredecessorHalfFin13Atom2044 chi ∧
      ¬PredecessorHalfFin13Atom2045 chi ∧
      ¬PredecessorHalfFin13Atom2052 chi ∧
      ¬PredecessorHalfFin13Atom2077 chi ∧
      ¬PredecessorHalfFin13Atom2112 chi ∧
      ¬PredecessorHalfFin13Atom2182 chi))) ∨
      ((¬PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom1832 chi ∧
      ¬PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom1843 chi ∧
      ¬PredecessorHalfFin13Atom1850 chi ∧
      ¬PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom1864 chi ∧
      ¬PredecessorHalfFin13Atom1871 chi ∧
      ¬PredecessorHalfFin13Atom1896 chi ∧
      ¬PredecessorHalfFin13Atom1918 chi ∧
      ¬PredecessorHalfFin13Atom1920 chi ∧
      ¬PredecessorHalfFin13Atom1927 chi ∧
      ¬PredecessorHalfFin13Atom1952 chi ∧
      ¬PredecessorHalfFin13Atom1987 chi ∧
      ¬PredecessorHalfFin13Atom2044 chi ∧
      ¬PredecessorHalfFin13Atom2046 chi ∧
      ¬PredecessorHalfFin13Atom2053 chi ∧
      ¬PredecessorHalfFin13Atom2078 chi ∧
      ¬PredecessorHalfFin13Atom2113 chi ∧
      ¬PredecessorHalfFin13Atom2183 chi) ∨
      ((¬PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom1851 chi ∧
      ¬PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom1865 chi ∧
      ¬PredecessorHalfFin13Atom1872 chi ∧
      ¬PredecessorHalfFin13Atom1897 chi ∧
      ¬PredecessorHalfFin13Atom1918 chi ∧
      ¬PredecessorHalfFin13Atom1921 chi ∧
      ¬PredecessorHalfFin13Atom1928 chi ∧
      ¬PredecessorHalfFin13Atom1953 chi ∧
      ¬PredecessorHalfFin13Atom1988 chi ∧
      ¬PredecessorHalfFin13Atom2044 chi ∧
      ¬PredecessorHalfFin13Atom2047 chi ∧
      ¬PredecessorHalfFin13Atom2054 chi ∧
      ¬PredecessorHalfFin13Atom2079 chi ∧
      ¬PredecessorHalfFin13Atom2114 chi ∧
      ¬PredecessorHalfFin13Atom2184 chi) ∨
      (¬PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom1832 chi ∧
      ¬PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom1843 chi ∧
      ¬PredecessorHalfFin13Atom1852 chi ∧
      ¬PredecessorHalfFin13Atom1863 chi ∧
      ¬PredecessorHalfFin13Atom1864 chi ∧
      ¬PredecessorHalfFin13Atom1873 chi ∧
      ¬PredecessorHalfFin13Atom1898 chi ∧
      ¬PredecessorHalfFin13Atom1919 chi ∧
      ¬PredecessorHalfFin13Atom1920 chi ∧
      ¬PredecessorHalfFin13Atom1929 chi ∧
      ¬PredecessorHalfFin13Atom1954 chi ∧
      ¬PredecessorHalfFin13Atom1989 chi ∧
      ¬PredecessorHalfFin13Atom2045 chi ∧
      ¬PredecessorHalfFin13Atom2046 chi ∧
      ¬PredecessorHalfFin13Atom2055 chi ∧
      ¬PredecessorHalfFin13Atom2080 chi ∧
      ¬PredecessorHalfFin13Atom2115 chi ∧
      ¬PredecessorHalfFin13Atom2185 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom1863 chi ∧
      ¬PredecessorHalfFin13Atom1865 chi ∧
      ¬PredecessorHalfFin13Atom1874 chi ∧
      ¬PredecessorHalfFin13Atom1899 chi ∧
      ¬PredecessorHalfFin13Atom1919 chi ∧
      ¬PredecessorHalfFin13Atom1921 chi ∧
      ¬PredecessorHalfFin13Atom1930 chi ∧
      ¬PredecessorHalfFin13Atom1955 chi ∧
      ¬PredecessorHalfFin13Atom1990 chi ∧
      ¬PredecessorHalfFin13Atom2045 chi ∧
      ¬PredecessorHalfFin13Atom2047 chi ∧
      ¬PredecessorHalfFin13Atom2056 chi ∧
      ¬PredecessorHalfFin13Atom2081 chi ∧
      ¬PredecessorHalfFin13Atom2116 chi ∧
      ¬PredecessorHalfFin13Atom2186 chi) ∨
      ((¬PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom1832 chi ∧
      ¬PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom1843 chi ∧
      ¬PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom1854 chi ∧
      ¬PredecessorHalfFin13Atom1864 chi ∧
      ¬PredecessorHalfFin13Atom1865 chi ∧
      ¬PredecessorHalfFin13Atom1875 chi ∧
      ¬PredecessorHalfFin13Atom1900 chi ∧
      ¬PredecessorHalfFin13Atom1920 chi ∧
      ¬PredecessorHalfFin13Atom1921 chi ∧
      ¬PredecessorHalfFin13Atom1931 chi ∧
      ¬PredecessorHalfFin13Atom1956 chi ∧
      ¬PredecessorHalfFin13Atom1991 chi ∧
      ¬PredecessorHalfFin13Atom2046 chi ∧
      ¬PredecessorHalfFin13Atom2047 chi ∧
      ¬PredecessorHalfFin13Atom2057 chi ∧
      ¬PredecessorHalfFin13Atom2082 chi ∧
      ¬PredecessorHalfFin13Atom2117 chi ∧
      ¬PredecessorHalfFin13Atom2187 chi) ∨
      (¬PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom1866 chi ∧
      ¬PredecessorHalfFin13Atom1867 chi ∧
      ¬PredecessorHalfFin13Atom1870 chi ∧
      ¬PredecessorHalfFin13Atom1901 chi ∧
      ¬PredecessorHalfFin13Atom1922 chi ∧
      ¬PredecessorHalfFin13Atom1923 chi ∧
      ¬PredecessorHalfFin13Atom1926 chi ∧
      ¬PredecessorHalfFin13Atom1957 chi ∧
      ¬PredecessorHalfFin13Atom1992 chi ∧
      ¬PredecessorHalfFin13Atom2048 chi ∧
      ¬PredecessorHalfFin13Atom2049 chi ∧
      ¬PredecessorHalfFin13Atom2052 chi ∧
      ¬PredecessorHalfFin13Atom2083 chi ∧
      ¬PredecessorHalfFin13Atom2118 chi ∧
      ¬PredecessorHalfFin13Atom2188 chi))) ∨
      ((¬PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom1832 chi ∧
      ¬PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom1847 chi ∧
      ¬PredecessorHalfFin13Atom1850 chi ∧
      ¬PredecessorHalfFin13Atom1866 chi ∧
      ¬PredecessorHalfFin13Atom1868 chi ∧
      ¬PredecessorHalfFin13Atom1871 chi ∧
      ¬PredecessorHalfFin13Atom1902 chi ∧
      ¬PredecessorHalfFin13Atom1922 chi ∧
      ¬PredecessorHalfFin13Atom1924 chi ∧
      ¬PredecessorHalfFin13Atom1927 chi ∧
      ¬PredecessorHalfFin13Atom1958 chi ∧
      ¬PredecessorHalfFin13Atom1993 chi ∧
      ¬PredecessorHalfFin13Atom2048 chi ∧
      ¬PredecessorHalfFin13Atom2050 chi ∧
      ¬PredecessorHalfFin13Atom2053 chi ∧
      ¬PredecessorHalfFin13Atom2084 chi ∧
      ¬PredecessorHalfFin13Atom2119 chi ∧
      ¬PredecessorHalfFin13Atom2189 chi) ∨
      ((¬PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom1851 chi ∧
      ¬PredecessorHalfFin13Atom1866 chi ∧
      ¬PredecessorHalfFin13Atom1869 chi ∧
      ¬PredecessorHalfFin13Atom1872 chi ∧
      ¬PredecessorHalfFin13Atom1903 chi ∧
      ¬PredecessorHalfFin13Atom1922 chi ∧
      ¬PredecessorHalfFin13Atom1925 chi ∧
      ¬PredecessorHalfFin13Atom1928 chi ∧
      ¬PredecessorHalfFin13Atom1959 chi ∧
      ¬PredecessorHalfFin13Atom1994 chi ∧
      ¬PredecessorHalfFin13Atom2048 chi ∧
      ¬PredecessorHalfFin13Atom2051 chi ∧
      ¬PredecessorHalfFin13Atom2054 chi ∧
      ¬PredecessorHalfFin13Atom2085 chi ∧
      ¬PredecessorHalfFin13Atom2120 chi ∧
      ¬PredecessorHalfFin13Atom2190 chi) ∨
      (¬PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom1832 chi ∧
      ¬PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom1847 chi ∧
      ¬PredecessorHalfFin13Atom1852 chi ∧
      ¬PredecessorHalfFin13Atom1867 chi ∧
      ¬PredecessorHalfFin13Atom1868 chi ∧
      ¬PredecessorHalfFin13Atom1873 chi ∧
      ¬PredecessorHalfFin13Atom1904 chi ∧
      ¬PredecessorHalfFin13Atom1923 chi ∧
      ¬PredecessorHalfFin13Atom1924 chi ∧
      ¬PredecessorHalfFin13Atom1929 chi ∧
      ¬PredecessorHalfFin13Atom1960 chi ∧
      ¬PredecessorHalfFin13Atom1995 chi ∧
      ¬PredecessorHalfFin13Atom2049 chi ∧
      ¬PredecessorHalfFin13Atom2050 chi ∧
      ¬PredecessorHalfFin13Atom2055 chi ∧
      ¬PredecessorHalfFin13Atom2086 chi ∧
      ¬PredecessorHalfFin13Atom2121 chi ∧
      ¬PredecessorHalfFin13Atom2191 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom1867 chi ∧
      ¬PredecessorHalfFin13Atom1869 chi ∧
      ¬PredecessorHalfFin13Atom1874 chi ∧
      ¬PredecessorHalfFin13Atom1905 chi ∧
      ¬PredecessorHalfFin13Atom1923 chi ∧
      ¬PredecessorHalfFin13Atom1925 chi ∧
      ¬PredecessorHalfFin13Atom1930 chi ∧
      ¬PredecessorHalfFin13Atom1961 chi ∧
      ¬PredecessorHalfFin13Atom1996 chi ∧
      ¬PredecessorHalfFin13Atom2049 chi ∧
      ¬PredecessorHalfFin13Atom2051 chi ∧
      ¬PredecessorHalfFin13Atom2056 chi ∧
      ¬PredecessorHalfFin13Atom2087 chi ∧
      ¬PredecessorHalfFin13Atom2122 chi ∧
      ¬PredecessorHalfFin13Atom2192 chi) ∨
      ((¬PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom1832 chi ∧
      ¬PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom1847 chi ∧
      ¬PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom1854 chi ∧
      ¬PredecessorHalfFin13Atom1868 chi ∧
      ¬PredecessorHalfFin13Atom1869 chi ∧
      ¬PredecessorHalfFin13Atom1875 chi ∧
      ¬PredecessorHalfFin13Atom1906 chi ∧
      ¬PredecessorHalfFin13Atom1924 chi ∧
      ¬PredecessorHalfFin13Atom1925 chi ∧
      ¬PredecessorHalfFin13Atom1931 chi ∧
      ¬PredecessorHalfFin13Atom1962 chi ∧
      ¬PredecessorHalfFin13Atom1997 chi ∧
      ¬PredecessorHalfFin13Atom2050 chi ∧
      ¬PredecessorHalfFin13Atom2051 chi ∧
      ¬PredecessorHalfFin13Atom2057 chi ∧
      ¬PredecessorHalfFin13Atom2088 chi ∧
      ¬PredecessorHalfFin13Atom2123 chi ∧
      ¬PredecessorHalfFin13Atom2193 chi) ∨
      (¬PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom1832 chi ∧
      ¬PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom1850 chi ∧
      ¬PredecessorHalfFin13Atom1852 chi ∧
      ¬PredecessorHalfFin13Atom1870 chi ∧
      ¬PredecessorHalfFin13Atom1871 chi ∧
      ¬PredecessorHalfFin13Atom1873 chi ∧
      ¬PredecessorHalfFin13Atom1907 chi ∧
      ¬PredecessorHalfFin13Atom1926 chi ∧
      ¬PredecessorHalfFin13Atom1927 chi ∧
      ¬PredecessorHalfFin13Atom1929 chi ∧
      ¬PredecessorHalfFin13Atom1963 chi ∧
      ¬PredecessorHalfFin13Atom1998 chi ∧
      ¬PredecessorHalfFin13Atom2052 chi ∧
      ¬PredecessorHalfFin13Atom2053 chi ∧
      ¬PredecessorHalfFin13Atom2055 chi ∧
      ¬PredecessorHalfFin13Atom2089 chi ∧
      ¬PredecessorHalfFin13Atom2124 chi ∧
      ¬PredecessorHalfFin13Atom2194 chi))) ∨
      ((¬PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom1851 chi ∧
      ¬PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom1870 chi ∧
      ¬PredecessorHalfFin13Atom1872 chi ∧
      ¬PredecessorHalfFin13Atom1874 chi ∧
      ¬PredecessorHalfFin13Atom1908 chi ∧
      ¬PredecessorHalfFin13Atom1926 chi ∧
      ¬PredecessorHalfFin13Atom1928 chi ∧
      ¬PredecessorHalfFin13Atom1930 chi ∧
      ¬PredecessorHalfFin13Atom1964 chi ∧
      ¬PredecessorHalfFin13Atom1999 chi ∧
      ¬PredecessorHalfFin13Atom2052 chi ∧
      ¬PredecessorHalfFin13Atom2054 chi ∧
      ¬PredecessorHalfFin13Atom2056 chi ∧
      ¬PredecessorHalfFin13Atom2090 chi ∧
      ¬PredecessorHalfFin13Atom2125 chi ∧
      ¬PredecessorHalfFin13Atom2195 chi) ∨
      ((¬PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom1832 chi ∧
      ¬PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom1850 chi ∧
      ¬PredecessorHalfFin13Atom1851 chi ∧
      ¬PredecessorHalfFin13Atom1854 chi ∧
      ¬PredecessorHalfFin13Atom1871 chi ∧
      ¬PredecessorHalfFin13Atom1872 chi ∧
      ¬PredecessorHalfFin13Atom1875 chi ∧
      ¬PredecessorHalfFin13Atom1909 chi ∧
      ¬PredecessorHalfFin13Atom1927 chi ∧
      ¬PredecessorHalfFin13Atom1928 chi ∧
      ¬PredecessorHalfFin13Atom1931 chi ∧
      ¬PredecessorHalfFin13Atom1965 chi ∧
      ¬PredecessorHalfFin13Atom2000 chi ∧
      ¬PredecessorHalfFin13Atom2053 chi ∧
      ¬PredecessorHalfFin13Atom2054 chi ∧
      ¬PredecessorHalfFin13Atom2057 chi ∧
      ¬PredecessorHalfFin13Atom2091 chi ∧
      ¬PredecessorHalfFin13Atom2126 chi ∧
      ¬PredecessorHalfFin13Atom2196 chi) ∨
      (¬PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom1832 chi ∧
      ¬PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom1852 chi ∧
      ¬PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom1854 chi ∧
      ¬PredecessorHalfFin13Atom1873 chi ∧
      ¬PredecessorHalfFin13Atom1874 chi ∧
      ¬PredecessorHalfFin13Atom1875 chi ∧
      ¬PredecessorHalfFin13Atom1910 chi ∧
      ¬PredecessorHalfFin13Atom1929 chi ∧
      ¬PredecessorHalfFin13Atom1930 chi ∧
      ¬PredecessorHalfFin13Atom1931 chi ∧
      ¬PredecessorHalfFin13Atom1966 chi ∧
      ¬PredecessorHalfFin13Atom2001 chi ∧
      ¬PredecessorHalfFin13Atom2055 chi ∧
      ¬PredecessorHalfFin13Atom2056 chi ∧
      ¬PredecessorHalfFin13Atom2057 chi ∧
      ¬PredecessorHalfFin13Atom2092 chi ∧
      ¬PredecessorHalfFin13Atom2127 chi ∧
      ¬PredecessorHalfFin13Atom2197 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom1881 chi ∧
      ¬PredecessorHalfFin13Atom1891 chi ∧
      ¬PredecessorHalfFin13Atom1932 chi ∧
      ¬PredecessorHalfFin13Atom1933 chi ∧
      ¬PredecessorHalfFin13Atom1937 chi ∧
      ¬PredecessorHalfFin13Atom1947 chi ∧
      ¬PredecessorHalfFin13Atom2002 chi ∧
      ¬PredecessorHalfFin13Atom2058 chi ∧
      ¬PredecessorHalfFin13Atom2059 chi ∧
      ¬PredecessorHalfFin13Atom2063 chi ∧
      ¬PredecessorHalfFin13Atom2073 chi ∧
      ¬PredecessorHalfFin13Atom2128 chi ∧
      ¬PredecessorHalfFin13Atom2198 chi) ∨
      ((¬PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom1878 chi ∧
      ¬PredecessorHalfFin13Atom1882 chi ∧
      ¬PredecessorHalfFin13Atom1892 chi ∧
      ¬PredecessorHalfFin13Atom1932 chi ∧
      ¬PredecessorHalfFin13Atom1934 chi ∧
      ¬PredecessorHalfFin13Atom1938 chi ∧
      ¬PredecessorHalfFin13Atom1948 chi ∧
      ¬PredecessorHalfFin13Atom2003 chi ∧
      ¬PredecessorHalfFin13Atom2058 chi ∧
      ¬PredecessorHalfFin13Atom2060 chi ∧
      ¬PredecessorHalfFin13Atom2064 chi ∧
      ¬PredecessorHalfFin13Atom2074 chi ∧
      ¬PredecessorHalfFin13Atom2129 chi ∧
      ¬PredecessorHalfFin13Atom2199 chi) ∨
      (¬PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom1838 chi ∧
      ¬PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom1843 chi ∧
      ¬PredecessorHalfFin13Atom1847 chi ∧
      ¬PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom1879 chi ∧
      ¬PredecessorHalfFin13Atom1883 chi ∧
      ¬PredecessorHalfFin13Atom1893 chi ∧
      ¬PredecessorHalfFin13Atom1932 chi ∧
      ¬PredecessorHalfFin13Atom1935 chi ∧
      ¬PredecessorHalfFin13Atom1939 chi ∧
      ¬PredecessorHalfFin13Atom1949 chi ∧
      ¬PredecessorHalfFin13Atom2004 chi ∧
      ¬PredecessorHalfFin13Atom2058 chi ∧
      ¬PredecessorHalfFin13Atom2061 chi ∧
      ¬PredecessorHalfFin13Atom2065 chi ∧
      ¬PredecessorHalfFin13Atom2075 chi ∧
      ¬PredecessorHalfFin13Atom2130 chi ∧
      ¬PredecessorHalfFin13Atom2200 chi))) ∨
      (((¬PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom1839 chi ∧
      ¬PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom1880 chi ∧
      ¬PredecessorHalfFin13Atom1884 chi ∧
      ¬PredecessorHalfFin13Atom1894 chi ∧
      ¬PredecessorHalfFin13Atom1932 chi ∧
      ¬PredecessorHalfFin13Atom1936 chi ∧
      ¬PredecessorHalfFin13Atom1940 chi ∧
      ¬PredecessorHalfFin13Atom1950 chi ∧
      ¬PredecessorHalfFin13Atom2005 chi ∧
      ¬PredecessorHalfFin13Atom2058 chi ∧
      ¬PredecessorHalfFin13Atom2062 chi ∧
      ¬PredecessorHalfFin13Atom2066 chi ∧
      ¬PredecessorHalfFin13Atom2076 chi ∧
      ¬PredecessorHalfFin13Atom2131 chi ∧
      ¬PredecessorHalfFin13Atom2201 chi) ∨
      (¬PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom1878 chi ∧
      ¬PredecessorHalfFin13Atom1885 chi ∧
      ¬PredecessorHalfFin13Atom1895 chi ∧
      ¬PredecessorHalfFin13Atom1933 chi ∧
      ¬PredecessorHalfFin13Atom1934 chi ∧
      ¬PredecessorHalfFin13Atom1941 chi ∧
      ¬PredecessorHalfFin13Atom1951 chi ∧
      ¬PredecessorHalfFin13Atom2006 chi ∧
      ¬PredecessorHalfFin13Atom2059 chi ∧
      ¬PredecessorHalfFin13Atom2060 chi ∧
      ¬PredecessorHalfFin13Atom2067 chi ∧
      ¬PredecessorHalfFin13Atom2077 chi ∧
      ¬PredecessorHalfFin13Atom2132 chi ∧
      ¬PredecessorHalfFin13Atom2202 chi)) ∨
      ((¬PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom1838 chi ∧
      ¬PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom1843 chi ∧
      ¬PredecessorHalfFin13Atom1850 chi ∧
      ¬PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom1879 chi ∧
      ¬PredecessorHalfFin13Atom1886 chi ∧
      ¬PredecessorHalfFin13Atom1896 chi ∧
      ¬PredecessorHalfFin13Atom1933 chi ∧
      ¬PredecessorHalfFin13Atom1935 chi ∧
      ¬PredecessorHalfFin13Atom1942 chi ∧
      ¬PredecessorHalfFin13Atom1952 chi ∧
      ¬PredecessorHalfFin13Atom2007 chi ∧
      ¬PredecessorHalfFin13Atom2059 chi ∧
      ¬PredecessorHalfFin13Atom2061 chi ∧
      ¬PredecessorHalfFin13Atom2068 chi ∧
      ¬PredecessorHalfFin13Atom2078 chi ∧
      ¬PredecessorHalfFin13Atom2133 chi ∧
      ¬PredecessorHalfFin13Atom2203 chi) ∨
      (¬PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom1839 chi ∧
      ¬PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom1851 chi ∧
      ¬PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom1880 chi ∧
      ¬PredecessorHalfFin13Atom1887 chi ∧
      ¬PredecessorHalfFin13Atom1897 chi ∧
      ¬PredecessorHalfFin13Atom1933 chi ∧
      ¬PredecessorHalfFin13Atom1936 chi ∧
      ¬PredecessorHalfFin13Atom1943 chi ∧
      ¬PredecessorHalfFin13Atom1953 chi ∧
      ¬PredecessorHalfFin13Atom2008 chi ∧
      ¬PredecessorHalfFin13Atom2059 chi ∧
      ¬PredecessorHalfFin13Atom2062 chi ∧
      ¬PredecessorHalfFin13Atom2069 chi ∧
      ¬PredecessorHalfFin13Atom2079 chi ∧
      ¬PredecessorHalfFin13Atom2134 chi ∧
      ¬PredecessorHalfFin13Atom2204 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom1838 chi ∧
      ¬PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom1843 chi ∧
      ¬PredecessorHalfFin13Atom1852 chi ∧
      ¬PredecessorHalfFin13Atom1878 chi ∧
      ¬PredecessorHalfFin13Atom1879 chi ∧
      ¬PredecessorHalfFin13Atom1888 chi ∧
      ¬PredecessorHalfFin13Atom1898 chi ∧
      ¬PredecessorHalfFin13Atom1934 chi ∧
      ¬PredecessorHalfFin13Atom1935 chi ∧
      ¬PredecessorHalfFin13Atom1944 chi ∧
      ¬PredecessorHalfFin13Atom1954 chi ∧
      ¬PredecessorHalfFin13Atom2009 chi ∧
      ¬PredecessorHalfFin13Atom2060 chi ∧
      ¬PredecessorHalfFin13Atom2061 chi ∧
      ¬PredecessorHalfFin13Atom2070 chi ∧
      ¬PredecessorHalfFin13Atom2080 chi ∧
      ¬PredecessorHalfFin13Atom2135 chi ∧
      ¬PredecessorHalfFin13Atom2205 chi) ∨
      ((¬PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom1839 chi ∧
      ¬PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom1878 chi ∧
      ¬PredecessorHalfFin13Atom1880 chi ∧
      ¬PredecessorHalfFin13Atom1889 chi ∧
      ¬PredecessorHalfFin13Atom1899 chi ∧
      ¬PredecessorHalfFin13Atom1934 chi ∧
      ¬PredecessorHalfFin13Atom1936 chi ∧
      ¬PredecessorHalfFin13Atom1945 chi ∧
      ¬PredecessorHalfFin13Atom1955 chi ∧
      ¬PredecessorHalfFin13Atom2010 chi ∧
      ¬PredecessorHalfFin13Atom2060 chi ∧
      ¬PredecessorHalfFin13Atom2062 chi ∧
      ¬PredecessorHalfFin13Atom2071 chi ∧
      ¬PredecessorHalfFin13Atom2081 chi ∧
      ¬PredecessorHalfFin13Atom2136 chi ∧
      ¬PredecessorHalfFin13Atom2206 chi) ∨
      (¬PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom1881 chi ∧
      ¬PredecessorHalfFin13Atom1882 chi ∧
      ¬PredecessorHalfFin13Atom1885 chi ∧
      ¬PredecessorHalfFin13Atom1901 chi ∧
      ¬PredecessorHalfFin13Atom1937 chi ∧
      ¬PredecessorHalfFin13Atom1938 chi ∧
      ¬PredecessorHalfFin13Atom1941 chi ∧
      ¬PredecessorHalfFin13Atom1957 chi ∧
      ¬PredecessorHalfFin13Atom2012 chi ∧
      ¬PredecessorHalfFin13Atom2063 chi ∧
      ¬PredecessorHalfFin13Atom2064 chi ∧
      ¬PredecessorHalfFin13Atom2067 chi ∧
      ¬PredecessorHalfFin13Atom2083 chi ∧
      ¬PredecessorHalfFin13Atom2138 chi ∧
      ¬PredecessorHalfFin13Atom2208 chi))) ∨
      ((¬PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom1839 chi ∧
      ¬PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom1851 chi ∧
      ¬PredecessorHalfFin13Atom1881 chi ∧
      ¬PredecessorHalfFin13Atom1884 chi ∧
      ¬PredecessorHalfFin13Atom1887 chi ∧
      ¬PredecessorHalfFin13Atom1903 chi ∧
      ¬PredecessorHalfFin13Atom1937 chi ∧
      ¬PredecessorHalfFin13Atom1940 chi ∧
      ¬PredecessorHalfFin13Atom1943 chi ∧
      ¬PredecessorHalfFin13Atom1959 chi ∧
      ¬PredecessorHalfFin13Atom2014 chi ∧
      ¬PredecessorHalfFin13Atom2063 chi ∧
      ¬PredecessorHalfFin13Atom2066 chi ∧
      ¬PredecessorHalfFin13Atom2069 chi ∧
      ¬PredecessorHalfFin13Atom2085 chi ∧
      ¬PredecessorHalfFin13Atom2140 chi ∧
      ¬PredecessorHalfFin13Atom2210 chi) ∨
      ((¬PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom1838 chi ∧
      ¬PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom1847 chi ∧
      ¬PredecessorHalfFin13Atom1852 chi ∧
      ¬PredecessorHalfFin13Atom1882 chi ∧
      ¬PredecessorHalfFin13Atom1883 chi ∧
      ¬PredecessorHalfFin13Atom1888 chi ∧
      ¬PredecessorHalfFin13Atom1904 chi ∧
      ¬PredecessorHalfFin13Atom1938 chi ∧
      ¬PredecessorHalfFin13Atom1939 chi ∧
      ¬PredecessorHalfFin13Atom1944 chi ∧
      ¬PredecessorHalfFin13Atom1960 chi ∧
      ¬PredecessorHalfFin13Atom2015 chi ∧
      ¬PredecessorHalfFin13Atom2064 chi ∧
      ¬PredecessorHalfFin13Atom2065 chi ∧
      ¬PredecessorHalfFin13Atom2070 chi ∧
      ¬PredecessorHalfFin13Atom2086 chi ∧
      ¬PredecessorHalfFin13Atom2141 chi ∧
      ¬PredecessorHalfFin13Atom2211 chi) ∨
      (¬PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom1839 chi ∧
      ¬PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom1882 chi ∧
      ¬PredecessorHalfFin13Atom1884 chi ∧
      ¬PredecessorHalfFin13Atom1889 chi ∧
      ¬PredecessorHalfFin13Atom1905 chi ∧
      ¬PredecessorHalfFin13Atom1938 chi ∧
      ¬PredecessorHalfFin13Atom1940 chi ∧
      ¬PredecessorHalfFin13Atom1945 chi ∧
      ¬PredecessorHalfFin13Atom1961 chi ∧
      ¬PredecessorHalfFin13Atom2016 chi ∧
      ¬PredecessorHalfFin13Atom2064 chi ∧
      ¬PredecessorHalfFin13Atom2066 chi ∧
      ¬PredecessorHalfFin13Atom2071 chi ∧
      ¬PredecessorHalfFin13Atom2087 chi ∧
      ¬PredecessorHalfFin13Atom2142 chi ∧
      ¬PredecessorHalfFin13Atom2212 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom1838 chi ∧
      ¬PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom1850 chi ∧
      ¬PredecessorHalfFin13Atom1852 chi ∧
      ¬PredecessorHalfFin13Atom1885 chi ∧
      ¬PredecessorHalfFin13Atom1886 chi ∧
      ¬PredecessorHalfFin13Atom1888 chi ∧
      ¬PredecessorHalfFin13Atom1907 chi ∧
      ¬PredecessorHalfFin13Atom1941 chi ∧
      ¬PredecessorHalfFin13Atom1942 chi ∧
      ¬PredecessorHalfFin13Atom1944 chi ∧
      ¬PredecessorHalfFin13Atom1963 chi ∧
      ¬PredecessorHalfFin13Atom2018 chi ∧
      ¬PredecessorHalfFin13Atom2067 chi ∧
      ¬PredecessorHalfFin13Atom2068 chi ∧
      ¬PredecessorHalfFin13Atom2070 chi ∧
      ¬PredecessorHalfFin13Atom2089 chi ∧
      ¬PredecessorHalfFin13Atom2144 chi ∧
      ¬PredecessorHalfFin13Atom2214 chi) ∨
      ((¬PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom1839 chi ∧
      ¬PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom1851 chi ∧
      ¬PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom1885 chi ∧
      ¬PredecessorHalfFin13Atom1887 chi ∧
      ¬PredecessorHalfFin13Atom1889 chi ∧
      ¬PredecessorHalfFin13Atom1908 chi ∧
      ¬PredecessorHalfFin13Atom1941 chi ∧
      ¬PredecessorHalfFin13Atom1943 chi ∧
      ¬PredecessorHalfFin13Atom1945 chi ∧
      ¬PredecessorHalfFin13Atom1964 chi ∧
      ¬PredecessorHalfFin13Atom2019 chi ∧
      ¬PredecessorHalfFin13Atom2067 chi ∧
      ¬PredecessorHalfFin13Atom2069 chi ∧
      ¬PredecessorHalfFin13Atom2071 chi ∧
      ¬PredecessorHalfFin13Atom2090 chi ∧
      ¬PredecessorHalfFin13Atom2145 chi ∧
      ¬PredecessorHalfFin13Atom2215 chi) ∨
      (¬PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom1891 chi ∧
      ¬PredecessorHalfFin13Atom1892 chi ∧
      ¬PredecessorHalfFin13Atom1895 chi ∧
      ¬PredecessorHalfFin13Atom1901 chi ∧
      ¬PredecessorHalfFin13Atom1947 chi ∧
      ¬PredecessorHalfFin13Atom1948 chi ∧
      ¬PredecessorHalfFin13Atom1951 chi ∧
      ¬PredecessorHalfFin13Atom1957 chi ∧
      ¬PredecessorHalfFin13Atom2022 chi ∧
      ¬PredecessorHalfFin13Atom2073 chi ∧
      ¬PredecessorHalfFin13Atom2074 chi ∧
      ¬PredecessorHalfFin13Atom2077 chi ∧
      ¬PredecessorHalfFin13Atom2083 chi ∧
      ¬PredecessorHalfFin13Atom2148 chi ∧
      ¬PredecessorHalfFin13Atom2218 chi))) ∨
      ((¬PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom1843 chi ∧
      ¬PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom1847 chi ∧
      ¬PredecessorHalfFin13Atom1850 chi ∧
      ¬PredecessorHalfFin13Atom1891 chi ∧
      ¬PredecessorHalfFin13Atom1893 chi ∧
      ¬PredecessorHalfFin13Atom1896 chi ∧
      ¬PredecessorHalfFin13Atom1902 chi ∧
      ¬PredecessorHalfFin13Atom1947 chi ∧
      ¬PredecessorHalfFin13Atom1949 chi ∧
      ¬PredecessorHalfFin13Atom1952 chi ∧
      ¬PredecessorHalfFin13Atom1958 chi ∧
      ¬PredecessorHalfFin13Atom2023 chi ∧
      ¬PredecessorHalfFin13Atom2073 chi ∧
      ¬PredecessorHalfFin13Atom2075 chi ∧
      ¬PredecessorHalfFin13Atom2078 chi ∧
      ¬PredecessorHalfFin13Atom2084 chi ∧
      ¬PredecessorHalfFin13Atom2149 chi ∧
      ¬PredecessorHalfFin13Atom2219 chi) ∨
      ((¬PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom1851 chi ∧
      ¬PredecessorHalfFin13Atom1891 chi ∧
      ¬PredecessorHalfFin13Atom1894 chi ∧
      ¬PredecessorHalfFin13Atom1897 chi ∧
      ¬PredecessorHalfFin13Atom1903 chi ∧
      ¬PredecessorHalfFin13Atom1947 chi ∧
      ¬PredecessorHalfFin13Atom1950 chi ∧
      ¬PredecessorHalfFin13Atom1953 chi ∧
      ¬PredecessorHalfFin13Atom1959 chi ∧
      ¬PredecessorHalfFin13Atom2024 chi ∧
      ¬PredecessorHalfFin13Atom2073 chi ∧
      ¬PredecessorHalfFin13Atom2076 chi ∧
      ¬PredecessorHalfFin13Atom2079 chi ∧
      ¬PredecessorHalfFin13Atom2085 chi ∧
      ¬PredecessorHalfFin13Atom2150 chi ∧
      ¬PredecessorHalfFin13Atom2220 chi) ∨
      (¬PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom1843 chi ∧
      ¬PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom1847 chi ∧
      ¬PredecessorHalfFin13Atom1852 chi ∧
      ¬PredecessorHalfFin13Atom1892 chi ∧
      ¬PredecessorHalfFin13Atom1893 chi ∧
      ¬PredecessorHalfFin13Atom1898 chi ∧
      ¬PredecessorHalfFin13Atom1904 chi ∧
      ¬PredecessorHalfFin13Atom1948 chi ∧
      ¬PredecessorHalfFin13Atom1949 chi ∧
      ¬PredecessorHalfFin13Atom1954 chi ∧
      ¬PredecessorHalfFin13Atom1960 chi ∧
      ¬PredecessorHalfFin13Atom2025 chi ∧
      ¬PredecessorHalfFin13Atom2074 chi ∧
      ¬PredecessorHalfFin13Atom2075 chi ∧
      ¬PredecessorHalfFin13Atom2080 chi ∧
      ¬PredecessorHalfFin13Atom2086 chi ∧
      ¬PredecessorHalfFin13Atom2151 chi ∧
      ¬PredecessorHalfFin13Atom2221 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom1892 chi ∧
      ¬PredecessorHalfFin13Atom1894 chi ∧
      ¬PredecessorHalfFin13Atom1899 chi ∧
      ¬PredecessorHalfFin13Atom1905 chi ∧
      ¬PredecessorHalfFin13Atom1948 chi ∧
      ¬PredecessorHalfFin13Atom1950 chi ∧
      ¬PredecessorHalfFin13Atom1955 chi ∧
      ¬PredecessorHalfFin13Atom1961 chi ∧
      ¬PredecessorHalfFin13Atom2026 chi ∧
      ¬PredecessorHalfFin13Atom2074 chi ∧
      ¬PredecessorHalfFin13Atom2076 chi ∧
      ¬PredecessorHalfFin13Atom2081 chi ∧
      ¬PredecessorHalfFin13Atom2087 chi ∧
      ¬PredecessorHalfFin13Atom2152 chi ∧
      ¬PredecessorHalfFin13Atom2222 chi) ∨
      ((¬PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom1843 chi ∧
      ¬PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom1850 chi ∧
      ¬PredecessorHalfFin13Atom1852 chi ∧
      ¬PredecessorHalfFin13Atom1895 chi ∧
      ¬PredecessorHalfFin13Atom1896 chi ∧
      ¬PredecessorHalfFin13Atom1898 chi ∧
      ¬PredecessorHalfFin13Atom1907 chi ∧
      ¬PredecessorHalfFin13Atom1951 chi ∧
      ¬PredecessorHalfFin13Atom1952 chi ∧
      ¬PredecessorHalfFin13Atom1954 chi ∧
      ¬PredecessorHalfFin13Atom1963 chi ∧
      ¬PredecessorHalfFin13Atom2028 chi ∧
      ¬PredecessorHalfFin13Atom2077 chi ∧
      ¬PredecessorHalfFin13Atom2078 chi ∧
      ¬PredecessorHalfFin13Atom2080 chi ∧
      ¬PredecessorHalfFin13Atom2089 chi ∧
      ¬PredecessorHalfFin13Atom2154 chi ∧
      ¬PredecessorHalfFin13Atom2224 chi) ∨
      (¬PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom1851 chi ∧
      ¬PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom1895 chi ∧
      ¬PredecessorHalfFin13Atom1897 chi ∧
      ¬PredecessorHalfFin13Atom1899 chi ∧
      ¬PredecessorHalfFin13Atom1908 chi ∧
      ¬PredecessorHalfFin13Atom1951 chi ∧
      ¬PredecessorHalfFin13Atom1953 chi ∧
      ¬PredecessorHalfFin13Atom1955 chi ∧
      ¬PredecessorHalfFin13Atom1964 chi ∧
      ¬PredecessorHalfFin13Atom2029 chi ∧
      ¬PredecessorHalfFin13Atom2077 chi ∧
      ¬PredecessorHalfFin13Atom2079 chi ∧
      ¬PredecessorHalfFin13Atom2081 chi ∧
      ¬PredecessorHalfFin13Atom2090 chi ∧
      ¬PredecessorHalfFin13Atom2155 chi ∧
      ¬PredecessorHalfFin13Atom2225 chi))) ∨
      ((¬PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom1843 chi ∧
      ¬PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom1852 chi ∧
      ¬PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom1854 chi ∧
      ¬PredecessorHalfFin13Atom1898 chi ∧
      ¬PredecessorHalfFin13Atom1899 chi ∧
      ¬PredecessorHalfFin13Atom1900 chi ∧
      ¬PredecessorHalfFin13Atom1910 chi ∧
      ¬PredecessorHalfFin13Atom1954 chi ∧
      ¬PredecessorHalfFin13Atom1955 chi ∧
      ¬PredecessorHalfFin13Atom1956 chi ∧
      ¬PredecessorHalfFin13Atom1966 chi ∧
      ¬PredecessorHalfFin13Atom2031 chi ∧
      ¬PredecessorHalfFin13Atom2080 chi ∧
      ¬PredecessorHalfFin13Atom2081 chi ∧
      ¬PredecessorHalfFin13Atom2082 chi ∧
      ¬PredecessorHalfFin13Atom2092 chi ∧
      ¬PredecessorHalfFin13Atom2157 chi ∧
      ¬PredecessorHalfFin13Atom2227 chi) ∨
      ((¬PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom1851 chi ∧
      ¬PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom1901 chi ∧
      ¬PredecessorHalfFin13Atom1903 chi ∧
      ¬PredecessorHalfFin13Atom1905 chi ∧
      ¬PredecessorHalfFin13Atom1908 chi ∧
      ¬PredecessorHalfFin13Atom1957 chi ∧
      ¬PredecessorHalfFin13Atom1959 chi ∧
      ¬PredecessorHalfFin13Atom1961 chi ∧
      ¬PredecessorHalfFin13Atom1964 chi ∧
      ¬PredecessorHalfFin13Atom2033 chi ∧
      ¬PredecessorHalfFin13Atom2083 chi ∧
      ¬PredecessorHalfFin13Atom2085 chi ∧
      ¬PredecessorHalfFin13Atom2087 chi ∧
      ¬PredecessorHalfFin13Atom2090 chi ∧
      ¬PredecessorHalfFin13Atom2159 chi ∧
      ¬PredecessorHalfFin13Atom2229 chi) ∨
      (¬PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom1847 chi ∧
      ¬PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom1852 chi ∧
      ¬PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom1854 chi ∧
      ¬PredecessorHalfFin13Atom1904 chi ∧
      ¬PredecessorHalfFin13Atom1905 chi ∧
      ¬PredecessorHalfFin13Atom1906 chi ∧
      ¬PredecessorHalfFin13Atom1910 chi ∧
      ¬PredecessorHalfFin13Atom1960 chi ∧
      ¬PredecessorHalfFin13Atom1961 chi ∧
      ¬PredecessorHalfFin13Atom1962 chi ∧
      ¬PredecessorHalfFin13Atom1966 chi ∧
      ¬PredecessorHalfFin13Atom2035 chi ∧
      ¬PredecessorHalfFin13Atom2086 chi ∧
      ¬PredecessorHalfFin13Atom2087 chi ∧
      ¬PredecessorHalfFin13Atom2088 chi ∧
      ¬PredecessorHalfFin13Atom2092 chi ∧
      ¬PredecessorHalfFin13Atom2161 chi ∧
      ¬PredecessorHalfFin13Atom2231 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom1861 chi ∧
      ¬PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom1866 chi ∧
      ¬PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom1881 chi ∧
      ¬PredecessorHalfFin13Atom1891 chi ∧
      ¬PredecessorHalfFin13Atom1967 chi ∧
      ¬PredecessorHalfFin13Atom1968 chi ∧
      ¬PredecessorHalfFin13Atom1972 chi ∧
      ¬PredecessorHalfFin13Atom1982 chi ∧
      ¬PredecessorHalfFin13Atom2002 chi ∧
      ¬PredecessorHalfFin13Atom2093 chi ∧
      ¬PredecessorHalfFin13Atom2094 chi ∧
      ¬PredecessorHalfFin13Atom2098 chi ∧
      ¬PredecessorHalfFin13Atom2108 chi ∧
      ¬PredecessorHalfFin13Atom2128 chi ∧
      ¬PredecessorHalfFin13Atom2233 chi) ∨
      ((¬PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom1858 chi ∧
      ¬PredecessorHalfFin13Atom1861 chi ∧
      ¬PredecessorHalfFin13Atom1863 chi ∧
      ¬PredecessorHalfFin13Atom1867 chi ∧
      ¬PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom1878 chi ∧
      ¬PredecessorHalfFin13Atom1882 chi ∧
      ¬PredecessorHalfFin13Atom1892 chi ∧
      ¬PredecessorHalfFin13Atom1967 chi ∧
      ¬PredecessorHalfFin13Atom1969 chi ∧
      ¬PredecessorHalfFin13Atom1973 chi ∧
      ¬PredecessorHalfFin13Atom1983 chi ∧
      ¬PredecessorHalfFin13Atom2003 chi ∧
      ¬PredecessorHalfFin13Atom2093 chi ∧
      ¬PredecessorHalfFin13Atom2095 chi ∧
      ¬PredecessorHalfFin13Atom2099 chi ∧
      ¬PredecessorHalfFin13Atom2109 chi ∧
      ¬PredecessorHalfFin13Atom2129 chi ∧
      ¬PredecessorHalfFin13Atom2234 chi) ∨
      (¬PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom1859 chi ∧
      ¬PredecessorHalfFin13Atom1861 chi ∧
      ¬PredecessorHalfFin13Atom1864 chi ∧
      ¬PredecessorHalfFin13Atom1868 chi ∧
      ¬PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom1879 chi ∧
      ¬PredecessorHalfFin13Atom1883 chi ∧
      ¬PredecessorHalfFin13Atom1893 chi ∧
      ¬PredecessorHalfFin13Atom1967 chi ∧
      ¬PredecessorHalfFin13Atom1970 chi ∧
      ¬PredecessorHalfFin13Atom1974 chi ∧
      ¬PredecessorHalfFin13Atom1984 chi ∧
      ¬PredecessorHalfFin13Atom2004 chi ∧
      ¬PredecessorHalfFin13Atom2093 chi ∧
      ¬PredecessorHalfFin13Atom2096 chi ∧
      ¬PredecessorHalfFin13Atom2100 chi ∧
      ¬PredecessorHalfFin13Atom2110 chi ∧
      ¬PredecessorHalfFin13Atom2130 chi ∧
      ¬PredecessorHalfFin13Atom2235 chi))) ∨
      (((¬PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom1860 chi ∧
      ¬PredecessorHalfFin13Atom1861 chi ∧
      ¬PredecessorHalfFin13Atom1865 chi ∧
      ¬PredecessorHalfFin13Atom1869 chi ∧
      ¬PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom1880 chi ∧
      ¬PredecessorHalfFin13Atom1884 chi ∧
      ¬PredecessorHalfFin13Atom1894 chi ∧
      ¬PredecessorHalfFin13Atom1967 chi ∧
      ¬PredecessorHalfFin13Atom1971 chi ∧
      ¬PredecessorHalfFin13Atom1975 chi ∧
      ¬PredecessorHalfFin13Atom1985 chi ∧
      ¬PredecessorHalfFin13Atom2005 chi ∧
      ¬PredecessorHalfFin13Atom2093 chi ∧
      ¬PredecessorHalfFin13Atom2097 chi ∧
      ¬PredecessorHalfFin13Atom2101 chi ∧
      ¬PredecessorHalfFin13Atom2111 chi ∧
      ¬PredecessorHalfFin13Atom2131 chi ∧
      ¬PredecessorHalfFin13Atom2236 chi) ∨
      (¬PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom1858 chi ∧
      ¬PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom1863 chi ∧
      ¬PredecessorHalfFin13Atom1870 chi ∧
      ¬PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom1878 chi ∧
      ¬PredecessorHalfFin13Atom1885 chi ∧
      ¬PredecessorHalfFin13Atom1895 chi ∧
      ¬PredecessorHalfFin13Atom1968 chi ∧
      ¬PredecessorHalfFin13Atom1969 chi ∧
      ¬PredecessorHalfFin13Atom1976 chi ∧
      ¬PredecessorHalfFin13Atom1986 chi ∧
      ¬PredecessorHalfFin13Atom2006 chi ∧
      ¬PredecessorHalfFin13Atom2094 chi ∧
      ¬PredecessorHalfFin13Atom2095 chi ∧
      ¬PredecessorHalfFin13Atom2102 chi ∧
      ¬PredecessorHalfFin13Atom2112 chi ∧
      ¬PredecessorHalfFin13Atom2132 chi ∧
      ¬PredecessorHalfFin13Atom2237 chi)) ∨
      ((¬PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom1859 chi ∧
      ¬PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom1864 chi ∧
      ¬PredecessorHalfFin13Atom1871 chi ∧
      ¬PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom1879 chi ∧
      ¬PredecessorHalfFin13Atom1886 chi ∧
      ¬PredecessorHalfFin13Atom1896 chi ∧
      ¬PredecessorHalfFin13Atom1968 chi ∧
      ¬PredecessorHalfFin13Atom1970 chi ∧
      ¬PredecessorHalfFin13Atom1977 chi ∧
      ¬PredecessorHalfFin13Atom1987 chi ∧
      ¬PredecessorHalfFin13Atom2007 chi ∧
      ¬PredecessorHalfFin13Atom2094 chi ∧
      ¬PredecessorHalfFin13Atom2096 chi ∧
      ¬PredecessorHalfFin13Atom2103 chi ∧
      ¬PredecessorHalfFin13Atom2113 chi ∧
      ¬PredecessorHalfFin13Atom2133 chi ∧
      ¬PredecessorHalfFin13Atom2238 chi) ∨
      (¬PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom1860 chi ∧
      ¬PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom1865 chi ∧
      ¬PredecessorHalfFin13Atom1872 chi ∧
      ¬PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom1880 chi ∧
      ¬PredecessorHalfFin13Atom1887 chi ∧
      ¬PredecessorHalfFin13Atom1897 chi ∧
      ¬PredecessorHalfFin13Atom1968 chi ∧
      ¬PredecessorHalfFin13Atom1971 chi ∧
      ¬PredecessorHalfFin13Atom1978 chi ∧
      ¬PredecessorHalfFin13Atom1988 chi ∧
      ¬PredecessorHalfFin13Atom2008 chi ∧
      ¬PredecessorHalfFin13Atom2094 chi ∧
      ¬PredecessorHalfFin13Atom2097 chi ∧
      ¬PredecessorHalfFin13Atom2104 chi ∧
      ¬PredecessorHalfFin13Atom2114 chi ∧
      ¬PredecessorHalfFin13Atom2134 chi ∧
      ¬PredecessorHalfFin13Atom2239 chi))))))))) := by
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
              exact predecessorHalfFin13_clause27422 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27425 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27429 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27434 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27439 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27440 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27442 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27443 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27445 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27447 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27449 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27451 chi hno hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27453 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27456 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27459 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27461 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27463 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27466 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27470 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27474 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27476 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27478 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27481 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27485 chi hno hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27490 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27495 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27497 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27499 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27502 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27506 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27511 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27517 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27985 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27986 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27987 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27988 chi hno hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27989 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27990 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27991 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27992 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27993 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27994 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause27995 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27996 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27997 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause27998 chi hno hbad
              ·
                exact predecessorHalfFin13_clause27999 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28000 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28001 chi hno hbad
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
              exact predecessorHalfFin13_clause28002 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28003 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28004 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28005 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28006 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28007 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28008 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28009 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28010 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28011 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28012 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28013 chi hno hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28014 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28015 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28016 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28017 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28018 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28019 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28020 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28021 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28022 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28023 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28024 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28025 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28026 chi hno hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28027 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28028 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28030 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28032 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28033 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28034 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28036 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28037 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28040 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28041 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28042 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28043 chi hno hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28044 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28046 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28047 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28049 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28051 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28053 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28055 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28056 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28057 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28058 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28059 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28060 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28061 chi hno hbad

end ErdosSzekeres

end
