module

public import ErdosSzekeres.Fin15AnchoredClauseChunk199
public import ErdosSzekeres.Fin15AnchoredClauseChunk200
public import ErdosSzekeres.Fin15AnchoredClauseChunk201

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 101. -/

theorem fin15Anchored_rejectSemanticSegment101
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((¬Fin15AnchoredAtom4136 chi ∧
      Fin15AnchoredAtom1357 chi ∧
      Fin15AnchoredAtom1358 chi ∧
      Fin15AnchoredAtom1365 chi ∧
      Fin15AnchoredAtom1475 chi ∧
      Fin15AnchoredAtom1595 chi) ∨
      ((Fin15AnchoredAtom4137 chi ∧
      ¬Fin15AnchoredAtom1476 chi) ∨
      (Fin15AnchoredAtom4137 chi ∧
      ¬Fin15AnchoredAtom1596 chi))) ∨
      (((Fin15AnchoredAtom4138 chi ∧
      ¬Fin15AnchoredAtom1367 chi) ∨
      (Fin15AnchoredAtom4138 chi ∧
      ¬Fin15AnchoredAtom1597 chi)) ∨
      ((Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom1358 chi) ∨
      (Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom1359 chi)))) ∨
      ((((Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom1368 chi) ∨
      (Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom1478 chi)) ∨
      ((Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom1598 chi) ∨
      (¬Fin15AnchoredAtom4139 chi ∧
      Fin15AnchoredAtom1358 chi ∧
      Fin15AnchoredAtom1359 chi ∧
      Fin15AnchoredAtom1368 chi ∧
      Fin15AnchoredAtom1478 chi ∧
      Fin15AnchoredAtom1598 chi))) ∨
      (((Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom1358 chi) ∨
      (Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom1360 chi)) ∨
      ((Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom1369 chi) ∨
      (Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom1479 chi))))) ∨
      (((((Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom1599 chi) ∨
      (¬Fin15AnchoredAtom4140 chi ∧
      Fin15AnchoredAtom1358 chi ∧
      Fin15AnchoredAtom1360 chi ∧
      Fin15AnchoredAtom1369 chi ∧
      Fin15AnchoredAtom1479 chi ∧
      Fin15AnchoredAtom1599 chi)) ∨
      ((Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom1359 chi) ∨
      (Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom1360 chi))) ∨
      (((Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom1370 chi) ∨
      (Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom1480 chi)) ∨
      ((Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom1600 chi) ∨
      (¬Fin15AnchoredAtom4141 chi ∧
      Fin15AnchoredAtom1359 chi ∧
      Fin15AnchoredAtom1360 chi ∧
      Fin15AnchoredAtom1370 chi ∧
      Fin15AnchoredAtom1480 chi ∧
      Fin15AnchoredAtom1600 chi)))) ∨
      ((((Fin15AnchoredAtom4142 chi ∧
      ¬Fin15AnchoredAtom1362 chi) ∨
      (Fin15AnchoredAtom4142 chi ∧
      ¬Fin15AnchoredAtom1365 chi)) ∨
      ((Fin15AnchoredAtom4142 chi ∧
      ¬Fin15AnchoredAtom1601 chi) ∨
      (Fin15AnchoredAtom4143 chi ∧
      ¬Fin15AnchoredAtom1363 chi))) ∨
      (((Fin15AnchoredAtom4143 chi ∧
      ¬Fin15AnchoredAtom1482 chi) ∨
      (Fin15AnchoredAtom4143 chi ∧
      ¬Fin15AnchoredAtom1602 chi)) ∨
      ((Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom1362 chi) ∨
      (Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom1363 chi)))))) ∨
      ((((((Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom1368 chi) ∨
      (Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom1484 chi)) ∨
      ((Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom1604 chi) ∨
      (¬Fin15AnchoredAtom4145 chi ∧
      Fin15AnchoredAtom1362 chi ∧
      Fin15AnchoredAtom1363 chi ∧
      Fin15AnchoredAtom1368 chi ∧
      Fin15AnchoredAtom1484 chi ∧
      Fin15AnchoredAtom1604 chi))) ∨
      (((Fin15AnchoredAtom4146 chi ∧
      ¬Fin15AnchoredAtom1362 chi) ∨
      (Fin15AnchoredAtom4146 chi ∧
      ¬Fin15AnchoredAtom1364 chi)) ∨
      ((Fin15AnchoredAtom4146 chi ∧
      ¬Fin15AnchoredAtom1369 chi) ∨
      (Fin15AnchoredAtom4146 chi ∧
      ¬Fin15AnchoredAtom1485 chi)))) ∨
      ((((Fin15AnchoredAtom4146 chi ∧
      ¬Fin15AnchoredAtom1605 chi) ∨
      (¬Fin15AnchoredAtom4146 chi ∧
      Fin15AnchoredAtom1362 chi ∧
      Fin15AnchoredAtom1364 chi ∧
      Fin15AnchoredAtom1369 chi ∧
      Fin15AnchoredAtom1485 chi ∧
      Fin15AnchoredAtom1605 chi)) ∨
      ((Fin15AnchoredAtom4147 chi ∧
      ¬Fin15AnchoredAtom1363 chi) ∨
      (Fin15AnchoredAtom4147 chi ∧
      ¬Fin15AnchoredAtom1364 chi))) ∨
      (((Fin15AnchoredAtom4147 chi ∧
      ¬Fin15AnchoredAtom1370 chi) ∨
      (Fin15AnchoredAtom4147 chi ∧
      ¬Fin15AnchoredAtom1486 chi)) ∨
      ((Fin15AnchoredAtom4147 chi ∧
      ¬Fin15AnchoredAtom1606 chi) ∨
      (¬Fin15AnchoredAtom4147 chi ∧
      Fin15AnchoredAtom1363 chi ∧
      Fin15AnchoredAtom1364 chi ∧
      Fin15AnchoredAtom1370 chi ∧
      Fin15AnchoredAtom1486 chi ∧
      Fin15AnchoredAtom1606 chi))))) ∨
      (((((Fin15AnchoredAtom4148 chi ∧
      ¬Fin15AnchoredAtom1607 chi) ∨
      (Fin15AnchoredAtom4149 chi ∧
      ¬Fin15AnchoredAtom1369 chi)) ∨
      ((Fin15AnchoredAtom4151 chi ∧
      ¬Fin15AnchoredAtom1368 chi) ∨
      (Fin15AnchoredAtom4151 chi ∧
      ¬Fin15AnchoredAtom1369 chi))) ∨
      (((Fin15AnchoredAtom4151 chi ∧
      ¬Fin15AnchoredAtom1370 chi) ∨
      (Fin15AnchoredAtom4151 chi ∧
      ¬Fin15AnchoredAtom1490 chi)) ∨
      ((Fin15AnchoredAtom4151 chi ∧
      ¬Fin15AnchoredAtom1610 chi) ∨
      (¬Fin15AnchoredAtom4151 chi ∧
      Fin15AnchoredAtom1368 chi ∧
      Fin15AnchoredAtom1369 chi ∧
      Fin15AnchoredAtom1370 chi ∧
      Fin15AnchoredAtom1490 chi ∧
      Fin15AnchoredAtom1610 chi)))) ∨
      ((((Fin15AnchoredAtom4152 chi ∧
      ¬Fin15AnchoredAtom1371 chi) ∨
      (Fin15AnchoredAtom4152 chi ∧
      ¬Fin15AnchoredAtom1372 chi)) ∨
      ((Fin15AnchoredAtom4152 chi ∧
      ¬Fin15AnchoredAtom1379 chi) ∨
      (Fin15AnchoredAtom4152 chi ∧
      ¬Fin15AnchoredAtom1407 chi))) ∨
      (((Fin15AnchoredAtom4152 chi ∧
      ¬Fin15AnchoredAtom1611 chi) ∨
      (¬Fin15AnchoredAtom4152 chi ∧
      Fin15AnchoredAtom1371 chi ∧
      Fin15AnchoredAtom1372 chi ∧
      Fin15AnchoredAtom1379 chi ∧
      Fin15AnchoredAtom1407 chi ∧
      Fin15AnchoredAtom1611 chi)) ∨
      ((Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom1371 chi) ∨
      (Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom1373 chi))))))) ∨
      ((((((Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom1380 chi) ∨
      ((Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom1408 chi) ∨
      (Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom1612 chi))) ∨
      (((¬Fin15AnchoredAtom4153 chi ∧
      Fin15AnchoredAtom1371 chi ∧
      Fin15AnchoredAtom1373 chi ∧
      Fin15AnchoredAtom1380 chi ∧
      Fin15AnchoredAtom1408 chi ∧
      Fin15AnchoredAtom1612 chi) ∨
      (Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom1371 chi)) ∨
      ((Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom1374 chi) ∨
      (Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom1381 chi)))) ∨
      ((((Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom1409 chi) ∨
      (Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom1613 chi)) ∨
      ((¬Fin15AnchoredAtom4154 chi ∧
      Fin15AnchoredAtom1371 chi ∧
      Fin15AnchoredAtom1374 chi ∧
      Fin15AnchoredAtom1381 chi ∧
      Fin15AnchoredAtom1409 chi ∧
      Fin15AnchoredAtom1613 chi) ∨
      (Fin15AnchoredAtom4155 chi ∧
      ¬Fin15AnchoredAtom1410 chi))) ∨
      (((¬Fin15AnchoredAtom4155 chi ∧
      Fin15AnchoredAtom1371 chi ∧
      Fin15AnchoredAtom1375 chi ∧
      Fin15AnchoredAtom1382 chi ∧
      Fin15AnchoredAtom1410 chi ∧
      Fin15AnchoredAtom1614 chi) ∨
      (Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom1371 chi)) ∨
      ((Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom1376 chi) ∨
      (Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom1383 chi))))) ∨
      (((((Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom1411 chi) ∨
      (Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom1615 chi)) ∨
      ((¬Fin15AnchoredAtom4156 chi ∧
      Fin15AnchoredAtom1371 chi ∧
      Fin15AnchoredAtom1376 chi ∧
      Fin15AnchoredAtom1383 chi ∧
      Fin15AnchoredAtom1411 chi ∧
      Fin15AnchoredAtom1615 chi) ∨
      (Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom1371 chi))) ∨
      (((Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom1377 chi) ∨
      (Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom1384 chi)) ∨
      ((Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom1412 chi) ∨
      (Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom1616 chi)))) ∨
      ((((¬Fin15AnchoredAtom4157 chi ∧
      Fin15AnchoredAtom1371 chi ∧
      Fin15AnchoredAtom1377 chi ∧
      Fin15AnchoredAtom1384 chi ∧
      Fin15AnchoredAtom1412 chi ∧
      Fin15AnchoredAtom1616 chi) ∨
      (Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom1371 chi)) ∨
      ((Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom1378 chi) ∨
      (Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom1385 chi))) ∨
      (((Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom1413 chi) ∨
      (Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom1617 chi)) ∨
      ((¬Fin15AnchoredAtom4158 chi ∧
      Fin15AnchoredAtom1371 chi ∧
      Fin15AnchoredAtom1378 chi ∧
      Fin15AnchoredAtom1385 chi ∧
      Fin15AnchoredAtom1413 chi ∧
      Fin15AnchoredAtom1617 chi) ∨
      (Fin15AnchoredAtom4159 chi ∧
      ¬Fin15AnchoredAtom1372 chi)))))) ∨
      ((((((Fin15AnchoredAtom4159 chi ∧
      ¬Fin15AnchoredAtom1373 chi) ∨
      (Fin15AnchoredAtom4159 chi ∧
      ¬Fin15AnchoredAtom1386 chi)) ∨
      ((Fin15AnchoredAtom4159 chi ∧
      ¬Fin15AnchoredAtom1414 chi) ∨
      (Fin15AnchoredAtom4159 chi ∧
      ¬Fin15AnchoredAtom1618 chi))) ∨
      (((¬Fin15AnchoredAtom4159 chi ∧
      Fin15AnchoredAtom1372 chi ∧
      Fin15AnchoredAtom1373 chi ∧
      Fin15AnchoredAtom1386 chi ∧
      Fin15AnchoredAtom1414 chi ∧
      Fin15AnchoredAtom1618 chi) ∨
      (Fin15AnchoredAtom4160 chi ∧
      ¬Fin15AnchoredAtom1372 chi)) ∨
      ((Fin15AnchoredAtom4160 chi ∧
      ¬Fin15AnchoredAtom1374 chi) ∨
      (Fin15AnchoredAtom4160 chi ∧
      ¬Fin15AnchoredAtom1387 chi)))) ∨
      ((((Fin15AnchoredAtom4160 chi ∧
      ¬Fin15AnchoredAtom1415 chi) ∨
      (Fin15AnchoredAtom4160 chi ∧
      ¬Fin15AnchoredAtom1619 chi)) ∨
      ((¬Fin15AnchoredAtom4160 chi ∧
      Fin15AnchoredAtom1372 chi ∧
      Fin15AnchoredAtom1374 chi ∧
      Fin15AnchoredAtom1387 chi ∧
      Fin15AnchoredAtom1415 chi ∧
      Fin15AnchoredAtom1619 chi) ∨
      (Fin15AnchoredAtom4162 chi ∧
      ¬Fin15AnchoredAtom1372 chi))) ∨
      (((Fin15AnchoredAtom4162 chi ∧
      ¬Fin15AnchoredAtom1376 chi) ∨
      (Fin15AnchoredAtom4162 chi ∧
      ¬Fin15AnchoredAtom1417 chi)) ∨
      ((Fin15AnchoredAtom4162 chi ∧
      ¬Fin15AnchoredAtom1621 chi) ∨
      (¬Fin15AnchoredAtom4162 chi ∧
      Fin15AnchoredAtom1372 chi ∧
      Fin15AnchoredAtom1376 chi ∧
      Fin15AnchoredAtom1389 chi ∧
      Fin15AnchoredAtom1417 chi ∧
      Fin15AnchoredAtom1621 chi))))) ∨
      (((((Fin15AnchoredAtom4163 chi ∧
      ¬Fin15AnchoredAtom1372 chi) ∨
      (Fin15AnchoredAtom4163 chi ∧
      ¬Fin15AnchoredAtom1377 chi)) ∨
      ((Fin15AnchoredAtom4163 chi ∧
      ¬Fin15AnchoredAtom1390 chi) ∨
      (Fin15AnchoredAtom4163 chi ∧
      ¬Fin15AnchoredAtom1418 chi))) ∨
      (((Fin15AnchoredAtom4163 chi ∧
      ¬Fin15AnchoredAtom1622 chi) ∨
      (¬Fin15AnchoredAtom4163 chi ∧
      Fin15AnchoredAtom1372 chi ∧
      Fin15AnchoredAtom1377 chi ∧
      Fin15AnchoredAtom1390 chi ∧
      Fin15AnchoredAtom1418 chi ∧
      Fin15AnchoredAtom1622 chi)) ∨
      ((Fin15AnchoredAtom4164 chi ∧
      ¬Fin15AnchoredAtom1372 chi) ∨
      (Fin15AnchoredAtom4164 chi ∧
      ¬Fin15AnchoredAtom1378 chi)))) ∨
      ((((Fin15AnchoredAtom4164 chi ∧
      ¬Fin15AnchoredAtom1391 chi) ∨
      (Fin15AnchoredAtom4164 chi ∧
      ¬Fin15AnchoredAtom1419 chi)) ∨
      ((Fin15AnchoredAtom4164 chi ∧
      ¬Fin15AnchoredAtom1623 chi) ∨
      (¬Fin15AnchoredAtom4164 chi ∧
      Fin15AnchoredAtom1372 chi ∧
      Fin15AnchoredAtom1378 chi ∧
      Fin15AnchoredAtom1391 chi ∧
      Fin15AnchoredAtom1419 chi ∧
      Fin15AnchoredAtom1623 chi))) ∨
      (((Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom1373 chi) ∨
      (Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom1374 chi)) ∨
      ((Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom1392 chi) ∨
      (Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom1420 chi)))))))) ∨
      (((((((Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom1624 chi) ∨
      ((¬Fin15AnchoredAtom4165 chi ∧
      Fin15AnchoredAtom1373 chi ∧
      Fin15AnchoredAtom1374 chi ∧
      Fin15AnchoredAtom1392 chi ∧
      Fin15AnchoredAtom1420 chi ∧
      Fin15AnchoredAtom1624 chi) ∨
      (Fin15AnchoredAtom4166 chi ∧
      ¬Fin15AnchoredAtom1373 chi))) ∨
      (((Fin15AnchoredAtom4166 chi ∧
      ¬Fin15AnchoredAtom1375 chi) ∨
      (Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom1373 chi)) ∨
      ((Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom1376 chi) ∨
      (Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom1394 chi)))) ∨
      ((((Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom1422 chi) ∨
      (Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom1626 chi)) ∨
      ((¬Fin15AnchoredAtom4167 chi ∧
      Fin15AnchoredAtom1373 chi ∧
      Fin15AnchoredAtom1376 chi ∧
      Fin15AnchoredAtom1394 chi ∧
      Fin15AnchoredAtom1422 chi ∧
      Fin15AnchoredAtom1626 chi) ∨
      (Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom1373 chi))) ∨
      (((Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom1377 chi) ∨
      (Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom1395 chi)) ∨
      ((Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom1423 chi) ∨
      (Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom1627 chi))))) ∨
      (((((¬Fin15AnchoredAtom4168 chi ∧
      Fin15AnchoredAtom1373 chi ∧
      Fin15AnchoredAtom1377 chi ∧
      Fin15AnchoredAtom1395 chi ∧
      Fin15AnchoredAtom1423 chi ∧
      Fin15AnchoredAtom1627 chi) ∨
      (Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom1373 chi)) ∨
      ((Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom1378 chi) ∨
      (Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom1396 chi))) ∨
      (((Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom1424 chi) ∨
      (Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom1628 chi)) ∨
      ((¬Fin15AnchoredAtom4169 chi ∧
      Fin15AnchoredAtom1373 chi ∧
      Fin15AnchoredAtom1378 chi ∧
      Fin15AnchoredAtom1396 chi ∧
      Fin15AnchoredAtom1424 chi ∧
      Fin15AnchoredAtom1628 chi) ∨
      (Fin15AnchoredAtom4170 chi ∧
      ¬Fin15AnchoredAtom1374 chi)))) ∨
      ((((Fin15AnchoredAtom4170 chi ∧
      ¬Fin15AnchoredAtom1425 chi) ∨
      (¬Fin15AnchoredAtom4170 chi ∧
      Fin15AnchoredAtom1374 chi ∧
      Fin15AnchoredAtom1375 chi ∧
      Fin15AnchoredAtom1397 chi ∧
      Fin15AnchoredAtom1425 chi ∧
      Fin15AnchoredAtom1629 chi)) ∨
      ((Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom1374 chi) ∨
      (Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom1376 chi))) ∨
      (((Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom1398 chi) ∨
      (Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom1426 chi)) ∨
      ((Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom1630 chi) ∨
      (¬Fin15AnchoredAtom4171 chi ∧
      Fin15AnchoredAtom1374 chi ∧
      Fin15AnchoredAtom1376 chi ∧
      Fin15AnchoredAtom1398 chi ∧
      Fin15AnchoredAtom1426 chi ∧
      Fin15AnchoredAtom1630 chi)))))) ∨
      ((((((Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom1374 chi) ∨
      (Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom1377 chi)) ∨
      ((Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom1399 chi) ∨
      (Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom1427 chi))) ∨
      (((Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom1631 chi) ∨
      (¬Fin15AnchoredAtom4172 chi ∧
      Fin15AnchoredAtom1374 chi ∧
      Fin15AnchoredAtom1377 chi ∧
      Fin15AnchoredAtom1399 chi ∧
      Fin15AnchoredAtom1427 chi ∧
      Fin15AnchoredAtom1631 chi)) ∨
      ((Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom1374 chi) ∨
      (Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom1378 chi)))) ∨
      ((((Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom1400 chi) ∨
      (Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom1428 chi)) ∨
      ((Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom1632 chi) ∨
      (¬Fin15AnchoredAtom4173 chi ∧
      Fin15AnchoredAtom1374 chi ∧
      Fin15AnchoredAtom1378 chi ∧
      Fin15AnchoredAtom1400 chi ∧
      Fin15AnchoredAtom1428 chi ∧
      Fin15AnchoredAtom1632 chi))) ∨
      (((¬Fin15AnchoredAtom4174 chi ∧
      Fin15AnchoredAtom1375 chi ∧
      Fin15AnchoredAtom1376 chi ∧
      Fin15AnchoredAtom1401 chi ∧
      Fin15AnchoredAtom1429 chi ∧
      Fin15AnchoredAtom1633 chi) ∨
      (Fin15AnchoredAtom4176 chi ∧
      ¬Fin15AnchoredAtom1375 chi)) ∨
      ((Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom1376 chi) ∨
      (Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom1377 chi))))) ∨
      (((((Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom1404 chi) ∨
      (Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom1432 chi)) ∨
      ((Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom1636 chi) ∨
      (¬Fin15AnchoredAtom4177 chi ∧
      Fin15AnchoredAtom1376 chi ∧
      Fin15AnchoredAtom1377 chi ∧
      Fin15AnchoredAtom1404 chi ∧
      Fin15AnchoredAtom1432 chi ∧
      Fin15AnchoredAtom1636 chi))) ∨
      (((Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom1376 chi) ∨
      (Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom1378 chi)) ∨
      ((Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom1405 chi) ∨
      (Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom1433 chi)))) ∨
      ((((Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom1637 chi) ∨
      (¬Fin15AnchoredAtom4178 chi ∧
      Fin15AnchoredAtom1376 chi ∧
      Fin15AnchoredAtom1378 chi ∧
      Fin15AnchoredAtom1405 chi ∧
      Fin15AnchoredAtom1433 chi ∧
      Fin15AnchoredAtom1637 chi)) ∨
      ((Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom1377 chi) ∨
      (Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom1378 chi))) ∨
      (((Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom1406 chi) ∨
      (Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom1434 chi)) ∨
      ((Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom1638 chi) ∨
      (¬Fin15AnchoredAtom4179 chi ∧
      Fin15AnchoredAtom1377 chi ∧
      Fin15AnchoredAtom1378 chi ∧
      Fin15AnchoredAtom1406 chi ∧
      Fin15AnchoredAtom1434 chi ∧
      Fin15AnchoredAtom1638 chi))))))) ∨
      (((((((Fin15AnchoredAtom4180 chi ∧
      ¬Fin15AnchoredAtom1379 chi) ∨
      (Fin15AnchoredAtom4180 chi ∧
      ¬Fin15AnchoredAtom1380 chi)) ∨
      ((Fin15AnchoredAtom4180 chi ∧
      ¬Fin15AnchoredAtom1386 chi) ∨
      (Fin15AnchoredAtom4180 chi ∧
      ¬Fin15AnchoredAtom1435 chi))) ∨
      (((Fin15AnchoredAtom4180 chi ∧
      ¬Fin15AnchoredAtom1639 chi) ∨
      (¬Fin15AnchoredAtom4180 chi ∧
      Fin15AnchoredAtom1379 chi ∧
      Fin15AnchoredAtom1380 chi ∧
      Fin15AnchoredAtom1386 chi ∧
      Fin15AnchoredAtom1435 chi ∧
      Fin15AnchoredAtom1639 chi)) ∨
      ((Fin15AnchoredAtom4181 chi ∧
      ¬Fin15AnchoredAtom1379 chi) ∨
      (Fin15AnchoredAtom4181 chi ∧
      ¬Fin15AnchoredAtom1381 chi)))) ∨
      ((((Fin15AnchoredAtom4181 chi ∧
      ¬Fin15AnchoredAtom1387 chi) ∨
      (Fin15AnchoredAtom4181 chi ∧
      ¬Fin15AnchoredAtom1436 chi)) ∨
      ((Fin15AnchoredAtom4181 chi ∧
      ¬Fin15AnchoredAtom1640 chi) ∨
      (¬Fin15AnchoredAtom4181 chi ∧
      Fin15AnchoredAtom1379 chi ∧
      Fin15AnchoredAtom1381 chi ∧
      Fin15AnchoredAtom1387 chi ∧
      Fin15AnchoredAtom1436 chi ∧
      Fin15AnchoredAtom1640 chi))) ∨
      (((Fin15AnchoredAtom4183 chi ∧
      ¬Fin15AnchoredAtom1379 chi) ∨
      (Fin15AnchoredAtom4183 chi ∧
      ¬Fin15AnchoredAtom1383 chi)) ∨
      ((Fin15AnchoredAtom4183 chi ∧
      ¬Fin15AnchoredAtom1389 chi) ∨
      (Fin15AnchoredAtom4183 chi ∧
      ¬Fin15AnchoredAtom1438 chi))))) ∨
      (((((Fin15AnchoredAtom4183 chi ∧
      ¬Fin15AnchoredAtom1642 chi) ∨
      (¬Fin15AnchoredAtom4183 chi ∧
      Fin15AnchoredAtom1379 chi ∧
      Fin15AnchoredAtom1383 chi ∧
      Fin15AnchoredAtom1389 chi ∧
      Fin15AnchoredAtom1438 chi ∧
      Fin15AnchoredAtom1642 chi)) ∨
      ((Fin15AnchoredAtom4184 chi ∧
      ¬Fin15AnchoredAtom1379 chi) ∨
      (Fin15AnchoredAtom4184 chi ∧
      ¬Fin15AnchoredAtom1384 chi))) ∨
      (((Fin15AnchoredAtom4184 chi ∧
      ¬Fin15AnchoredAtom1390 chi) ∨
      (Fin15AnchoredAtom4184 chi ∧
      ¬Fin15AnchoredAtom1439 chi)) ∨
      ((Fin15AnchoredAtom4184 chi ∧
      ¬Fin15AnchoredAtom1643 chi) ∨
      (¬Fin15AnchoredAtom4184 chi ∧
      Fin15AnchoredAtom1379 chi ∧
      Fin15AnchoredAtom1384 chi ∧
      Fin15AnchoredAtom1390 chi ∧
      Fin15AnchoredAtom1439 chi ∧
      Fin15AnchoredAtom1643 chi)))) ∨
      ((((Fin15AnchoredAtom4185 chi ∧
      ¬Fin15AnchoredAtom1379 chi) ∨
      (Fin15AnchoredAtom4185 chi ∧
      ¬Fin15AnchoredAtom1385 chi)) ∨
      ((Fin15AnchoredAtom4185 chi ∧
      ¬Fin15AnchoredAtom1391 chi) ∨
      (Fin15AnchoredAtom4185 chi ∧
      ¬Fin15AnchoredAtom1440 chi))) ∨
      (((Fin15AnchoredAtom4185 chi ∧
      ¬Fin15AnchoredAtom1644 chi) ∨
      (¬Fin15AnchoredAtom4185 chi ∧
      Fin15AnchoredAtom1379 chi ∧
      Fin15AnchoredAtom1385 chi ∧
      Fin15AnchoredAtom1391 chi ∧
      Fin15AnchoredAtom1440 chi ∧
      Fin15AnchoredAtom1644 chi)) ∨
      ((Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom1380 chi) ∨
      (Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom1381 chi)))))) ∨
      ((((((Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom1392 chi) ∨
      (Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom1441 chi)) ∨
      ((Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom1645 chi) ∨
      (¬Fin15AnchoredAtom4186 chi ∧
      Fin15AnchoredAtom1380 chi ∧
      Fin15AnchoredAtom1381 chi ∧
      Fin15AnchoredAtom1392 chi ∧
      Fin15AnchoredAtom1441 chi ∧
      Fin15AnchoredAtom1645 chi))) ∨
      (((Fin15AnchoredAtom4187 chi ∧
      ¬Fin15AnchoredAtom1380 chi) ∨
      (Fin15AnchoredAtom4187 chi ∧
      ¬Fin15AnchoredAtom1382 chi)) ∨
      ((Fin15AnchoredAtom4187 chi ∧
      ¬Fin15AnchoredAtom1442 chi) ∨
      (Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom1380 chi)))) ∨
      ((((Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom1383 chi) ∨
      (Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom1394 chi)) ∨
      ((Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom1443 chi) ∨
      (Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom1647 chi))) ∨
      (((¬Fin15AnchoredAtom4188 chi ∧
      Fin15AnchoredAtom1380 chi ∧
      Fin15AnchoredAtom1383 chi ∧
      Fin15AnchoredAtom1394 chi ∧
      Fin15AnchoredAtom1443 chi ∧
      Fin15AnchoredAtom1647 chi) ∨
      (Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom1380 chi)) ∨
      ((Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom1384 chi) ∨
      (Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom1395 chi))))) ∨
      (((((Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom1444 chi) ∨
      (Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom1648 chi)) ∨
      ((¬Fin15AnchoredAtom4189 chi ∧
      Fin15AnchoredAtom1380 chi ∧
      Fin15AnchoredAtom1384 chi ∧
      Fin15AnchoredAtom1395 chi ∧
      Fin15AnchoredAtom1444 chi ∧
      Fin15AnchoredAtom1648 chi) ∨
      (Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom1380 chi))) ∨
      (((Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom1385 chi) ∨
      (Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom1396 chi)) ∨
      ((Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom1445 chi) ∨
      (Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom1649 chi)))) ∨
      ((((¬Fin15AnchoredAtom4190 chi ∧
      Fin15AnchoredAtom1380 chi ∧
      Fin15AnchoredAtom1385 chi ∧
      Fin15AnchoredAtom1396 chi ∧
      Fin15AnchoredAtom1445 chi ∧
      Fin15AnchoredAtom1649 chi) ∨
      (Fin15AnchoredAtom4191 chi ∧
      ¬Fin15AnchoredAtom1381 chi)) ∨
      ((Fin15AnchoredAtom4191 chi ∧
      ¬Fin15AnchoredAtom1446 chi) ∨
      (Fin15AnchoredAtom4191 chi ∧
      ¬Fin15AnchoredAtom1650 chi))) ∨
      (((¬Fin15AnchoredAtom4191 chi ∧
      Fin15AnchoredAtom1381 chi ∧
      Fin15AnchoredAtom1382 chi ∧
      Fin15AnchoredAtom1397 chi ∧
      Fin15AnchoredAtom1446 chi ∧
      Fin15AnchoredAtom1650 chi) ∨
      (Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom1381 chi)) ∨
      ((Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom1383 chi) ∨
      (Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom1398 chi)))))))))) := by
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
                exact fin15Anchored_clause25492 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25493 chi hbad
                ·
                  exact fin15Anchored_clause25494 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25495 chi hbad
                ·
                  exact fin15Anchored_clause25496 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25497 chi hbad
                ·
                  exact fin15Anchored_clause25498 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25499 chi hbad
                ·
                  exact fin15Anchored_clause25500 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25501 chi hbad
                ·
                  exact fin15Anchored_clause25502 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25503 chi hbad
                ·
                  exact fin15Anchored_clause25504 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25505 chi hbad
                ·
                  exact fin15Anchored_clause25506 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25507 chi hbad
                ·
                  exact fin15Anchored_clause25508 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25509 chi hbad
                ·
                  exact fin15Anchored_clause25510 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25511 chi hbad
                ·
                  exact fin15Anchored_clause25512 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25513 chi hbad
                ·
                  exact fin15Anchored_clause25514 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25515 chi hbad
                ·
                  exact fin15Anchored_clause25516 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25517 chi hbad
                ·
                  exact fin15Anchored_clause25518 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25519 chi hbad
                ·
                  exact fin15Anchored_clause25520 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25521 chi hbad
                ·
                  exact fin15Anchored_clause25522 chi hbad
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
                  exact fin15Anchored_clause25523 chi hbad
                ·
                  exact fin15Anchored_clause25524 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25525 chi hbad
                ·
                  exact fin15Anchored_clause25526 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25527 chi hbad
                ·
                  exact fin15Anchored_clause25528 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25529 chi hbad
                ·
                  exact fin15Anchored_clause25530 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25531 chi hbad
                ·
                  exact fin15Anchored_clause25532 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25533 chi hbad
                ·
                  exact fin15Anchored_clause25534 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25535 chi hbad
                ·
                  exact fin15Anchored_clause25536 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25537 chi hbad
                ·
                  exact fin15Anchored_clause25538 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25539 chi hbad
                ·
                  exact fin15Anchored_clause25540 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25541 chi hbad
                ·
                  exact fin15Anchored_clause25542 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25543 chi hbad
                ·
                  exact fin15Anchored_clause25544 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25545 chi hbad
                ·
                  exact fin15Anchored_clause25546 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25547 chi hbad
                ·
                  exact fin15Anchored_clause25548 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25549 chi hbad
                ·
                  exact fin15Anchored_clause25550 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25551 chi hbad
                ·
                  exact fin15Anchored_clause25552 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25553 chi hbad
                ·
                  exact fin15Anchored_clause25554 chi hbad
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
                exact fin15Anchored_clause25555 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25556 chi hbad
                ·
                  exact fin15Anchored_clause25557 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25558 chi hbad
                ·
                  exact fin15Anchored_clause25559 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25560 chi hbad
                ·
                  exact fin15Anchored_clause25561 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25562 chi hbad
                ·
                  exact fin15Anchored_clause25563 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25564 chi hbad
                ·
                  exact fin15Anchored_clause25565 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25566 chi hbad
                ·
                  exact fin15Anchored_clause25567 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25568 chi hbad
                ·
                  exact fin15Anchored_clause25569 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25570 chi hbad
                ·
                  exact fin15Anchored_clause25571 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25572 chi hbad
                ·
                  exact fin15Anchored_clause25573 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25574 chi hbad
                ·
                  exact fin15Anchored_clause25575 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25576 chi hbad
                ·
                  exact fin15Anchored_clause25577 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25578 chi hbad
                ·
                  exact fin15Anchored_clause25579 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25580 chi hbad
                ·
                  exact fin15Anchored_clause25581 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25582 chi hbad
                ·
                  exact fin15Anchored_clause25583 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25584 chi hbad
                ·
                  exact fin15Anchored_clause25585 chi hbad
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
                  exact fin15Anchored_clause25586 chi hbad
                ·
                  exact fin15Anchored_clause25587 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25588 chi hbad
                ·
                  exact fin15Anchored_clause25589 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25590 chi hbad
                ·
                  exact fin15Anchored_clause25591 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25592 chi hbad
                ·
                  exact fin15Anchored_clause25593 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25594 chi hbad
                ·
                  exact fin15Anchored_clause25595 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25596 chi hbad
                ·
                  exact fin15Anchored_clause25597 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25598 chi hbad
                ·
                  exact fin15Anchored_clause25599 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25600 chi hbad
                ·
                  exact fin15Anchored_clause25601 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25602 chi hbad
                ·
                  exact fin15Anchored_clause25603 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25604 chi hbad
                ·
                  exact fin15Anchored_clause25605 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25606 chi hbad
                ·
                  exact fin15Anchored_clause25607 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25608 chi hbad
                ·
                  exact fin15Anchored_clause25609 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25610 chi hbad
                ·
                  exact fin15Anchored_clause25611 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25612 chi hbad
                ·
                  exact fin15Anchored_clause25613 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25614 chi hbad
                ·
                  exact fin15Anchored_clause25615 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25616 chi hbad
                ·
                  exact fin15Anchored_clause25617 chi hbad
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
                exact fin15Anchored_clause25618 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25619 chi hbad
                ·
                  exact fin15Anchored_clause25620 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25621 chi hbad
                ·
                  exact fin15Anchored_clause25622 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25623 chi hbad
                ·
                  exact fin15Anchored_clause25624 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25625 chi hbad
                ·
                  exact fin15Anchored_clause25626 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25627 chi hbad
                ·
                  exact fin15Anchored_clause25628 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25629 chi hbad
                ·
                  exact fin15Anchored_clause25630 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25631 chi hbad
                ·
                  exact fin15Anchored_clause25632 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25633 chi hbad
                ·
                  exact fin15Anchored_clause25634 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25635 chi hbad
                ·
                  exact fin15Anchored_clause25636 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25637 chi hbad
                ·
                  exact fin15Anchored_clause25638 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25639 chi hbad
                ·
                  exact fin15Anchored_clause25640 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25641 chi hbad
                ·
                  exact fin15Anchored_clause25642 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25643 chi hbad
                ·
                  exact fin15Anchored_clause25644 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25645 chi hbad
                ·
                  exact fin15Anchored_clause25646 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25647 chi hbad
                ·
                  exact fin15Anchored_clause25648 chi hbad
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
                  exact fin15Anchored_clause25649 chi hbad
                ·
                  exact fin15Anchored_clause25650 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25651 chi hbad
                ·
                  exact fin15Anchored_clause25652 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25653 chi hbad
                ·
                  exact fin15Anchored_clause25654 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25655 chi hbad
                ·
                  exact fin15Anchored_clause25656 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25657 chi hbad
                ·
                  exact fin15Anchored_clause25658 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25659 chi hbad
                ·
                  exact fin15Anchored_clause25660 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25661 chi hbad
                ·
                  exact fin15Anchored_clause25662 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25663 chi hbad
                ·
                  exact fin15Anchored_clause25664 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25665 chi hbad
                ·
                  exact fin15Anchored_clause25666 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25667 chi hbad
                ·
                  exact fin15Anchored_clause25668 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25669 chi hbad
                ·
                  exact fin15Anchored_clause25670 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25671 chi hbad
                ·
                  exact fin15Anchored_clause25672 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25673 chi hbad
                ·
                  exact fin15Anchored_clause25674 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25675 chi hbad
                ·
                  exact fin15Anchored_clause25676 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25677 chi hbad
                ·
                  exact fin15Anchored_clause25678 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25679 chi hbad
                ·
                  exact fin15Anchored_clause25680 chi hbad
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
                  exact fin15Anchored_clause25681 chi hbad
                ·
                  exact fin15Anchored_clause25682 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25683 chi hbad
                ·
                  exact fin15Anchored_clause25684 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25685 chi hbad
                ·
                  exact fin15Anchored_clause25686 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25687 chi hbad
                ·
                  exact fin15Anchored_clause25688 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25689 chi hbad
                ·
                  exact fin15Anchored_clause25690 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25691 chi hbad
                ·
                  exact fin15Anchored_clause25692 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25693 chi hbad
                ·
                  exact fin15Anchored_clause25694 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25695 chi hbad
                ·
                  exact fin15Anchored_clause25696 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25697 chi hbad
                ·
                  exact fin15Anchored_clause25698 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25699 chi hbad
                ·
                  exact fin15Anchored_clause25700 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25701 chi hbad
                ·
                  exact fin15Anchored_clause25702 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25703 chi hbad
                ·
                  exact fin15Anchored_clause25704 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25705 chi hbad
                ·
                  exact fin15Anchored_clause25706 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25707 chi hbad
                ·
                  exact fin15Anchored_clause25708 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25709 chi hbad
                ·
                  exact fin15Anchored_clause25710 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25711 chi hbad
                ·
                  exact fin15Anchored_clause25712 chi hbad
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
                  exact fin15Anchored_clause25713 chi hbad
                ·
                  exact fin15Anchored_clause25714 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25715 chi hbad
                ·
                  exact fin15Anchored_clause25716 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25717 chi hbad
                ·
                  exact fin15Anchored_clause25718 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25719 chi hbad
                ·
                  exact fin15Anchored_clause25720 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25721 chi hbad
                ·
                  exact fin15Anchored_clause25722 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25723 chi hbad
                ·
                  exact fin15Anchored_clause25724 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25725 chi hbad
                ·
                  exact fin15Anchored_clause25726 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25727 chi hbad
                ·
                  exact fin15Anchored_clause25728 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25729 chi hbad
                ·
                  exact fin15Anchored_clause25730 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25731 chi hbad
                ·
                  exact fin15Anchored_clause25732 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25733 chi hbad
                ·
                  exact fin15Anchored_clause25734 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25735 chi hbad
                ·
                  exact fin15Anchored_clause25736 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25737 chi hbad
                ·
                  exact fin15Anchored_clause25738 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25739 chi hbad
                ·
                  exact fin15Anchored_clause25740 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25741 chi hbad
                ·
                  exact fin15Anchored_clause25742 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25743 chi hbad
                ·
                  exact fin15Anchored_clause25744 chi hbad

end ErdosSzekeres

end
