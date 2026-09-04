module

public import ErdosSzekeres.Fin15AnchoredClauseChunk197
public import ErdosSzekeres.Fin15AnchoredClauseChunk198
public import ErdosSzekeres.Fin15AnchoredClauseChunk199

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 100. -/

theorem fin15Anchored_rejectSemanticSegment100
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom4080 chi ∧
      ¬Fin15AnchoredAtom1342 chi) ∨
      ((Fin15AnchoredAtom4080 chi ∧
      ¬Fin15AnchoredAtom1355 chi) ∨
      (Fin15AnchoredAtom4080 chi ∧
      ¬Fin15AnchoredAtom1419 chi))) ∨
      (((Fin15AnchoredAtom4080 chi ∧
      ¬Fin15AnchoredAtom1539 chi) ∨
      (¬Fin15AnchoredAtom4080 chi ∧
      Fin15AnchoredAtom1336 chi ∧
      Fin15AnchoredAtom1342 chi ∧
      Fin15AnchoredAtom1355 chi ∧
      Fin15AnchoredAtom1419 chi ∧
      Fin15AnchoredAtom1539 chi)) ∨
      ((Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom1337 chi) ∨
      (Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom1338 chi)))) ∨
      ((((Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom1356 chi) ∨
      (Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom1420 chi)) ∨
      ((Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom1540 chi) ∨
      (¬Fin15AnchoredAtom4081 chi ∧
      Fin15AnchoredAtom1337 chi ∧
      Fin15AnchoredAtom1338 chi ∧
      Fin15AnchoredAtom1356 chi ∧
      Fin15AnchoredAtom1420 chi ∧
      Fin15AnchoredAtom1540 chi))) ∨
      (((Fin15AnchoredAtom4082 chi ∧
      ¬Fin15AnchoredAtom1357 chi) ∨
      (Fin15AnchoredAtom4082 chi ∧
      ¬Fin15AnchoredAtom1421 chi)) ∨
      ((¬Fin15AnchoredAtom4082 chi ∧
      Fin15AnchoredAtom1337 chi ∧
      Fin15AnchoredAtom1339 chi ∧
      Fin15AnchoredAtom1357 chi ∧
      Fin15AnchoredAtom1421 chi ∧
      Fin15AnchoredAtom1541 chi) ∨
      (Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom1337 chi))))) ∨
      (((((Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom1340 chi) ∨
      (Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom1358 chi)) ∨
      ((Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom1422 chi) ∨
      (Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom1542 chi))) ∨
      (((¬Fin15AnchoredAtom4083 chi ∧
      Fin15AnchoredAtom1337 chi ∧
      Fin15AnchoredAtom1340 chi ∧
      Fin15AnchoredAtom1358 chi ∧
      Fin15AnchoredAtom1422 chi ∧
      Fin15AnchoredAtom1542 chi) ∨
      (Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom1337 chi)) ∨
      ((Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom1341 chi) ∨
      (Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom1359 chi)))) ∨
      ((((Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom1423 chi) ∨
      (Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom1543 chi)) ∨
      ((¬Fin15AnchoredAtom4084 chi ∧
      Fin15AnchoredAtom1337 chi ∧
      Fin15AnchoredAtom1341 chi ∧
      Fin15AnchoredAtom1359 chi ∧
      Fin15AnchoredAtom1423 chi ∧
      Fin15AnchoredAtom1543 chi) ∨
      (Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom1337 chi))) ∨
      (((Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom1342 chi) ∨
      (Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom1360 chi)) ∨
      ((Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom1424 chi) ∨
      (Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom1544 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom4085 chi ∧
      Fin15AnchoredAtom1337 chi ∧
      Fin15AnchoredAtom1342 chi ∧
      Fin15AnchoredAtom1360 chi ∧
      Fin15AnchoredAtom1424 chi ∧
      Fin15AnchoredAtom1544 chi) ∨
      (Fin15AnchoredAtom4086 chi ∧
      ¬Fin15AnchoredAtom1425 chi)) ∨
      ((Fin15AnchoredAtom4086 chi ∧
      ¬Fin15AnchoredAtom1545 chi) ∨
      (¬Fin15AnchoredAtom4086 chi ∧
      Fin15AnchoredAtom1338 chi ∧
      Fin15AnchoredAtom1339 chi ∧
      Fin15AnchoredAtom1361 chi ∧
      Fin15AnchoredAtom1425 chi ∧
      Fin15AnchoredAtom1545 chi))) ∨
      (((Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom1338 chi) ∨
      (Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom1340 chi)) ∨
      ((Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom1362 chi) ∨
      (Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom1426 chi)))) ∨
      ((((Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom1546 chi) ∨
      (¬Fin15AnchoredAtom4087 chi ∧
      Fin15AnchoredAtom1338 chi ∧
      Fin15AnchoredAtom1340 chi ∧
      Fin15AnchoredAtom1362 chi ∧
      Fin15AnchoredAtom1426 chi ∧
      Fin15AnchoredAtom1546 chi)) ∨
      ((Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom1338 chi) ∨
      (Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom1341 chi))) ∨
      (((Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom1363 chi) ∨
      (Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom1427 chi)) ∨
      ((Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom1547 chi) ∨
      (¬Fin15AnchoredAtom4088 chi ∧
      Fin15AnchoredAtom1338 chi ∧
      Fin15AnchoredAtom1341 chi ∧
      Fin15AnchoredAtom1363 chi ∧
      Fin15AnchoredAtom1427 chi ∧
      Fin15AnchoredAtom1547 chi))))) ∨
      (((((Fin15AnchoredAtom4089 chi ∧
      ¬Fin15AnchoredAtom1338 chi) ∨
      (Fin15AnchoredAtom4089 chi ∧
      ¬Fin15AnchoredAtom1342 chi)) ∨
      ((Fin15AnchoredAtom4089 chi ∧
      ¬Fin15AnchoredAtom1364 chi) ∨
      (Fin15AnchoredAtom4089 chi ∧
      ¬Fin15AnchoredAtom1428 chi))) ∨
      (((Fin15AnchoredAtom4089 chi ∧
      ¬Fin15AnchoredAtom1548 chi) ∨
      (¬Fin15AnchoredAtom4089 chi ∧
      Fin15AnchoredAtom1338 chi ∧
      Fin15AnchoredAtom1342 chi ∧
      Fin15AnchoredAtom1364 chi ∧
      Fin15AnchoredAtom1428 chi ∧
      Fin15AnchoredAtom1548 chi)) ∨
      ((Fin15AnchoredAtom4090 chi ∧
      ¬Fin15AnchoredAtom1340 chi) ∨
      (Fin15AnchoredAtom4091 chi ∧
      ¬Fin15AnchoredAtom1430 chi)))) ∨
      ((((Fin15AnchoredAtom4092 chi ∧
      ¬Fin15AnchoredAtom1367 chi) ∨
      (Fin15AnchoredAtom4093 chi ∧
      ¬Fin15AnchoredAtom1340 chi)) ∨
      ((Fin15AnchoredAtom4093 chi ∧
      ¬Fin15AnchoredAtom1341 chi) ∨
      (Fin15AnchoredAtom4093 chi ∧
      ¬Fin15AnchoredAtom1368 chi))) ∨
      (((Fin15AnchoredAtom4093 chi ∧
      ¬Fin15AnchoredAtom1432 chi) ∨
      (Fin15AnchoredAtom4093 chi ∧
      ¬Fin15AnchoredAtom1552 chi)) ∨
      ((¬Fin15AnchoredAtom4093 chi ∧
      Fin15AnchoredAtom1340 chi ∧
      Fin15AnchoredAtom1341 chi ∧
      Fin15AnchoredAtom1368 chi ∧
      Fin15AnchoredAtom1432 chi ∧
      Fin15AnchoredAtom1552 chi) ∨
      (Fin15AnchoredAtom4094 chi ∧
      ¬Fin15AnchoredAtom1340 chi))))))) ∨
      ((((((Fin15AnchoredAtom4094 chi ∧
      ¬Fin15AnchoredAtom1342 chi) ∨
      ((Fin15AnchoredAtom4094 chi ∧
      ¬Fin15AnchoredAtom1369 chi) ∨
      (Fin15AnchoredAtom4094 chi ∧
      ¬Fin15AnchoredAtom1433 chi))) ∨
      (((Fin15AnchoredAtom4094 chi ∧
      ¬Fin15AnchoredAtom1553 chi) ∨
      (¬Fin15AnchoredAtom4094 chi ∧
      Fin15AnchoredAtom1340 chi ∧
      Fin15AnchoredAtom1342 chi ∧
      Fin15AnchoredAtom1369 chi ∧
      Fin15AnchoredAtom1433 chi ∧
      Fin15AnchoredAtom1553 chi)) ∨
      ((Fin15AnchoredAtom4095 chi ∧
      ¬Fin15AnchoredAtom1341 chi) ∨
      (Fin15AnchoredAtom4095 chi ∧
      ¬Fin15AnchoredAtom1342 chi)))) ∨
      ((((Fin15AnchoredAtom4095 chi ∧
      ¬Fin15AnchoredAtom1370 chi) ∨
      (Fin15AnchoredAtom4095 chi ∧
      ¬Fin15AnchoredAtom1434 chi)) ∨
      ((Fin15AnchoredAtom4095 chi ∧
      ¬Fin15AnchoredAtom1554 chi) ∨
      (¬Fin15AnchoredAtom4095 chi ∧
      Fin15AnchoredAtom1341 chi ∧
      Fin15AnchoredAtom1342 chi ∧
      Fin15AnchoredAtom1370 chi ∧
      Fin15AnchoredAtom1434 chi ∧
      Fin15AnchoredAtom1554 chi))) ∨
      (((Fin15AnchoredAtom4096 chi ∧
      ¬Fin15AnchoredAtom1343 chi) ∨
      (Fin15AnchoredAtom4096 chi ∧
      ¬Fin15AnchoredAtom1344 chi)) ∨
      ((Fin15AnchoredAtom4096 chi ∧
      ¬Fin15AnchoredAtom1350 chi) ∨
      (Fin15AnchoredAtom4096 chi ∧
      ¬Fin15AnchoredAtom1435 chi))))) ∨
      (((((Fin15AnchoredAtom4096 chi ∧
      ¬Fin15AnchoredAtom1555 chi) ∨
      (¬Fin15AnchoredAtom4096 chi ∧
      Fin15AnchoredAtom1343 chi ∧
      Fin15AnchoredAtom1344 chi ∧
      Fin15AnchoredAtom1350 chi ∧
      Fin15AnchoredAtom1435 chi ∧
      Fin15AnchoredAtom1555 chi)) ∨
      ((Fin15AnchoredAtom4097 chi ∧
      ¬Fin15AnchoredAtom1343 chi) ∨
      (Fin15AnchoredAtom4097 chi ∧
      ¬Fin15AnchoredAtom1345 chi))) ∨
      (((Fin15AnchoredAtom4097 chi ∧
      ¬Fin15AnchoredAtom1351 chi) ∨
      (Fin15AnchoredAtom4097 chi ∧
      ¬Fin15AnchoredAtom1436 chi)) ∨
      ((Fin15AnchoredAtom4097 chi ∧
      ¬Fin15AnchoredAtom1556 chi) ∨
      (¬Fin15AnchoredAtom4097 chi ∧
      Fin15AnchoredAtom1343 chi ∧
      Fin15AnchoredAtom1345 chi ∧
      Fin15AnchoredAtom1351 chi ∧
      Fin15AnchoredAtom1436 chi ∧
      Fin15AnchoredAtom1556 chi)))) ∨
      ((((Fin15AnchoredAtom4099 chi ∧
      ¬Fin15AnchoredAtom1343 chi) ∨
      (Fin15AnchoredAtom4099 chi ∧
      ¬Fin15AnchoredAtom1347 chi)) ∨
      ((Fin15AnchoredAtom4099 chi ∧
      ¬Fin15AnchoredAtom1353 chi) ∨
      (Fin15AnchoredAtom4099 chi ∧
      ¬Fin15AnchoredAtom1438 chi))) ∨
      (((Fin15AnchoredAtom4099 chi ∧
      ¬Fin15AnchoredAtom1558 chi) ∨
      (¬Fin15AnchoredAtom4099 chi ∧
      Fin15AnchoredAtom1343 chi ∧
      Fin15AnchoredAtom1347 chi ∧
      Fin15AnchoredAtom1353 chi ∧
      Fin15AnchoredAtom1438 chi ∧
      Fin15AnchoredAtom1558 chi)) ∨
      ((Fin15AnchoredAtom4100 chi ∧
      ¬Fin15AnchoredAtom1343 chi) ∨
      (Fin15AnchoredAtom4100 chi ∧
      ¬Fin15AnchoredAtom1348 chi)))))) ∨
      ((((((Fin15AnchoredAtom4100 chi ∧
      ¬Fin15AnchoredAtom1354 chi) ∨
      (Fin15AnchoredAtom4100 chi ∧
      ¬Fin15AnchoredAtom1439 chi)) ∨
      ((Fin15AnchoredAtom4100 chi ∧
      ¬Fin15AnchoredAtom1559 chi) ∨
      (¬Fin15AnchoredAtom4100 chi ∧
      Fin15AnchoredAtom1343 chi ∧
      Fin15AnchoredAtom1348 chi ∧
      Fin15AnchoredAtom1354 chi ∧
      Fin15AnchoredAtom1439 chi ∧
      Fin15AnchoredAtom1559 chi))) ∨
      (((Fin15AnchoredAtom4101 chi ∧
      ¬Fin15AnchoredAtom1343 chi) ∨
      (Fin15AnchoredAtom4101 chi ∧
      ¬Fin15AnchoredAtom1349 chi)) ∨
      ((Fin15AnchoredAtom4101 chi ∧
      ¬Fin15AnchoredAtom1355 chi) ∨
      (Fin15AnchoredAtom4101 chi ∧
      ¬Fin15AnchoredAtom1440 chi)))) ∨
      ((((Fin15AnchoredAtom4101 chi ∧
      ¬Fin15AnchoredAtom1560 chi) ∨
      (¬Fin15AnchoredAtom4101 chi ∧
      Fin15AnchoredAtom1343 chi ∧
      Fin15AnchoredAtom1349 chi ∧
      Fin15AnchoredAtom1355 chi ∧
      Fin15AnchoredAtom1440 chi ∧
      Fin15AnchoredAtom1560 chi)) ∨
      ((Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom1344 chi) ∨
      (Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom1345 chi))) ∨
      (((Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom1356 chi) ∨
      (Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom1441 chi)) ∨
      ((Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom1561 chi) ∨
      (¬Fin15AnchoredAtom4102 chi ∧
      Fin15AnchoredAtom1344 chi ∧
      Fin15AnchoredAtom1345 chi ∧
      Fin15AnchoredAtom1356 chi ∧
      Fin15AnchoredAtom1441 chi ∧
      Fin15AnchoredAtom1561 chi))))) ∨
      (((((Fin15AnchoredAtom4103 chi ∧
      ¬Fin15AnchoredAtom1344 chi) ∨
      (Fin15AnchoredAtom4103 chi ∧
      ¬Fin15AnchoredAtom1562 chi)) ∨
      ((Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom1344 chi) ∨
      (Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom1347 chi))) ∨
      (((Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom1358 chi) ∨
      (Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom1443 chi)) ∨
      ((Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom1563 chi) ∨
      (¬Fin15AnchoredAtom4104 chi ∧
      Fin15AnchoredAtom1344 chi ∧
      Fin15AnchoredAtom1347 chi ∧
      Fin15AnchoredAtom1358 chi ∧
      Fin15AnchoredAtom1443 chi ∧
      Fin15AnchoredAtom1563 chi)))) ∨
      ((((Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom1344 chi) ∨
      (Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom1348 chi)) ∨
      ((Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom1359 chi) ∨
      (Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom1444 chi))) ∨
      (((Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom1564 chi) ∨
      (¬Fin15AnchoredAtom4105 chi ∧
      Fin15AnchoredAtom1344 chi ∧
      Fin15AnchoredAtom1348 chi ∧
      Fin15AnchoredAtom1359 chi ∧
      Fin15AnchoredAtom1444 chi ∧
      Fin15AnchoredAtom1564 chi)) ∨
      ((Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom1344 chi) ∨
      (Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom1349 chi)))))))) ∨
      (((((((Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom1360 chi) ∨
      ((Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom1445 chi) ∨
      (Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom1565 chi))) ∨
      (((¬Fin15AnchoredAtom4106 chi ∧
      Fin15AnchoredAtom1344 chi ∧
      Fin15AnchoredAtom1349 chi ∧
      Fin15AnchoredAtom1360 chi ∧
      Fin15AnchoredAtom1445 chi ∧
      Fin15AnchoredAtom1565 chi) ∨
      (Fin15AnchoredAtom4107 chi ∧
      ¬Fin15AnchoredAtom1345 chi)) ∨
      ((Fin15AnchoredAtom4107 chi ∧
      ¬Fin15AnchoredAtom1566 chi) ∨
      (Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom1345 chi)))) ∨
      ((((Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom1347 chi) ∨
      (Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom1362 chi)) ∨
      ((Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom1447 chi) ∨
      (Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom1567 chi))) ∨
      (((¬Fin15AnchoredAtom4108 chi ∧
      Fin15AnchoredAtom1345 chi ∧
      Fin15AnchoredAtom1347 chi ∧
      Fin15AnchoredAtom1362 chi ∧
      Fin15AnchoredAtom1447 chi ∧
      Fin15AnchoredAtom1567 chi) ∨
      (Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom1345 chi)) ∨
      ((Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom1348 chi) ∨
      (Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom1363 chi))))) ∨
      (((((Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom1448 chi) ∨
      (Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom1568 chi)) ∨
      ((¬Fin15AnchoredAtom4109 chi ∧
      Fin15AnchoredAtom1345 chi ∧
      Fin15AnchoredAtom1348 chi ∧
      Fin15AnchoredAtom1363 chi ∧
      Fin15AnchoredAtom1448 chi ∧
      Fin15AnchoredAtom1568 chi) ∨
      (Fin15AnchoredAtom4110 chi ∧
      ¬Fin15AnchoredAtom1345 chi))) ∨
      (((Fin15AnchoredAtom4110 chi ∧
      ¬Fin15AnchoredAtom1349 chi) ∨
      (Fin15AnchoredAtom4110 chi ∧
      ¬Fin15AnchoredAtom1364 chi)) ∨
      ((Fin15AnchoredAtom4110 chi ∧
      ¬Fin15AnchoredAtom1449 chi) ∨
      (Fin15AnchoredAtom4110 chi ∧
      ¬Fin15AnchoredAtom1569 chi)))) ∨
      ((((¬Fin15AnchoredAtom4110 chi ∧
      Fin15AnchoredAtom1345 chi ∧
      Fin15AnchoredAtom1349 chi ∧
      Fin15AnchoredAtom1364 chi ∧
      Fin15AnchoredAtom1449 chi ∧
      Fin15AnchoredAtom1569 chi) ∨
      (Fin15AnchoredAtom4111 chi ∧
      ¬Fin15AnchoredAtom1347 chi)) ∨
      ((Fin15AnchoredAtom4111 chi ∧
      ¬Fin15AnchoredAtom1570 chi) ∨
      (¬Fin15AnchoredAtom4111 chi ∧
      Fin15AnchoredAtom1346 chi ∧
      Fin15AnchoredAtom1347 chi ∧
      Fin15AnchoredAtom1365 chi ∧
      Fin15AnchoredAtom1450 chi ∧
      Fin15AnchoredAtom1570 chi))) ∨
      (((Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom1347 chi) ∨
      (Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom1348 chi)) ∨
      ((Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom1368 chi) ∨
      (Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom1453 chi)))))) ∨
      ((((((Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom1573 chi) ∨
      (¬Fin15AnchoredAtom4114 chi ∧
      Fin15AnchoredAtom1347 chi ∧
      Fin15AnchoredAtom1348 chi ∧
      Fin15AnchoredAtom1368 chi ∧
      Fin15AnchoredAtom1453 chi ∧
      Fin15AnchoredAtom1573 chi)) ∨
      ((Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom1347 chi) ∨
      (Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom1349 chi))) ∨
      (((Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom1369 chi) ∨
      (Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom1454 chi)) ∨
      ((Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom1574 chi) ∨
      (¬Fin15AnchoredAtom4115 chi ∧
      Fin15AnchoredAtom1347 chi ∧
      Fin15AnchoredAtom1349 chi ∧
      Fin15AnchoredAtom1369 chi ∧
      Fin15AnchoredAtom1454 chi ∧
      Fin15AnchoredAtom1574 chi)))) ∨
      ((((Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom1348 chi) ∨
      (Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom1349 chi)) ∨
      ((Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom1370 chi) ∨
      (Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom1455 chi))) ∨
      (((Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom1575 chi) ∨
      (¬Fin15AnchoredAtom4116 chi ∧
      Fin15AnchoredAtom1348 chi ∧
      Fin15AnchoredAtom1349 chi ∧
      Fin15AnchoredAtom1370 chi ∧
      Fin15AnchoredAtom1455 chi ∧
      Fin15AnchoredAtom1575 chi)) ∨
      ((Fin15AnchoredAtom4117 chi ∧
      ¬Fin15AnchoredAtom1350 chi) ∨
      (Fin15AnchoredAtom4117 chi ∧
      ¬Fin15AnchoredAtom1351 chi))))) ∨
      (((((Fin15AnchoredAtom4117 chi ∧
      ¬Fin15AnchoredAtom1356 chi) ∨
      (Fin15AnchoredAtom4117 chi ∧
      ¬Fin15AnchoredAtom1456 chi)) ∨
      ((Fin15AnchoredAtom4117 chi ∧
      ¬Fin15AnchoredAtom1576 chi) ∨
      (¬Fin15AnchoredAtom4117 chi ∧
      Fin15AnchoredAtom1350 chi ∧
      Fin15AnchoredAtom1351 chi ∧
      Fin15AnchoredAtom1356 chi ∧
      Fin15AnchoredAtom1456 chi ∧
      Fin15AnchoredAtom1576 chi))) ∨
      (((Fin15AnchoredAtom4119 chi ∧
      ¬Fin15AnchoredAtom1350 chi) ∨
      (Fin15AnchoredAtom4119 chi ∧
      ¬Fin15AnchoredAtom1353 chi)) ∨
      ((Fin15AnchoredAtom4119 chi ∧
      ¬Fin15AnchoredAtom1358 chi) ∨
      (Fin15AnchoredAtom4119 chi ∧
      ¬Fin15AnchoredAtom1458 chi)))) ∨
      ((((Fin15AnchoredAtom4119 chi ∧
      ¬Fin15AnchoredAtom1578 chi) ∨
      (¬Fin15AnchoredAtom4119 chi ∧
      Fin15AnchoredAtom1350 chi ∧
      Fin15AnchoredAtom1353 chi ∧
      Fin15AnchoredAtom1358 chi ∧
      Fin15AnchoredAtom1458 chi ∧
      Fin15AnchoredAtom1578 chi)) ∨
      ((Fin15AnchoredAtom4120 chi ∧
      ¬Fin15AnchoredAtom1350 chi) ∨
      (Fin15AnchoredAtom4120 chi ∧
      ¬Fin15AnchoredAtom1354 chi))) ∨
      (((Fin15AnchoredAtom4120 chi ∧
      ¬Fin15AnchoredAtom1359 chi) ∨
      (Fin15AnchoredAtom4120 chi ∧
      ¬Fin15AnchoredAtom1459 chi)) ∨
      ((Fin15AnchoredAtom4120 chi ∧
      ¬Fin15AnchoredAtom1579 chi) ∨
      (¬Fin15AnchoredAtom4120 chi ∧
      Fin15AnchoredAtom1350 chi ∧
      Fin15AnchoredAtom1354 chi ∧
      Fin15AnchoredAtom1359 chi ∧
      Fin15AnchoredAtom1459 chi ∧
      Fin15AnchoredAtom1579 chi))))))) ∨
      ((((((Fin15AnchoredAtom4121 chi ∧
      ¬Fin15AnchoredAtom1350 chi) ∨
      ((Fin15AnchoredAtom4121 chi ∧
      ¬Fin15AnchoredAtom1360 chi) ∨
      (Fin15AnchoredAtom4121 chi ∧
      ¬Fin15AnchoredAtom1460 chi))) ∨
      (((Fin15AnchoredAtom4121 chi ∧
      ¬Fin15AnchoredAtom1580 chi) ∨
      (¬Fin15AnchoredAtom4121 chi ∧
      Fin15AnchoredAtom1350 chi ∧
      Fin15AnchoredAtom1355 chi ∧
      Fin15AnchoredAtom1360 chi ∧
      Fin15AnchoredAtom1460 chi ∧
      Fin15AnchoredAtom1580 chi)) ∨
      ((Fin15AnchoredAtom4123 chi ∧
      ¬Fin15AnchoredAtom1351 chi) ∨
      (Fin15AnchoredAtom4123 chi ∧
      ¬Fin15AnchoredAtom1353 chi)))) ∨
      ((((Fin15AnchoredAtom4123 chi ∧
      ¬Fin15AnchoredAtom1362 chi) ∨
      (Fin15AnchoredAtom4123 chi ∧
      ¬Fin15AnchoredAtom1462 chi)) ∨
      ((Fin15AnchoredAtom4123 chi ∧
      ¬Fin15AnchoredAtom1582 chi) ∨
      (¬Fin15AnchoredAtom4123 chi ∧
      Fin15AnchoredAtom1351 chi ∧
      Fin15AnchoredAtom1353 chi ∧
      Fin15AnchoredAtom1362 chi ∧
      Fin15AnchoredAtom1462 chi ∧
      Fin15AnchoredAtom1582 chi))) ∨
      (((Fin15AnchoredAtom4124 chi ∧
      ¬Fin15AnchoredAtom1351 chi) ∨
      (Fin15AnchoredAtom4124 chi ∧
      ¬Fin15AnchoredAtom1354 chi)) ∨
      ((Fin15AnchoredAtom4124 chi ∧
      ¬Fin15AnchoredAtom1363 chi) ∨
      (Fin15AnchoredAtom4124 chi ∧
      ¬Fin15AnchoredAtom1463 chi))))) ∨
      (((((Fin15AnchoredAtom4124 chi ∧
      ¬Fin15AnchoredAtom1583 chi) ∨
      (¬Fin15AnchoredAtom4124 chi ∧
      Fin15AnchoredAtom1351 chi ∧
      Fin15AnchoredAtom1354 chi ∧
      Fin15AnchoredAtom1363 chi ∧
      Fin15AnchoredAtom1463 chi ∧
      Fin15AnchoredAtom1583 chi)) ∨
      ((Fin15AnchoredAtom4125 chi ∧
      ¬Fin15AnchoredAtom1351 chi) ∨
      (Fin15AnchoredAtom4125 chi ∧
      ¬Fin15AnchoredAtom1355 chi))) ∨
      (((Fin15AnchoredAtom4125 chi ∧
      ¬Fin15AnchoredAtom1364 chi) ∨
      (Fin15AnchoredAtom4125 chi ∧
      ¬Fin15AnchoredAtom1464 chi)) ∨
      ((Fin15AnchoredAtom4125 chi ∧
      ¬Fin15AnchoredAtom1584 chi) ∨
      (¬Fin15AnchoredAtom4125 chi ∧
      Fin15AnchoredAtom1351 chi ∧
      Fin15AnchoredAtom1355 chi ∧
      Fin15AnchoredAtom1364 chi ∧
      Fin15AnchoredAtom1464 chi ∧
      Fin15AnchoredAtom1584 chi)))) ∨
      ((((Fin15AnchoredAtom4129 chi ∧
      ¬Fin15AnchoredAtom1353 chi) ∨
      (Fin15AnchoredAtom4129 chi ∧
      ¬Fin15AnchoredAtom1354 chi)) ∨
      ((Fin15AnchoredAtom4129 chi ∧
      ¬Fin15AnchoredAtom1368 chi) ∨
      (Fin15AnchoredAtom4129 chi ∧
      ¬Fin15AnchoredAtom1468 chi))) ∨
      (((Fin15AnchoredAtom4129 chi ∧
      ¬Fin15AnchoredAtom1588 chi) ∨
      (¬Fin15AnchoredAtom4129 chi ∧
      Fin15AnchoredAtom1353 chi ∧
      Fin15AnchoredAtom1354 chi ∧
      Fin15AnchoredAtom1368 chi ∧
      Fin15AnchoredAtom1468 chi ∧
      Fin15AnchoredAtom1588 chi)) ∨
      ((Fin15AnchoredAtom4130 chi ∧
      ¬Fin15AnchoredAtom1353 chi) ∨
      (Fin15AnchoredAtom4130 chi ∧
      ¬Fin15AnchoredAtom1355 chi)))))) ∨
      ((((((Fin15AnchoredAtom4130 chi ∧
      ¬Fin15AnchoredAtom1369 chi) ∨
      (Fin15AnchoredAtom4130 chi ∧
      ¬Fin15AnchoredAtom1589 chi)) ∨
      ((¬Fin15AnchoredAtom4130 chi ∧
      Fin15AnchoredAtom1353 chi ∧
      Fin15AnchoredAtom1355 chi ∧
      Fin15AnchoredAtom1369 chi ∧
      Fin15AnchoredAtom1469 chi ∧
      Fin15AnchoredAtom1589 chi) ∨
      (Fin15AnchoredAtom4131 chi ∧
      ¬Fin15AnchoredAtom1354 chi))) ∨
      (((Fin15AnchoredAtom4131 chi ∧
      ¬Fin15AnchoredAtom1355 chi) ∨
      (Fin15AnchoredAtom4131 chi ∧
      ¬Fin15AnchoredAtom1370 chi)) ∨
      ((Fin15AnchoredAtom4131 chi ∧
      ¬Fin15AnchoredAtom1470 chi) ∨
      (Fin15AnchoredAtom4131 chi ∧
      ¬Fin15AnchoredAtom1590 chi)))) ∨
      ((((¬Fin15AnchoredAtom4131 chi ∧
      Fin15AnchoredAtom1354 chi ∧
      Fin15AnchoredAtom1355 chi ∧
      Fin15AnchoredAtom1370 chi ∧
      Fin15AnchoredAtom1470 chi ∧
      Fin15AnchoredAtom1590 chi) ∨
      (Fin15AnchoredAtom4132 chi ∧
      ¬Fin15AnchoredAtom1471 chi)) ∨
      ((Fin15AnchoredAtom4132 chi ∧
      ¬Fin15AnchoredAtom1591 chi) ∨
      (¬Fin15AnchoredAtom4132 chi ∧
      Fin15AnchoredAtom1356 chi ∧
      Fin15AnchoredAtom1357 chi ∧
      Fin15AnchoredAtom1361 chi ∧
      Fin15AnchoredAtom1471 chi ∧
      Fin15AnchoredAtom1591 chi))) ∨
      (((Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom1356 chi) ∨
      (Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom1358 chi)) ∨
      ((Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom1362 chi) ∨
      (Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom1472 chi))))) ∨
      (((((Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom1592 chi) ∨
      (¬Fin15AnchoredAtom4133 chi ∧
      Fin15AnchoredAtom1356 chi ∧
      Fin15AnchoredAtom1358 chi ∧
      Fin15AnchoredAtom1362 chi ∧
      Fin15AnchoredAtom1472 chi ∧
      Fin15AnchoredAtom1592 chi)) ∨
      ((Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom1356 chi) ∨
      (Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom1359 chi))) ∨
      (((Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom1363 chi) ∨
      (Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom1473 chi)) ∨
      ((Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom1593 chi) ∨
      (¬Fin15AnchoredAtom4134 chi ∧
      Fin15AnchoredAtom1356 chi ∧
      Fin15AnchoredAtom1359 chi ∧
      Fin15AnchoredAtom1363 chi ∧
      Fin15AnchoredAtom1473 chi ∧
      Fin15AnchoredAtom1593 chi)))) ∨
      ((((Fin15AnchoredAtom4135 chi ∧
      ¬Fin15AnchoredAtom1356 chi) ∨
      (Fin15AnchoredAtom4135 chi ∧
      ¬Fin15AnchoredAtom1360 chi)) ∨
      ((Fin15AnchoredAtom4135 chi ∧
      ¬Fin15AnchoredAtom1364 chi) ∨
      (Fin15AnchoredAtom4135 chi ∧
      ¬Fin15AnchoredAtom1474 chi))) ∨
      (((Fin15AnchoredAtom4135 chi ∧
      ¬Fin15AnchoredAtom1594 chi) ∨
      (¬Fin15AnchoredAtom4135 chi ∧
      Fin15AnchoredAtom1356 chi ∧
      Fin15AnchoredAtom1360 chi ∧
      Fin15AnchoredAtom1364 chi ∧
      Fin15AnchoredAtom1474 chi ∧
      Fin15AnchoredAtom1594 chi)) ∨
      ((Fin15AnchoredAtom4136 chi ∧
      ¬Fin15AnchoredAtom1475 chi) ∨
      (Fin15AnchoredAtom4136 chi ∧
      ¬Fin15AnchoredAtom1595 chi)))))))))) := by
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
                exact fin15Anchored_clause25240 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25241 chi hbad
                ·
                  exact fin15Anchored_clause25242 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25243 chi hbad
                ·
                  exact fin15Anchored_clause25244 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25245 chi hbad
                ·
                  exact fin15Anchored_clause25246 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25247 chi hbad
                ·
                  exact fin15Anchored_clause25248 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25249 chi hbad
                ·
                  exact fin15Anchored_clause25250 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25251 chi hbad
                ·
                  exact fin15Anchored_clause25252 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25253 chi hbad
                ·
                  exact fin15Anchored_clause25254 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25255 chi hbad
                ·
                  exact fin15Anchored_clause25256 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25257 chi hbad
                ·
                  exact fin15Anchored_clause25258 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25259 chi hbad
                ·
                  exact fin15Anchored_clause25260 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25261 chi hbad
                ·
                  exact fin15Anchored_clause25262 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25263 chi hbad
                ·
                  exact fin15Anchored_clause25264 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25265 chi hbad
                ·
                  exact fin15Anchored_clause25266 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25267 chi hbad
                ·
                  exact fin15Anchored_clause25268 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25269 chi hbad
                ·
                  exact fin15Anchored_clause25270 chi hbad
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
                  exact fin15Anchored_clause25271 chi hbad
                ·
                  exact fin15Anchored_clause25272 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25273 chi hbad
                ·
                  exact fin15Anchored_clause25274 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25275 chi hbad
                ·
                  exact fin15Anchored_clause25276 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25277 chi hbad
                ·
                  exact fin15Anchored_clause25278 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25279 chi hbad
                ·
                  exact fin15Anchored_clause25280 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25281 chi hbad
                ·
                  exact fin15Anchored_clause25282 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25283 chi hbad
                ·
                  exact fin15Anchored_clause25284 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25285 chi hbad
                ·
                  exact fin15Anchored_clause25286 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25287 chi hbad
                ·
                  exact fin15Anchored_clause25288 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25289 chi hbad
                ·
                  exact fin15Anchored_clause25290 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25291 chi hbad
                ·
                  exact fin15Anchored_clause25292 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25293 chi hbad
                ·
                  exact fin15Anchored_clause25294 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25295 chi hbad
                ·
                  exact fin15Anchored_clause25296 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25297 chi hbad
                ·
                  exact fin15Anchored_clause25298 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25299 chi hbad
                ·
                  exact fin15Anchored_clause25300 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25301 chi hbad
                ·
                  exact fin15Anchored_clause25302 chi hbad
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
                exact fin15Anchored_clause25303 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25304 chi hbad
                ·
                  exact fin15Anchored_clause25305 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25306 chi hbad
                ·
                  exact fin15Anchored_clause25307 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25308 chi hbad
                ·
                  exact fin15Anchored_clause25309 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25310 chi hbad
                ·
                  exact fin15Anchored_clause25311 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25312 chi hbad
                ·
                  exact fin15Anchored_clause25313 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25314 chi hbad
                ·
                  exact fin15Anchored_clause25315 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25316 chi hbad
                ·
                  exact fin15Anchored_clause25317 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25318 chi hbad
                ·
                  exact fin15Anchored_clause25319 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25320 chi hbad
                ·
                  exact fin15Anchored_clause25321 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25322 chi hbad
                ·
                  exact fin15Anchored_clause25323 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25324 chi hbad
                ·
                  exact fin15Anchored_clause25325 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25326 chi hbad
                ·
                  exact fin15Anchored_clause25327 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25328 chi hbad
                ·
                  exact fin15Anchored_clause25329 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25330 chi hbad
                ·
                  exact fin15Anchored_clause25331 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25332 chi hbad
                ·
                  exact fin15Anchored_clause25333 chi hbad
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
                  exact fin15Anchored_clause25334 chi hbad
                ·
                  exact fin15Anchored_clause25335 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25336 chi hbad
                ·
                  exact fin15Anchored_clause25337 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25338 chi hbad
                ·
                  exact fin15Anchored_clause25339 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25340 chi hbad
                ·
                  exact fin15Anchored_clause25341 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25342 chi hbad
                ·
                  exact fin15Anchored_clause25343 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25344 chi hbad
                ·
                  exact fin15Anchored_clause25345 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25346 chi hbad
                ·
                  exact fin15Anchored_clause25347 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25348 chi hbad
                ·
                  exact fin15Anchored_clause25349 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25350 chi hbad
                ·
                  exact fin15Anchored_clause25351 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25352 chi hbad
                ·
                  exact fin15Anchored_clause25353 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25354 chi hbad
                ·
                  exact fin15Anchored_clause25355 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25356 chi hbad
                ·
                  exact fin15Anchored_clause25357 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25358 chi hbad
                ·
                  exact fin15Anchored_clause25359 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25360 chi hbad
                ·
                  exact fin15Anchored_clause25361 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25362 chi hbad
                ·
                  exact fin15Anchored_clause25363 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25364 chi hbad
                ·
                  exact fin15Anchored_clause25365 chi hbad
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
                exact fin15Anchored_clause25366 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25367 chi hbad
                ·
                  exact fin15Anchored_clause25368 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25369 chi hbad
                ·
                  exact fin15Anchored_clause25370 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25371 chi hbad
                ·
                  exact fin15Anchored_clause25372 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25373 chi hbad
                ·
                  exact fin15Anchored_clause25374 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25375 chi hbad
                ·
                  exact fin15Anchored_clause25376 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25377 chi hbad
                ·
                  exact fin15Anchored_clause25378 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25379 chi hbad
                ·
                  exact fin15Anchored_clause25380 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25381 chi hbad
                ·
                  exact fin15Anchored_clause25382 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25383 chi hbad
                ·
                  exact fin15Anchored_clause25384 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25385 chi hbad
                ·
                  exact fin15Anchored_clause25386 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25387 chi hbad
                ·
                  exact fin15Anchored_clause25388 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25389 chi hbad
                ·
                  exact fin15Anchored_clause25390 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25391 chi hbad
                ·
                  exact fin15Anchored_clause25392 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25393 chi hbad
                ·
                  exact fin15Anchored_clause25394 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25395 chi hbad
                ·
                  exact fin15Anchored_clause25396 chi hbad
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
                  exact fin15Anchored_clause25397 chi hbad
                ·
                  exact fin15Anchored_clause25398 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25399 chi hbad
                ·
                  exact fin15Anchored_clause25400 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25401 chi hbad
                ·
                  exact fin15Anchored_clause25402 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25403 chi hbad
                ·
                  exact fin15Anchored_clause25404 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25405 chi hbad
                ·
                  exact fin15Anchored_clause25406 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25407 chi hbad
                ·
                  exact fin15Anchored_clause25408 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25409 chi hbad
                ·
                  exact fin15Anchored_clause25410 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25411 chi hbad
                ·
                  exact fin15Anchored_clause25412 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25413 chi hbad
                ·
                  exact fin15Anchored_clause25414 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25415 chi hbad
                ·
                  exact fin15Anchored_clause25416 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25417 chi hbad
                ·
                  exact fin15Anchored_clause25418 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25419 chi hbad
                ·
                  exact fin15Anchored_clause25420 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25421 chi hbad
                ·
                  exact fin15Anchored_clause25422 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25423 chi hbad
                ·
                  exact fin15Anchored_clause25424 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25425 chi hbad
                ·
                  exact fin15Anchored_clause25426 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25427 chi hbad
                ·
                  exact fin15Anchored_clause25428 chi hbad
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
                exact fin15Anchored_clause25429 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25430 chi hbad
                ·
                  exact fin15Anchored_clause25431 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25432 chi hbad
                ·
                  exact fin15Anchored_clause25433 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25434 chi hbad
                ·
                  exact fin15Anchored_clause25435 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25436 chi hbad
                ·
                  exact fin15Anchored_clause25437 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25438 chi hbad
                ·
                  exact fin15Anchored_clause25439 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25440 chi hbad
                ·
                  exact fin15Anchored_clause25441 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25442 chi hbad
                ·
                  exact fin15Anchored_clause25443 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25444 chi hbad
                ·
                  exact fin15Anchored_clause25445 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25446 chi hbad
                ·
                  exact fin15Anchored_clause25447 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25448 chi hbad
                ·
                  exact fin15Anchored_clause25449 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25450 chi hbad
                ·
                  exact fin15Anchored_clause25451 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25452 chi hbad
                ·
                  exact fin15Anchored_clause25453 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25454 chi hbad
                ·
                  exact fin15Anchored_clause25455 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25456 chi hbad
                ·
                  exact fin15Anchored_clause25457 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25458 chi hbad
                ·
                  exact fin15Anchored_clause25459 chi hbad
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
                  exact fin15Anchored_clause25460 chi hbad
                ·
                  exact fin15Anchored_clause25461 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25462 chi hbad
                ·
                  exact fin15Anchored_clause25463 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25464 chi hbad
                ·
                  exact fin15Anchored_clause25465 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25466 chi hbad
                ·
                  exact fin15Anchored_clause25467 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25468 chi hbad
                ·
                  exact fin15Anchored_clause25469 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25470 chi hbad
                ·
                  exact fin15Anchored_clause25471 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25472 chi hbad
                ·
                  exact fin15Anchored_clause25473 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25474 chi hbad
                ·
                  exact fin15Anchored_clause25475 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25476 chi hbad
                ·
                  exact fin15Anchored_clause25477 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25478 chi hbad
                ·
                  exact fin15Anchored_clause25479 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25480 chi hbad
                ·
                  exact fin15Anchored_clause25481 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25482 chi hbad
                ·
                  exact fin15Anchored_clause25483 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25484 chi hbad
                ·
                  exact fin15Anchored_clause25485 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25486 chi hbad
                ·
                  exact fin15Anchored_clause25487 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25488 chi hbad
                ·
                  exact fin15Anchored_clause25489 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25490 chi hbad
                ·
                  exact fin15Anchored_clause25491 chi hbad

end ErdosSzekeres

end
