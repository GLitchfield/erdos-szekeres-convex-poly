module

public import ErdosSzekeres.Fin15AnchoredClauseChunk203
public import ErdosSzekeres.Fin15AnchoredClauseChunk204
public import ErdosSzekeres.Fin15AnchoredClauseChunk205

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 103. -/

theorem fin15Anchored_rejectSemanticSegment103
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom1432 chi) ∨
      ((Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom1453 chi) ∨
      (Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom1713 chi))) ∨
      (((¬Fin15AnchoredAtom4254 chi ∧
      Fin15AnchoredAtom1411 chi ∧
      Fin15AnchoredAtom1412 chi ∧
      Fin15AnchoredAtom1432 chi ∧
      Fin15AnchoredAtom1453 chi ∧
      Fin15AnchoredAtom1713 chi) ∨
      (Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom1411 chi)) ∨
      ((Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom1413 chi) ∨
      (Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom1433 chi)))) ∨
      ((((Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom1454 chi) ∨
      (Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom1714 chi)) ∨
      ((¬Fin15AnchoredAtom4255 chi ∧
      Fin15AnchoredAtom1411 chi ∧
      Fin15AnchoredAtom1413 chi ∧
      Fin15AnchoredAtom1433 chi ∧
      Fin15AnchoredAtom1454 chi ∧
      Fin15AnchoredAtom1714 chi) ∨
      (Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom1412 chi))) ∨
      (((Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom1413 chi) ∨
      (Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom1434 chi)) ∨
      ((Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom1455 chi) ∨
      (Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom1715 chi))))) ∨
      (((((¬Fin15AnchoredAtom4256 chi ∧
      Fin15AnchoredAtom1412 chi ∧
      Fin15AnchoredAtom1413 chi ∧
      Fin15AnchoredAtom1434 chi ∧
      Fin15AnchoredAtom1455 chi ∧
      Fin15AnchoredAtom1715 chi) ∨
      (Fin15AnchoredAtom4257 chi ∧
      ¬Fin15AnchoredAtom1414 chi)) ∨
      ((Fin15AnchoredAtom4257 chi ∧
      ¬Fin15AnchoredAtom1415 chi) ∨
      (Fin15AnchoredAtom4257 chi ∧
      ¬Fin15AnchoredAtom1420 chi))) ∨
      (((Fin15AnchoredAtom4257 chi ∧
      ¬Fin15AnchoredAtom1456 chi) ∨
      (Fin15AnchoredAtom4257 chi ∧
      ¬Fin15AnchoredAtom1716 chi)) ∨
      ((¬Fin15AnchoredAtom4257 chi ∧
      Fin15AnchoredAtom1414 chi ∧
      Fin15AnchoredAtom1415 chi ∧
      Fin15AnchoredAtom1420 chi ∧
      Fin15AnchoredAtom1456 chi ∧
      Fin15AnchoredAtom1716 chi) ∨
      (Fin15AnchoredAtom4259 chi ∧
      ¬Fin15AnchoredAtom1414 chi)))) ∨
      ((((Fin15AnchoredAtom4259 chi ∧
      ¬Fin15AnchoredAtom1417 chi) ∨
      (Fin15AnchoredAtom4259 chi ∧
      ¬Fin15AnchoredAtom1422 chi)) ∨
      ((Fin15AnchoredAtom4259 chi ∧
      ¬Fin15AnchoredAtom1458 chi) ∨
      (Fin15AnchoredAtom4259 chi ∧
      ¬Fin15AnchoredAtom1718 chi))) ∨
      (((¬Fin15AnchoredAtom4259 chi ∧
      Fin15AnchoredAtom1414 chi ∧
      Fin15AnchoredAtom1417 chi ∧
      Fin15AnchoredAtom1422 chi ∧
      Fin15AnchoredAtom1458 chi ∧
      Fin15AnchoredAtom1718 chi) ∨
      (Fin15AnchoredAtom4260 chi ∧
      ¬Fin15AnchoredAtom1414 chi)) ∨
      ((Fin15AnchoredAtom4260 chi ∧
      ¬Fin15AnchoredAtom1418 chi) ∨
      (Fin15AnchoredAtom4260 chi ∧
      ¬Fin15AnchoredAtom1423 chi)))))) ∨
      ((((((Fin15AnchoredAtom4260 chi ∧
      ¬Fin15AnchoredAtom1459 chi) ∨
      (Fin15AnchoredAtom4260 chi ∧
      ¬Fin15AnchoredAtom1719 chi)) ∨
      ((¬Fin15AnchoredAtom4260 chi ∧
      Fin15AnchoredAtom1414 chi ∧
      Fin15AnchoredAtom1418 chi ∧
      Fin15AnchoredAtom1423 chi ∧
      Fin15AnchoredAtom1459 chi ∧
      Fin15AnchoredAtom1719 chi) ∨
      (Fin15AnchoredAtom4261 chi ∧
      ¬Fin15AnchoredAtom1414 chi))) ∨
      (((Fin15AnchoredAtom4261 chi ∧
      ¬Fin15AnchoredAtom1419 chi) ∨
      (Fin15AnchoredAtom4261 chi ∧
      ¬Fin15AnchoredAtom1424 chi)) ∨
      ((Fin15AnchoredAtom4261 chi ∧
      ¬Fin15AnchoredAtom1460 chi) ∨
      (Fin15AnchoredAtom4261 chi ∧
      ¬Fin15AnchoredAtom1720 chi)))) ∨
      ((((¬Fin15AnchoredAtom4261 chi ∧
      Fin15AnchoredAtom1414 chi ∧
      Fin15AnchoredAtom1419 chi ∧
      Fin15AnchoredAtom1424 chi ∧
      Fin15AnchoredAtom1460 chi ∧
      Fin15AnchoredAtom1720 chi) ∨
      (Fin15AnchoredAtom4263 chi ∧
      ¬Fin15AnchoredAtom1415 chi)) ∨
      ((Fin15AnchoredAtom4263 chi ∧
      ¬Fin15AnchoredAtom1426 chi) ∨
      (Fin15AnchoredAtom4263 chi ∧
      ¬Fin15AnchoredAtom1462 chi))) ∨
      (((Fin15AnchoredAtom4263 chi ∧
      ¬Fin15AnchoredAtom1722 chi) ∨
      (¬Fin15AnchoredAtom4263 chi ∧
      Fin15AnchoredAtom1415 chi ∧
      Fin15AnchoredAtom1417 chi ∧
      Fin15AnchoredAtom1426 chi ∧
      Fin15AnchoredAtom1462 chi ∧
      Fin15AnchoredAtom1722 chi)) ∨
      ((Fin15AnchoredAtom4264 chi ∧
      ¬Fin15AnchoredAtom1415 chi) ∨
      (Fin15AnchoredAtom4264 chi ∧
      ¬Fin15AnchoredAtom1418 chi))))) ∨
      (((((Fin15AnchoredAtom4264 chi ∧
      ¬Fin15AnchoredAtom1427 chi) ∨
      (Fin15AnchoredAtom4264 chi ∧
      ¬Fin15AnchoredAtom1463 chi)) ∨
      ((Fin15AnchoredAtom4264 chi ∧
      ¬Fin15AnchoredAtom1723 chi) ∨
      (¬Fin15AnchoredAtom4264 chi ∧
      Fin15AnchoredAtom1415 chi ∧
      Fin15AnchoredAtom1418 chi ∧
      Fin15AnchoredAtom1427 chi ∧
      Fin15AnchoredAtom1463 chi ∧
      Fin15AnchoredAtom1723 chi))) ∨
      (((Fin15AnchoredAtom4265 chi ∧
      ¬Fin15AnchoredAtom1415 chi) ∨
      (Fin15AnchoredAtom4265 chi ∧
      ¬Fin15AnchoredAtom1419 chi)) ∨
      ((Fin15AnchoredAtom4265 chi ∧
      ¬Fin15AnchoredAtom1428 chi) ∨
      (Fin15AnchoredAtom4265 chi ∧
      ¬Fin15AnchoredAtom1464 chi)))) ∨
      ((((Fin15AnchoredAtom4265 chi ∧
      ¬Fin15AnchoredAtom1724 chi) ∨
      (¬Fin15AnchoredAtom4265 chi ∧
      Fin15AnchoredAtom1415 chi ∧
      Fin15AnchoredAtom1419 chi ∧
      Fin15AnchoredAtom1428 chi ∧
      Fin15AnchoredAtom1464 chi ∧
      Fin15AnchoredAtom1724 chi)) ∨
      ((Fin15AnchoredAtom4269 chi ∧
      ¬Fin15AnchoredAtom1417 chi) ∨
      (Fin15AnchoredAtom4269 chi ∧
      ¬Fin15AnchoredAtom1418 chi))) ∨
      (((Fin15AnchoredAtom4269 chi ∧
      ¬Fin15AnchoredAtom1432 chi) ∨
      (Fin15AnchoredAtom4269 chi ∧
      ¬Fin15AnchoredAtom1468 chi)) ∨
      ((Fin15AnchoredAtom4269 chi ∧
      ¬Fin15AnchoredAtom1728 chi) ∨
      (¬Fin15AnchoredAtom4269 chi ∧
      Fin15AnchoredAtom1417 chi ∧
      Fin15AnchoredAtom1418 chi ∧
      Fin15AnchoredAtom1432 chi ∧
      Fin15AnchoredAtom1468 chi ∧
      Fin15AnchoredAtom1728 chi))))))) ∨
      ((((((Fin15AnchoredAtom4270 chi ∧
      ¬Fin15AnchoredAtom1417 chi) ∨
      ((Fin15AnchoredAtom4270 chi ∧
      ¬Fin15AnchoredAtom1419 chi) ∨
      (Fin15AnchoredAtom4270 chi ∧
      ¬Fin15AnchoredAtom1433 chi))) ∨
      (((Fin15AnchoredAtom4270 chi ∧
      ¬Fin15AnchoredAtom1469 chi) ∨
      (Fin15AnchoredAtom4270 chi ∧
      ¬Fin15AnchoredAtom1729 chi)) ∨
      ((¬Fin15AnchoredAtom4270 chi ∧
      Fin15AnchoredAtom1417 chi ∧
      Fin15AnchoredAtom1419 chi ∧
      Fin15AnchoredAtom1433 chi ∧
      Fin15AnchoredAtom1469 chi ∧
      Fin15AnchoredAtom1729 chi) ∨
      (Fin15AnchoredAtom4271 chi ∧
      ¬Fin15AnchoredAtom1418 chi)))) ∨
      ((((Fin15AnchoredAtom4271 chi ∧
      ¬Fin15AnchoredAtom1419 chi) ∨
      (Fin15AnchoredAtom4271 chi ∧
      ¬Fin15AnchoredAtom1434 chi)) ∨
      ((Fin15AnchoredAtom4271 chi ∧
      ¬Fin15AnchoredAtom1470 chi) ∨
      (Fin15AnchoredAtom4271 chi ∧
      ¬Fin15AnchoredAtom1730 chi))) ∨
      (((¬Fin15AnchoredAtom4271 chi ∧
      Fin15AnchoredAtom1418 chi ∧
      Fin15AnchoredAtom1419 chi ∧
      Fin15AnchoredAtom1434 chi ∧
      Fin15AnchoredAtom1470 chi ∧
      Fin15AnchoredAtom1730 chi) ∨
      (Fin15AnchoredAtom4272 chi ∧
      ¬Fin15AnchoredAtom1471 chi)) ∨
      ((Fin15AnchoredAtom4272 chi ∧
      ¬Fin15AnchoredAtom1731 chi) ∨
      (¬Fin15AnchoredAtom4272 chi ∧
      Fin15AnchoredAtom1420 chi ∧
      Fin15AnchoredAtom1421 chi ∧
      Fin15AnchoredAtom1425 chi ∧
      Fin15AnchoredAtom1471 chi ∧
      Fin15AnchoredAtom1731 chi))))) ∨
      (((((Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom1420 chi) ∨
      (Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom1422 chi)) ∨
      ((Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom1426 chi) ∨
      (Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom1472 chi))) ∨
      (((Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom1732 chi) ∨
      (¬Fin15AnchoredAtom4273 chi ∧
      Fin15AnchoredAtom1420 chi ∧
      Fin15AnchoredAtom1422 chi ∧
      Fin15AnchoredAtom1426 chi ∧
      Fin15AnchoredAtom1472 chi ∧
      Fin15AnchoredAtom1732 chi)) ∨
      ((Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom1420 chi) ∨
      (Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom1423 chi)))) ∨
      ((((Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom1427 chi) ∨
      (Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom1473 chi)) ∨
      ((Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom1733 chi) ∨
      (¬Fin15AnchoredAtom4274 chi ∧
      Fin15AnchoredAtom1420 chi ∧
      Fin15AnchoredAtom1423 chi ∧
      Fin15AnchoredAtom1427 chi ∧
      Fin15AnchoredAtom1473 chi ∧
      Fin15AnchoredAtom1733 chi))) ∨
      (((Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom1420 chi) ∨
      (Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom1424 chi)) ∨
      ((Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom1428 chi) ∨
      (Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom1474 chi)))))) ∨
      ((((((Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom1734 chi) ∨
      (¬Fin15AnchoredAtom4275 chi ∧
      Fin15AnchoredAtom1420 chi ∧
      Fin15AnchoredAtom1424 chi ∧
      Fin15AnchoredAtom1428 chi ∧
      Fin15AnchoredAtom1474 chi ∧
      Fin15AnchoredAtom1734 chi)) ∨
      ((Fin15AnchoredAtom4276 chi ∧
      ¬Fin15AnchoredAtom1735 chi) ∨
      (¬Fin15AnchoredAtom4276 chi ∧
      Fin15AnchoredAtom1421 chi ∧
      Fin15AnchoredAtom1422 chi ∧
      Fin15AnchoredAtom1429 chi ∧
      Fin15AnchoredAtom1475 chi ∧
      Fin15AnchoredAtom1735 chi))) ∨
      (((Fin15AnchoredAtom4277 chi ∧
      ¬Fin15AnchoredAtom1423 chi) ∨
      (Fin15AnchoredAtom4278 chi ∧
      ¬Fin15AnchoredAtom1737 chi)) ∨
      ((Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom1422 chi) ∨
      (Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom1423 chi)))) ∨
      ((((Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom1432 chi) ∨
      (Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom1478 chi)) ∨
      ((Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom1738 chi) ∨
      (¬Fin15AnchoredAtom4279 chi ∧
      Fin15AnchoredAtom1422 chi ∧
      Fin15AnchoredAtom1423 chi ∧
      Fin15AnchoredAtom1432 chi ∧
      Fin15AnchoredAtom1478 chi ∧
      Fin15AnchoredAtom1738 chi))) ∨
      (((Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom1422 chi) ∨
      (Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom1424 chi)) ∨
      ((Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom1433 chi) ∨
      (Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom1479 chi))))) ∨
      (((((Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom1739 chi) ∨
      (¬Fin15AnchoredAtom4280 chi ∧
      Fin15AnchoredAtom1422 chi ∧
      Fin15AnchoredAtom1424 chi ∧
      Fin15AnchoredAtom1433 chi ∧
      Fin15AnchoredAtom1479 chi ∧
      Fin15AnchoredAtom1739 chi)) ∨
      ((Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom1423 chi) ∨
      (Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom1424 chi))) ∨
      (((Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom1434 chi) ∨
      (Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom1480 chi)) ∨
      ((Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom1740 chi) ∨
      (¬Fin15AnchoredAtom4281 chi ∧
      Fin15AnchoredAtom1423 chi ∧
      Fin15AnchoredAtom1424 chi ∧
      Fin15AnchoredAtom1434 chi ∧
      Fin15AnchoredAtom1480 chi ∧
      Fin15AnchoredAtom1740 chi)))) ∨
      ((((Fin15AnchoredAtom4282 chi ∧
      ¬Fin15AnchoredAtom1426 chi) ∨
      (Fin15AnchoredAtom4282 chi ∧
      ¬Fin15AnchoredAtom1741 chi)) ∨
      ((¬Fin15AnchoredAtom4282 chi ∧
      Fin15AnchoredAtom1425 chi ∧
      Fin15AnchoredAtom1426 chi ∧
      Fin15AnchoredAtom1429 chi ∧
      Fin15AnchoredAtom1481 chi ∧
      Fin15AnchoredAtom1741 chi) ∨
      (Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom1426 chi))) ∨
      (((Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom1427 chi) ∨
      (Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom1432 chi)) ∨
      ((Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom1484 chi) ∨
      (Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom1744 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom4285 chi ∧
      Fin15AnchoredAtom1426 chi ∧
      Fin15AnchoredAtom1427 chi ∧
      Fin15AnchoredAtom1432 chi ∧
      Fin15AnchoredAtom1484 chi ∧
      Fin15AnchoredAtom1744 chi) ∨
      ((Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom1426 chi) ∨
      (Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom1428 chi))) ∨
      (((Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom1433 chi) ∨
      (Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom1485 chi)) ∨
      ((Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom1745 chi) ∨
      (¬Fin15AnchoredAtom4286 chi ∧
      Fin15AnchoredAtom1426 chi ∧
      Fin15AnchoredAtom1428 chi ∧
      Fin15AnchoredAtom1433 chi ∧
      Fin15AnchoredAtom1485 chi ∧
      Fin15AnchoredAtom1745 chi)))) ∨
      ((((Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom1427 chi) ∨
      (Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom1428 chi)) ∨
      ((Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom1434 chi) ∨
      (Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom1486 chi))) ∨
      (((Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom1746 chi) ∨
      (¬Fin15AnchoredAtom4287 chi ∧
      Fin15AnchoredAtom1427 chi ∧
      Fin15AnchoredAtom1428 chi ∧
      Fin15AnchoredAtom1434 chi ∧
      Fin15AnchoredAtom1486 chi ∧
      Fin15AnchoredAtom1746 chi)) ∨
      ((¬Fin15AnchoredAtom4288 chi ∧
      Fin15AnchoredAtom1429 chi ∧
      Fin15AnchoredAtom1430 chi ∧
      Fin15AnchoredAtom1432 chi ∧
      Fin15AnchoredAtom1487 chi ∧
      Fin15AnchoredAtom1747 chi) ∨
      (Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom1432 chi))))) ∨
      (((((Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom1433 chi) ∨
      (Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom1434 chi)) ∨
      ((Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom1490 chi) ∨
      (Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom1750 chi))) ∨
      (((¬Fin15AnchoredAtom4291 chi ∧
      Fin15AnchoredAtom1432 chi ∧
      Fin15AnchoredAtom1433 chi ∧
      Fin15AnchoredAtom1434 chi ∧
      Fin15AnchoredAtom1490 chi ∧
      Fin15AnchoredAtom1750 chi) ∨
      (Fin15AnchoredAtom4292 chi ∧
      ¬Fin15AnchoredAtom1435 chi)) ∨
      ((Fin15AnchoredAtom4292 chi ∧
      ¬Fin15AnchoredAtom1436 chi) ∨
      (Fin15AnchoredAtom4292 chi ∧
      ¬Fin15AnchoredAtom1441 chi)))) ∨
      ((((Fin15AnchoredAtom4292 chi ∧
      ¬Fin15AnchoredAtom1751 chi) ∨
      (¬Fin15AnchoredAtom4292 chi ∧
      Fin15AnchoredAtom1435 chi ∧
      Fin15AnchoredAtom1436 chi ∧
      Fin15AnchoredAtom1441 chi ∧
      Fin15AnchoredAtom1456 chi ∧
      Fin15AnchoredAtom1751 chi)) ∨
      ((Fin15AnchoredAtom4294 chi ∧
      ¬Fin15AnchoredAtom1435 chi) ∨
      (Fin15AnchoredAtom4294 chi ∧
      ¬Fin15AnchoredAtom1438 chi))) ∨
      (((Fin15AnchoredAtom4294 chi ∧
      ¬Fin15AnchoredAtom1443 chi) ∨
      (Fin15AnchoredAtom4294 chi ∧
      ¬Fin15AnchoredAtom1753 chi)) ∨
      ((¬Fin15AnchoredAtom4294 chi ∧
      Fin15AnchoredAtom1435 chi ∧
      Fin15AnchoredAtom1438 chi ∧
      Fin15AnchoredAtom1443 chi ∧
      Fin15AnchoredAtom1458 chi ∧
      Fin15AnchoredAtom1753 chi) ∨
      (Fin15AnchoredAtom4295 chi ∧
      ¬Fin15AnchoredAtom1435 chi)))))) ∨
      ((((((Fin15AnchoredAtom4295 chi ∧
      ¬Fin15AnchoredAtom1439 chi) ∨
      (Fin15AnchoredAtom4295 chi ∧
      ¬Fin15AnchoredAtom1444 chi)) ∨
      ((Fin15AnchoredAtom4295 chi ∧
      ¬Fin15AnchoredAtom1754 chi) ∨
      (¬Fin15AnchoredAtom4295 chi ∧
      Fin15AnchoredAtom1435 chi ∧
      Fin15AnchoredAtom1439 chi ∧
      Fin15AnchoredAtom1444 chi ∧
      Fin15AnchoredAtom1459 chi ∧
      Fin15AnchoredAtom1754 chi))) ∨
      (((Fin15AnchoredAtom4296 chi ∧
      ¬Fin15AnchoredAtom1435 chi) ∨
      (Fin15AnchoredAtom4296 chi ∧
      ¬Fin15AnchoredAtom1440 chi)) ∨
      ((Fin15AnchoredAtom4296 chi ∧
      ¬Fin15AnchoredAtom1445 chi) ∨
      (Fin15AnchoredAtom4296 chi ∧
      ¬Fin15AnchoredAtom1460 chi)))) ∨
      ((((Fin15AnchoredAtom4296 chi ∧
      ¬Fin15AnchoredAtom1755 chi) ∨
      (¬Fin15AnchoredAtom4296 chi ∧
      Fin15AnchoredAtom1435 chi ∧
      Fin15AnchoredAtom1440 chi ∧
      Fin15AnchoredAtom1445 chi ∧
      Fin15AnchoredAtom1460 chi ∧
      Fin15AnchoredAtom1755 chi)) ∨
      ((Fin15AnchoredAtom4298 chi ∧
      ¬Fin15AnchoredAtom1436 chi) ∨
      (Fin15AnchoredAtom4298 chi ∧
      ¬Fin15AnchoredAtom1438 chi))) ∨
      (((Fin15AnchoredAtom4298 chi ∧
      ¬Fin15AnchoredAtom1447 chi) ∨
      (Fin15AnchoredAtom4298 chi ∧
      ¬Fin15AnchoredAtom1757 chi)) ∨
      ((¬Fin15AnchoredAtom4298 chi ∧
      Fin15AnchoredAtom1436 chi ∧
      Fin15AnchoredAtom1438 chi ∧
      Fin15AnchoredAtom1447 chi ∧
      Fin15AnchoredAtom1462 chi ∧
      Fin15AnchoredAtom1757 chi) ∨
      (Fin15AnchoredAtom4299 chi ∧
      ¬Fin15AnchoredAtom1436 chi))))) ∨
      (((((Fin15AnchoredAtom4299 chi ∧
      ¬Fin15AnchoredAtom1439 chi) ∨
      (Fin15AnchoredAtom4299 chi ∧
      ¬Fin15AnchoredAtom1448 chi)) ∨
      ((Fin15AnchoredAtom4299 chi ∧
      ¬Fin15AnchoredAtom1463 chi) ∨
      (Fin15AnchoredAtom4299 chi ∧
      ¬Fin15AnchoredAtom1758 chi))) ∨
      (((¬Fin15AnchoredAtom4299 chi ∧
      Fin15AnchoredAtom1436 chi ∧
      Fin15AnchoredAtom1439 chi ∧
      Fin15AnchoredAtom1448 chi ∧
      Fin15AnchoredAtom1463 chi ∧
      Fin15AnchoredAtom1758 chi) ∨
      (Fin15AnchoredAtom4300 chi ∧
      ¬Fin15AnchoredAtom1436 chi)) ∨
      ((Fin15AnchoredAtom4300 chi ∧
      ¬Fin15AnchoredAtom1440 chi) ∨
      (Fin15AnchoredAtom4300 chi ∧
      ¬Fin15AnchoredAtom1449 chi)))) ∨
      ((((Fin15AnchoredAtom4300 chi ∧
      ¬Fin15AnchoredAtom1464 chi) ∨
      (Fin15AnchoredAtom4300 chi ∧
      ¬Fin15AnchoredAtom1759 chi)) ∨
      ((¬Fin15AnchoredAtom4300 chi ∧
      Fin15AnchoredAtom1436 chi ∧
      Fin15AnchoredAtom1440 chi ∧
      Fin15AnchoredAtom1449 chi ∧
      Fin15AnchoredAtom1464 chi ∧
      Fin15AnchoredAtom1759 chi) ∨
      (Fin15AnchoredAtom4304 chi ∧
      ¬Fin15AnchoredAtom1438 chi))) ∨
      (((Fin15AnchoredAtom4304 chi ∧
      ¬Fin15AnchoredAtom1439 chi) ∨
      (Fin15AnchoredAtom4304 chi ∧
      ¬Fin15AnchoredAtom1453 chi)) ∨
      ((Fin15AnchoredAtom4304 chi ∧
      ¬Fin15AnchoredAtom1468 chi) ∨
      (Fin15AnchoredAtom4304 chi ∧
      ¬Fin15AnchoredAtom1763 chi))))))) ∨
      (((((((¬Fin15AnchoredAtom4304 chi ∧
      Fin15AnchoredAtom1438 chi ∧
      Fin15AnchoredAtom1439 chi ∧
      Fin15AnchoredAtom1453 chi ∧
      Fin15AnchoredAtom1468 chi ∧
      Fin15AnchoredAtom1763 chi) ∨
      (Fin15AnchoredAtom4305 chi ∧
      ¬Fin15AnchoredAtom1438 chi)) ∨
      ((Fin15AnchoredAtom4305 chi ∧
      ¬Fin15AnchoredAtom1440 chi) ∨
      (Fin15AnchoredAtom4305 chi ∧
      ¬Fin15AnchoredAtom1454 chi))) ∨
      (((Fin15AnchoredAtom4305 chi ∧
      ¬Fin15AnchoredAtom1469 chi) ∨
      (Fin15AnchoredAtom4305 chi ∧
      ¬Fin15AnchoredAtom1764 chi)) ∨
      ((¬Fin15AnchoredAtom4305 chi ∧
      Fin15AnchoredAtom1438 chi ∧
      Fin15AnchoredAtom1440 chi ∧
      Fin15AnchoredAtom1454 chi ∧
      Fin15AnchoredAtom1469 chi ∧
      Fin15AnchoredAtom1764 chi) ∨
      (Fin15AnchoredAtom4306 chi ∧
      ¬Fin15AnchoredAtom1439 chi)))) ∨
      ((((Fin15AnchoredAtom4306 chi ∧
      ¬Fin15AnchoredAtom1440 chi) ∨
      (Fin15AnchoredAtom4306 chi ∧
      ¬Fin15AnchoredAtom1455 chi)) ∨
      ((Fin15AnchoredAtom4306 chi ∧
      ¬Fin15AnchoredAtom1765 chi) ∨
      (¬Fin15AnchoredAtom4306 chi ∧
      Fin15AnchoredAtom1439 chi ∧
      Fin15AnchoredAtom1440 chi ∧
      Fin15AnchoredAtom1455 chi ∧
      Fin15AnchoredAtom1470 chi ∧
      Fin15AnchoredAtom1765 chi))) ∨
      (((Fin15AnchoredAtom4307 chi ∧
      ¬Fin15AnchoredAtom1441 chi) ∨
      (Fin15AnchoredAtom4307 chi ∧
      ¬Fin15AnchoredAtom1766 chi)) ∨
      ((Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom1441 chi) ∨
      (Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom1443 chi))))) ∨
      (((((Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom1447 chi) ∨
      (Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom1472 chi)) ∨
      ((Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom1767 chi) ∨
      (¬Fin15AnchoredAtom4308 chi ∧
      Fin15AnchoredAtom1441 chi ∧
      Fin15AnchoredAtom1443 chi ∧
      Fin15AnchoredAtom1447 chi ∧
      Fin15AnchoredAtom1472 chi ∧
      Fin15AnchoredAtom1767 chi))) ∨
      (((Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom1441 chi) ∨
      (Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom1444 chi)) ∨
      ((Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom1448 chi) ∨
      (Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom1473 chi)))) ∨
      ((((Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom1768 chi) ∨
      (¬Fin15AnchoredAtom4309 chi ∧
      Fin15AnchoredAtom1441 chi ∧
      Fin15AnchoredAtom1444 chi ∧
      Fin15AnchoredAtom1448 chi ∧
      Fin15AnchoredAtom1473 chi ∧
      Fin15AnchoredAtom1768 chi)) ∨
      ((Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom1441 chi) ∨
      (Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom1445 chi))) ∨
      (((Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom1449 chi) ∨
      (Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom1474 chi)) ∨
      ((Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom1769 chi) ∨
      (¬Fin15AnchoredAtom4310 chi ∧
      Fin15AnchoredAtom1441 chi ∧
      Fin15AnchoredAtom1445 chi ∧
      Fin15AnchoredAtom1449 chi ∧
      Fin15AnchoredAtom1474 chi ∧
      Fin15AnchoredAtom1769 chi)))))) ∨
      ((((((Fin15AnchoredAtom4311 chi ∧
      ¬Fin15AnchoredAtom1443 chi) ∨
      (Fin15AnchoredAtom4311 chi ∧
      ¬Fin15AnchoredAtom1450 chi)) ∨
      ((Fin15AnchoredAtom4311 chi ∧
      ¬Fin15AnchoredAtom1770 chi) ∨
      (Fin15AnchoredAtom4312 chi ∧
      ¬Fin15AnchoredAtom1444 chi))) ∨
      (((Fin15AnchoredAtom4313 chi ∧
      ¬Fin15AnchoredAtom1445 chi) ∨
      (Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom1443 chi)) ∨
      ((Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom1444 chi) ∨
      (Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom1453 chi)))) ∨
      ((((Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom1478 chi) ∨
      (Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom1773 chi)) ∨
      ((¬Fin15AnchoredAtom4314 chi ∧
      Fin15AnchoredAtom1443 chi ∧
      Fin15AnchoredAtom1444 chi ∧
      Fin15AnchoredAtom1453 chi ∧
      Fin15AnchoredAtom1478 chi ∧
      Fin15AnchoredAtom1773 chi) ∨
      (Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom1443 chi))) ∨
      (((Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom1445 chi) ∨
      (Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom1454 chi)) ∨
      ((Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom1479 chi) ∨
      (Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom1774 chi))))) ∨
      (((((¬Fin15AnchoredAtom4315 chi ∧
      Fin15AnchoredAtom1443 chi ∧
      Fin15AnchoredAtom1445 chi ∧
      Fin15AnchoredAtom1454 chi ∧
      Fin15AnchoredAtom1479 chi ∧
      Fin15AnchoredAtom1774 chi) ∨
      (Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom1444 chi)) ∨
      ((Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom1445 chi) ∨
      (Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom1455 chi))) ∨
      (((Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom1480 chi) ∨
      (Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom1775 chi)) ∨
      ((¬Fin15AnchoredAtom4316 chi ∧
      Fin15AnchoredAtom1444 chi ∧
      Fin15AnchoredAtom1445 chi ∧
      Fin15AnchoredAtom1455 chi ∧
      Fin15AnchoredAtom1480 chi ∧
      Fin15AnchoredAtom1775 chi) ∨
      (Fin15AnchoredAtom4317 chi ∧
      ¬Fin15AnchoredAtom1447 chi)))) ∨
      ((((Fin15AnchoredAtom4317 chi ∧
      ¬Fin15AnchoredAtom1481 chi) ∨
      (Fin15AnchoredAtom4317 chi ∧
      ¬Fin15AnchoredAtom1776 chi)) ∨
      ((Fin15AnchoredAtom4318 chi ∧
      ¬Fin15AnchoredAtom1448 chi) ∨
      (Fin15AnchoredAtom4318 chi ∧
      ¬Fin15AnchoredAtom1777 chi))) ∨
      (((Fin15AnchoredAtom4319 chi ∧
      ¬Fin15AnchoredAtom1449 chi) ∨
      (Fin15AnchoredAtom4319 chi ∧
      ¬Fin15AnchoredAtom1483 chi)) ∨
      ((Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom1447 chi) ∨
      (Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom1448 chi)))))))))) := by
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
                exact fin15Anchored_clause25997 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25998 chi hbad
                ·
                  exact fin15Anchored_clause25999 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26000 chi hbad
                ·
                  exact fin15Anchored_clause26001 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26002 chi hbad
                ·
                  exact fin15Anchored_clause26003 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26004 chi hbad
                ·
                  exact fin15Anchored_clause26005 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26006 chi hbad
                ·
                  exact fin15Anchored_clause26007 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26008 chi hbad
                ·
                  exact fin15Anchored_clause26009 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26010 chi hbad
                ·
                  exact fin15Anchored_clause26011 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26012 chi hbad
                ·
                  exact fin15Anchored_clause26013 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26014 chi hbad
                ·
                  exact fin15Anchored_clause26015 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26016 chi hbad
                ·
                  exact fin15Anchored_clause26017 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26018 chi hbad
                ·
                  exact fin15Anchored_clause26019 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26020 chi hbad
                ·
                  exact fin15Anchored_clause26021 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26022 chi hbad
                ·
                  exact fin15Anchored_clause26023 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26024 chi hbad
                ·
                  exact fin15Anchored_clause26025 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26026 chi hbad
                ·
                  exact fin15Anchored_clause26027 chi hbad
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
                  exact fin15Anchored_clause26028 chi hbad
                ·
                  exact fin15Anchored_clause26029 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26030 chi hbad
                ·
                  exact fin15Anchored_clause26031 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26032 chi hbad
                ·
                  exact fin15Anchored_clause26033 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26034 chi hbad
                ·
                  exact fin15Anchored_clause26035 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26036 chi hbad
                ·
                  exact fin15Anchored_clause26037 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26038 chi hbad
                ·
                  exact fin15Anchored_clause26039 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26040 chi hbad
                ·
                  exact fin15Anchored_clause26041 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26042 chi hbad
                ·
                  exact fin15Anchored_clause26043 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26044 chi hbad
                ·
                  exact fin15Anchored_clause26045 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26046 chi hbad
                ·
                  exact fin15Anchored_clause26047 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26048 chi hbad
                ·
                  exact fin15Anchored_clause26049 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26050 chi hbad
                ·
                  exact fin15Anchored_clause26051 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26052 chi hbad
                ·
                  exact fin15Anchored_clause26053 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26054 chi hbad
                ·
                  exact fin15Anchored_clause26055 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26056 chi hbad
                ·
                  exact fin15Anchored_clause26057 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26058 chi hbad
                ·
                  exact fin15Anchored_clause26059 chi hbad
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
                exact fin15Anchored_clause26060 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26061 chi hbad
                ·
                  exact fin15Anchored_clause26062 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26063 chi hbad
                ·
                  exact fin15Anchored_clause26064 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26065 chi hbad
                ·
                  exact fin15Anchored_clause26066 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26067 chi hbad
                ·
                  exact fin15Anchored_clause26068 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26069 chi hbad
                ·
                  exact fin15Anchored_clause26070 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26071 chi hbad
                ·
                  exact fin15Anchored_clause26072 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26073 chi hbad
                ·
                  exact fin15Anchored_clause26074 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26075 chi hbad
                ·
                  exact fin15Anchored_clause26076 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26077 chi hbad
                ·
                  exact fin15Anchored_clause26078 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26079 chi hbad
                ·
                  exact fin15Anchored_clause26080 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26081 chi hbad
                ·
                  exact fin15Anchored_clause26082 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26083 chi hbad
                ·
                  exact fin15Anchored_clause26084 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26085 chi hbad
                ·
                  exact fin15Anchored_clause26086 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26087 chi hbad
                ·
                  exact fin15Anchored_clause26088 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26089 chi hbad
                ·
                  exact fin15Anchored_clause26090 chi hbad
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
                  exact fin15Anchored_clause26091 chi hbad
                ·
                  exact fin15Anchored_clause26092 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26093 chi hbad
                ·
                  exact fin15Anchored_clause26094 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26095 chi hbad
                ·
                  exact fin15Anchored_clause26096 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26097 chi hbad
                ·
                  exact fin15Anchored_clause26098 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26099 chi hbad
                ·
                  exact fin15Anchored_clause26100 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26101 chi hbad
                ·
                  exact fin15Anchored_clause26102 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26103 chi hbad
                ·
                  exact fin15Anchored_clause26104 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26105 chi hbad
                ·
                  exact fin15Anchored_clause26106 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26107 chi hbad
                ·
                  exact fin15Anchored_clause26108 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26109 chi hbad
                ·
                  exact fin15Anchored_clause26110 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26111 chi hbad
                ·
                  exact fin15Anchored_clause26112 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26113 chi hbad
                ·
                  exact fin15Anchored_clause26114 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26115 chi hbad
                ·
                  exact fin15Anchored_clause26116 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26117 chi hbad
                ·
                  exact fin15Anchored_clause26118 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26119 chi hbad
                ·
                  exact fin15Anchored_clause26120 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26121 chi hbad
                ·
                  exact fin15Anchored_clause26122 chi hbad
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
                exact fin15Anchored_clause26123 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26124 chi hbad
                ·
                  exact fin15Anchored_clause26125 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26126 chi hbad
                ·
                  exact fin15Anchored_clause26127 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26128 chi hbad
                ·
                  exact fin15Anchored_clause26129 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26130 chi hbad
                ·
                  exact fin15Anchored_clause26131 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26132 chi hbad
                ·
                  exact fin15Anchored_clause26133 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26134 chi hbad
                ·
                  exact fin15Anchored_clause26135 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26136 chi hbad
                ·
                  exact fin15Anchored_clause26137 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26138 chi hbad
                ·
                  exact fin15Anchored_clause26139 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26140 chi hbad
                ·
                  exact fin15Anchored_clause26141 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26142 chi hbad
                ·
                  exact fin15Anchored_clause26143 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26144 chi hbad
                ·
                  exact fin15Anchored_clause26145 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26146 chi hbad
                ·
                  exact fin15Anchored_clause26147 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26148 chi hbad
                ·
                  exact fin15Anchored_clause26149 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26150 chi hbad
                ·
                  exact fin15Anchored_clause26151 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26152 chi hbad
                ·
                  exact fin15Anchored_clause26153 chi hbad
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
                  exact fin15Anchored_clause26154 chi hbad
                ·
                  exact fin15Anchored_clause26155 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26156 chi hbad
                ·
                  exact fin15Anchored_clause26157 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26158 chi hbad
                ·
                  exact fin15Anchored_clause26159 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26160 chi hbad
                ·
                  exact fin15Anchored_clause26161 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26162 chi hbad
                ·
                  exact fin15Anchored_clause26163 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26164 chi hbad
                ·
                  exact fin15Anchored_clause26165 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26166 chi hbad
                ·
                  exact fin15Anchored_clause26167 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26168 chi hbad
                ·
                  exact fin15Anchored_clause26169 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26170 chi hbad
                ·
                  exact fin15Anchored_clause26171 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26172 chi hbad
                ·
                  exact fin15Anchored_clause26173 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26174 chi hbad
                ·
                  exact fin15Anchored_clause26175 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26176 chi hbad
                ·
                  exact fin15Anchored_clause26177 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26178 chi hbad
                ·
                  exact fin15Anchored_clause26179 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26180 chi hbad
                ·
                  exact fin15Anchored_clause26181 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26182 chi hbad
                ·
                  exact fin15Anchored_clause26183 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26184 chi hbad
                ·
                  exact fin15Anchored_clause26185 chi hbad
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
                  exact fin15Anchored_clause26186 chi hbad
                ·
                  exact fin15Anchored_clause26187 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26188 chi hbad
                ·
                  exact fin15Anchored_clause26189 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26190 chi hbad
                ·
                  exact fin15Anchored_clause26191 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26192 chi hbad
                ·
                  exact fin15Anchored_clause26193 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26194 chi hbad
                ·
                  exact fin15Anchored_clause26195 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26196 chi hbad
                ·
                  exact fin15Anchored_clause26197 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26198 chi hbad
                ·
                  exact fin15Anchored_clause26199 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26200 chi hbad
                ·
                  exact fin15Anchored_clause26201 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26202 chi hbad
                ·
                  exact fin15Anchored_clause26203 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26204 chi hbad
                ·
                  exact fin15Anchored_clause26205 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26206 chi hbad
                ·
                  exact fin15Anchored_clause26207 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26208 chi hbad
                ·
                  exact fin15Anchored_clause26209 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26210 chi hbad
                ·
                  exact fin15Anchored_clause26211 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26212 chi hbad
                ·
                  exact fin15Anchored_clause26213 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26214 chi hbad
                ·
                  exact fin15Anchored_clause26215 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26216 chi hbad
                ·
                  exact fin15Anchored_clause26217 chi hbad
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
                  exact fin15Anchored_clause26218 chi hbad
                ·
                  exact fin15Anchored_clause26219 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26220 chi hbad
                ·
                  exact fin15Anchored_clause26221 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26222 chi hbad
                ·
                  exact fin15Anchored_clause26223 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26224 chi hbad
                ·
                  exact fin15Anchored_clause26225 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26226 chi hbad
                ·
                  exact fin15Anchored_clause26227 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26228 chi hbad
                ·
                  exact fin15Anchored_clause26229 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26230 chi hbad
                ·
                  exact fin15Anchored_clause26231 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26232 chi hbad
                ·
                  exact fin15Anchored_clause26233 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26234 chi hbad
                ·
                  exact fin15Anchored_clause26235 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26236 chi hbad
                ·
                  exact fin15Anchored_clause26237 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26238 chi hbad
                ·
                  exact fin15Anchored_clause26239 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26240 chi hbad
                ·
                  exact fin15Anchored_clause26241 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26242 chi hbad
                ·
                  exact fin15Anchored_clause26243 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26244 chi hbad
                ·
                  exact fin15Anchored_clause26245 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26246 chi hbad
                ·
                  exact fin15Anchored_clause26247 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26248 chi hbad
                ·
                  exact fin15Anchored_clause26249 chi hbad

end ErdosSzekeres

end
