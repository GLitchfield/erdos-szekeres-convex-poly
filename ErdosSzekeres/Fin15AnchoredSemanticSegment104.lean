module

public import ErdosSzekeres.Fin15AnchoredClauseChunk205
public import ErdosSzekeres.Fin15AnchoredClauseChunk206
public import ErdosSzekeres.Fin15AnchoredClauseChunk207

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 104. -/

theorem fin15Anchored_rejectSemanticSegment104
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom1453 chi) ∨
      ((Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom1484 chi) ∨
      (Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom1779 chi))) ∨
      (((¬Fin15AnchoredAtom4320 chi ∧
      Fin15AnchoredAtom1447 chi ∧
      Fin15AnchoredAtom1448 chi ∧
      Fin15AnchoredAtom1453 chi ∧
      Fin15AnchoredAtom1484 chi ∧
      Fin15AnchoredAtom1779 chi) ∨
      (Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom1447 chi)) ∨
      ((Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom1449 chi) ∨
      (Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom1454 chi)))) ∨
      ((((Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom1485 chi) ∨
      (Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom1780 chi)) ∨
      ((¬Fin15AnchoredAtom4321 chi ∧
      Fin15AnchoredAtom1447 chi ∧
      Fin15AnchoredAtom1449 chi ∧
      Fin15AnchoredAtom1454 chi ∧
      Fin15AnchoredAtom1485 chi ∧
      Fin15AnchoredAtom1780 chi) ∨
      (Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom1448 chi))) ∨
      (((Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom1449 chi) ∨
      (Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom1455 chi)) ∨
      ((Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom1486 chi) ∨
      (Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom1781 chi))))) ∨
      (((((¬Fin15AnchoredAtom4322 chi ∧
      Fin15AnchoredAtom1448 chi ∧
      Fin15AnchoredAtom1449 chi ∧
      Fin15AnchoredAtom1455 chi ∧
      Fin15AnchoredAtom1486 chi ∧
      Fin15AnchoredAtom1781 chi) ∨
      (Fin15AnchoredAtom4323 chi ∧
      ¬Fin15AnchoredAtom1487 chi)) ∨
      ((Fin15AnchoredAtom4324 chi ∧
      ¬Fin15AnchoredAtom1454 chi) ∨
      (Fin15AnchoredAtom4324 chi ∧
      ¬Fin15AnchoredAtom1488 chi))) ∨
      (((Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom1453 chi) ∨
      (Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom1454 chi)) ∨
      ((Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom1455 chi) ∨
      (Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom1490 chi)))) ∨
      ((((Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom1785 chi) ∨
      (¬Fin15AnchoredAtom4326 chi ∧
      Fin15AnchoredAtom1453 chi ∧
      Fin15AnchoredAtom1454 chi ∧
      Fin15AnchoredAtom1455 chi ∧
      Fin15AnchoredAtom1490 chi ∧
      Fin15AnchoredAtom1785 chi)) ∨
      ((Fin15AnchoredAtom4328 chi ∧
      ¬Fin15AnchoredAtom1456 chi) ∨
      (Fin15AnchoredAtom4328 chi ∧
      ¬Fin15AnchoredAtom1458 chi))) ∨
      (((Fin15AnchoredAtom4328 chi ∧
      ¬Fin15AnchoredAtom1472 chi) ∨
      (Fin15AnchoredAtom4328 chi ∧
      ¬Fin15AnchoredAtom1787 chi)) ∨
      ((¬Fin15AnchoredAtom4328 chi ∧
      Fin15AnchoredAtom1456 chi ∧
      Fin15AnchoredAtom1458 chi ∧
      Fin15AnchoredAtom1462 chi ∧
      Fin15AnchoredAtom1472 chi ∧
      Fin15AnchoredAtom1787 chi) ∨
      (Fin15AnchoredAtom4329 chi ∧
      ¬Fin15AnchoredAtom1456 chi)))))) ∨
      ((((((Fin15AnchoredAtom4329 chi ∧
      ¬Fin15AnchoredAtom1459 chi) ∨
      (Fin15AnchoredAtom4329 chi ∧
      ¬Fin15AnchoredAtom1463 chi)) ∨
      ((Fin15AnchoredAtom4329 chi ∧
      ¬Fin15AnchoredAtom1473 chi) ∨
      (Fin15AnchoredAtom4329 chi ∧
      ¬Fin15AnchoredAtom1788 chi))) ∨
      (((¬Fin15AnchoredAtom4329 chi ∧
      Fin15AnchoredAtom1456 chi ∧
      Fin15AnchoredAtom1459 chi ∧
      Fin15AnchoredAtom1463 chi ∧
      Fin15AnchoredAtom1473 chi ∧
      Fin15AnchoredAtom1788 chi) ∨
      (Fin15AnchoredAtom4330 chi ∧
      ¬Fin15AnchoredAtom1456 chi)) ∨
      ((Fin15AnchoredAtom4330 chi ∧
      ¬Fin15AnchoredAtom1460 chi) ∨
      (Fin15AnchoredAtom4330 chi ∧
      ¬Fin15AnchoredAtom1474 chi)))) ∨
      ((((Fin15AnchoredAtom4330 chi ∧
      ¬Fin15AnchoredAtom1789 chi) ∨
      (Fin15AnchoredAtom4334 chi ∧
      ¬Fin15AnchoredAtom1458 chi)) ∨
      ((Fin15AnchoredAtom4334 chi ∧
      ¬Fin15AnchoredAtom1459 chi) ∨
      (Fin15AnchoredAtom4334 chi ∧
      ¬Fin15AnchoredAtom1468 chi))) ∨
      (((Fin15AnchoredAtom4334 chi ∧
      ¬Fin15AnchoredAtom1478 chi) ∨
      (Fin15AnchoredAtom4334 chi ∧
      ¬Fin15AnchoredAtom1793 chi)) ∨
      ((¬Fin15AnchoredAtom4334 chi ∧
      Fin15AnchoredAtom1458 chi ∧
      Fin15AnchoredAtom1459 chi ∧
      Fin15AnchoredAtom1468 chi ∧
      Fin15AnchoredAtom1478 chi ∧
      Fin15AnchoredAtom1793 chi) ∨
      (Fin15AnchoredAtom4335 chi ∧
      ¬Fin15AnchoredAtom1458 chi))))) ∨
      (((((Fin15AnchoredAtom4335 chi ∧
      ¬Fin15AnchoredAtom1460 chi) ∨
      (Fin15AnchoredAtom4335 chi ∧
      ¬Fin15AnchoredAtom1469 chi)) ∨
      ((Fin15AnchoredAtom4335 chi ∧
      ¬Fin15AnchoredAtom1479 chi) ∨
      (Fin15AnchoredAtom4335 chi ∧
      ¬Fin15AnchoredAtom1794 chi))) ∨
      (((¬Fin15AnchoredAtom4335 chi ∧
      Fin15AnchoredAtom1458 chi ∧
      Fin15AnchoredAtom1460 chi ∧
      Fin15AnchoredAtom1469 chi ∧
      Fin15AnchoredAtom1479 chi ∧
      Fin15AnchoredAtom1794 chi) ∨
      (Fin15AnchoredAtom4336 chi ∧
      ¬Fin15AnchoredAtom1459 chi)) ∨
      ((Fin15AnchoredAtom4336 chi ∧
      ¬Fin15AnchoredAtom1460 chi) ∨
      (Fin15AnchoredAtom4336 chi ∧
      ¬Fin15AnchoredAtom1470 chi)))) ∨
      ((((Fin15AnchoredAtom4336 chi ∧
      ¬Fin15AnchoredAtom1480 chi) ∨
      (Fin15AnchoredAtom4336 chi ∧
      ¬Fin15AnchoredAtom1795 chi)) ∨
      ((¬Fin15AnchoredAtom4336 chi ∧
      Fin15AnchoredAtom1459 chi ∧
      Fin15AnchoredAtom1460 chi ∧
      Fin15AnchoredAtom1470 chi ∧
      Fin15AnchoredAtom1480 chi ∧
      Fin15AnchoredAtom1795 chi) ∨
      (Fin15AnchoredAtom4340 chi ∧
      ¬Fin15AnchoredAtom1462 chi))) ∨
      (((Fin15AnchoredAtom4340 chi ∧
      ¬Fin15AnchoredAtom1463 chi) ∨
      (Fin15AnchoredAtom4340 chi ∧
      ¬Fin15AnchoredAtom1468 chi)) ∨
      ((Fin15AnchoredAtom4340 chi ∧
      ¬Fin15AnchoredAtom1484 chi) ∨
      (Fin15AnchoredAtom4340 chi ∧
      ¬Fin15AnchoredAtom1799 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom4340 chi ∧
      Fin15AnchoredAtom1462 chi ∧
      Fin15AnchoredAtom1463 chi ∧
      Fin15AnchoredAtom1468 chi ∧
      Fin15AnchoredAtom1484 chi ∧
      Fin15AnchoredAtom1799 chi) ∨
      ((Fin15AnchoredAtom4341 chi ∧
      ¬Fin15AnchoredAtom1462 chi) ∨
      (Fin15AnchoredAtom4341 chi ∧
      ¬Fin15AnchoredAtom1464 chi))) ∨
      (((Fin15AnchoredAtom4341 chi ∧
      ¬Fin15AnchoredAtom1469 chi) ∨
      (Fin15AnchoredAtom4341 chi ∧
      ¬Fin15AnchoredAtom1485 chi)) ∨
      ((Fin15AnchoredAtom4341 chi ∧
      ¬Fin15AnchoredAtom1800 chi) ∨
      (¬Fin15AnchoredAtom4341 chi ∧
      Fin15AnchoredAtom1462 chi ∧
      Fin15AnchoredAtom1464 chi ∧
      Fin15AnchoredAtom1469 chi ∧
      Fin15AnchoredAtom1485 chi ∧
      Fin15AnchoredAtom1800 chi)))) ∨
      ((((Fin15AnchoredAtom4342 chi ∧
      ¬Fin15AnchoredAtom1463 chi) ∨
      (Fin15AnchoredAtom4342 chi ∧
      ¬Fin15AnchoredAtom1464 chi)) ∨
      ((Fin15AnchoredAtom4342 chi ∧
      ¬Fin15AnchoredAtom1470 chi) ∨
      (Fin15AnchoredAtom4342 chi ∧
      ¬Fin15AnchoredAtom1486 chi))) ∨
      (((Fin15AnchoredAtom4342 chi ∧
      ¬Fin15AnchoredAtom1801 chi) ∨
      (¬Fin15AnchoredAtom4342 chi ∧
      Fin15AnchoredAtom1463 chi ∧
      Fin15AnchoredAtom1464 chi ∧
      Fin15AnchoredAtom1470 chi ∧
      Fin15AnchoredAtom1486 chi ∧
      Fin15AnchoredAtom1801 chi)) ∨
      ((Fin15AnchoredAtom4346 chi ∧
      ¬Fin15AnchoredAtom1468 chi) ∨
      (Fin15AnchoredAtom4346 chi ∧
      ¬Fin15AnchoredAtom1469 chi))))) ∨
      (((((Fin15AnchoredAtom4346 chi ∧
      ¬Fin15AnchoredAtom1490 chi) ∨
      (Fin15AnchoredAtom4346 chi ∧
      ¬Fin15AnchoredAtom1805 chi)) ∨
      ((¬Fin15AnchoredAtom4346 chi ∧
      Fin15AnchoredAtom1468 chi ∧
      Fin15AnchoredAtom1469 chi ∧
      Fin15AnchoredAtom1470 chi ∧
      Fin15AnchoredAtom1490 chi ∧
      Fin15AnchoredAtom1805 chi) ∨
      (Fin15AnchoredAtom4347 chi ∧
      ¬Fin15AnchoredAtom1472 chi))) ∨
      (((Fin15AnchoredAtom4347 chi ∧
      ¬Fin15AnchoredAtom1806 chi) ∨
      (¬Fin15AnchoredAtom4347 chi ∧
      Fin15AnchoredAtom1471 chi ∧
      Fin15AnchoredAtom1472 chi ∧
      Fin15AnchoredAtom1475 chi ∧
      Fin15AnchoredAtom1481 chi ∧
      Fin15AnchoredAtom1806 chi)) ∨
      ((Fin15AnchoredAtom4348 chi ∧
      ¬Fin15AnchoredAtom1471 chi) ∨
      (Fin15AnchoredAtom4348 chi ∧
      ¬Fin15AnchoredAtom1473 chi)))) ∨
      ((((Fin15AnchoredAtom4348 chi ∧
      ¬Fin15AnchoredAtom1476 chi) ∨
      (Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom1472 chi)) ∨
      ((Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom1473 chi) ∨
      (Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom1478 chi))) ∨
      (((Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom1484 chi) ∨
      (Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom1809 chi)) ∨
      ((¬Fin15AnchoredAtom4350 chi ∧
      Fin15AnchoredAtom1472 chi ∧
      Fin15AnchoredAtom1473 chi ∧
      Fin15AnchoredAtom1478 chi ∧
      Fin15AnchoredAtom1484 chi ∧
      Fin15AnchoredAtom1809 chi) ∨
      (Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom1472 chi)))))) ∨
      ((((((Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom1474 chi) ∨
      (Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom1479 chi)) ∨
      ((Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom1485 chi) ∨
      (Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom1810 chi))) ∨
      (((¬Fin15AnchoredAtom4351 chi ∧
      Fin15AnchoredAtom1472 chi ∧
      Fin15AnchoredAtom1474 chi ∧
      Fin15AnchoredAtom1479 chi ∧
      Fin15AnchoredAtom1485 chi ∧
      Fin15AnchoredAtom1810 chi) ∨
      (Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom1473 chi)) ∨
      ((Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom1474 chi) ∨
      (Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom1480 chi)))) ∨
      ((((Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom1486 chi) ∨
      (Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom1811 chi)) ∨
      ((¬Fin15AnchoredAtom4352 chi ∧
      Fin15AnchoredAtom1473 chi ∧
      Fin15AnchoredAtom1474 chi ∧
      Fin15AnchoredAtom1480 chi ∧
      Fin15AnchoredAtom1486 chi ∧
      Fin15AnchoredAtom1811 chi) ∨
      (Fin15AnchoredAtom4353 chi ∧
      ¬Fin15AnchoredAtom1478 chi))) ∨
      (((Fin15AnchoredAtom4354 chi ∧
      ¬Fin15AnchoredAtom1475 chi) ∨
      (Fin15AnchoredAtom4354 chi ∧
      ¬Fin15AnchoredAtom1479 chi)) ∨
      ((Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom1478 chi) ∨
      (Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom1479 chi))))) ∨
      (((((Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom1480 chi) ∨
      (Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom1490 chi)) ∨
      ((Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom1815 chi) ∨
      (¬Fin15AnchoredAtom4356 chi ∧
      Fin15AnchoredAtom1478 chi ∧
      Fin15AnchoredAtom1479 chi ∧
      Fin15AnchoredAtom1480 chi ∧
      Fin15AnchoredAtom1490 chi ∧
      Fin15AnchoredAtom1815 chi))) ∨
      (((Fin15AnchoredAtom4357 chi ∧
      ¬Fin15AnchoredAtom1484 chi) ∨
      (Fin15AnchoredAtom4357 chi ∧
      ¬Fin15AnchoredAtom1487 chi)) ∨
      ((¬Fin15AnchoredAtom4357 chi ∧
      Fin15AnchoredAtom1481 chi ∧
      Fin15AnchoredAtom1482 chi ∧
      Fin15AnchoredAtom1484 chi ∧
      Fin15AnchoredAtom1487 chi ∧
      Fin15AnchoredAtom1816 chi) ∨
      (Fin15AnchoredAtom4358 chi ∧
      ¬Fin15AnchoredAtom1485 chi)))) ∨
      ((((Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom1484 chi) ∨
      (Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom1485 chi)) ∨
      ((Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom1486 chi) ∨
      (Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom1490 chi))) ∨
      (((Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom1819 chi) ∨
      (¬Fin15AnchoredAtom4360 chi ∧
      Fin15AnchoredAtom1484 chi ∧
      Fin15AnchoredAtom1485 chi ∧
      Fin15AnchoredAtom1486 chi ∧
      Fin15AnchoredAtom1490 chi ∧
      Fin15AnchoredAtom1819 chi)) ∨
      ((Fin15AnchoredAtom4362 chi ∧
      ¬Fin15AnchoredAtom1491 chi) ∨
      (Fin15AnchoredAtom4362 chi ∧
      ¬Fin15AnchoredAtom1492 chi)))))))) ∨
      (((((((Fin15AnchoredAtom4362 chi ∧
      ¬Fin15AnchoredAtom1499 chi) ∨
      ((Fin15AnchoredAtom4362 chi ∧
      ¬Fin15AnchoredAtom1527 chi) ∨
      (Fin15AnchoredAtom4362 chi ∧
      ¬Fin15AnchoredAtom1611 chi))) ∨
      (((¬Fin15AnchoredAtom4362 chi ∧
      Fin15AnchoredAtom1491 chi ∧
      Fin15AnchoredAtom1492 chi ∧
      Fin15AnchoredAtom1499 chi ∧
      Fin15AnchoredAtom1527 chi ∧
      Fin15AnchoredAtom1611 chi) ∨
      (Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom1491 chi)) ∨
      ((Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom1493 chi) ∨
      (Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom1500 chi)))) ∨
      ((((Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom1528 chi) ∨
      (Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom1612 chi)) ∨
      ((¬Fin15AnchoredAtom4363 chi ∧
      Fin15AnchoredAtom1491 chi ∧
      Fin15AnchoredAtom1493 chi ∧
      Fin15AnchoredAtom1500 chi ∧
      Fin15AnchoredAtom1528 chi ∧
      Fin15AnchoredAtom1612 chi) ∨
      (Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom1491 chi))) ∨
      (((Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom1494 chi) ∨
      (Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom1501 chi)) ∨
      ((Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom1529 chi) ∨
      (Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom1613 chi))))) ∨
      (((((¬Fin15AnchoredAtom4364 chi ∧
      Fin15AnchoredAtom1491 chi ∧
      Fin15AnchoredAtom1494 chi ∧
      Fin15AnchoredAtom1501 chi ∧
      Fin15AnchoredAtom1529 chi ∧
      Fin15AnchoredAtom1613 chi) ∨
      (Fin15AnchoredAtom4365 chi ∧
      ¬Fin15AnchoredAtom1502 chi)) ∨
      ((Fin15AnchoredAtom4365 chi ∧
      ¬Fin15AnchoredAtom1614 chi) ∨
      (¬Fin15AnchoredAtom4365 chi ∧
      Fin15AnchoredAtom1491 chi ∧
      Fin15AnchoredAtom1495 chi ∧
      Fin15AnchoredAtom1502 chi ∧
      Fin15AnchoredAtom1530 chi ∧
      Fin15AnchoredAtom1614 chi))) ∨
      (((Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom1491 chi) ∨
      (Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom1496 chi)) ∨
      ((Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom1503 chi) ∨
      (Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom1531 chi)))) ∨
      ((((Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom1615 chi) ∨
      (¬Fin15AnchoredAtom4366 chi ∧
      Fin15AnchoredAtom1491 chi ∧
      Fin15AnchoredAtom1496 chi ∧
      Fin15AnchoredAtom1503 chi ∧
      Fin15AnchoredAtom1531 chi ∧
      Fin15AnchoredAtom1615 chi)) ∨
      ((Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom1491 chi) ∨
      (Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom1497 chi))) ∨
      (((Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom1504 chi) ∨
      (Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom1532 chi)) ∨
      ((Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom1616 chi) ∨
      (¬Fin15AnchoredAtom4367 chi ∧
      Fin15AnchoredAtom1491 chi ∧
      Fin15AnchoredAtom1497 chi ∧
      Fin15AnchoredAtom1504 chi ∧
      Fin15AnchoredAtom1532 chi ∧
      Fin15AnchoredAtom1616 chi)))))) ∨
      ((((((Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom1491 chi) ∨
      (Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom1498 chi)) ∨
      ((Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom1505 chi) ∨
      (Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom1533 chi))) ∨
      (((Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom1617 chi) ∨
      (¬Fin15AnchoredAtom4368 chi ∧
      Fin15AnchoredAtom1491 chi ∧
      Fin15AnchoredAtom1498 chi ∧
      Fin15AnchoredAtom1505 chi ∧
      Fin15AnchoredAtom1533 chi ∧
      Fin15AnchoredAtom1617 chi)) ∨
      ((Fin15AnchoredAtom4369 chi ∧
      ¬Fin15AnchoredAtom1492 chi) ∨
      (Fin15AnchoredAtom4369 chi ∧
      ¬Fin15AnchoredAtom1493 chi)))) ∨
      ((((Fin15AnchoredAtom4369 chi ∧
      ¬Fin15AnchoredAtom1506 chi) ∨
      (Fin15AnchoredAtom4369 chi ∧
      ¬Fin15AnchoredAtom1534 chi)) ∨
      ((Fin15AnchoredAtom4369 chi ∧
      ¬Fin15AnchoredAtom1618 chi) ∨
      (¬Fin15AnchoredAtom4369 chi ∧
      Fin15AnchoredAtom1492 chi ∧
      Fin15AnchoredAtom1493 chi ∧
      Fin15AnchoredAtom1506 chi ∧
      Fin15AnchoredAtom1534 chi ∧
      Fin15AnchoredAtom1618 chi))) ∨
      (((Fin15AnchoredAtom4370 chi ∧
      ¬Fin15AnchoredAtom1492 chi) ∨
      (Fin15AnchoredAtom4370 chi ∧
      ¬Fin15AnchoredAtom1494 chi)) ∨
      ((Fin15AnchoredAtom4370 chi ∧
      ¬Fin15AnchoredAtom1507 chi) ∨
      (Fin15AnchoredAtom4370 chi ∧
      ¬Fin15AnchoredAtom1535 chi))))) ∨
      (((((Fin15AnchoredAtom4370 chi ∧
      ¬Fin15AnchoredAtom1619 chi) ∨
      (¬Fin15AnchoredAtom4370 chi ∧
      Fin15AnchoredAtom1492 chi ∧
      Fin15AnchoredAtom1494 chi ∧
      Fin15AnchoredAtom1507 chi ∧
      Fin15AnchoredAtom1535 chi ∧
      Fin15AnchoredAtom1619 chi)) ∨
      ((Fin15AnchoredAtom4372 chi ∧
      ¬Fin15AnchoredAtom1492 chi) ∨
      (Fin15AnchoredAtom4372 chi ∧
      ¬Fin15AnchoredAtom1496 chi))) ∨
      (((Fin15AnchoredAtom4372 chi ∧
      ¬Fin15AnchoredAtom1509 chi) ∨
      (Fin15AnchoredAtom4372 chi ∧
      ¬Fin15AnchoredAtom1537 chi)) ∨
      ((Fin15AnchoredAtom4372 chi ∧
      ¬Fin15AnchoredAtom1621 chi) ∨
      (¬Fin15AnchoredAtom4372 chi ∧
      Fin15AnchoredAtom1492 chi ∧
      Fin15AnchoredAtom1496 chi ∧
      Fin15AnchoredAtom1509 chi ∧
      Fin15AnchoredAtom1537 chi ∧
      Fin15AnchoredAtom1621 chi)))) ∨
      ((((Fin15AnchoredAtom4373 chi ∧
      ¬Fin15AnchoredAtom1492 chi) ∨
      (Fin15AnchoredAtom4373 chi ∧
      ¬Fin15AnchoredAtom1497 chi)) ∨
      ((Fin15AnchoredAtom4373 chi ∧
      ¬Fin15AnchoredAtom1510 chi) ∨
      (Fin15AnchoredAtom4373 chi ∧
      ¬Fin15AnchoredAtom1538 chi))) ∨
      (((Fin15AnchoredAtom4373 chi ∧
      ¬Fin15AnchoredAtom1622 chi) ∨
      (¬Fin15AnchoredAtom4373 chi ∧
      Fin15AnchoredAtom1492 chi ∧
      Fin15AnchoredAtom1497 chi ∧
      Fin15AnchoredAtom1510 chi ∧
      Fin15AnchoredAtom1538 chi ∧
      Fin15AnchoredAtom1622 chi)) ∨
      ((Fin15AnchoredAtom4374 chi ∧
      ¬Fin15AnchoredAtom1492 chi) ∨
      (Fin15AnchoredAtom4374 chi ∧
      ¬Fin15AnchoredAtom1498 chi))))))) ∨
      ((((((Fin15AnchoredAtom4374 chi ∧
      ¬Fin15AnchoredAtom1511 chi) ∨
      ((Fin15AnchoredAtom4374 chi ∧
      ¬Fin15AnchoredAtom1539 chi) ∨
      (Fin15AnchoredAtom4374 chi ∧
      ¬Fin15AnchoredAtom1623 chi))) ∨
      (((¬Fin15AnchoredAtom4374 chi ∧
      Fin15AnchoredAtom1492 chi ∧
      Fin15AnchoredAtom1498 chi ∧
      Fin15AnchoredAtom1511 chi ∧
      Fin15AnchoredAtom1539 chi ∧
      Fin15AnchoredAtom1623 chi) ∨
      (Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom1493 chi)) ∨
      ((Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom1494 chi) ∨
      (Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom1512 chi)))) ∨
      ((((Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom1540 chi) ∨
      (Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom1624 chi)) ∨
      ((¬Fin15AnchoredAtom4375 chi ∧
      Fin15AnchoredAtom1493 chi ∧
      Fin15AnchoredAtom1494 chi ∧
      Fin15AnchoredAtom1512 chi ∧
      Fin15AnchoredAtom1540 chi ∧
      Fin15AnchoredAtom1624 chi) ∨
      (Fin15AnchoredAtom4376 chi ∧
      ¬Fin15AnchoredAtom1493 chi))) ∨
      (((¬Fin15AnchoredAtom4376 chi ∧
      Fin15AnchoredAtom1493 chi ∧
      Fin15AnchoredAtom1495 chi ∧
      Fin15AnchoredAtom1513 chi ∧
      Fin15AnchoredAtom1541 chi ∧
      Fin15AnchoredAtom1625 chi) ∨
      (Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom1493 chi)) ∨
      ((Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom1496 chi) ∨
      (Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom1514 chi))))) ∨
      (((((Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom1542 chi) ∨
      (Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom1626 chi)) ∨
      ((¬Fin15AnchoredAtom4377 chi ∧
      Fin15AnchoredAtom1493 chi ∧
      Fin15AnchoredAtom1496 chi ∧
      Fin15AnchoredAtom1514 chi ∧
      Fin15AnchoredAtom1542 chi ∧
      Fin15AnchoredAtom1626 chi) ∨
      (Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom1493 chi))) ∨
      (((Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom1497 chi) ∨
      (Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom1515 chi)) ∨
      ((Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom1543 chi) ∨
      (Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom1627 chi)))) ∨
      ((((¬Fin15AnchoredAtom4378 chi ∧
      Fin15AnchoredAtom1493 chi ∧
      Fin15AnchoredAtom1497 chi ∧
      Fin15AnchoredAtom1515 chi ∧
      Fin15AnchoredAtom1543 chi ∧
      Fin15AnchoredAtom1627 chi) ∨
      (Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom1493 chi)) ∨
      ((Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom1498 chi) ∨
      (Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom1516 chi))) ∨
      (((Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom1544 chi) ∨
      (Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom1628 chi)) ∨
      ((¬Fin15AnchoredAtom4379 chi ∧
      Fin15AnchoredAtom1493 chi ∧
      Fin15AnchoredAtom1498 chi ∧
      Fin15AnchoredAtom1516 chi ∧
      Fin15AnchoredAtom1544 chi ∧
      Fin15AnchoredAtom1628 chi) ∨
      (Fin15AnchoredAtom4380 chi ∧
      ¬Fin15AnchoredAtom1494 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom4380 chi ∧
      Fin15AnchoredAtom1494 chi ∧
      Fin15AnchoredAtom1495 chi ∧
      Fin15AnchoredAtom1517 chi ∧
      Fin15AnchoredAtom1545 chi ∧
      Fin15AnchoredAtom1629 chi) ∨
      (Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom1494 chi)) ∨
      ((Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom1496 chi) ∨
      (Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom1518 chi))) ∨
      (((Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom1546 chi) ∨
      (Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom1630 chi)) ∨
      ((¬Fin15AnchoredAtom4381 chi ∧
      Fin15AnchoredAtom1494 chi ∧
      Fin15AnchoredAtom1496 chi ∧
      Fin15AnchoredAtom1518 chi ∧
      Fin15AnchoredAtom1546 chi ∧
      Fin15AnchoredAtom1630 chi) ∨
      (Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom1494 chi)))) ∨
      ((((Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom1497 chi) ∨
      (Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom1519 chi)) ∨
      ((Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom1547 chi) ∨
      (Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom1631 chi))) ∨
      (((¬Fin15AnchoredAtom4382 chi ∧
      Fin15AnchoredAtom1494 chi ∧
      Fin15AnchoredAtom1497 chi ∧
      Fin15AnchoredAtom1519 chi ∧
      Fin15AnchoredAtom1547 chi ∧
      Fin15AnchoredAtom1631 chi) ∨
      (Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom1494 chi)) ∨
      ((Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom1498 chi) ∨
      (Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom1520 chi))))) ∨
      (((((Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom1548 chi) ∨
      (Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom1632 chi)) ∨
      ((¬Fin15AnchoredAtom4383 chi ∧
      Fin15AnchoredAtom1494 chi ∧
      Fin15AnchoredAtom1498 chi ∧
      Fin15AnchoredAtom1520 chi ∧
      Fin15AnchoredAtom1548 chi ∧
      Fin15AnchoredAtom1632 chi) ∨
      (Fin15AnchoredAtom4384 chi ∧
      ¬Fin15AnchoredAtom1496 chi))) ∨
      (((Fin15AnchoredAtom4384 chi ∧
      ¬Fin15AnchoredAtom1633 chi) ∨
      (¬Fin15AnchoredAtom4384 chi ∧
      Fin15AnchoredAtom1495 chi ∧
      Fin15AnchoredAtom1496 chi ∧
      Fin15AnchoredAtom1521 chi ∧
      Fin15AnchoredAtom1549 chi ∧
      Fin15AnchoredAtom1633 chi)) ∨
      ((Fin15AnchoredAtom4385 chi ∧
      ¬Fin15AnchoredAtom1497 chi) ∨
      (Fin15AnchoredAtom4386 chi ∧
      ¬Fin15AnchoredAtom1498 chi)))) ∨
      ((((Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom1496 chi) ∨
      (Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom1497 chi)) ∨
      ((Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom1524 chi) ∨
      (Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom1552 chi))) ∨
      (((Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom1636 chi) ∨
      (¬Fin15AnchoredAtom4387 chi ∧
      Fin15AnchoredAtom1496 chi ∧
      Fin15AnchoredAtom1497 chi ∧
      Fin15AnchoredAtom1524 chi ∧
      Fin15AnchoredAtom1552 chi ∧
      Fin15AnchoredAtom1636 chi)) ∨
      ((Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom1496 chi) ∨
      (Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom1498 chi)))))))))) := by
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
                exact fin15Anchored_clause26250 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26251 chi hbad
                ·
                  exact fin15Anchored_clause26252 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26253 chi hbad
                ·
                  exact fin15Anchored_clause26254 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26255 chi hbad
                ·
                  exact fin15Anchored_clause26256 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26257 chi hbad
                ·
                  exact fin15Anchored_clause26258 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26259 chi hbad
                ·
                  exact fin15Anchored_clause26260 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26261 chi hbad
                ·
                  exact fin15Anchored_clause26262 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26263 chi hbad
                ·
                  exact fin15Anchored_clause26264 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26265 chi hbad
                ·
                  exact fin15Anchored_clause26266 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26267 chi hbad
                ·
                  exact fin15Anchored_clause26268 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26269 chi hbad
                ·
                  exact fin15Anchored_clause26270 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26271 chi hbad
                ·
                  exact fin15Anchored_clause26272 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26273 chi hbad
                ·
                  exact fin15Anchored_clause26274 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26275 chi hbad
                ·
                  exact fin15Anchored_clause26276 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26277 chi hbad
                ·
                  exact fin15Anchored_clause26278 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26279 chi hbad
                ·
                  exact fin15Anchored_clause26280 chi hbad
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
                  exact fin15Anchored_clause26281 chi hbad
                ·
                  exact fin15Anchored_clause26282 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26283 chi hbad
                ·
                  exact fin15Anchored_clause26284 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26285 chi hbad
                ·
                  exact fin15Anchored_clause26286 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26287 chi hbad
                ·
                  exact fin15Anchored_clause26288 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26289 chi hbad
                ·
                  exact fin15Anchored_clause26290 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26291 chi hbad
                ·
                  exact fin15Anchored_clause26292 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26293 chi hbad
                ·
                  exact fin15Anchored_clause26294 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26295 chi hbad
                ·
                  exact fin15Anchored_clause26296 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26297 chi hbad
                ·
                  exact fin15Anchored_clause26298 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26299 chi hbad
                ·
                  exact fin15Anchored_clause26300 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26301 chi hbad
                ·
                  exact fin15Anchored_clause26302 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26303 chi hbad
                ·
                  exact fin15Anchored_clause26304 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26305 chi hbad
                ·
                  exact fin15Anchored_clause26306 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26307 chi hbad
                ·
                  exact fin15Anchored_clause26308 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26309 chi hbad
                ·
                  exact fin15Anchored_clause26310 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26311 chi hbad
                ·
                  exact fin15Anchored_clause26312 chi hbad
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
                exact fin15Anchored_clause26313 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26314 chi hbad
                ·
                  exact fin15Anchored_clause26315 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26316 chi hbad
                ·
                  exact fin15Anchored_clause26317 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26318 chi hbad
                ·
                  exact fin15Anchored_clause26319 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26320 chi hbad
                ·
                  exact fin15Anchored_clause26321 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26322 chi hbad
                ·
                  exact fin15Anchored_clause26323 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26324 chi hbad
                ·
                  exact fin15Anchored_clause26325 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26326 chi hbad
                ·
                  exact fin15Anchored_clause26327 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26328 chi hbad
                ·
                  exact fin15Anchored_clause26329 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26330 chi hbad
                ·
                  exact fin15Anchored_clause26331 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26332 chi hbad
                ·
                  exact fin15Anchored_clause26333 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26334 chi hbad
                ·
                  exact fin15Anchored_clause26335 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26336 chi hbad
                ·
                  exact fin15Anchored_clause26337 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26338 chi hbad
                ·
                  exact fin15Anchored_clause26339 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26340 chi hbad
                ·
                  exact fin15Anchored_clause26341 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26342 chi hbad
                ·
                  exact fin15Anchored_clause26343 chi hbad
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
                  exact fin15Anchored_clause26344 chi hbad
                ·
                  exact fin15Anchored_clause26345 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26346 chi hbad
                ·
                  exact fin15Anchored_clause26347 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26348 chi hbad
                ·
                  exact fin15Anchored_clause26349 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26350 chi hbad
                ·
                  exact fin15Anchored_clause26351 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26352 chi hbad
                ·
                  exact fin15Anchored_clause26353 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26354 chi hbad
                ·
                  exact fin15Anchored_clause26355 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26356 chi hbad
                ·
                  exact fin15Anchored_clause26357 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26358 chi hbad
                ·
                  exact fin15Anchored_clause26359 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26360 chi hbad
                ·
                  exact fin15Anchored_clause26361 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26362 chi hbad
                ·
                  exact fin15Anchored_clause26363 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26364 chi hbad
                ·
                  exact fin15Anchored_clause26365 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26366 chi hbad
                ·
                  exact fin15Anchored_clause26367 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26368 chi hbad
                ·
                  exact fin15Anchored_clause26369 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26370 chi hbad
                ·
                  exact fin15Anchored_clause26371 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26372 chi hbad
                ·
                  exact fin15Anchored_clause26373 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26374 chi hbad
                ·
                  exact fin15Anchored_clause26375 chi hbad
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
                exact fin15Anchored_clause26376 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26377 chi hbad
                ·
                  exact fin15Anchored_clause26378 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26379 chi hbad
                ·
                  exact fin15Anchored_clause26380 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26381 chi hbad
                ·
                  exact fin15Anchored_clause26382 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26383 chi hbad
                ·
                  exact fin15Anchored_clause26384 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26385 chi hbad
                ·
                  exact fin15Anchored_clause26386 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26387 chi hbad
                ·
                  exact fin15Anchored_clause26388 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26389 chi hbad
                ·
                  exact fin15Anchored_clause26390 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26391 chi hbad
                ·
                  exact fin15Anchored_clause26392 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26393 chi hbad
                ·
                  exact fin15Anchored_clause26394 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26395 chi hbad
                ·
                  exact fin15Anchored_clause26396 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26397 chi hbad
                ·
                  exact fin15Anchored_clause26398 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26399 chi hbad
                ·
                  exact fin15Anchored_clause26400 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26401 chi hbad
                ·
                  exact fin15Anchored_clause26402 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26403 chi hbad
                ·
                  exact fin15Anchored_clause26404 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26405 chi hbad
                ·
                  exact fin15Anchored_clause26406 chi hbad
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
                  exact fin15Anchored_clause26407 chi hbad
                ·
                  exact fin15Anchored_clause26408 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26409 chi hbad
                ·
                  exact fin15Anchored_clause26410 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26411 chi hbad
                ·
                  exact fin15Anchored_clause26412 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26413 chi hbad
                ·
                  exact fin15Anchored_clause26414 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26415 chi hbad
                ·
                  exact fin15Anchored_clause26416 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26417 chi hbad
                ·
                  exact fin15Anchored_clause26418 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26419 chi hbad
                ·
                  exact fin15Anchored_clause26420 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26421 chi hbad
                ·
                  exact fin15Anchored_clause26422 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26423 chi hbad
                ·
                  exact fin15Anchored_clause26424 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26425 chi hbad
                ·
                  exact fin15Anchored_clause26426 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26427 chi hbad
                ·
                  exact fin15Anchored_clause26428 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26429 chi hbad
                ·
                  exact fin15Anchored_clause26430 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26431 chi hbad
                ·
                  exact fin15Anchored_clause26432 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26433 chi hbad
                ·
                  exact fin15Anchored_clause26434 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26435 chi hbad
                ·
                  exact fin15Anchored_clause26436 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26437 chi hbad
                ·
                  exact fin15Anchored_clause26438 chi hbad
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
                exact fin15Anchored_clause26439 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26440 chi hbad
                ·
                  exact fin15Anchored_clause26441 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26442 chi hbad
                ·
                  exact fin15Anchored_clause26443 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26444 chi hbad
                ·
                  exact fin15Anchored_clause26445 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26446 chi hbad
                ·
                  exact fin15Anchored_clause26447 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26448 chi hbad
                ·
                  exact fin15Anchored_clause26449 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26450 chi hbad
                ·
                  exact fin15Anchored_clause26451 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26452 chi hbad
                ·
                  exact fin15Anchored_clause26453 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26454 chi hbad
                ·
                  exact fin15Anchored_clause26455 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26456 chi hbad
                ·
                  exact fin15Anchored_clause26457 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26458 chi hbad
                ·
                  exact fin15Anchored_clause26459 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26460 chi hbad
                ·
                  exact fin15Anchored_clause26461 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26462 chi hbad
                ·
                  exact fin15Anchored_clause26463 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26464 chi hbad
                ·
                  exact fin15Anchored_clause26465 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26466 chi hbad
                ·
                  exact fin15Anchored_clause26467 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26468 chi hbad
                ·
                  exact fin15Anchored_clause26469 chi hbad
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
                  exact fin15Anchored_clause26470 chi hbad
                ·
                  exact fin15Anchored_clause26471 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26472 chi hbad
                ·
                  exact fin15Anchored_clause26473 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26474 chi hbad
                ·
                  exact fin15Anchored_clause26475 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26476 chi hbad
                ·
                  exact fin15Anchored_clause26477 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26478 chi hbad
                ·
                  exact fin15Anchored_clause26479 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26480 chi hbad
                ·
                  exact fin15Anchored_clause26481 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26482 chi hbad
                ·
                  exact fin15Anchored_clause26483 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26484 chi hbad
                ·
                  exact fin15Anchored_clause26485 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26486 chi hbad
                ·
                  exact fin15Anchored_clause26487 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26488 chi hbad
                ·
                  exact fin15Anchored_clause26489 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26490 chi hbad
                ·
                  exact fin15Anchored_clause26491 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26492 chi hbad
                ·
                  exact fin15Anchored_clause26493 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26494 chi hbad
                ·
                  exact fin15Anchored_clause26495 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26496 chi hbad
                ·
                  exact fin15Anchored_clause26497 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26498 chi hbad
                ·
                  exact fin15Anchored_clause26499 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26500 chi hbad
                ·
                  exact fin15Anchored_clause26501 chi hbad

end ErdosSzekeres

end
