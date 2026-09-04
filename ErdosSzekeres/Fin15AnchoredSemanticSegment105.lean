module

public import ErdosSzekeres.Fin15AnchoredClauseChunk207
public import ErdosSzekeres.Fin15AnchoredClauseChunk208
public import ErdosSzekeres.Fin15AnchoredClauseChunk209

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 105. -/

theorem fin15Anchored_rejectSemanticSegment105
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom1525 chi) ∨
      ((Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom1553 chi) ∨
      (Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom1637 chi))) ∨
      (((¬Fin15AnchoredAtom4388 chi ∧
      Fin15AnchoredAtom1496 chi ∧
      Fin15AnchoredAtom1498 chi ∧
      Fin15AnchoredAtom1525 chi ∧
      Fin15AnchoredAtom1553 chi ∧
      Fin15AnchoredAtom1637 chi) ∨
      (Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom1497 chi)) ∨
      ((Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom1498 chi) ∨
      (Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom1526 chi)))) ∨
      ((((Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom1554 chi) ∨
      (Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom1638 chi)) ∨
      ((¬Fin15AnchoredAtom4389 chi ∧
      Fin15AnchoredAtom1497 chi ∧
      Fin15AnchoredAtom1498 chi ∧
      Fin15AnchoredAtom1526 chi ∧
      Fin15AnchoredAtom1554 chi ∧
      Fin15AnchoredAtom1638 chi) ∨
      (Fin15AnchoredAtom4390 chi ∧
      ¬Fin15AnchoredAtom1499 chi))) ∨
      (((Fin15AnchoredAtom4390 chi ∧
      ¬Fin15AnchoredAtom1500 chi) ∨
      (Fin15AnchoredAtom4390 chi ∧
      ¬Fin15AnchoredAtom1506 chi)) ∨
      ((Fin15AnchoredAtom4390 chi ∧
      ¬Fin15AnchoredAtom1555 chi) ∨
      (Fin15AnchoredAtom4390 chi ∧
      ¬Fin15AnchoredAtom1639 chi))))) ∨
      (((((¬Fin15AnchoredAtom4390 chi ∧
      Fin15AnchoredAtom1499 chi ∧
      Fin15AnchoredAtom1500 chi ∧
      Fin15AnchoredAtom1506 chi ∧
      Fin15AnchoredAtom1555 chi ∧
      Fin15AnchoredAtom1639 chi) ∨
      (Fin15AnchoredAtom4391 chi ∧
      ¬Fin15AnchoredAtom1499 chi)) ∨
      ((Fin15AnchoredAtom4391 chi ∧
      ¬Fin15AnchoredAtom1501 chi) ∨
      (Fin15AnchoredAtom4391 chi ∧
      ¬Fin15AnchoredAtom1507 chi))) ∨
      (((Fin15AnchoredAtom4391 chi ∧
      ¬Fin15AnchoredAtom1556 chi) ∨
      (Fin15AnchoredAtom4391 chi ∧
      ¬Fin15AnchoredAtom1640 chi)) ∨
      ((¬Fin15AnchoredAtom4391 chi ∧
      Fin15AnchoredAtom1499 chi ∧
      Fin15AnchoredAtom1501 chi ∧
      Fin15AnchoredAtom1507 chi ∧
      Fin15AnchoredAtom1556 chi ∧
      Fin15AnchoredAtom1640 chi) ∨
      (Fin15AnchoredAtom4393 chi ∧
      ¬Fin15AnchoredAtom1499 chi)))) ∨
      ((((Fin15AnchoredAtom4393 chi ∧
      ¬Fin15AnchoredAtom1503 chi) ∨
      (Fin15AnchoredAtom4393 chi ∧
      ¬Fin15AnchoredAtom1509 chi)) ∨
      ((Fin15AnchoredAtom4393 chi ∧
      ¬Fin15AnchoredAtom1558 chi) ∨
      (Fin15AnchoredAtom4393 chi ∧
      ¬Fin15AnchoredAtom1642 chi))) ∨
      (((¬Fin15AnchoredAtom4393 chi ∧
      Fin15AnchoredAtom1499 chi ∧
      Fin15AnchoredAtom1503 chi ∧
      Fin15AnchoredAtom1509 chi ∧
      Fin15AnchoredAtom1558 chi ∧
      Fin15AnchoredAtom1642 chi) ∨
      (Fin15AnchoredAtom4394 chi ∧
      ¬Fin15AnchoredAtom1499 chi)) ∨
      ((Fin15AnchoredAtom4394 chi ∧
      ¬Fin15AnchoredAtom1504 chi) ∨
      (Fin15AnchoredAtom4394 chi ∧
      ¬Fin15AnchoredAtom1510 chi)))))) ∨
      ((((((Fin15AnchoredAtom4394 chi ∧
      ¬Fin15AnchoredAtom1559 chi) ∨
      (Fin15AnchoredAtom4394 chi ∧
      ¬Fin15AnchoredAtom1643 chi)) ∨
      ((¬Fin15AnchoredAtom4394 chi ∧
      Fin15AnchoredAtom1499 chi ∧
      Fin15AnchoredAtom1504 chi ∧
      Fin15AnchoredAtom1510 chi ∧
      Fin15AnchoredAtom1559 chi ∧
      Fin15AnchoredAtom1643 chi) ∨
      (Fin15AnchoredAtom4395 chi ∧
      ¬Fin15AnchoredAtom1499 chi))) ∨
      (((Fin15AnchoredAtom4395 chi ∧
      ¬Fin15AnchoredAtom1505 chi) ∨
      (Fin15AnchoredAtom4395 chi ∧
      ¬Fin15AnchoredAtom1511 chi)) ∨
      ((Fin15AnchoredAtom4395 chi ∧
      ¬Fin15AnchoredAtom1560 chi) ∨
      (Fin15AnchoredAtom4395 chi ∧
      ¬Fin15AnchoredAtom1644 chi)))) ∨
      ((((¬Fin15AnchoredAtom4395 chi ∧
      Fin15AnchoredAtom1499 chi ∧
      Fin15AnchoredAtom1505 chi ∧
      Fin15AnchoredAtom1511 chi ∧
      Fin15AnchoredAtom1560 chi ∧
      Fin15AnchoredAtom1644 chi) ∨
      (Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom1500 chi)) ∨
      ((Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom1501 chi) ∨
      (Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom1512 chi))) ∨
      (((Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom1561 chi) ∨
      (Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom1645 chi)) ∨
      ((¬Fin15AnchoredAtom4396 chi ∧
      Fin15AnchoredAtom1500 chi ∧
      Fin15AnchoredAtom1501 chi ∧
      Fin15AnchoredAtom1512 chi ∧
      Fin15AnchoredAtom1561 chi ∧
      Fin15AnchoredAtom1645 chi) ∨
      (Fin15AnchoredAtom4397 chi ∧
      ¬Fin15AnchoredAtom1500 chi))))) ∨
      (((((Fin15AnchoredAtom4397 chi ∧
      ¬Fin15AnchoredAtom1502 chi) ∨
      (Fin15AnchoredAtom4397 chi ∧
      ¬Fin15AnchoredAtom1646 chi)) ∨
      ((¬Fin15AnchoredAtom4397 chi ∧
      Fin15AnchoredAtom1500 chi ∧
      Fin15AnchoredAtom1502 chi ∧
      Fin15AnchoredAtom1513 chi ∧
      Fin15AnchoredAtom1562 chi ∧
      Fin15AnchoredAtom1646 chi) ∨
      (Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom1500 chi))) ∨
      (((Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom1503 chi) ∨
      (Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom1514 chi)) ∨
      ((Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom1563 chi) ∨
      (Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom1647 chi)))) ∨
      ((((¬Fin15AnchoredAtom4398 chi ∧
      Fin15AnchoredAtom1500 chi ∧
      Fin15AnchoredAtom1503 chi ∧
      Fin15AnchoredAtom1514 chi ∧
      Fin15AnchoredAtom1563 chi ∧
      Fin15AnchoredAtom1647 chi) ∨
      (Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom1500 chi)) ∨
      ((Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom1504 chi) ∨
      (Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom1515 chi))) ∨
      (((Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom1564 chi) ∨
      (Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom1648 chi)) ∨
      ((¬Fin15AnchoredAtom4399 chi ∧
      Fin15AnchoredAtom1500 chi ∧
      Fin15AnchoredAtom1504 chi ∧
      Fin15AnchoredAtom1515 chi ∧
      Fin15AnchoredAtom1564 chi ∧
      Fin15AnchoredAtom1648 chi) ∨
      (Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom1500 chi))))))) ∨
      ((((((Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom1505 chi) ∨
      ((Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom1516 chi) ∨
      (Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom1565 chi))) ∨
      (((Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom1649 chi) ∨
      (¬Fin15AnchoredAtom4400 chi ∧
      Fin15AnchoredAtom1500 chi ∧
      Fin15AnchoredAtom1505 chi ∧
      Fin15AnchoredAtom1516 chi ∧
      Fin15AnchoredAtom1565 chi ∧
      Fin15AnchoredAtom1649 chi)) ∨
      ((Fin15AnchoredAtom4401 chi ∧
      ¬Fin15AnchoredAtom1501 chi) ∨
      (Fin15AnchoredAtom4401 chi ∧
      ¬Fin15AnchoredAtom1502 chi)))) ∨
      ((((Fin15AnchoredAtom4401 chi ∧
      ¬Fin15AnchoredAtom1566 chi) ∨
      (Fin15AnchoredAtom4401 chi ∧
      ¬Fin15AnchoredAtom1650 chi)) ∨
      ((¬Fin15AnchoredAtom4401 chi ∧
      Fin15AnchoredAtom1501 chi ∧
      Fin15AnchoredAtom1502 chi ∧
      Fin15AnchoredAtom1517 chi ∧
      Fin15AnchoredAtom1566 chi ∧
      Fin15AnchoredAtom1650 chi) ∨
      (Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom1501 chi))) ∨
      (((Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom1503 chi) ∨
      (Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom1518 chi)) ∨
      ((Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom1567 chi) ∨
      (Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom1651 chi))))) ∨
      (((((¬Fin15AnchoredAtom4402 chi ∧
      Fin15AnchoredAtom1501 chi ∧
      Fin15AnchoredAtom1503 chi ∧
      Fin15AnchoredAtom1518 chi ∧
      Fin15AnchoredAtom1567 chi ∧
      Fin15AnchoredAtom1651 chi) ∨
      (Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom1501 chi)) ∨
      ((Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom1504 chi) ∨
      (Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom1519 chi))) ∨
      (((Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom1568 chi) ∨
      (Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom1652 chi)) ∨
      ((¬Fin15AnchoredAtom4403 chi ∧
      Fin15AnchoredAtom1501 chi ∧
      Fin15AnchoredAtom1504 chi ∧
      Fin15AnchoredAtom1519 chi ∧
      Fin15AnchoredAtom1568 chi ∧
      Fin15AnchoredAtom1652 chi) ∨
      (Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom1501 chi)))) ∨
      ((((Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom1505 chi) ∨
      (Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom1520 chi)) ∨
      ((Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom1569 chi) ∨
      (Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom1653 chi))) ∨
      (((¬Fin15AnchoredAtom4404 chi ∧
      Fin15AnchoredAtom1501 chi ∧
      Fin15AnchoredAtom1505 chi ∧
      Fin15AnchoredAtom1520 chi ∧
      Fin15AnchoredAtom1569 chi ∧
      Fin15AnchoredAtom1653 chi) ∨
      (Fin15AnchoredAtom4405 chi ∧
      ¬Fin15AnchoredAtom1503 chi)) ∨
      ((Fin15AnchoredAtom4405 chi ∧
      ¬Fin15AnchoredAtom1654 chi) ∨
      (¬Fin15AnchoredAtom4405 chi ∧
      Fin15AnchoredAtom1502 chi ∧
      Fin15AnchoredAtom1503 chi ∧
      Fin15AnchoredAtom1521 chi ∧
      Fin15AnchoredAtom1570 chi ∧
      Fin15AnchoredAtom1654 chi)))))) ∨
      ((((((Fin15AnchoredAtom4406 chi ∧
      ¬Fin15AnchoredAtom1502 chi) ∨
      (Fin15AnchoredAtom4406 chi ∧
      ¬Fin15AnchoredAtom1504 chi)) ∨
      ((Fin15AnchoredAtom4407 chi ∧
      ¬Fin15AnchoredAtom1656 chi) ∨
      (Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom1503 chi))) ∨
      (((Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom1504 chi) ∨
      (Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom1524 chi)) ∨
      ((Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom1573 chi) ∨
      (Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom1657 chi)))) ∨
      ((((¬Fin15AnchoredAtom4408 chi ∧
      Fin15AnchoredAtom1503 chi ∧
      Fin15AnchoredAtom1504 chi ∧
      Fin15AnchoredAtom1524 chi ∧
      Fin15AnchoredAtom1573 chi ∧
      Fin15AnchoredAtom1657 chi) ∨
      (Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom1503 chi)) ∨
      ((Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom1505 chi) ∨
      (Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom1525 chi))) ∨
      (((Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom1574 chi) ∨
      (Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom1658 chi)) ∨
      ((¬Fin15AnchoredAtom4409 chi ∧
      Fin15AnchoredAtom1503 chi ∧
      Fin15AnchoredAtom1505 chi ∧
      Fin15AnchoredAtom1525 chi ∧
      Fin15AnchoredAtom1574 chi ∧
      Fin15AnchoredAtom1658 chi) ∨
      (Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom1504 chi))))) ∨
      (((((Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom1505 chi) ∨
      (Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom1526 chi)) ∨
      ((Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom1575 chi) ∨
      (Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom1659 chi))) ∨
      (((¬Fin15AnchoredAtom4410 chi ∧
      Fin15AnchoredAtom1504 chi ∧
      Fin15AnchoredAtom1505 chi ∧
      Fin15AnchoredAtom1526 chi ∧
      Fin15AnchoredAtom1575 chi ∧
      Fin15AnchoredAtom1659 chi) ∨
      (Fin15AnchoredAtom4411 chi ∧
      ¬Fin15AnchoredAtom1506 chi)) ∨
      ((Fin15AnchoredAtom4411 chi ∧
      ¬Fin15AnchoredAtom1507 chi) ∨
      (Fin15AnchoredAtom4411 chi ∧
      ¬Fin15AnchoredAtom1512 chi)))) ∨
      ((((Fin15AnchoredAtom4411 chi ∧
      ¬Fin15AnchoredAtom1576 chi) ∨
      (Fin15AnchoredAtom4411 chi ∧
      ¬Fin15AnchoredAtom1660 chi)) ∨
      ((¬Fin15AnchoredAtom4411 chi ∧
      Fin15AnchoredAtom1506 chi ∧
      Fin15AnchoredAtom1507 chi ∧
      Fin15AnchoredAtom1512 chi ∧
      Fin15AnchoredAtom1576 chi ∧
      Fin15AnchoredAtom1660 chi) ∨
      (Fin15AnchoredAtom4413 chi ∧
      ¬Fin15AnchoredAtom1506 chi))) ∨
      (((Fin15AnchoredAtom4413 chi ∧
      ¬Fin15AnchoredAtom1509 chi) ∨
      (Fin15AnchoredAtom4413 chi ∧
      ¬Fin15AnchoredAtom1514 chi)) ∨
      ((Fin15AnchoredAtom4413 chi ∧
      ¬Fin15AnchoredAtom1578 chi) ∨
      (Fin15AnchoredAtom4413 chi ∧
      ¬Fin15AnchoredAtom1662 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom4413 chi ∧
      Fin15AnchoredAtom1506 chi ∧
      Fin15AnchoredAtom1509 chi ∧
      Fin15AnchoredAtom1514 chi ∧
      Fin15AnchoredAtom1578 chi ∧
      Fin15AnchoredAtom1662 chi) ∨
      ((Fin15AnchoredAtom4414 chi ∧
      ¬Fin15AnchoredAtom1506 chi) ∨
      (Fin15AnchoredAtom4414 chi ∧
      ¬Fin15AnchoredAtom1510 chi))) ∨
      (((Fin15AnchoredAtom4414 chi ∧
      ¬Fin15AnchoredAtom1515 chi) ∨
      (Fin15AnchoredAtom4414 chi ∧
      ¬Fin15AnchoredAtom1579 chi)) ∨
      ((Fin15AnchoredAtom4414 chi ∧
      ¬Fin15AnchoredAtom1663 chi) ∨
      (¬Fin15AnchoredAtom4414 chi ∧
      Fin15AnchoredAtom1506 chi ∧
      Fin15AnchoredAtom1510 chi ∧
      Fin15AnchoredAtom1515 chi ∧
      Fin15AnchoredAtom1579 chi ∧
      Fin15AnchoredAtom1663 chi)))) ∨
      ((((Fin15AnchoredAtom4415 chi ∧
      ¬Fin15AnchoredAtom1506 chi) ∨
      (Fin15AnchoredAtom4415 chi ∧
      ¬Fin15AnchoredAtom1511 chi)) ∨
      ((Fin15AnchoredAtom4415 chi ∧
      ¬Fin15AnchoredAtom1516 chi) ∨
      (Fin15AnchoredAtom4415 chi ∧
      ¬Fin15AnchoredAtom1664 chi))) ∨
      (((¬Fin15AnchoredAtom4415 chi ∧
      Fin15AnchoredAtom1506 chi ∧
      Fin15AnchoredAtom1511 chi ∧
      Fin15AnchoredAtom1516 chi ∧
      Fin15AnchoredAtom1580 chi ∧
      Fin15AnchoredAtom1664 chi) ∨
      (Fin15AnchoredAtom4417 chi ∧
      ¬Fin15AnchoredAtom1507 chi)) ∨
      ((Fin15AnchoredAtom4417 chi ∧
      ¬Fin15AnchoredAtom1509 chi) ∨
      (Fin15AnchoredAtom4417 chi ∧
      ¬Fin15AnchoredAtom1518 chi))))) ∨
      (((((Fin15AnchoredAtom4417 chi ∧
      ¬Fin15AnchoredAtom1582 chi) ∨
      (Fin15AnchoredAtom4417 chi ∧
      ¬Fin15AnchoredAtom1666 chi)) ∨
      ((¬Fin15AnchoredAtom4417 chi ∧
      Fin15AnchoredAtom1507 chi ∧
      Fin15AnchoredAtom1509 chi ∧
      Fin15AnchoredAtom1518 chi ∧
      Fin15AnchoredAtom1582 chi ∧
      Fin15AnchoredAtom1666 chi) ∨
      (Fin15AnchoredAtom4418 chi ∧
      ¬Fin15AnchoredAtom1507 chi))) ∨
      (((Fin15AnchoredAtom4418 chi ∧
      ¬Fin15AnchoredAtom1510 chi) ∨
      (Fin15AnchoredAtom4418 chi ∧
      ¬Fin15AnchoredAtom1519 chi)) ∨
      ((Fin15AnchoredAtom4418 chi ∧
      ¬Fin15AnchoredAtom1583 chi) ∨
      (Fin15AnchoredAtom4418 chi ∧
      ¬Fin15AnchoredAtom1667 chi)))) ∨
      ((((¬Fin15AnchoredAtom4418 chi ∧
      Fin15AnchoredAtom1507 chi ∧
      Fin15AnchoredAtom1510 chi ∧
      Fin15AnchoredAtom1519 chi ∧
      Fin15AnchoredAtom1583 chi ∧
      Fin15AnchoredAtom1667 chi) ∨
      (Fin15AnchoredAtom4419 chi ∧
      ¬Fin15AnchoredAtom1507 chi)) ∨
      ((Fin15AnchoredAtom4419 chi ∧
      ¬Fin15AnchoredAtom1511 chi) ∨
      (Fin15AnchoredAtom4419 chi ∧
      ¬Fin15AnchoredAtom1520 chi))) ∨
      (((Fin15AnchoredAtom4419 chi ∧
      ¬Fin15AnchoredAtom1584 chi) ∨
      (Fin15AnchoredAtom4419 chi ∧
      ¬Fin15AnchoredAtom1668 chi)) ∨
      ((¬Fin15AnchoredAtom4419 chi ∧
      Fin15AnchoredAtom1507 chi ∧
      Fin15AnchoredAtom1511 chi ∧
      Fin15AnchoredAtom1520 chi ∧
      Fin15AnchoredAtom1584 chi ∧
      Fin15AnchoredAtom1668 chi) ∨
      (Fin15AnchoredAtom4423 chi ∧
      ¬Fin15AnchoredAtom1509 chi)))))) ∨
      ((((((Fin15AnchoredAtom4423 chi ∧
      ¬Fin15AnchoredAtom1510 chi) ∨
      (Fin15AnchoredAtom4423 chi ∧
      ¬Fin15AnchoredAtom1524 chi)) ∨
      ((Fin15AnchoredAtom4423 chi ∧
      ¬Fin15AnchoredAtom1588 chi) ∨
      (Fin15AnchoredAtom4423 chi ∧
      ¬Fin15AnchoredAtom1672 chi))) ∨
      (((¬Fin15AnchoredAtom4423 chi ∧
      Fin15AnchoredAtom1509 chi ∧
      Fin15AnchoredAtom1510 chi ∧
      Fin15AnchoredAtom1524 chi ∧
      Fin15AnchoredAtom1588 chi ∧
      Fin15AnchoredAtom1672 chi) ∨
      (Fin15AnchoredAtom4424 chi ∧
      ¬Fin15AnchoredAtom1509 chi)) ∨
      ((Fin15AnchoredAtom4424 chi ∧
      ¬Fin15AnchoredAtom1511 chi) ∨
      (Fin15AnchoredAtom4424 chi ∧
      ¬Fin15AnchoredAtom1525 chi)))) ∨
      ((((Fin15AnchoredAtom4424 chi ∧
      ¬Fin15AnchoredAtom1673 chi) ∨
      (¬Fin15AnchoredAtom4424 chi ∧
      Fin15AnchoredAtom1509 chi ∧
      Fin15AnchoredAtom1511 chi ∧
      Fin15AnchoredAtom1525 chi ∧
      Fin15AnchoredAtom1589 chi ∧
      Fin15AnchoredAtom1673 chi)) ∨
      ((Fin15AnchoredAtom4425 chi ∧
      ¬Fin15AnchoredAtom1510 chi) ∨
      (Fin15AnchoredAtom4425 chi ∧
      ¬Fin15AnchoredAtom1511 chi))) ∨
      (((Fin15AnchoredAtom4425 chi ∧
      ¬Fin15AnchoredAtom1526 chi) ∨
      (Fin15AnchoredAtom4425 chi ∧
      ¬Fin15AnchoredAtom1590 chi)) ∨
      ((Fin15AnchoredAtom4425 chi ∧
      ¬Fin15AnchoredAtom1674 chi) ∨
      (¬Fin15AnchoredAtom4425 chi ∧
      Fin15AnchoredAtom1510 chi ∧
      Fin15AnchoredAtom1511 chi ∧
      Fin15AnchoredAtom1526 chi ∧
      Fin15AnchoredAtom1590 chi ∧
      Fin15AnchoredAtom1674 chi))))) ∨
      (((((Fin15AnchoredAtom4426 chi ∧
      ¬Fin15AnchoredAtom1591 chi) ∨
      (Fin15AnchoredAtom4426 chi ∧
      ¬Fin15AnchoredAtom1675 chi)) ∨
      ((¬Fin15AnchoredAtom4426 chi ∧
      Fin15AnchoredAtom1512 chi ∧
      Fin15AnchoredAtom1513 chi ∧
      Fin15AnchoredAtom1517 chi ∧
      Fin15AnchoredAtom1591 chi ∧
      Fin15AnchoredAtom1675 chi) ∨
      (Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom1512 chi))) ∨
      (((Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom1514 chi) ∨
      (Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom1518 chi)) ∨
      ((Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom1592 chi) ∨
      (Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom1676 chi)))) ∨
      ((((¬Fin15AnchoredAtom4427 chi ∧
      Fin15AnchoredAtom1512 chi ∧
      Fin15AnchoredAtom1514 chi ∧
      Fin15AnchoredAtom1518 chi ∧
      Fin15AnchoredAtom1592 chi ∧
      Fin15AnchoredAtom1676 chi) ∨
      (Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom1512 chi)) ∨
      ((Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom1515 chi) ∨
      (Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom1519 chi))) ∨
      (((Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom1593 chi) ∨
      (Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom1677 chi)) ∨
      ((¬Fin15AnchoredAtom4428 chi ∧
      Fin15AnchoredAtom1512 chi ∧
      Fin15AnchoredAtom1515 chi ∧
      Fin15AnchoredAtom1519 chi ∧
      Fin15AnchoredAtom1593 chi ∧
      Fin15AnchoredAtom1677 chi) ∨
      (Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom1512 chi))))))) ∨
      (((((((Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom1516 chi) ∨
      (Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom1520 chi)) ∨
      ((Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom1594 chi) ∨
      (Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom1678 chi))) ∨
      (((¬Fin15AnchoredAtom4429 chi ∧
      Fin15AnchoredAtom1512 chi ∧
      Fin15AnchoredAtom1516 chi ∧
      Fin15AnchoredAtom1520 chi ∧
      Fin15AnchoredAtom1594 chi ∧
      Fin15AnchoredAtom1678 chi) ∨
      (Fin15AnchoredAtom4430 chi ∧
      ¬Fin15AnchoredAtom1521 chi)) ∨
      ((Fin15AnchoredAtom4430 chi ∧
      ¬Fin15AnchoredAtom1595 chi) ∨
      (Fin15AnchoredAtom4430 chi ∧
      ¬Fin15AnchoredAtom1679 chi)))) ∨
      ((((¬Fin15AnchoredAtom4430 chi ∧
      Fin15AnchoredAtom1513 chi ∧
      Fin15AnchoredAtom1514 chi ∧
      Fin15AnchoredAtom1521 chi ∧
      Fin15AnchoredAtom1595 chi ∧
      Fin15AnchoredAtom1679 chi) ∨
      (Fin15AnchoredAtom4431 chi ∧
      ¬Fin15AnchoredAtom1513 chi)) ∨
      ((Fin15AnchoredAtom4431 chi ∧
      ¬Fin15AnchoredAtom1596 chi) ∨
      (Fin15AnchoredAtom4431 chi ∧
      ¬Fin15AnchoredAtom1680 chi))) ∨
      (((¬Fin15AnchoredAtom4431 chi ∧
      Fin15AnchoredAtom1513 chi ∧
      Fin15AnchoredAtom1515 chi ∧
      Fin15AnchoredAtom1522 chi ∧
      Fin15AnchoredAtom1596 chi ∧
      Fin15AnchoredAtom1680 chi) ∨
      (Fin15AnchoredAtom4432 chi ∧
      ¬Fin15AnchoredAtom1516 chi)) ∨
      ((Fin15AnchoredAtom4432 chi ∧
      ¬Fin15AnchoredAtom1597 chi) ∨
      (Fin15AnchoredAtom4432 chi ∧
      ¬Fin15AnchoredAtom1681 chi))))) ∨
      (((((¬Fin15AnchoredAtom4432 chi ∧
      Fin15AnchoredAtom1513 chi ∧
      Fin15AnchoredAtom1516 chi ∧
      Fin15AnchoredAtom1523 chi ∧
      Fin15AnchoredAtom1597 chi ∧
      Fin15AnchoredAtom1681 chi) ∨
      (Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom1514 chi)) ∨
      ((Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom1515 chi) ∨
      (Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom1524 chi))) ∨
      (((Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom1598 chi) ∨
      (Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom1682 chi)) ∨
      ((¬Fin15AnchoredAtom4433 chi ∧
      Fin15AnchoredAtom1514 chi ∧
      Fin15AnchoredAtom1515 chi ∧
      Fin15AnchoredAtom1524 chi ∧
      Fin15AnchoredAtom1598 chi ∧
      Fin15AnchoredAtom1682 chi) ∨
      (Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom1514 chi)))) ∨
      ((((Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom1516 chi) ∨
      (Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom1525 chi)) ∨
      ((Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom1599 chi) ∨
      (Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom1683 chi))) ∨
      (((¬Fin15AnchoredAtom4434 chi ∧
      Fin15AnchoredAtom1514 chi ∧
      Fin15AnchoredAtom1516 chi ∧
      Fin15AnchoredAtom1525 chi ∧
      Fin15AnchoredAtom1599 chi ∧
      Fin15AnchoredAtom1683 chi) ∨
      (Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom1515 chi)) ∨
      ((Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom1516 chi) ∨
      (Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom1526 chi)))))) ∨
      ((((((Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom1600 chi) ∨
      (Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom1684 chi)) ∨
      ((¬Fin15AnchoredAtom4435 chi ∧
      Fin15AnchoredAtom1515 chi ∧
      Fin15AnchoredAtom1516 chi ∧
      Fin15AnchoredAtom1526 chi ∧
      Fin15AnchoredAtom1600 chi ∧
      Fin15AnchoredAtom1684 chi) ∨
      (Fin15AnchoredAtom4436 chi ∧
      ¬Fin15AnchoredAtom1518 chi))) ∨
      (((Fin15AnchoredAtom4436 chi ∧
      ¬Fin15AnchoredAtom1521 chi) ∨
      (Fin15AnchoredAtom4436 chi ∧
      ¬Fin15AnchoredAtom1601 chi)) ∨
      ((Fin15AnchoredAtom4436 chi ∧
      ¬Fin15AnchoredAtom1685 chi) ∨
      (¬Fin15AnchoredAtom4436 chi ∧
      Fin15AnchoredAtom1517 chi ∧
      Fin15AnchoredAtom1518 chi ∧
      Fin15AnchoredAtom1521 chi ∧
      Fin15AnchoredAtom1601 chi ∧
      Fin15AnchoredAtom1685 chi)))) ∨
      ((((Fin15AnchoredAtom4437 chi ∧
      ¬Fin15AnchoredAtom1519 chi) ∨
      (Fin15AnchoredAtom4437 chi ∧
      ¬Fin15AnchoredAtom1686 chi)) ∨
      ((¬Fin15AnchoredAtom4437 chi ∧
      Fin15AnchoredAtom1517 chi ∧
      Fin15AnchoredAtom1519 chi ∧
      Fin15AnchoredAtom1522 chi ∧
      Fin15AnchoredAtom1602 chi ∧
      Fin15AnchoredAtom1686 chi) ∨
      (Fin15AnchoredAtom4438 chi ∧
      ¬Fin15AnchoredAtom1520 chi))) ∨
      (((Fin15AnchoredAtom4438 chi ∧
      ¬Fin15AnchoredAtom1687 chi) ∨
      (Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom1518 chi)) ∨
      ((Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom1519 chi) ∨
      (Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom1524 chi))))) ∨
      (((((Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom1604 chi) ∨
      (Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom1688 chi)) ∨
      ((¬Fin15AnchoredAtom4439 chi ∧
      Fin15AnchoredAtom1518 chi ∧
      Fin15AnchoredAtom1519 chi ∧
      Fin15AnchoredAtom1524 chi ∧
      Fin15AnchoredAtom1604 chi ∧
      Fin15AnchoredAtom1688 chi) ∨
      (Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom1518 chi))) ∨
      (((Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom1520 chi) ∨
      (Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom1525 chi)) ∨
      ((Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom1605 chi) ∨
      (Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom1689 chi)))) ∨
      ((((¬Fin15AnchoredAtom4440 chi ∧
      Fin15AnchoredAtom1518 chi ∧
      Fin15AnchoredAtom1520 chi ∧
      Fin15AnchoredAtom1525 chi ∧
      Fin15AnchoredAtom1605 chi ∧
      Fin15AnchoredAtom1689 chi) ∨
      (Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom1519 chi)) ∨
      ((Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom1520 chi) ∨
      (Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom1526 chi))) ∨
      (((Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom1606 chi) ∨
      (Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom1690 chi)) ∨
      ((¬Fin15AnchoredAtom4441 chi ∧
      Fin15AnchoredAtom1519 chi ∧
      Fin15AnchoredAtom1520 chi ∧
      Fin15AnchoredAtom1526 chi ∧
      Fin15AnchoredAtom1606 chi ∧
      Fin15AnchoredAtom1690 chi) ∨
      (Fin15AnchoredAtom4442 chi ∧
      ¬Fin15AnchoredAtom1607 chi)))))))))) := by
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
                exact fin15Anchored_clause26502 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26503 chi hbad
                ·
                  exact fin15Anchored_clause26504 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26505 chi hbad
                ·
                  exact fin15Anchored_clause26506 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26507 chi hbad
                ·
                  exact fin15Anchored_clause26508 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26509 chi hbad
                ·
                  exact fin15Anchored_clause26510 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26511 chi hbad
                ·
                  exact fin15Anchored_clause26512 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26513 chi hbad
                ·
                  exact fin15Anchored_clause26514 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26515 chi hbad
                ·
                  exact fin15Anchored_clause26516 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26517 chi hbad
                ·
                  exact fin15Anchored_clause26518 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26519 chi hbad
                ·
                  exact fin15Anchored_clause26520 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26521 chi hbad
                ·
                  exact fin15Anchored_clause26522 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26523 chi hbad
                ·
                  exact fin15Anchored_clause26524 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26525 chi hbad
                ·
                  exact fin15Anchored_clause26526 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26527 chi hbad
                ·
                  exact fin15Anchored_clause26528 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26529 chi hbad
                ·
                  exact fin15Anchored_clause26530 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26531 chi hbad
                ·
                  exact fin15Anchored_clause26532 chi hbad
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
                  exact fin15Anchored_clause26533 chi hbad
                ·
                  exact fin15Anchored_clause26534 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26535 chi hbad
                ·
                  exact fin15Anchored_clause26536 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26537 chi hbad
                ·
                  exact fin15Anchored_clause26538 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26539 chi hbad
                ·
                  exact fin15Anchored_clause26540 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26541 chi hbad
                ·
                  exact fin15Anchored_clause26542 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26543 chi hbad
                ·
                  exact fin15Anchored_clause26544 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26545 chi hbad
                ·
                  exact fin15Anchored_clause26546 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26547 chi hbad
                ·
                  exact fin15Anchored_clause26548 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26549 chi hbad
                ·
                  exact fin15Anchored_clause26550 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26551 chi hbad
                ·
                  exact fin15Anchored_clause26552 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26553 chi hbad
                ·
                  exact fin15Anchored_clause26554 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26555 chi hbad
                ·
                  exact fin15Anchored_clause26556 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26557 chi hbad
                ·
                  exact fin15Anchored_clause26558 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26559 chi hbad
                ·
                  exact fin15Anchored_clause26560 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26561 chi hbad
                ·
                  exact fin15Anchored_clause26562 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26563 chi hbad
                ·
                  exact fin15Anchored_clause26564 chi hbad
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
                exact fin15Anchored_clause26565 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26566 chi hbad
                ·
                  exact fin15Anchored_clause26567 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26568 chi hbad
                ·
                  exact fin15Anchored_clause26569 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26570 chi hbad
                ·
                  exact fin15Anchored_clause26571 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26572 chi hbad
                ·
                  exact fin15Anchored_clause26573 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26574 chi hbad
                ·
                  exact fin15Anchored_clause26575 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26576 chi hbad
                ·
                  exact fin15Anchored_clause26577 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26578 chi hbad
                ·
                  exact fin15Anchored_clause26579 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26580 chi hbad
                ·
                  exact fin15Anchored_clause26581 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26582 chi hbad
                ·
                  exact fin15Anchored_clause26583 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26584 chi hbad
                ·
                  exact fin15Anchored_clause26585 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26586 chi hbad
                ·
                  exact fin15Anchored_clause26587 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26588 chi hbad
                ·
                  exact fin15Anchored_clause26589 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26590 chi hbad
                ·
                  exact fin15Anchored_clause26591 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26592 chi hbad
                ·
                  exact fin15Anchored_clause26593 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26594 chi hbad
                ·
                  exact fin15Anchored_clause26595 chi hbad
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
                  exact fin15Anchored_clause26596 chi hbad
                ·
                  exact fin15Anchored_clause26597 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26598 chi hbad
                ·
                  exact fin15Anchored_clause26599 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26600 chi hbad
                ·
                  exact fin15Anchored_clause26601 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26602 chi hbad
                ·
                  exact fin15Anchored_clause26603 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26604 chi hbad
                ·
                  exact fin15Anchored_clause26605 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26606 chi hbad
                ·
                  exact fin15Anchored_clause26607 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26608 chi hbad
                ·
                  exact fin15Anchored_clause26609 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26610 chi hbad
                ·
                  exact fin15Anchored_clause26611 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26612 chi hbad
                ·
                  exact fin15Anchored_clause26613 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26614 chi hbad
                ·
                  exact fin15Anchored_clause26615 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26616 chi hbad
                ·
                  exact fin15Anchored_clause26617 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26618 chi hbad
                ·
                  exact fin15Anchored_clause26619 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26620 chi hbad
                ·
                  exact fin15Anchored_clause26621 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26622 chi hbad
                ·
                  exact fin15Anchored_clause26623 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26624 chi hbad
                ·
                  exact fin15Anchored_clause26625 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26626 chi hbad
                ·
                  exact fin15Anchored_clause26627 chi hbad
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
                exact fin15Anchored_clause26628 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26629 chi hbad
                ·
                  exact fin15Anchored_clause26630 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26631 chi hbad
                ·
                  exact fin15Anchored_clause26632 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26633 chi hbad
                ·
                  exact fin15Anchored_clause26634 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26635 chi hbad
                ·
                  exact fin15Anchored_clause26636 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26637 chi hbad
                ·
                  exact fin15Anchored_clause26638 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26639 chi hbad
                ·
                  exact fin15Anchored_clause26640 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26641 chi hbad
                ·
                  exact fin15Anchored_clause26642 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26643 chi hbad
                ·
                  exact fin15Anchored_clause26644 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26645 chi hbad
                ·
                  exact fin15Anchored_clause26646 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26647 chi hbad
                ·
                  exact fin15Anchored_clause26648 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26649 chi hbad
                ·
                  exact fin15Anchored_clause26650 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26651 chi hbad
                ·
                  exact fin15Anchored_clause26652 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26653 chi hbad
                ·
                  exact fin15Anchored_clause26654 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26655 chi hbad
                ·
                  exact fin15Anchored_clause26656 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26657 chi hbad
                ·
                  exact fin15Anchored_clause26658 chi hbad
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
                  exact fin15Anchored_clause26659 chi hbad
                ·
                  exact fin15Anchored_clause26660 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26661 chi hbad
                ·
                  exact fin15Anchored_clause26662 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26663 chi hbad
                ·
                  exact fin15Anchored_clause26664 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26665 chi hbad
                ·
                  exact fin15Anchored_clause26666 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26667 chi hbad
                ·
                  exact fin15Anchored_clause26668 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26669 chi hbad
                ·
                  exact fin15Anchored_clause26670 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26671 chi hbad
                ·
                  exact fin15Anchored_clause26672 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26673 chi hbad
                ·
                  exact fin15Anchored_clause26674 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26675 chi hbad
                ·
                  exact fin15Anchored_clause26676 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26677 chi hbad
                ·
                  exact fin15Anchored_clause26678 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26679 chi hbad
                ·
                  exact fin15Anchored_clause26680 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26681 chi hbad
                ·
                  exact fin15Anchored_clause26682 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26683 chi hbad
                ·
                  exact fin15Anchored_clause26684 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26685 chi hbad
                ·
                  exact fin15Anchored_clause26686 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26687 chi hbad
                ·
                  exact fin15Anchored_clause26688 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26689 chi hbad
                ·
                  exact fin15Anchored_clause26690 chi hbad
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
                  exact fin15Anchored_clause26691 chi hbad
                ·
                  exact fin15Anchored_clause26692 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26693 chi hbad
                ·
                  exact fin15Anchored_clause26694 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26695 chi hbad
                ·
                  exact fin15Anchored_clause26696 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26697 chi hbad
                ·
                  exact fin15Anchored_clause26698 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26699 chi hbad
                ·
                  exact fin15Anchored_clause26700 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26701 chi hbad
                ·
                  exact fin15Anchored_clause26702 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26703 chi hbad
                ·
                  exact fin15Anchored_clause26704 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26705 chi hbad
                ·
                  exact fin15Anchored_clause26706 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26707 chi hbad
                ·
                  exact fin15Anchored_clause26708 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26709 chi hbad
                ·
                  exact fin15Anchored_clause26710 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26711 chi hbad
                ·
                  exact fin15Anchored_clause26712 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26713 chi hbad
                ·
                  exact fin15Anchored_clause26714 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26715 chi hbad
                ·
                  exact fin15Anchored_clause26716 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26717 chi hbad
                ·
                  exact fin15Anchored_clause26718 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26719 chi hbad
                ·
                  exact fin15Anchored_clause26720 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26721 chi hbad
                ·
                  exact fin15Anchored_clause26722 chi hbad
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
                  exact fin15Anchored_clause26723 chi hbad
                ·
                  exact fin15Anchored_clause26724 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26725 chi hbad
                ·
                  exact fin15Anchored_clause26726 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26727 chi hbad
                ·
                  exact fin15Anchored_clause26728 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26729 chi hbad
                ·
                  exact fin15Anchored_clause26730 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26731 chi hbad
                ·
                  exact fin15Anchored_clause26732 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26733 chi hbad
                ·
                  exact fin15Anchored_clause26734 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26735 chi hbad
                ·
                  exact fin15Anchored_clause26736 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26737 chi hbad
                ·
                  exact fin15Anchored_clause26738 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26739 chi hbad
                ·
                  exact fin15Anchored_clause26740 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26741 chi hbad
                ·
                  exact fin15Anchored_clause26742 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26743 chi hbad
                ·
                  exact fin15Anchored_clause26744 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26745 chi hbad
                ·
                  exact fin15Anchored_clause26746 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26747 chi hbad
                ·
                  exact fin15Anchored_clause26748 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26749 chi hbad
                ·
                  exact fin15Anchored_clause26750 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26751 chi hbad
                ·
                  exact fin15Anchored_clause26752 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26753 chi hbad
                ·
                  exact fin15Anchored_clause26754 chi hbad

end ErdosSzekeres

end
