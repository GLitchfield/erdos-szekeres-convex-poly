module

public import ErdosSzekeres.Fin15AnchoredClauseChunk201
public import ErdosSzekeres.Fin15AnchoredClauseChunk202
public import ErdosSzekeres.Fin15AnchoredClauseChunk203

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 102. -/

theorem fin15Anchored_rejectSemanticSegment102
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom1447 chi) ∨
      ((Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom1651 chi) ∨
      (¬Fin15AnchoredAtom4192 chi ∧
      Fin15AnchoredAtom1381 chi ∧
      Fin15AnchoredAtom1383 chi ∧
      Fin15AnchoredAtom1398 chi ∧
      Fin15AnchoredAtom1447 chi ∧
      Fin15AnchoredAtom1651 chi))) ∨
      (((Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom1381 chi) ∨
      (Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom1384 chi)) ∨
      ((Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom1399 chi) ∨
      (Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom1448 chi)))) ∨
      ((((Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom1652 chi) ∨
      (¬Fin15AnchoredAtom4193 chi ∧
      Fin15AnchoredAtom1381 chi ∧
      Fin15AnchoredAtom1384 chi ∧
      Fin15AnchoredAtom1399 chi ∧
      Fin15AnchoredAtom1448 chi ∧
      Fin15AnchoredAtom1652 chi)) ∨
      ((Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom1381 chi) ∨
      (Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom1385 chi))) ∨
      (((Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom1400 chi) ∨
      (Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom1449 chi)) ∨
      ((Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom1653 chi) ∨
      (¬Fin15AnchoredAtom4194 chi ∧
      Fin15AnchoredAtom1381 chi ∧
      Fin15AnchoredAtom1385 chi ∧
      Fin15AnchoredAtom1400 chi ∧
      Fin15AnchoredAtom1449 chi ∧
      Fin15AnchoredAtom1653 chi))))) ∨
      (((((Fin15AnchoredAtom4195 chi ∧
      ¬Fin15AnchoredAtom1382 chi) ∨
      (Fin15AnchoredAtom4195 chi ∧
      ¬Fin15AnchoredAtom1383 chi)) ∨
      ((Fin15AnchoredAtom4195 chi ∧
      ¬Fin15AnchoredAtom1450 chi) ∨
      (Fin15AnchoredAtom4195 chi ∧
      ¬Fin15AnchoredAtom1654 chi))) ∨
      (((Fin15AnchoredAtom4196 chi ∧
      ¬Fin15AnchoredAtom1384 chi) ∨
      (Fin15AnchoredAtom4197 chi ∧
      ¬Fin15AnchoredAtom1385 chi)) ∨
      ((Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom1383 chi) ∨
      (Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom1384 chi)))) ∨
      ((((Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom1404 chi) ∨
      (Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom1453 chi)) ∨
      ((Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom1657 chi) ∨
      (¬Fin15AnchoredAtom4198 chi ∧
      Fin15AnchoredAtom1383 chi ∧
      Fin15AnchoredAtom1384 chi ∧
      Fin15AnchoredAtom1404 chi ∧
      Fin15AnchoredAtom1453 chi ∧
      Fin15AnchoredAtom1657 chi))) ∨
      (((Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom1383 chi) ∨
      (Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom1385 chi)) ∨
      ((Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom1405 chi) ∨
      (Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom1454 chi)))))) ∨
      ((((((Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom1658 chi) ∨
      (¬Fin15AnchoredAtom4199 chi ∧
      Fin15AnchoredAtom1383 chi ∧
      Fin15AnchoredAtom1385 chi ∧
      Fin15AnchoredAtom1405 chi ∧
      Fin15AnchoredAtom1454 chi ∧
      Fin15AnchoredAtom1658 chi)) ∨
      ((Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom1384 chi) ∨
      (Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom1385 chi))) ∨
      (((Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom1406 chi) ∨
      (Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom1455 chi)) ∨
      ((Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom1659 chi) ∨
      (¬Fin15AnchoredAtom4200 chi ∧
      Fin15AnchoredAtom1384 chi ∧
      Fin15AnchoredAtom1385 chi ∧
      Fin15AnchoredAtom1406 chi ∧
      Fin15AnchoredAtom1455 chi ∧
      Fin15AnchoredAtom1659 chi)))) ∨
      ((((Fin15AnchoredAtom4201 chi ∧
      ¬Fin15AnchoredAtom1386 chi) ∨
      (Fin15AnchoredAtom4201 chi ∧
      ¬Fin15AnchoredAtom1387 chi)) ∨
      ((Fin15AnchoredAtom4201 chi ∧
      ¬Fin15AnchoredAtom1392 chi) ∨
      (Fin15AnchoredAtom4201 chi ∧
      ¬Fin15AnchoredAtom1456 chi))) ∨
      (((Fin15AnchoredAtom4201 chi ∧
      ¬Fin15AnchoredAtom1660 chi) ∨
      (¬Fin15AnchoredAtom4201 chi ∧
      Fin15AnchoredAtom1386 chi ∧
      Fin15AnchoredAtom1387 chi ∧
      Fin15AnchoredAtom1392 chi ∧
      Fin15AnchoredAtom1456 chi ∧
      Fin15AnchoredAtom1660 chi)) ∨
      ((Fin15AnchoredAtom4203 chi ∧
      ¬Fin15AnchoredAtom1386 chi) ∨
      (Fin15AnchoredAtom4203 chi ∧
      ¬Fin15AnchoredAtom1389 chi))))) ∨
      (((((Fin15AnchoredAtom4203 chi ∧
      ¬Fin15AnchoredAtom1394 chi) ∨
      (Fin15AnchoredAtom4203 chi ∧
      ¬Fin15AnchoredAtom1458 chi)) ∨
      ((Fin15AnchoredAtom4203 chi ∧
      ¬Fin15AnchoredAtom1662 chi) ∨
      (¬Fin15AnchoredAtom4203 chi ∧
      Fin15AnchoredAtom1386 chi ∧
      Fin15AnchoredAtom1389 chi ∧
      Fin15AnchoredAtom1394 chi ∧
      Fin15AnchoredAtom1458 chi ∧
      Fin15AnchoredAtom1662 chi))) ∨
      (((Fin15AnchoredAtom4204 chi ∧
      ¬Fin15AnchoredAtom1386 chi) ∨
      (Fin15AnchoredAtom4204 chi ∧
      ¬Fin15AnchoredAtom1390 chi)) ∨
      ((Fin15AnchoredAtom4204 chi ∧
      ¬Fin15AnchoredAtom1395 chi) ∨
      (Fin15AnchoredAtom4204 chi ∧
      ¬Fin15AnchoredAtom1459 chi)))) ∨
      ((((Fin15AnchoredAtom4204 chi ∧
      ¬Fin15AnchoredAtom1663 chi) ∨
      (¬Fin15AnchoredAtom4204 chi ∧
      Fin15AnchoredAtom1386 chi ∧
      Fin15AnchoredAtom1390 chi ∧
      Fin15AnchoredAtom1395 chi ∧
      Fin15AnchoredAtom1459 chi ∧
      Fin15AnchoredAtom1663 chi)) ∨
      ((Fin15AnchoredAtom4205 chi ∧
      ¬Fin15AnchoredAtom1386 chi) ∨
      (Fin15AnchoredAtom4205 chi ∧
      ¬Fin15AnchoredAtom1391 chi))) ∨
      (((Fin15AnchoredAtom4205 chi ∧
      ¬Fin15AnchoredAtom1396 chi) ∨
      (Fin15AnchoredAtom4205 chi ∧
      ¬Fin15AnchoredAtom1460 chi)) ∨
      ((Fin15AnchoredAtom4205 chi ∧
      ¬Fin15AnchoredAtom1664 chi) ∨
      (¬Fin15AnchoredAtom4205 chi ∧
      Fin15AnchoredAtom1386 chi ∧
      Fin15AnchoredAtom1391 chi ∧
      Fin15AnchoredAtom1396 chi ∧
      Fin15AnchoredAtom1460 chi ∧
      Fin15AnchoredAtom1664 chi))))))) ∨
      ((((((Fin15AnchoredAtom4207 chi ∧
      ¬Fin15AnchoredAtom1387 chi) ∨
      ((Fin15AnchoredAtom4207 chi ∧
      ¬Fin15AnchoredAtom1389 chi) ∨
      (Fin15AnchoredAtom4207 chi ∧
      ¬Fin15AnchoredAtom1398 chi))) ∨
      (((Fin15AnchoredAtom4207 chi ∧
      ¬Fin15AnchoredAtom1462 chi) ∨
      (Fin15AnchoredAtom4207 chi ∧
      ¬Fin15AnchoredAtom1666 chi)) ∨
      ((¬Fin15AnchoredAtom4207 chi ∧
      Fin15AnchoredAtom1387 chi ∧
      Fin15AnchoredAtom1389 chi ∧
      Fin15AnchoredAtom1398 chi ∧
      Fin15AnchoredAtom1462 chi ∧
      Fin15AnchoredAtom1666 chi) ∨
      (Fin15AnchoredAtom4208 chi ∧
      ¬Fin15AnchoredAtom1387 chi)))) ∨
      ((((Fin15AnchoredAtom4208 chi ∧
      ¬Fin15AnchoredAtom1390 chi) ∨
      (Fin15AnchoredAtom4208 chi ∧
      ¬Fin15AnchoredAtom1399 chi)) ∨
      ((Fin15AnchoredAtom4208 chi ∧
      ¬Fin15AnchoredAtom1463 chi) ∨
      (Fin15AnchoredAtom4208 chi ∧
      ¬Fin15AnchoredAtom1667 chi))) ∨
      (((¬Fin15AnchoredAtom4208 chi ∧
      Fin15AnchoredAtom1387 chi ∧
      Fin15AnchoredAtom1390 chi ∧
      Fin15AnchoredAtom1399 chi ∧
      Fin15AnchoredAtom1463 chi ∧
      Fin15AnchoredAtom1667 chi) ∨
      (Fin15AnchoredAtom4209 chi ∧
      ¬Fin15AnchoredAtom1387 chi)) ∨
      ((Fin15AnchoredAtom4209 chi ∧
      ¬Fin15AnchoredAtom1391 chi) ∨
      (Fin15AnchoredAtom4209 chi ∧
      ¬Fin15AnchoredAtom1400 chi))))) ∨
      (((((Fin15AnchoredAtom4209 chi ∧
      ¬Fin15AnchoredAtom1668 chi) ∨
      (Fin15AnchoredAtom4213 chi ∧
      ¬Fin15AnchoredAtom1389 chi)) ∨
      ((Fin15AnchoredAtom4213 chi ∧
      ¬Fin15AnchoredAtom1390 chi) ∨
      (Fin15AnchoredAtom4213 chi ∧
      ¬Fin15AnchoredAtom1468 chi))) ∨
      (((Fin15AnchoredAtom4213 chi ∧
      ¬Fin15AnchoredAtom1672 chi) ∨
      (¬Fin15AnchoredAtom4213 chi ∧
      Fin15AnchoredAtom1389 chi ∧
      Fin15AnchoredAtom1390 chi ∧
      Fin15AnchoredAtom1404 chi ∧
      Fin15AnchoredAtom1468 chi ∧
      Fin15AnchoredAtom1672 chi)) ∨
      ((Fin15AnchoredAtom4214 chi ∧
      ¬Fin15AnchoredAtom1389 chi) ∨
      (Fin15AnchoredAtom4214 chi ∧
      ¬Fin15AnchoredAtom1391 chi)))) ∨
      ((((Fin15AnchoredAtom4214 chi ∧
      ¬Fin15AnchoredAtom1405 chi) ∨
      (Fin15AnchoredAtom4214 chi ∧
      ¬Fin15AnchoredAtom1469 chi)) ∨
      ((Fin15AnchoredAtom4214 chi ∧
      ¬Fin15AnchoredAtom1673 chi) ∨
      (¬Fin15AnchoredAtom4214 chi ∧
      Fin15AnchoredAtom1389 chi ∧
      Fin15AnchoredAtom1391 chi ∧
      Fin15AnchoredAtom1405 chi ∧
      Fin15AnchoredAtom1469 chi ∧
      Fin15AnchoredAtom1673 chi))) ∨
      (((Fin15AnchoredAtom4215 chi ∧
      ¬Fin15AnchoredAtom1390 chi) ∨
      (Fin15AnchoredAtom4215 chi ∧
      ¬Fin15AnchoredAtom1391 chi)) ∨
      ((Fin15AnchoredAtom4215 chi ∧
      ¬Fin15AnchoredAtom1406 chi) ∨
      (Fin15AnchoredAtom4215 chi ∧
      ¬Fin15AnchoredAtom1470 chi)))))) ∨
      ((((((Fin15AnchoredAtom4215 chi ∧
      ¬Fin15AnchoredAtom1674 chi) ∨
      (¬Fin15AnchoredAtom4215 chi ∧
      Fin15AnchoredAtom1390 chi ∧
      Fin15AnchoredAtom1391 chi ∧
      Fin15AnchoredAtom1406 chi ∧
      Fin15AnchoredAtom1470 chi ∧
      Fin15AnchoredAtom1674 chi)) ∨
      ((Fin15AnchoredAtom4216 chi ∧
      ¬Fin15AnchoredAtom1392 chi) ∨
      (Fin15AnchoredAtom4216 chi ∧
      ¬Fin15AnchoredAtom1393 chi))) ∨
      (((Fin15AnchoredAtom4216 chi ∧
      ¬Fin15AnchoredAtom1397 chi) ∨
      (Fin15AnchoredAtom4216 chi ∧
      ¬Fin15AnchoredAtom1471 chi)) ∨
      ((Fin15AnchoredAtom4216 chi ∧
      ¬Fin15AnchoredAtom1675 chi) ∨
      (¬Fin15AnchoredAtom4216 chi ∧
      Fin15AnchoredAtom1392 chi ∧
      Fin15AnchoredAtom1393 chi ∧
      Fin15AnchoredAtom1397 chi ∧
      Fin15AnchoredAtom1471 chi ∧
      Fin15AnchoredAtom1675 chi)))) ∨
      ((((Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom1392 chi) ∨
      (Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom1394 chi)) ∨
      ((Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom1398 chi) ∨
      (Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom1472 chi))) ∨
      (((Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom1676 chi) ∨
      (¬Fin15AnchoredAtom4217 chi ∧
      Fin15AnchoredAtom1392 chi ∧
      Fin15AnchoredAtom1394 chi ∧
      Fin15AnchoredAtom1398 chi ∧
      Fin15AnchoredAtom1472 chi ∧
      Fin15AnchoredAtom1676 chi)) ∨
      ((Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom1392 chi) ∨
      (Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom1395 chi))))) ∨
      (((((Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom1399 chi) ∨
      (Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom1473 chi)) ∨
      ((Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom1677 chi) ∨
      (¬Fin15AnchoredAtom4218 chi ∧
      Fin15AnchoredAtom1392 chi ∧
      Fin15AnchoredAtom1395 chi ∧
      Fin15AnchoredAtom1399 chi ∧
      Fin15AnchoredAtom1473 chi ∧
      Fin15AnchoredAtom1677 chi))) ∨
      (((Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom1392 chi) ∨
      (Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom1396 chi)) ∨
      ((Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom1400 chi) ∨
      (Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom1474 chi)))) ∨
      ((((Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom1678 chi) ∨
      (¬Fin15AnchoredAtom4219 chi ∧
      Fin15AnchoredAtom1392 chi ∧
      Fin15AnchoredAtom1396 chi ∧
      Fin15AnchoredAtom1400 chi ∧
      Fin15AnchoredAtom1474 chi ∧
      Fin15AnchoredAtom1678 chi)) ∨
      ((Fin15AnchoredAtom4220 chi ∧
      ¬Fin15AnchoredAtom1394 chi) ∨
      (Fin15AnchoredAtom4220 chi ∧
      ¬Fin15AnchoredAtom1679 chi))) ∨
      (((Fin15AnchoredAtom4221 chi ∧
      ¬Fin15AnchoredAtom1680 chi) ∨
      (Fin15AnchoredAtom4222 chi ∧
      ¬Fin15AnchoredAtom1396 chi)) ∨
      ((Fin15AnchoredAtom4222 chi ∧
      ¬Fin15AnchoredAtom1681 chi) ∨
      (Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom1394 chi)))))))) ∨
      (((((((Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom1395 chi) ∨
      ((Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom1404 chi) ∨
      (Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom1478 chi))) ∨
      (((Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom1682 chi) ∨
      (¬Fin15AnchoredAtom4223 chi ∧
      Fin15AnchoredAtom1394 chi ∧
      Fin15AnchoredAtom1395 chi ∧
      Fin15AnchoredAtom1404 chi ∧
      Fin15AnchoredAtom1478 chi ∧
      Fin15AnchoredAtom1682 chi)) ∨
      ((Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom1394 chi) ∨
      (Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom1396 chi)))) ∨
      ((((Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom1405 chi) ∨
      (Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom1479 chi)) ∨
      ((Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom1683 chi) ∨
      (¬Fin15AnchoredAtom4224 chi ∧
      Fin15AnchoredAtom1394 chi ∧
      Fin15AnchoredAtom1396 chi ∧
      Fin15AnchoredAtom1405 chi ∧
      Fin15AnchoredAtom1479 chi ∧
      Fin15AnchoredAtom1683 chi))) ∨
      (((Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom1395 chi) ∨
      (Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom1396 chi)) ∨
      ((Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom1406 chi) ∨
      (Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom1480 chi))))) ∨
      (((((Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom1684 chi) ∨
      (¬Fin15AnchoredAtom4225 chi ∧
      Fin15AnchoredAtom1395 chi ∧
      Fin15AnchoredAtom1396 chi ∧
      Fin15AnchoredAtom1406 chi ∧
      Fin15AnchoredAtom1480 chi ∧
      Fin15AnchoredAtom1684 chi)) ∨
      ((Fin15AnchoredAtom4226 chi ∧
      ¬Fin15AnchoredAtom1398 chi) ∨
      (Fin15AnchoredAtom4226 chi ∧
      ¬Fin15AnchoredAtom1481 chi))) ∨
      (((Fin15AnchoredAtom4226 chi ∧
      ¬Fin15AnchoredAtom1685 chi) ∨
      (Fin15AnchoredAtom4227 chi ∧
      ¬Fin15AnchoredAtom1399 chi)) ∨
      ((Fin15AnchoredAtom4227 chi ∧
      ¬Fin15AnchoredAtom1686 chi) ∨
      (¬Fin15AnchoredAtom4227 chi ∧
      Fin15AnchoredAtom1397 chi ∧
      Fin15AnchoredAtom1399 chi ∧
      Fin15AnchoredAtom1402 chi ∧
      Fin15AnchoredAtom1482 chi ∧
      Fin15AnchoredAtom1686 chi)))) ∨
      ((((Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom1398 chi) ∨
      (Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom1399 chi)) ∨
      ((Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom1404 chi) ∨
      (Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom1484 chi))) ∨
      (((Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom1688 chi) ∨
      (¬Fin15AnchoredAtom4229 chi ∧
      Fin15AnchoredAtom1398 chi ∧
      Fin15AnchoredAtom1399 chi ∧
      Fin15AnchoredAtom1404 chi ∧
      Fin15AnchoredAtom1484 chi ∧
      Fin15AnchoredAtom1688 chi)) ∨
      ((Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom1398 chi) ∨
      (Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom1400 chi)))))) ∨
      ((((((Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom1405 chi) ∨
      (Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom1485 chi)) ∨
      ((Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom1689 chi) ∨
      (¬Fin15AnchoredAtom4230 chi ∧
      Fin15AnchoredAtom1398 chi ∧
      Fin15AnchoredAtom1400 chi ∧
      Fin15AnchoredAtom1405 chi ∧
      Fin15AnchoredAtom1485 chi ∧
      Fin15AnchoredAtom1689 chi))) ∨
      (((Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom1399 chi) ∨
      (Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom1400 chi)) ∨
      ((Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom1406 chi) ∨
      (Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom1486 chi)))) ∨
      ((((Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom1690 chi) ∨
      (¬Fin15AnchoredAtom4231 chi ∧
      Fin15AnchoredAtom1399 chi ∧
      Fin15AnchoredAtom1400 chi ∧
      Fin15AnchoredAtom1406 chi ∧
      Fin15AnchoredAtom1486 chi ∧
      Fin15AnchoredAtom1690 chi)) ∨
      ((Fin15AnchoredAtom4232 chi ∧
      ¬Fin15AnchoredAtom1487 chi) ∨
      (Fin15AnchoredAtom4232 chi ∧
      ¬Fin15AnchoredAtom1691 chi))) ∨
      (((Fin15AnchoredAtom4233 chi ∧
      ¬Fin15AnchoredAtom1405 chi) ∨
      (Fin15AnchoredAtom4234 chi ∧
      ¬Fin15AnchoredAtom1693 chi)) ∨
      ((¬Fin15AnchoredAtom4234 chi ∧
      Fin15AnchoredAtom1402 chi ∧
      Fin15AnchoredAtom1403 chi ∧
      Fin15AnchoredAtom1406 chi ∧
      Fin15AnchoredAtom1489 chi ∧
      Fin15AnchoredAtom1693 chi) ∨
      (Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom1404 chi))))) ∨
      (((((Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom1405 chi) ∨
      (Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom1406 chi)) ∨
      ((Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom1490 chi) ∨
      (Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom1694 chi))) ∨
      (((¬Fin15AnchoredAtom4235 chi ∧
      Fin15AnchoredAtom1404 chi ∧
      Fin15AnchoredAtom1405 chi ∧
      Fin15AnchoredAtom1406 chi ∧
      Fin15AnchoredAtom1490 chi ∧
      Fin15AnchoredAtom1694 chi) ∨
      (Fin15AnchoredAtom4236 chi ∧
      ¬Fin15AnchoredAtom1407 chi)) ∨
      ((Fin15AnchoredAtom4236 chi ∧
      ¬Fin15AnchoredAtom1408 chi) ∨
      (Fin15AnchoredAtom4236 chi ∧
      ¬Fin15AnchoredAtom1435 chi)))) ∨
      ((((Fin15AnchoredAtom4236 chi ∧
      ¬Fin15AnchoredAtom1695 chi) ∨
      (¬Fin15AnchoredAtom4236 chi ∧
      Fin15AnchoredAtom1407 chi ∧
      Fin15AnchoredAtom1408 chi ∧
      Fin15AnchoredAtom1414 chi ∧
      Fin15AnchoredAtom1435 chi ∧
      Fin15AnchoredAtom1695 chi)) ∨
      ((Fin15AnchoredAtom4237 chi ∧
      ¬Fin15AnchoredAtom1407 chi) ∨
      (Fin15AnchoredAtom4237 chi ∧
      ¬Fin15AnchoredAtom1409 chi))) ∨
      (((Fin15AnchoredAtom4237 chi ∧
      ¬Fin15AnchoredAtom1415 chi) ∨
      (Fin15AnchoredAtom4237 chi ∧
      ¬Fin15AnchoredAtom1436 chi)) ∨
      ((Fin15AnchoredAtom4237 chi ∧
      ¬Fin15AnchoredAtom1696 chi) ∨
      (¬Fin15AnchoredAtom4237 chi ∧
      Fin15AnchoredAtom1407 chi ∧
      Fin15AnchoredAtom1409 chi ∧
      Fin15AnchoredAtom1415 chi ∧
      Fin15AnchoredAtom1436 chi ∧
      Fin15AnchoredAtom1696 chi))))))) ∨
      ((((((Fin15AnchoredAtom4239 chi ∧
      ¬Fin15AnchoredAtom1407 chi) ∨
      ((Fin15AnchoredAtom4239 chi ∧
      ¬Fin15AnchoredAtom1411 chi) ∨
      (Fin15AnchoredAtom4239 chi ∧
      ¬Fin15AnchoredAtom1417 chi))) ∨
      (((Fin15AnchoredAtom4239 chi ∧
      ¬Fin15AnchoredAtom1698 chi) ∨
      (¬Fin15AnchoredAtom4239 chi ∧
      Fin15AnchoredAtom1407 chi ∧
      Fin15AnchoredAtom1411 chi ∧
      Fin15AnchoredAtom1417 chi ∧
      Fin15AnchoredAtom1438 chi ∧
      Fin15AnchoredAtom1698 chi)) ∨
      ((Fin15AnchoredAtom4240 chi ∧
      ¬Fin15AnchoredAtom1407 chi) ∨
      (Fin15AnchoredAtom4240 chi ∧
      ¬Fin15AnchoredAtom1412 chi)))) ∨
      ((((Fin15AnchoredAtom4240 chi ∧
      ¬Fin15AnchoredAtom1418 chi) ∨
      (Fin15AnchoredAtom4240 chi ∧
      ¬Fin15AnchoredAtom1699 chi)) ∨
      ((¬Fin15AnchoredAtom4240 chi ∧
      Fin15AnchoredAtom1407 chi ∧
      Fin15AnchoredAtom1412 chi ∧
      Fin15AnchoredAtom1418 chi ∧
      Fin15AnchoredAtom1439 chi ∧
      Fin15AnchoredAtom1699 chi) ∨
      (Fin15AnchoredAtom4241 chi ∧
      ¬Fin15AnchoredAtom1407 chi))) ∨
      (((Fin15AnchoredAtom4241 chi ∧
      ¬Fin15AnchoredAtom1413 chi) ∨
      (Fin15AnchoredAtom4241 chi ∧
      ¬Fin15AnchoredAtom1419 chi)) ∨
      ((Fin15AnchoredAtom4241 chi ∧
      ¬Fin15AnchoredAtom1440 chi) ∨
      (Fin15AnchoredAtom4241 chi ∧
      ¬Fin15AnchoredAtom1700 chi))))) ∨
      (((((¬Fin15AnchoredAtom4241 chi ∧
      Fin15AnchoredAtom1407 chi ∧
      Fin15AnchoredAtom1413 chi ∧
      Fin15AnchoredAtom1419 chi ∧
      Fin15AnchoredAtom1440 chi ∧
      Fin15AnchoredAtom1700 chi) ∨
      (Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom1408 chi)) ∨
      ((Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom1409 chi) ∨
      (Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom1420 chi))) ∨
      (((Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom1441 chi) ∨
      (Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom1701 chi)) ∨
      ((¬Fin15AnchoredAtom4242 chi ∧
      Fin15AnchoredAtom1408 chi ∧
      Fin15AnchoredAtom1409 chi ∧
      Fin15AnchoredAtom1420 chi ∧
      Fin15AnchoredAtom1441 chi ∧
      Fin15AnchoredAtom1701 chi) ∨
      (Fin15AnchoredAtom4243 chi ∧
      ¬Fin15AnchoredAtom1408 chi)))) ∨
      ((((Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom1408 chi) ∨
      (Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom1411 chi)) ∨
      ((Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom1422 chi) ∨
      (Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom1443 chi))) ∨
      (((Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom1703 chi) ∨
      (¬Fin15AnchoredAtom4244 chi ∧
      Fin15AnchoredAtom1408 chi ∧
      Fin15AnchoredAtom1411 chi ∧
      Fin15AnchoredAtom1422 chi ∧
      Fin15AnchoredAtom1443 chi ∧
      Fin15AnchoredAtom1703 chi)) ∨
      ((Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom1408 chi) ∨
      (Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom1412 chi)))))) ∨
      ((((((Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom1423 chi) ∨
      (Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom1444 chi)) ∨
      ((Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom1704 chi) ∨
      (¬Fin15AnchoredAtom4245 chi ∧
      Fin15AnchoredAtom1408 chi ∧
      Fin15AnchoredAtom1412 chi ∧
      Fin15AnchoredAtom1423 chi ∧
      Fin15AnchoredAtom1444 chi ∧
      Fin15AnchoredAtom1704 chi))) ∨
      (((Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom1408 chi) ∨
      (Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom1413 chi)) ∨
      ((Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom1424 chi) ∨
      (Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom1445 chi)))) ∨
      ((((Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom1705 chi) ∨
      (¬Fin15AnchoredAtom4246 chi ∧
      Fin15AnchoredAtom1408 chi ∧
      Fin15AnchoredAtom1413 chi ∧
      Fin15AnchoredAtom1424 chi ∧
      Fin15AnchoredAtom1445 chi ∧
      Fin15AnchoredAtom1705 chi)) ∨
      ((Fin15AnchoredAtom4247 chi ∧
      ¬Fin15AnchoredAtom1706 chi) ∨
      (¬Fin15AnchoredAtom4247 chi ∧
      Fin15AnchoredAtom1409 chi ∧
      Fin15AnchoredAtom1410 chi ∧
      Fin15AnchoredAtom1425 chi ∧
      Fin15AnchoredAtom1446 chi ∧
      Fin15AnchoredAtom1706 chi))) ∨
      (((Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom1409 chi) ∨
      (Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom1411 chi)) ∨
      ((Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom1426 chi) ∨
      (Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom1447 chi))))) ∨
      (((((Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom1707 chi) ∨
      (¬Fin15AnchoredAtom4248 chi ∧
      Fin15AnchoredAtom1409 chi ∧
      Fin15AnchoredAtom1411 chi ∧
      Fin15AnchoredAtom1426 chi ∧
      Fin15AnchoredAtom1447 chi ∧
      Fin15AnchoredAtom1707 chi)) ∨
      ((Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom1409 chi) ∨
      (Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom1412 chi))) ∨
      (((Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom1427 chi) ∨
      (Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom1448 chi)) ∨
      ((Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom1708 chi) ∨
      (¬Fin15AnchoredAtom4249 chi ∧
      Fin15AnchoredAtom1409 chi ∧
      Fin15AnchoredAtom1412 chi ∧
      Fin15AnchoredAtom1427 chi ∧
      Fin15AnchoredAtom1448 chi ∧
      Fin15AnchoredAtom1708 chi)))) ∨
      ((((Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom1409 chi) ∨
      (Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom1413 chi)) ∨
      ((Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom1428 chi) ∨
      (Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom1449 chi))) ∨
      (((Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom1709 chi) ∨
      (¬Fin15AnchoredAtom4250 chi ∧
      Fin15AnchoredAtom1409 chi ∧
      Fin15AnchoredAtom1413 chi ∧
      Fin15AnchoredAtom1428 chi ∧
      Fin15AnchoredAtom1449 chi ∧
      Fin15AnchoredAtom1709 chi)) ∨
      ((Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom1411 chi) ∨
      (Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom1412 chi)))))))))) := by
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
                exact fin15Anchored_clause25745 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25746 chi hbad
                ·
                  exact fin15Anchored_clause25747 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25748 chi hbad
                ·
                  exact fin15Anchored_clause25749 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25750 chi hbad
                ·
                  exact fin15Anchored_clause25751 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25752 chi hbad
                ·
                  exact fin15Anchored_clause25753 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25754 chi hbad
                ·
                  exact fin15Anchored_clause25755 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25756 chi hbad
                ·
                  exact fin15Anchored_clause25757 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25758 chi hbad
                ·
                  exact fin15Anchored_clause25759 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25760 chi hbad
                ·
                  exact fin15Anchored_clause25761 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25762 chi hbad
                ·
                  exact fin15Anchored_clause25763 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25764 chi hbad
                ·
                  exact fin15Anchored_clause25765 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25766 chi hbad
                ·
                  exact fin15Anchored_clause25767 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25768 chi hbad
                ·
                  exact fin15Anchored_clause25769 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25770 chi hbad
                ·
                  exact fin15Anchored_clause25771 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25772 chi hbad
                ·
                  exact fin15Anchored_clause25773 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25774 chi hbad
                ·
                  exact fin15Anchored_clause25775 chi hbad
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
                  exact fin15Anchored_clause25776 chi hbad
                ·
                  exact fin15Anchored_clause25777 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25778 chi hbad
                ·
                  exact fin15Anchored_clause25779 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25780 chi hbad
                ·
                  exact fin15Anchored_clause25781 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25782 chi hbad
                ·
                  exact fin15Anchored_clause25783 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25784 chi hbad
                ·
                  exact fin15Anchored_clause25785 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25786 chi hbad
                ·
                  exact fin15Anchored_clause25787 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25788 chi hbad
                ·
                  exact fin15Anchored_clause25789 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25790 chi hbad
                ·
                  exact fin15Anchored_clause25791 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25792 chi hbad
                ·
                  exact fin15Anchored_clause25793 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25794 chi hbad
                ·
                  exact fin15Anchored_clause25795 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25796 chi hbad
                ·
                  exact fin15Anchored_clause25797 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25798 chi hbad
                ·
                  exact fin15Anchored_clause25799 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25800 chi hbad
                ·
                  exact fin15Anchored_clause25801 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25802 chi hbad
                ·
                  exact fin15Anchored_clause25803 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25804 chi hbad
                ·
                  exact fin15Anchored_clause25805 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25806 chi hbad
                ·
                  exact fin15Anchored_clause25807 chi hbad
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
                exact fin15Anchored_clause25808 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25809 chi hbad
                ·
                  exact fin15Anchored_clause25810 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25811 chi hbad
                ·
                  exact fin15Anchored_clause25812 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25813 chi hbad
                ·
                  exact fin15Anchored_clause25814 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25815 chi hbad
                ·
                  exact fin15Anchored_clause25816 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25817 chi hbad
                ·
                  exact fin15Anchored_clause25818 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25819 chi hbad
                ·
                  exact fin15Anchored_clause25820 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25821 chi hbad
                ·
                  exact fin15Anchored_clause25822 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25823 chi hbad
                ·
                  exact fin15Anchored_clause25824 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25825 chi hbad
                ·
                  exact fin15Anchored_clause25826 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25827 chi hbad
                ·
                  exact fin15Anchored_clause25828 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25829 chi hbad
                ·
                  exact fin15Anchored_clause25830 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25831 chi hbad
                ·
                  exact fin15Anchored_clause25832 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25833 chi hbad
                ·
                  exact fin15Anchored_clause25834 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25835 chi hbad
                ·
                  exact fin15Anchored_clause25836 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25837 chi hbad
                ·
                  exact fin15Anchored_clause25838 chi hbad
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
                  exact fin15Anchored_clause25839 chi hbad
                ·
                  exact fin15Anchored_clause25840 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25841 chi hbad
                ·
                  exact fin15Anchored_clause25842 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25843 chi hbad
                ·
                  exact fin15Anchored_clause25844 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25845 chi hbad
                ·
                  exact fin15Anchored_clause25846 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25847 chi hbad
                ·
                  exact fin15Anchored_clause25848 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25849 chi hbad
                ·
                  exact fin15Anchored_clause25850 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25851 chi hbad
                ·
                  exact fin15Anchored_clause25852 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25853 chi hbad
                ·
                  exact fin15Anchored_clause25854 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25855 chi hbad
                ·
                  exact fin15Anchored_clause25856 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25857 chi hbad
                ·
                  exact fin15Anchored_clause25858 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25859 chi hbad
                ·
                  exact fin15Anchored_clause25860 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25861 chi hbad
                ·
                  exact fin15Anchored_clause25862 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25863 chi hbad
                ·
                  exact fin15Anchored_clause25864 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25865 chi hbad
                ·
                  exact fin15Anchored_clause25866 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25867 chi hbad
                ·
                  exact fin15Anchored_clause25868 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25869 chi hbad
                ·
                  exact fin15Anchored_clause25870 chi hbad
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
                exact fin15Anchored_clause25871 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25872 chi hbad
                ·
                  exact fin15Anchored_clause25873 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25874 chi hbad
                ·
                  exact fin15Anchored_clause25875 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25876 chi hbad
                ·
                  exact fin15Anchored_clause25877 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25878 chi hbad
                ·
                  exact fin15Anchored_clause25879 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25880 chi hbad
                ·
                  exact fin15Anchored_clause25881 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25882 chi hbad
                ·
                  exact fin15Anchored_clause25883 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25884 chi hbad
                ·
                  exact fin15Anchored_clause25885 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25886 chi hbad
                ·
                  exact fin15Anchored_clause25887 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25888 chi hbad
                ·
                  exact fin15Anchored_clause25889 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25890 chi hbad
                ·
                  exact fin15Anchored_clause25891 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25892 chi hbad
                ·
                  exact fin15Anchored_clause25893 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25894 chi hbad
                ·
                  exact fin15Anchored_clause25895 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25896 chi hbad
                ·
                  exact fin15Anchored_clause25897 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25898 chi hbad
                ·
                  exact fin15Anchored_clause25899 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25900 chi hbad
                ·
                  exact fin15Anchored_clause25901 chi hbad
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
                  exact fin15Anchored_clause25902 chi hbad
                ·
                  exact fin15Anchored_clause25903 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25904 chi hbad
                ·
                  exact fin15Anchored_clause25905 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25906 chi hbad
                ·
                  exact fin15Anchored_clause25907 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25908 chi hbad
                ·
                  exact fin15Anchored_clause25909 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25910 chi hbad
                ·
                  exact fin15Anchored_clause25911 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25912 chi hbad
                ·
                  exact fin15Anchored_clause25913 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25914 chi hbad
                ·
                  exact fin15Anchored_clause25915 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25916 chi hbad
                ·
                  exact fin15Anchored_clause25917 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25918 chi hbad
                ·
                  exact fin15Anchored_clause25919 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25920 chi hbad
                ·
                  exact fin15Anchored_clause25921 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25922 chi hbad
                ·
                  exact fin15Anchored_clause25923 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25924 chi hbad
                ·
                  exact fin15Anchored_clause25925 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25926 chi hbad
                ·
                  exact fin15Anchored_clause25927 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25928 chi hbad
                ·
                  exact fin15Anchored_clause25929 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25930 chi hbad
                ·
                  exact fin15Anchored_clause25931 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25932 chi hbad
                ·
                  exact fin15Anchored_clause25933 chi hbad
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
                exact fin15Anchored_clause25934 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25935 chi hbad
                ·
                  exact fin15Anchored_clause25936 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25937 chi hbad
                ·
                  exact fin15Anchored_clause25938 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25939 chi hbad
                ·
                  exact fin15Anchored_clause25940 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25941 chi hbad
                ·
                  exact fin15Anchored_clause25942 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25943 chi hbad
                ·
                  exact fin15Anchored_clause25944 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25945 chi hbad
                ·
                  exact fin15Anchored_clause25946 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25947 chi hbad
                ·
                  exact fin15Anchored_clause25948 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25949 chi hbad
                ·
                  exact fin15Anchored_clause25950 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25951 chi hbad
                ·
                  exact fin15Anchored_clause25952 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25953 chi hbad
                ·
                  exact fin15Anchored_clause25954 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25955 chi hbad
                ·
                  exact fin15Anchored_clause25956 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25957 chi hbad
                ·
                  exact fin15Anchored_clause25958 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25959 chi hbad
                ·
                  exact fin15Anchored_clause25960 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25961 chi hbad
                ·
                  exact fin15Anchored_clause25962 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25963 chi hbad
                ·
                  exact fin15Anchored_clause25964 chi hbad
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
                  exact fin15Anchored_clause25965 chi hbad
                ·
                  exact fin15Anchored_clause25966 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25967 chi hbad
                ·
                  exact fin15Anchored_clause25968 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25969 chi hbad
                ·
                  exact fin15Anchored_clause25970 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25971 chi hbad
                ·
                  exact fin15Anchored_clause25972 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25973 chi hbad
                ·
                  exact fin15Anchored_clause25974 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25975 chi hbad
                ·
                  exact fin15Anchored_clause25976 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25977 chi hbad
                ·
                  exact fin15Anchored_clause25978 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25979 chi hbad
                ·
                  exact fin15Anchored_clause25980 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25981 chi hbad
                ·
                  exact fin15Anchored_clause25982 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25983 chi hbad
                ·
                  exact fin15Anchored_clause25984 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25985 chi hbad
                ·
                  exact fin15Anchored_clause25986 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25987 chi hbad
                ·
                  exact fin15Anchored_clause25988 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25989 chi hbad
                ·
                  exact fin15Anchored_clause25990 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25991 chi hbad
                ·
                  exact fin15Anchored_clause25992 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25993 chi hbad
                ·
                  exact fin15Anchored_clause25994 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause25995 chi hbad
                ·
                  exact fin15Anchored_clause25996 chi hbad

end ErdosSzekeres

end
