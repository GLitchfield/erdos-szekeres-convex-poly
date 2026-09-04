module

public import ErdosSzekeres.Fin15AnchoredClauseChunk143
public import ErdosSzekeres.Fin15AnchoredClauseChunk144
public import ErdosSzekeres.Fin15AnchoredClauseChunk145

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 073. -/

theorem fin15Anchored_rejectSemanticSegment073
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom2433 chi ∧
      ¬Fin15AnchoredAtom0624 chi) ∨
      ((Fin15AnchoredAtom2433 chi ∧
      ¬Fin15AnchoredAtom0625 chi) ∨
      (Fin15AnchoredAtom2433 chi ∧
      ¬Fin15AnchoredAtom0652 chi))) ∨
      (((Fin15AnchoredAtom2433 chi ∧
      ¬Fin15AnchoredAtom0761 chi) ∨
      (Fin15AnchoredAtom2433 chi ∧
      ¬Fin15AnchoredAtom1432 chi)) ∨
      ((¬Fin15AnchoredAtom2433 chi ∧
      Fin15AnchoredAtom0624 chi ∧
      Fin15AnchoredAtom0625 chi ∧
      Fin15AnchoredAtom0652 chi ∧
      Fin15AnchoredAtom0761 chi ∧
      Fin15AnchoredAtom1432 chi) ∨
      (Fin15AnchoredAtom2434 chi ∧
      ¬Fin15AnchoredAtom0624 chi)))) ∨
      ((((Fin15AnchoredAtom2434 chi ∧
      ¬Fin15AnchoredAtom0626 chi) ∨
      (Fin15AnchoredAtom2434 chi ∧
      ¬Fin15AnchoredAtom0653 chi)) ∨
      ((Fin15AnchoredAtom2434 chi ∧
      ¬Fin15AnchoredAtom0762 chi) ∨
      (Fin15AnchoredAtom2434 chi ∧
      ¬Fin15AnchoredAtom1433 chi))) ∨
      (((¬Fin15AnchoredAtom2434 chi ∧
      Fin15AnchoredAtom0624 chi ∧
      Fin15AnchoredAtom0626 chi ∧
      Fin15AnchoredAtom0653 chi ∧
      Fin15AnchoredAtom0762 chi ∧
      Fin15AnchoredAtom1433 chi) ∨
      (Fin15AnchoredAtom2435 chi ∧
      ¬Fin15AnchoredAtom0625 chi)) ∨
      ((Fin15AnchoredAtom2435 chi ∧
      ¬Fin15AnchoredAtom0626 chi) ∨
      (Fin15AnchoredAtom2435 chi ∧
      ¬Fin15AnchoredAtom0654 chi))))) ∨
      (((((Fin15AnchoredAtom2435 chi ∧
      ¬Fin15AnchoredAtom0763 chi) ∨
      (Fin15AnchoredAtom2435 chi ∧
      ¬Fin15AnchoredAtom1434 chi)) ∨
      ((¬Fin15AnchoredAtom2435 chi ∧
      Fin15AnchoredAtom0625 chi ∧
      Fin15AnchoredAtom0626 chi ∧
      Fin15AnchoredAtom0654 chi ∧
      Fin15AnchoredAtom0763 chi ∧
      Fin15AnchoredAtom1434 chi) ∨
      (Fin15AnchoredAtom2436 chi ∧
      ¬Fin15AnchoredAtom0627 chi))) ∨
      (((Fin15AnchoredAtom2436 chi ∧
      ¬Fin15AnchoredAtom0628 chi) ∨
      (Fin15AnchoredAtom2436 chi ∧
      ¬Fin15AnchoredAtom0634 chi)) ∨
      ((Fin15AnchoredAtom2436 chi ∧
      ¬Fin15AnchoredAtom0764 chi) ∨
      (Fin15AnchoredAtom2436 chi ∧
      ¬Fin15AnchoredAtom1435 chi)))) ∨
      ((((¬Fin15AnchoredAtom2436 chi ∧
      Fin15AnchoredAtom0627 chi ∧
      Fin15AnchoredAtom0628 chi ∧
      Fin15AnchoredAtom0634 chi ∧
      Fin15AnchoredAtom0764 chi ∧
      Fin15AnchoredAtom1435 chi) ∨
      (Fin15AnchoredAtom2437 chi ∧
      ¬Fin15AnchoredAtom0627 chi)) ∨
      ((Fin15AnchoredAtom2437 chi ∧
      ¬Fin15AnchoredAtom0629 chi) ∨
      (Fin15AnchoredAtom2437 chi ∧
      ¬Fin15AnchoredAtom0635 chi))) ∨
      (((Fin15AnchoredAtom2437 chi ∧
      ¬Fin15AnchoredAtom0765 chi) ∨
      (Fin15AnchoredAtom2437 chi ∧
      ¬Fin15AnchoredAtom1436 chi)) ∨
      ((¬Fin15AnchoredAtom2437 chi ∧
      Fin15AnchoredAtom0627 chi ∧
      Fin15AnchoredAtom0629 chi ∧
      Fin15AnchoredAtom0635 chi ∧
      Fin15AnchoredAtom0765 chi ∧
      Fin15AnchoredAtom1436 chi) ∨
      (Fin15AnchoredAtom2439 chi ∧
      ¬Fin15AnchoredAtom0627 chi)))))) ∨
      ((((((Fin15AnchoredAtom2439 chi ∧
      ¬Fin15AnchoredAtom0631 chi) ∨
      (Fin15AnchoredAtom2439 chi ∧
      ¬Fin15AnchoredAtom0637 chi)) ∨
      ((Fin15AnchoredAtom2439 chi ∧
      ¬Fin15AnchoredAtom0767 chi) ∨
      (Fin15AnchoredAtom2439 chi ∧
      ¬Fin15AnchoredAtom1438 chi))) ∨
      (((¬Fin15AnchoredAtom2439 chi ∧
      Fin15AnchoredAtom0627 chi ∧
      Fin15AnchoredAtom0631 chi ∧
      Fin15AnchoredAtom0637 chi ∧
      Fin15AnchoredAtom0767 chi ∧
      Fin15AnchoredAtom1438 chi) ∨
      (Fin15AnchoredAtom2440 chi ∧
      ¬Fin15AnchoredAtom0627 chi)) ∨
      ((Fin15AnchoredAtom2440 chi ∧
      ¬Fin15AnchoredAtom0632 chi) ∨
      (Fin15AnchoredAtom2440 chi ∧
      ¬Fin15AnchoredAtom0638 chi)))) ∨
      ((((Fin15AnchoredAtom2440 chi ∧
      ¬Fin15AnchoredAtom0768 chi) ∨
      (Fin15AnchoredAtom2440 chi ∧
      ¬Fin15AnchoredAtom1439 chi)) ∨
      ((¬Fin15AnchoredAtom2440 chi ∧
      Fin15AnchoredAtom0627 chi ∧
      Fin15AnchoredAtom0632 chi ∧
      Fin15AnchoredAtom0638 chi ∧
      Fin15AnchoredAtom0768 chi ∧
      Fin15AnchoredAtom1439 chi) ∨
      (Fin15AnchoredAtom2441 chi ∧
      ¬Fin15AnchoredAtom0627 chi))) ∨
      (((Fin15AnchoredAtom2441 chi ∧
      ¬Fin15AnchoredAtom0633 chi) ∨
      (Fin15AnchoredAtom2441 chi ∧
      ¬Fin15AnchoredAtom0639 chi)) ∨
      ((Fin15AnchoredAtom2441 chi ∧
      ¬Fin15AnchoredAtom0769 chi) ∨
      (Fin15AnchoredAtom2441 chi ∧
      ¬Fin15AnchoredAtom1440 chi))))) ∨
      (((((¬Fin15AnchoredAtom2441 chi ∧
      Fin15AnchoredAtom0627 chi ∧
      Fin15AnchoredAtom0633 chi ∧
      Fin15AnchoredAtom0639 chi ∧
      Fin15AnchoredAtom0769 chi ∧
      Fin15AnchoredAtom1440 chi) ∨
      (Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom0628 chi)) ∨
      ((Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom0629 chi) ∨
      (Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom0640 chi))) ∨
      (((Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom0770 chi) ∨
      (Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom1441 chi)) ∨
      ((¬Fin15AnchoredAtom2442 chi ∧
      Fin15AnchoredAtom0628 chi ∧
      Fin15AnchoredAtom0629 chi ∧
      Fin15AnchoredAtom0640 chi ∧
      Fin15AnchoredAtom0770 chi ∧
      Fin15AnchoredAtom1441 chi) ∨
      (Fin15AnchoredAtom2443 chi ∧
      ¬Fin15AnchoredAtom0628 chi)))) ∨
      ((((Fin15AnchoredAtom2443 chi ∧
      ¬Fin15AnchoredAtom0630 chi) ∨
      (Fin15AnchoredAtom2443 chi ∧
      ¬Fin15AnchoredAtom0641 chi)) ∨
      ((Fin15AnchoredAtom2443 chi ∧
      ¬Fin15AnchoredAtom0771 chi) ∨
      (Fin15AnchoredAtom2443 chi ∧
      ¬Fin15AnchoredAtom1442 chi))) ∨
      (((¬Fin15AnchoredAtom2443 chi ∧
      Fin15AnchoredAtom0628 chi ∧
      Fin15AnchoredAtom0630 chi ∧
      Fin15AnchoredAtom0641 chi ∧
      Fin15AnchoredAtom0771 chi ∧
      Fin15AnchoredAtom1442 chi) ∨
      (Fin15AnchoredAtom2444 chi ∧
      ¬Fin15AnchoredAtom0628 chi)) ∨
      ((Fin15AnchoredAtom2444 chi ∧
      ¬Fin15AnchoredAtom0631 chi) ∨
      (Fin15AnchoredAtom2444 chi ∧
      ¬Fin15AnchoredAtom0642 chi))))))) ∨
      ((((((Fin15AnchoredAtom2444 chi ∧
      ¬Fin15AnchoredAtom0772 chi) ∨
      ((Fin15AnchoredAtom2444 chi ∧
      ¬Fin15AnchoredAtom1443 chi) ∨
      (¬Fin15AnchoredAtom2444 chi ∧
      Fin15AnchoredAtom0628 chi ∧
      Fin15AnchoredAtom0631 chi ∧
      Fin15AnchoredAtom0642 chi ∧
      Fin15AnchoredAtom0772 chi ∧
      Fin15AnchoredAtom1443 chi))) ∨
      (((Fin15AnchoredAtom2445 chi ∧
      ¬Fin15AnchoredAtom0628 chi) ∨
      (Fin15AnchoredAtom2445 chi ∧
      ¬Fin15AnchoredAtom0632 chi)) ∨
      ((Fin15AnchoredAtom2445 chi ∧
      ¬Fin15AnchoredAtom0643 chi) ∨
      (Fin15AnchoredAtom2445 chi ∧
      ¬Fin15AnchoredAtom0773 chi)))) ∨
      ((((Fin15AnchoredAtom2445 chi ∧
      ¬Fin15AnchoredAtom1444 chi) ∨
      (¬Fin15AnchoredAtom2445 chi ∧
      Fin15AnchoredAtom0628 chi ∧
      Fin15AnchoredAtom0632 chi ∧
      Fin15AnchoredAtom0643 chi ∧
      Fin15AnchoredAtom0773 chi ∧
      Fin15AnchoredAtom1444 chi)) ∨
      ((Fin15AnchoredAtom2446 chi ∧
      ¬Fin15AnchoredAtom0628 chi) ∨
      (Fin15AnchoredAtom2446 chi ∧
      ¬Fin15AnchoredAtom0633 chi))) ∨
      (((Fin15AnchoredAtom2446 chi ∧
      ¬Fin15AnchoredAtom0644 chi) ∨
      (Fin15AnchoredAtom2446 chi ∧
      ¬Fin15AnchoredAtom0774 chi)) ∨
      ((Fin15AnchoredAtom2446 chi ∧
      ¬Fin15AnchoredAtom1445 chi) ∨
      (¬Fin15AnchoredAtom2446 chi ∧
      Fin15AnchoredAtom0628 chi ∧
      Fin15AnchoredAtom0633 chi ∧
      Fin15AnchoredAtom0644 chi ∧
      Fin15AnchoredAtom0774 chi ∧
      Fin15AnchoredAtom1445 chi))))) ∨
      (((((Fin15AnchoredAtom2447 chi ∧
      ¬Fin15AnchoredAtom0629 chi) ∨
      (Fin15AnchoredAtom2447 chi ∧
      ¬Fin15AnchoredAtom0630 chi)) ∨
      ((Fin15AnchoredAtom2447 chi ∧
      ¬Fin15AnchoredAtom0645 chi) ∨
      (Fin15AnchoredAtom2447 chi ∧
      ¬Fin15AnchoredAtom0775 chi))) ∨
      (((Fin15AnchoredAtom2447 chi ∧
      ¬Fin15AnchoredAtom1446 chi) ∨
      (¬Fin15AnchoredAtom2447 chi ∧
      Fin15AnchoredAtom0629 chi ∧
      Fin15AnchoredAtom0630 chi ∧
      Fin15AnchoredAtom0645 chi ∧
      Fin15AnchoredAtom0775 chi ∧
      Fin15AnchoredAtom1446 chi)) ∨
      ((Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom0629 chi) ∨
      (Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom0631 chi)))) ∨
      ((((Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom0646 chi) ∨
      (Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom0776 chi)) ∨
      ((Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom1447 chi) ∨
      (¬Fin15AnchoredAtom2448 chi ∧
      Fin15AnchoredAtom0629 chi ∧
      Fin15AnchoredAtom0631 chi ∧
      Fin15AnchoredAtom0646 chi ∧
      Fin15AnchoredAtom0776 chi ∧
      Fin15AnchoredAtom1447 chi))) ∨
      (((Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom0629 chi) ∨
      (Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom0632 chi)) ∨
      ((Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom0647 chi) ∨
      (Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom0777 chi)))))) ∨
      ((((((Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom1448 chi) ∨
      (¬Fin15AnchoredAtom2449 chi ∧
      Fin15AnchoredAtom0629 chi ∧
      Fin15AnchoredAtom0632 chi ∧
      Fin15AnchoredAtom0647 chi ∧
      Fin15AnchoredAtom0777 chi ∧
      Fin15AnchoredAtom1448 chi)) ∨
      ((Fin15AnchoredAtom2450 chi ∧
      ¬Fin15AnchoredAtom0629 chi) ∨
      (Fin15AnchoredAtom2450 chi ∧
      ¬Fin15AnchoredAtom0633 chi))) ∨
      (((Fin15AnchoredAtom2450 chi ∧
      ¬Fin15AnchoredAtom0648 chi) ∨
      (Fin15AnchoredAtom2450 chi ∧
      ¬Fin15AnchoredAtom0778 chi)) ∨
      ((Fin15AnchoredAtom2450 chi ∧
      ¬Fin15AnchoredAtom1449 chi) ∨
      (¬Fin15AnchoredAtom2450 chi ∧
      Fin15AnchoredAtom0629 chi ∧
      Fin15AnchoredAtom0633 chi ∧
      Fin15AnchoredAtom0648 chi ∧
      Fin15AnchoredAtom0778 chi ∧
      Fin15AnchoredAtom1449 chi)))) ∨
      ((((Fin15AnchoredAtom2451 chi ∧
      ¬Fin15AnchoredAtom0631 chi) ∨
      (Fin15AnchoredAtom2451 chi ∧
      ¬Fin15AnchoredAtom0649 chi)) ∨
      ((Fin15AnchoredAtom2451 chi ∧
      ¬Fin15AnchoredAtom0779 chi) ∨
      (Fin15AnchoredAtom2452 chi ∧
      ¬Fin15AnchoredAtom0632 chi))) ∨
      (((Fin15AnchoredAtom2452 chi ∧
      ¬Fin15AnchoredAtom0780 chi) ∨
      (Fin15AnchoredAtom2453 chi ∧
      ¬Fin15AnchoredAtom0630 chi)) ∨
      ((Fin15AnchoredAtom2453 chi ∧
      ¬Fin15AnchoredAtom0633 chi) ∨
      (Fin15AnchoredAtom2453 chi ∧
      ¬Fin15AnchoredAtom0651 chi))))) ∨
      (((((Fin15AnchoredAtom2453 chi ∧
      ¬Fin15AnchoredAtom0781 chi) ∨
      (Fin15AnchoredAtom2453 chi ∧
      ¬Fin15AnchoredAtom1452 chi)) ∨
      ((¬Fin15AnchoredAtom2453 chi ∧
      Fin15AnchoredAtom0630 chi ∧
      Fin15AnchoredAtom0633 chi ∧
      Fin15AnchoredAtom0651 chi ∧
      Fin15AnchoredAtom0781 chi ∧
      Fin15AnchoredAtom1452 chi) ∨
      (Fin15AnchoredAtom2454 chi ∧
      ¬Fin15AnchoredAtom0631 chi))) ∨
      (((Fin15AnchoredAtom2454 chi ∧
      ¬Fin15AnchoredAtom0632 chi) ∨
      (Fin15AnchoredAtom2454 chi ∧
      ¬Fin15AnchoredAtom0652 chi)) ∨
      ((Fin15AnchoredAtom2454 chi ∧
      ¬Fin15AnchoredAtom0782 chi) ∨
      (Fin15AnchoredAtom2454 chi ∧
      ¬Fin15AnchoredAtom1453 chi)))) ∨
      ((((¬Fin15AnchoredAtom2454 chi ∧
      Fin15AnchoredAtom0631 chi ∧
      Fin15AnchoredAtom0632 chi ∧
      Fin15AnchoredAtom0652 chi ∧
      Fin15AnchoredAtom0782 chi ∧
      Fin15AnchoredAtom1453 chi) ∨
      (Fin15AnchoredAtom2455 chi ∧
      ¬Fin15AnchoredAtom0631 chi)) ∨
      ((Fin15AnchoredAtom2455 chi ∧
      ¬Fin15AnchoredAtom0633 chi) ∨
      (Fin15AnchoredAtom2455 chi ∧
      ¬Fin15AnchoredAtom0653 chi))) ∨
      (((Fin15AnchoredAtom2455 chi ∧
      ¬Fin15AnchoredAtom0783 chi) ∨
      (Fin15AnchoredAtom2455 chi ∧
      ¬Fin15AnchoredAtom1454 chi)) ∨
      ((¬Fin15AnchoredAtom2455 chi ∧
      Fin15AnchoredAtom0631 chi ∧
      Fin15AnchoredAtom0633 chi ∧
      Fin15AnchoredAtom0653 chi ∧
      Fin15AnchoredAtom0783 chi ∧
      Fin15AnchoredAtom1454 chi) ∨
      (Fin15AnchoredAtom2456 chi ∧
      ¬Fin15AnchoredAtom0632 chi)))))))) ∨
      (((((((Fin15AnchoredAtom2456 chi ∧
      ¬Fin15AnchoredAtom0633 chi) ∨
      ((Fin15AnchoredAtom2456 chi ∧
      ¬Fin15AnchoredAtom0654 chi) ∨
      (Fin15AnchoredAtom2456 chi ∧
      ¬Fin15AnchoredAtom0784 chi))) ∨
      (((Fin15AnchoredAtom2456 chi ∧
      ¬Fin15AnchoredAtom1455 chi) ∨
      (¬Fin15AnchoredAtom2456 chi ∧
      Fin15AnchoredAtom0632 chi ∧
      Fin15AnchoredAtom0633 chi ∧
      Fin15AnchoredAtom0654 chi ∧
      Fin15AnchoredAtom0784 chi ∧
      Fin15AnchoredAtom1455 chi)) ∨
      ((Fin15AnchoredAtom2457 chi ∧
      ¬Fin15AnchoredAtom0634 chi) ∨
      (Fin15AnchoredAtom2457 chi ∧
      ¬Fin15AnchoredAtom0635 chi)))) ∨
      ((((Fin15AnchoredAtom2457 chi ∧
      ¬Fin15AnchoredAtom0640 chi) ∨
      (Fin15AnchoredAtom2457 chi ∧
      ¬Fin15AnchoredAtom0785 chi)) ∨
      ((Fin15AnchoredAtom2457 chi ∧
      ¬Fin15AnchoredAtom1456 chi) ∨
      (¬Fin15AnchoredAtom2457 chi ∧
      Fin15AnchoredAtom0634 chi ∧
      Fin15AnchoredAtom0635 chi ∧
      Fin15AnchoredAtom0640 chi ∧
      Fin15AnchoredAtom0785 chi ∧
      Fin15AnchoredAtom1456 chi))) ∨
      (((Fin15AnchoredAtom2459 chi ∧
      ¬Fin15AnchoredAtom0634 chi) ∨
      (Fin15AnchoredAtom2459 chi ∧
      ¬Fin15AnchoredAtom0637 chi)) ∨
      ((Fin15AnchoredAtom2459 chi ∧
      ¬Fin15AnchoredAtom0642 chi) ∨
      (Fin15AnchoredAtom2459 chi ∧
      ¬Fin15AnchoredAtom0787 chi))))) ∨
      (((((Fin15AnchoredAtom2459 chi ∧
      ¬Fin15AnchoredAtom1458 chi) ∨
      (¬Fin15AnchoredAtom2459 chi ∧
      Fin15AnchoredAtom0634 chi ∧
      Fin15AnchoredAtom0637 chi ∧
      Fin15AnchoredAtom0642 chi ∧
      Fin15AnchoredAtom0787 chi ∧
      Fin15AnchoredAtom1458 chi)) ∨
      ((Fin15AnchoredAtom2460 chi ∧
      ¬Fin15AnchoredAtom0634 chi) ∨
      (Fin15AnchoredAtom2460 chi ∧
      ¬Fin15AnchoredAtom0638 chi))) ∨
      (((Fin15AnchoredAtom2460 chi ∧
      ¬Fin15AnchoredAtom0643 chi) ∨
      (Fin15AnchoredAtom2460 chi ∧
      ¬Fin15AnchoredAtom0788 chi)) ∨
      ((Fin15AnchoredAtom2460 chi ∧
      ¬Fin15AnchoredAtom1459 chi) ∨
      (¬Fin15AnchoredAtom2460 chi ∧
      Fin15AnchoredAtom0634 chi ∧
      Fin15AnchoredAtom0638 chi ∧
      Fin15AnchoredAtom0643 chi ∧
      Fin15AnchoredAtom0788 chi ∧
      Fin15AnchoredAtom1459 chi)))) ∨
      ((((Fin15AnchoredAtom2461 chi ∧
      ¬Fin15AnchoredAtom0634 chi) ∨
      (Fin15AnchoredAtom2461 chi ∧
      ¬Fin15AnchoredAtom0639 chi)) ∨
      ((Fin15AnchoredAtom2461 chi ∧
      ¬Fin15AnchoredAtom0644 chi) ∨
      (Fin15AnchoredAtom2461 chi ∧
      ¬Fin15AnchoredAtom0789 chi))) ∨
      (((¬Fin15AnchoredAtom2461 chi ∧
      Fin15AnchoredAtom0634 chi ∧
      Fin15AnchoredAtom0639 chi ∧
      Fin15AnchoredAtom0644 chi ∧
      Fin15AnchoredAtom0789 chi ∧
      Fin15AnchoredAtom1460 chi) ∨
      (Fin15AnchoredAtom2463 chi ∧
      ¬Fin15AnchoredAtom0635 chi)) ∨
      ((Fin15AnchoredAtom2463 chi ∧
      ¬Fin15AnchoredAtom0637 chi) ∨
      (Fin15AnchoredAtom2463 chi ∧
      ¬Fin15AnchoredAtom0646 chi)))))) ∨
      ((((((Fin15AnchoredAtom2463 chi ∧
      ¬Fin15AnchoredAtom0791 chi) ∨
      (Fin15AnchoredAtom2463 chi ∧
      ¬Fin15AnchoredAtom1462 chi)) ∨
      ((¬Fin15AnchoredAtom2463 chi ∧
      Fin15AnchoredAtom0635 chi ∧
      Fin15AnchoredAtom0637 chi ∧
      Fin15AnchoredAtom0646 chi ∧
      Fin15AnchoredAtom0791 chi ∧
      Fin15AnchoredAtom1462 chi) ∨
      (Fin15AnchoredAtom2464 chi ∧
      ¬Fin15AnchoredAtom0635 chi))) ∨
      (((Fin15AnchoredAtom2464 chi ∧
      ¬Fin15AnchoredAtom0638 chi) ∨
      (Fin15AnchoredAtom2464 chi ∧
      ¬Fin15AnchoredAtom0647 chi)) ∨
      ((Fin15AnchoredAtom2464 chi ∧
      ¬Fin15AnchoredAtom0792 chi) ∨
      (¬Fin15AnchoredAtom2464 chi ∧
      Fin15AnchoredAtom0635 chi ∧
      Fin15AnchoredAtom0638 chi ∧
      Fin15AnchoredAtom0647 chi ∧
      Fin15AnchoredAtom0792 chi ∧
      Fin15AnchoredAtom1463 chi)))) ∨
      ((((Fin15AnchoredAtom2465 chi ∧
      ¬Fin15AnchoredAtom0635 chi) ∨
      (Fin15AnchoredAtom2465 chi ∧
      ¬Fin15AnchoredAtom0639 chi)) ∨
      ((Fin15AnchoredAtom2465 chi ∧
      ¬Fin15AnchoredAtom0648 chi) ∨
      (Fin15AnchoredAtom2465 chi ∧
      ¬Fin15AnchoredAtom0793 chi))) ∨
      (((¬Fin15AnchoredAtom2465 chi ∧
      Fin15AnchoredAtom0635 chi ∧
      Fin15AnchoredAtom0639 chi ∧
      Fin15AnchoredAtom0648 chi ∧
      Fin15AnchoredAtom0793 chi ∧
      Fin15AnchoredAtom1464 chi) ∨
      (Fin15AnchoredAtom2469 chi ∧
      ¬Fin15AnchoredAtom0637 chi)) ∨
      ((Fin15AnchoredAtom2469 chi ∧
      ¬Fin15AnchoredAtom0638 chi) ∨
      (Fin15AnchoredAtom2469 chi ∧
      ¬Fin15AnchoredAtom0652 chi))))) ∨
      (((((Fin15AnchoredAtom2469 chi ∧
      ¬Fin15AnchoredAtom0797 chi) ∨
      (¬Fin15AnchoredAtom2469 chi ∧
      Fin15AnchoredAtom0637 chi ∧
      Fin15AnchoredAtom0638 chi ∧
      Fin15AnchoredAtom0652 chi ∧
      Fin15AnchoredAtom0797 chi ∧
      Fin15AnchoredAtom1468 chi)) ∨
      ((Fin15AnchoredAtom2470 chi ∧
      ¬Fin15AnchoredAtom0637 chi) ∨
      (Fin15AnchoredAtom2470 chi ∧
      ¬Fin15AnchoredAtom0639 chi))) ∨
      (((Fin15AnchoredAtom2470 chi ∧
      ¬Fin15AnchoredAtom0653 chi) ∨
      (Fin15AnchoredAtom2470 chi ∧
      ¬Fin15AnchoredAtom0798 chi)) ∨
      ((¬Fin15AnchoredAtom2470 chi ∧
      Fin15AnchoredAtom0637 chi ∧
      Fin15AnchoredAtom0639 chi ∧
      Fin15AnchoredAtom0653 chi ∧
      Fin15AnchoredAtom0798 chi ∧
      Fin15AnchoredAtom1469 chi) ∨
      (Fin15AnchoredAtom2471 chi ∧
      ¬Fin15AnchoredAtom0638 chi)))) ∨
      ((((Fin15AnchoredAtom2471 chi ∧
      ¬Fin15AnchoredAtom0639 chi) ∨
      (Fin15AnchoredAtom2471 chi ∧
      ¬Fin15AnchoredAtom0654 chi)) ∨
      ((Fin15AnchoredAtom2471 chi ∧
      ¬Fin15AnchoredAtom0799 chi) ∨
      (Fin15AnchoredAtom2471 chi ∧
      ¬Fin15AnchoredAtom1470 chi))) ∨
      (((¬Fin15AnchoredAtom2471 chi ∧
      Fin15AnchoredAtom0638 chi ∧
      Fin15AnchoredAtom0639 chi ∧
      Fin15AnchoredAtom0654 chi ∧
      Fin15AnchoredAtom0799 chi ∧
      Fin15AnchoredAtom1470 chi) ∨
      (Fin15AnchoredAtom2472 chi ∧
      ¬Fin15AnchoredAtom0640 chi)) ∨
      ((Fin15AnchoredAtom2472 chi ∧
      ¬Fin15AnchoredAtom0800 chi) ∨
      (Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom0640 chi))))))) ∨
      ((((((Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom0642 chi) ∨
      ((Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom0646 chi) ∨
      (Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom0801 chi))) ∨
      (((Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom1472 chi) ∨
      (¬Fin15AnchoredAtom2473 chi ∧
      Fin15AnchoredAtom0640 chi ∧
      Fin15AnchoredAtom0642 chi ∧
      Fin15AnchoredAtom0646 chi ∧
      Fin15AnchoredAtom0801 chi ∧
      Fin15AnchoredAtom1472 chi)) ∨
      ((Fin15AnchoredAtom2474 chi ∧
      ¬Fin15AnchoredAtom0640 chi) ∨
      (Fin15AnchoredAtom2474 chi ∧
      ¬Fin15AnchoredAtom0643 chi)))) ∨
      ((((Fin15AnchoredAtom2474 chi ∧
      ¬Fin15AnchoredAtom0647 chi) ∨
      (Fin15AnchoredAtom2474 chi ∧
      ¬Fin15AnchoredAtom0802 chi)) ∨
      ((Fin15AnchoredAtom2474 chi ∧
      ¬Fin15AnchoredAtom1473 chi) ∨
      (¬Fin15AnchoredAtom2474 chi ∧
      Fin15AnchoredAtom0640 chi ∧
      Fin15AnchoredAtom0643 chi ∧
      Fin15AnchoredAtom0647 chi ∧
      Fin15AnchoredAtom0802 chi ∧
      Fin15AnchoredAtom1473 chi))) ∨
      (((Fin15AnchoredAtom2475 chi ∧
      ¬Fin15AnchoredAtom0640 chi) ∨
      (Fin15AnchoredAtom2475 chi ∧
      ¬Fin15AnchoredAtom0644 chi)) ∨
      ((Fin15AnchoredAtom2475 chi ∧
      ¬Fin15AnchoredAtom0648 chi) ∨
      (Fin15AnchoredAtom2475 chi ∧
      ¬Fin15AnchoredAtom0803 chi))))) ∨
      (((((Fin15AnchoredAtom2475 chi ∧
      ¬Fin15AnchoredAtom1474 chi) ∨
      (¬Fin15AnchoredAtom2475 chi ∧
      Fin15AnchoredAtom0640 chi ∧
      Fin15AnchoredAtom0644 chi ∧
      Fin15AnchoredAtom0648 chi ∧
      Fin15AnchoredAtom0803 chi ∧
      Fin15AnchoredAtom1474 chi)) ∨
      ((Fin15AnchoredAtom2476 chi ∧
      ¬Fin15AnchoredAtom0642 chi) ∨
      (Fin15AnchoredAtom2476 chi ∧
      ¬Fin15AnchoredAtom0649 chi))) ∨
      (((Fin15AnchoredAtom2476 chi ∧
      ¬Fin15AnchoredAtom0804 chi) ∨
      (¬Fin15AnchoredAtom2476 chi ∧
      Fin15AnchoredAtom0641 chi ∧
      Fin15AnchoredAtom0642 chi ∧
      Fin15AnchoredAtom0649 chi ∧
      Fin15AnchoredAtom0804 chi ∧
      Fin15AnchoredAtom1475 chi)) ∨
      ((Fin15AnchoredAtom2477 chi ∧
      ¬Fin15AnchoredAtom0641 chi) ∨
      (Fin15AnchoredAtom2477 chi ∧
      ¬Fin15AnchoredAtom0650 chi)))) ∨
      ((((Fin15AnchoredAtom2477 chi ∧
      ¬Fin15AnchoredAtom0805 chi) ∨
      (Fin15AnchoredAtom2477 chi ∧
      ¬Fin15AnchoredAtom1476 chi)) ∨
      ((¬Fin15AnchoredAtom2477 chi ∧
      Fin15AnchoredAtom0641 chi ∧
      Fin15AnchoredAtom0643 chi ∧
      Fin15AnchoredAtom0650 chi ∧
      Fin15AnchoredAtom0805 chi ∧
      Fin15AnchoredAtom1476 chi) ∨
      (Fin15AnchoredAtom2478 chi ∧
      ¬Fin15AnchoredAtom0806 chi))) ∨
      (((Fin15AnchoredAtom2479 chi ∧
      ¬Fin15AnchoredAtom0642 chi) ∨
      (Fin15AnchoredAtom2479 chi ∧
      ¬Fin15AnchoredAtom0643 chi)) ∨
      ((Fin15AnchoredAtom2479 chi ∧
      ¬Fin15AnchoredAtom0652 chi) ∨
      (Fin15AnchoredAtom2479 chi ∧
      ¬Fin15AnchoredAtom0807 chi)))))) ∨
      ((((((Fin15AnchoredAtom2479 chi ∧
      ¬Fin15AnchoredAtom1478 chi) ∨
      (¬Fin15AnchoredAtom2479 chi ∧
      Fin15AnchoredAtom0642 chi ∧
      Fin15AnchoredAtom0643 chi ∧
      Fin15AnchoredAtom0652 chi ∧
      Fin15AnchoredAtom0807 chi ∧
      Fin15AnchoredAtom1478 chi)) ∨
      ((Fin15AnchoredAtom2480 chi ∧
      ¬Fin15AnchoredAtom0642 chi) ∨
      (Fin15AnchoredAtom2480 chi ∧
      ¬Fin15AnchoredAtom0644 chi))) ∨
      (((Fin15AnchoredAtom2480 chi ∧
      ¬Fin15AnchoredAtom0653 chi) ∨
      (Fin15AnchoredAtom2480 chi ∧
      ¬Fin15AnchoredAtom0808 chi)) ∨
      ((Fin15AnchoredAtom2480 chi ∧
      ¬Fin15AnchoredAtom1479 chi) ∨
      (¬Fin15AnchoredAtom2480 chi ∧
      Fin15AnchoredAtom0642 chi ∧
      Fin15AnchoredAtom0644 chi ∧
      Fin15AnchoredAtom0653 chi ∧
      Fin15AnchoredAtom0808 chi ∧
      Fin15AnchoredAtom1479 chi)))) ∨
      ((((Fin15AnchoredAtom2481 chi ∧
      ¬Fin15AnchoredAtom0643 chi) ∨
      (Fin15AnchoredAtom2481 chi ∧
      ¬Fin15AnchoredAtom0644 chi)) ∨
      ((Fin15AnchoredAtom2481 chi ∧
      ¬Fin15AnchoredAtom0654 chi) ∨
      (Fin15AnchoredAtom2481 chi ∧
      ¬Fin15AnchoredAtom0809 chi))) ∨
      (((Fin15AnchoredAtom2481 chi ∧
      ¬Fin15AnchoredAtom1480 chi) ∨
      (¬Fin15AnchoredAtom2481 chi ∧
      Fin15AnchoredAtom0643 chi ∧
      Fin15AnchoredAtom0644 chi ∧
      Fin15AnchoredAtom0654 chi ∧
      Fin15AnchoredAtom0809 chi ∧
      Fin15AnchoredAtom1480 chi)) ∨
      ((Fin15AnchoredAtom2482 chi ∧
      ¬Fin15AnchoredAtom0645 chi) ∨
      (Fin15AnchoredAtom2482 chi ∧
      ¬Fin15AnchoredAtom0646 chi))))) ∨
      (((((Fin15AnchoredAtom2482 chi ∧
      ¬Fin15AnchoredAtom0649 chi) ∨
      (Fin15AnchoredAtom2482 chi ∧
      ¬Fin15AnchoredAtom0810 chi)) ∨
      ((Fin15AnchoredAtom2482 chi ∧
      ¬Fin15AnchoredAtom1481 chi) ∨
      (¬Fin15AnchoredAtom2482 chi ∧
      Fin15AnchoredAtom0645 chi ∧
      Fin15AnchoredAtom0646 chi ∧
      Fin15AnchoredAtom0649 chi ∧
      Fin15AnchoredAtom0810 chi ∧
      Fin15AnchoredAtom1481 chi))) ∨
      (((Fin15AnchoredAtom2483 chi ∧
      ¬Fin15AnchoredAtom0645 chi) ∨
      (Fin15AnchoredAtom2483 chi ∧
      ¬Fin15AnchoredAtom0647 chi)) ∨
      ((Fin15AnchoredAtom2483 chi ∧
      ¬Fin15AnchoredAtom0811 chi) ∨
      (Fin15AnchoredAtom2483 chi ∧
      ¬Fin15AnchoredAtom1482 chi)))) ∨
      ((((¬Fin15AnchoredAtom2483 chi ∧
      Fin15AnchoredAtom0645 chi ∧
      Fin15AnchoredAtom0647 chi ∧
      Fin15AnchoredAtom0650 chi ∧
      Fin15AnchoredAtom0811 chi ∧
      Fin15AnchoredAtom1482 chi) ∨
      (Fin15AnchoredAtom2484 chi ∧
      ¬Fin15AnchoredAtom0648 chi)) ∨
      ((Fin15AnchoredAtom2485 chi ∧
      ¬Fin15AnchoredAtom0646 chi) ∨
      (Fin15AnchoredAtom2485 chi ∧
      ¬Fin15AnchoredAtom0647 chi))) ∨
      (((Fin15AnchoredAtom2485 chi ∧
      ¬Fin15AnchoredAtom0652 chi) ∨
      (Fin15AnchoredAtom2485 chi ∧
      ¬Fin15AnchoredAtom0813 chi)) ∨
      ((Fin15AnchoredAtom2485 chi ∧
      ¬Fin15AnchoredAtom1484 chi) ∨
      (¬Fin15AnchoredAtom2485 chi ∧
      Fin15AnchoredAtom0646 chi ∧
      Fin15AnchoredAtom0647 chi ∧
      Fin15AnchoredAtom0652 chi ∧
      Fin15AnchoredAtom0813 chi ∧
      Fin15AnchoredAtom1484 chi)))))))))) := by
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
                exact fin15Anchored_clause18425 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18426 chi hbad
                ·
                  exact fin15Anchored_clause18427 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18428 chi hbad
                ·
                  exact fin15Anchored_clause18429 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18430 chi hbad
                ·
                  exact fin15Anchored_clause18431 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18432 chi hbad
                ·
                  exact fin15Anchored_clause18433 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18434 chi hbad
                ·
                  exact fin15Anchored_clause18435 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18436 chi hbad
                ·
                  exact fin15Anchored_clause18437 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18438 chi hbad
                ·
                  exact fin15Anchored_clause18439 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18440 chi hbad
                ·
                  exact fin15Anchored_clause18441 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18442 chi hbad
                ·
                  exact fin15Anchored_clause18443 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18444 chi hbad
                ·
                  exact fin15Anchored_clause18445 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18446 chi hbad
                ·
                  exact fin15Anchored_clause18447 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18448 chi hbad
                ·
                  exact fin15Anchored_clause18449 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18450 chi hbad
                ·
                  exact fin15Anchored_clause18451 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18452 chi hbad
                ·
                  exact fin15Anchored_clause18453 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18454 chi hbad
                ·
                  exact fin15Anchored_clause18455 chi hbad
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
                  exact fin15Anchored_clause18456 chi hbad
                ·
                  exact fin15Anchored_clause18457 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18458 chi hbad
                ·
                  exact fin15Anchored_clause18459 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18460 chi hbad
                ·
                  exact fin15Anchored_clause18461 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18462 chi hbad
                ·
                  exact fin15Anchored_clause18463 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18464 chi hbad
                ·
                  exact fin15Anchored_clause18465 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18466 chi hbad
                ·
                  exact fin15Anchored_clause18467 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18468 chi hbad
                ·
                  exact fin15Anchored_clause18469 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18470 chi hbad
                ·
                  exact fin15Anchored_clause18471 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18472 chi hbad
                ·
                  exact fin15Anchored_clause18473 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18474 chi hbad
                ·
                  exact fin15Anchored_clause18475 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18476 chi hbad
                ·
                  exact fin15Anchored_clause18477 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18478 chi hbad
                ·
                  exact fin15Anchored_clause18479 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18480 chi hbad
                ·
                  exact fin15Anchored_clause18481 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18482 chi hbad
                ·
                  exact fin15Anchored_clause18483 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18484 chi hbad
                ·
                  exact fin15Anchored_clause18485 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18486 chi hbad
                ·
                  exact fin15Anchored_clause18487 chi hbad
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
                exact fin15Anchored_clause18488 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18489 chi hbad
                ·
                  exact fin15Anchored_clause18490 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18491 chi hbad
                ·
                  exact fin15Anchored_clause18492 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18493 chi hbad
                ·
                  exact fin15Anchored_clause18494 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18495 chi hbad
                ·
                  exact fin15Anchored_clause18496 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18497 chi hbad
                ·
                  exact fin15Anchored_clause18498 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18499 chi hbad
                ·
                  exact fin15Anchored_clause18500 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18501 chi hbad
                ·
                  exact fin15Anchored_clause18502 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18503 chi hbad
                ·
                  exact fin15Anchored_clause18504 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18505 chi hbad
                ·
                  exact fin15Anchored_clause18506 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18507 chi hbad
                ·
                  exact fin15Anchored_clause18508 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18509 chi hbad
                ·
                  exact fin15Anchored_clause18510 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18511 chi hbad
                ·
                  exact fin15Anchored_clause18512 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18513 chi hbad
                ·
                  exact fin15Anchored_clause18514 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18515 chi hbad
                ·
                  exact fin15Anchored_clause18516 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18517 chi hbad
                ·
                  exact fin15Anchored_clause18518 chi hbad
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
                  exact fin15Anchored_clause18519 chi hbad
                ·
                  exact fin15Anchored_clause18520 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18521 chi hbad
                ·
                  exact fin15Anchored_clause18522 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18523 chi hbad
                ·
                  exact fin15Anchored_clause18524 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18525 chi hbad
                ·
                  exact fin15Anchored_clause18526 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18527 chi hbad
                ·
                  exact fin15Anchored_clause18528 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18529 chi hbad
                ·
                  exact fin15Anchored_clause18530 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18531 chi hbad
                ·
                  exact fin15Anchored_clause18532 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18533 chi hbad
                ·
                  exact fin15Anchored_clause18534 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18535 chi hbad
                ·
                  exact fin15Anchored_clause18536 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18537 chi hbad
                ·
                  exact fin15Anchored_clause18538 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18539 chi hbad
                ·
                  exact fin15Anchored_clause18540 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18541 chi hbad
                ·
                  exact fin15Anchored_clause18542 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18543 chi hbad
                ·
                  exact fin15Anchored_clause18544 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18545 chi hbad
                ·
                  exact fin15Anchored_clause18546 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18547 chi hbad
                ·
                  exact fin15Anchored_clause18548 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18549 chi hbad
                ·
                  exact fin15Anchored_clause18550 chi hbad
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
                exact fin15Anchored_clause18551 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18552 chi hbad
                ·
                  exact fin15Anchored_clause18553 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18554 chi hbad
                ·
                  exact fin15Anchored_clause18555 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18556 chi hbad
                ·
                  exact fin15Anchored_clause18557 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18558 chi hbad
                ·
                  exact fin15Anchored_clause18559 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18560 chi hbad
                ·
                  exact fin15Anchored_clause18561 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18562 chi hbad
                ·
                  exact fin15Anchored_clause18563 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18564 chi hbad
                ·
                  exact fin15Anchored_clause18565 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18566 chi hbad
                ·
                  exact fin15Anchored_clause18567 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18568 chi hbad
                ·
                  exact fin15Anchored_clause18569 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18570 chi hbad
                ·
                  exact fin15Anchored_clause18571 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18572 chi hbad
                ·
                  exact fin15Anchored_clause18573 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18574 chi hbad
                ·
                  exact fin15Anchored_clause18575 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18576 chi hbad
                ·
                  exact fin15Anchored_clause18577 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18578 chi hbad
                ·
                  exact fin15Anchored_clause18579 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18580 chi hbad
                ·
                  exact fin15Anchored_clause18581 chi hbad
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
                  exact fin15Anchored_clause18582 chi hbad
                ·
                  exact fin15Anchored_clause18583 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18584 chi hbad
                ·
                  exact fin15Anchored_clause18585 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18586 chi hbad
                ·
                  exact fin15Anchored_clause18587 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18588 chi hbad
                ·
                  exact fin15Anchored_clause18589 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18590 chi hbad
                ·
                  exact fin15Anchored_clause18591 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18592 chi hbad
                ·
                  exact fin15Anchored_clause18593 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18594 chi hbad
                ·
                  exact fin15Anchored_clause18595 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18596 chi hbad
                ·
                  exact fin15Anchored_clause18597 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18598 chi hbad
                ·
                  exact fin15Anchored_clause18599 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18600 chi hbad
                ·
                  exact fin15Anchored_clause18601 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18602 chi hbad
                ·
                  exact fin15Anchored_clause18603 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18604 chi hbad
                ·
                  exact fin15Anchored_clause18605 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18606 chi hbad
                ·
                  exact fin15Anchored_clause18607 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18608 chi hbad
                ·
                  exact fin15Anchored_clause18609 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18610 chi hbad
                ·
                  exact fin15Anchored_clause18611 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18612 chi hbad
                ·
                  exact fin15Anchored_clause18613 chi hbad
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
                exact fin15Anchored_clause18614 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18615 chi hbad
                ·
                  exact fin15Anchored_clause18616 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18617 chi hbad
                ·
                  exact fin15Anchored_clause18618 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18619 chi hbad
                ·
                  exact fin15Anchored_clause18620 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18621 chi hbad
                ·
                  exact fin15Anchored_clause18622 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18623 chi hbad
                ·
                  exact fin15Anchored_clause18624 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18625 chi hbad
                ·
                  exact fin15Anchored_clause18626 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18627 chi hbad
                ·
                  exact fin15Anchored_clause18628 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18629 chi hbad
                ·
                  exact fin15Anchored_clause18630 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18631 chi hbad
                ·
                  exact fin15Anchored_clause18632 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18633 chi hbad
                ·
                  exact fin15Anchored_clause18634 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18635 chi hbad
                ·
                  exact fin15Anchored_clause18636 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18637 chi hbad
                ·
                  exact fin15Anchored_clause18638 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18639 chi hbad
                ·
                  exact fin15Anchored_clause18640 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18641 chi hbad
                ·
                  exact fin15Anchored_clause18642 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18643 chi hbad
                ·
                  exact fin15Anchored_clause18644 chi hbad
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
                  exact fin15Anchored_clause18645 chi hbad
                ·
                  exact fin15Anchored_clause18646 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18647 chi hbad
                ·
                  exact fin15Anchored_clause18648 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18649 chi hbad
                ·
                  exact fin15Anchored_clause18650 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18651 chi hbad
                ·
                  exact fin15Anchored_clause18652 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18653 chi hbad
                ·
                  exact fin15Anchored_clause18654 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18655 chi hbad
                ·
                  exact fin15Anchored_clause18656 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18657 chi hbad
                ·
                  exact fin15Anchored_clause18658 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18659 chi hbad
                ·
                  exact fin15Anchored_clause18660 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18661 chi hbad
                ·
                  exact fin15Anchored_clause18662 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18663 chi hbad
                ·
                  exact fin15Anchored_clause18664 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18665 chi hbad
                ·
                  exact fin15Anchored_clause18666 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18667 chi hbad
                ·
                  exact fin15Anchored_clause18668 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18669 chi hbad
                ·
                  exact fin15Anchored_clause18670 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18671 chi hbad
                ·
                  exact fin15Anchored_clause18672 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18673 chi hbad
                ·
                  exact fin15Anchored_clause18674 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18675 chi hbad
                ·
                  exact fin15Anchored_clause18676 chi hbad

end ErdosSzekeres

end
