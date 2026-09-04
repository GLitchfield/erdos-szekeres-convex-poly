module

public import ErdosSzekeres.Fin15AnchoredClauseChunk145
public import ErdosSzekeres.Fin15AnchoredClauseChunk146
public import ErdosSzekeres.Fin15AnchoredClauseChunk147

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 074. -/

theorem fin15Anchored_rejectSemanticSegment074
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom2486 chi ∧
      ¬Fin15AnchoredAtom0646 chi) ∨
      ((Fin15AnchoredAtom2486 chi ∧
      ¬Fin15AnchoredAtom0648 chi) ∨
      (Fin15AnchoredAtom2486 chi ∧
      ¬Fin15AnchoredAtom0653 chi))) ∨
      (((Fin15AnchoredAtom2486 chi ∧
      ¬Fin15AnchoredAtom0814 chi) ∨
      (Fin15AnchoredAtom2486 chi ∧
      ¬Fin15AnchoredAtom1485 chi)) ∨
      ((¬Fin15AnchoredAtom2486 chi ∧
      Fin15AnchoredAtom0646 chi ∧
      Fin15AnchoredAtom0648 chi ∧
      Fin15AnchoredAtom0653 chi ∧
      Fin15AnchoredAtom0814 chi ∧
      Fin15AnchoredAtom1485 chi) ∨
      (Fin15AnchoredAtom2487 chi ∧
      ¬Fin15AnchoredAtom0647 chi)))) ∨
      ((((Fin15AnchoredAtom2487 chi ∧
      ¬Fin15AnchoredAtom0648 chi) ∨
      (Fin15AnchoredAtom2487 chi ∧
      ¬Fin15AnchoredAtom0654 chi)) ∨
      ((Fin15AnchoredAtom2487 chi ∧
      ¬Fin15AnchoredAtom0815 chi) ∨
      (Fin15AnchoredAtom2487 chi ∧
      ¬Fin15AnchoredAtom1486 chi))) ∨
      (((¬Fin15AnchoredAtom2487 chi ∧
      Fin15AnchoredAtom0647 chi ∧
      Fin15AnchoredAtom0648 chi ∧
      Fin15AnchoredAtom0654 chi ∧
      Fin15AnchoredAtom0815 chi ∧
      Fin15AnchoredAtom1486 chi) ∨
      (Fin15AnchoredAtom2488 chi ∧
      ¬Fin15AnchoredAtom0652 chi)) ∨
      ((Fin15AnchoredAtom2488 chi ∧
      ¬Fin15AnchoredAtom0816 chi) ∨
      (Fin15AnchoredAtom2488 chi ∧
      ¬Fin15AnchoredAtom1487 chi))))) ∨
      (((((¬Fin15AnchoredAtom2488 chi ∧
      Fin15AnchoredAtom0649 chi ∧
      Fin15AnchoredAtom0650 chi ∧
      Fin15AnchoredAtom0652 chi ∧
      Fin15AnchoredAtom0816 chi ∧
      Fin15AnchoredAtom1487 chi) ∨
      (Fin15AnchoredAtom2489 chi ∧
      ¬Fin15AnchoredAtom0653 chi)) ∨
      ((Fin15AnchoredAtom2490 chi ∧
      ¬Fin15AnchoredAtom0654 chi) ∨
      (Fin15AnchoredAtom2490 chi ∧
      ¬Fin15AnchoredAtom1489 chi))) ∨
      (((¬Fin15AnchoredAtom2490 chi ∧
      Fin15AnchoredAtom0650 chi ∧
      Fin15AnchoredAtom0651 chi ∧
      Fin15AnchoredAtom0654 chi ∧
      Fin15AnchoredAtom0818 chi ∧
      Fin15AnchoredAtom1489 chi) ∨
      (Fin15AnchoredAtom2491 chi ∧
      ¬Fin15AnchoredAtom0652 chi)) ∨
      ((Fin15AnchoredAtom2491 chi ∧
      ¬Fin15AnchoredAtom0653 chi) ∨
      (Fin15AnchoredAtom2491 chi ∧
      ¬Fin15AnchoredAtom0654 chi)))) ∨
      ((((Fin15AnchoredAtom2491 chi ∧
      ¬Fin15AnchoredAtom0819 chi) ∨
      (Fin15AnchoredAtom2491 chi ∧
      ¬Fin15AnchoredAtom1490 chi)) ∨
      ((¬Fin15AnchoredAtom2491 chi ∧
      Fin15AnchoredAtom0652 chi ∧
      Fin15AnchoredAtom0653 chi ∧
      Fin15AnchoredAtom0654 chi ∧
      Fin15AnchoredAtom0819 chi ∧
      Fin15AnchoredAtom1490 chi) ∨
      (Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom0655 chi))) ∨
      (((Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom0656 chi) ∨
      (Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom0664 chi)) ∨
      ((Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom0700 chi) ∨
      (Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom1491 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom2492 chi ∧
      Fin15AnchoredAtom0655 chi ∧
      Fin15AnchoredAtom0656 chi ∧
      Fin15AnchoredAtom0664 chi ∧
      Fin15AnchoredAtom0700 chi ∧
      Fin15AnchoredAtom1491 chi) ∨
      (Fin15AnchoredAtom2493 chi ∧
      ¬Fin15AnchoredAtom0655 chi)) ∨
      ((Fin15AnchoredAtom2493 chi ∧
      ¬Fin15AnchoredAtom0657 chi) ∨
      (Fin15AnchoredAtom2493 chi ∧
      ¬Fin15AnchoredAtom0665 chi))) ∨
      (((Fin15AnchoredAtom2493 chi ∧
      ¬Fin15AnchoredAtom0701 chi) ∨
      (Fin15AnchoredAtom2493 chi ∧
      ¬Fin15AnchoredAtom1492 chi)) ∨
      ((¬Fin15AnchoredAtom2493 chi ∧
      Fin15AnchoredAtom0655 chi ∧
      Fin15AnchoredAtom0657 chi ∧
      Fin15AnchoredAtom0665 chi ∧
      Fin15AnchoredAtom0701 chi ∧
      Fin15AnchoredAtom1492 chi) ∨
      (Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom0655 chi)))) ∨
      ((((Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom0658 chi) ∨
      (Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom0666 chi)) ∨
      ((Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom0702 chi) ∨
      (Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom1493 chi))) ∨
      (((¬Fin15AnchoredAtom2494 chi ∧
      Fin15AnchoredAtom0655 chi ∧
      Fin15AnchoredAtom0658 chi ∧
      Fin15AnchoredAtom0666 chi ∧
      Fin15AnchoredAtom0702 chi ∧
      Fin15AnchoredAtom1493 chi) ∨
      (Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom0655 chi)) ∨
      ((Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom0659 chi) ∨
      (Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom0667 chi))))) ∨
      (((((Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom0703 chi) ∨
      (Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom1494 chi)) ∨
      ((¬Fin15AnchoredAtom2495 chi ∧
      Fin15AnchoredAtom0655 chi ∧
      Fin15AnchoredAtom0659 chi ∧
      Fin15AnchoredAtom0667 chi ∧
      Fin15AnchoredAtom0703 chi ∧
      Fin15AnchoredAtom1494 chi) ∨
      (Fin15AnchoredAtom2496 chi ∧
      ¬Fin15AnchoredAtom0655 chi))) ∨
      (((Fin15AnchoredAtom2496 chi ∧
      ¬Fin15AnchoredAtom0704 chi) ∨
      (Fin15AnchoredAtom2496 chi ∧
      ¬Fin15AnchoredAtom1495 chi)) ∨
      ((¬Fin15AnchoredAtom2496 chi ∧
      Fin15AnchoredAtom0655 chi ∧
      Fin15AnchoredAtom0660 chi ∧
      Fin15AnchoredAtom0668 chi ∧
      Fin15AnchoredAtom0704 chi ∧
      Fin15AnchoredAtom1495 chi) ∨
      (Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom0655 chi)))) ∨
      ((((Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom0661 chi) ∨
      (Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom0669 chi)) ∨
      ((Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom0705 chi) ∨
      (Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom1496 chi))) ∨
      (((¬Fin15AnchoredAtom2497 chi ∧
      Fin15AnchoredAtom0655 chi ∧
      Fin15AnchoredAtom0661 chi ∧
      Fin15AnchoredAtom0669 chi ∧
      Fin15AnchoredAtom0705 chi ∧
      Fin15AnchoredAtom1496 chi) ∨
      (Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom0655 chi)) ∨
      ((Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom0662 chi) ∨
      (Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom0670 chi))))))) ∨
      ((((((Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom0706 chi) ∨
      ((Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom1497 chi) ∨
      (¬Fin15AnchoredAtom2498 chi ∧
      Fin15AnchoredAtom0655 chi ∧
      Fin15AnchoredAtom0662 chi ∧
      Fin15AnchoredAtom0670 chi ∧
      Fin15AnchoredAtom0706 chi ∧
      Fin15AnchoredAtom1497 chi))) ∨
      (((Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom0655 chi) ∨
      (Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom0663 chi)) ∨
      ((Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom0671 chi) ∨
      (Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom0707 chi)))) ∨
      ((((Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom1498 chi) ∨
      (¬Fin15AnchoredAtom2499 chi ∧
      Fin15AnchoredAtom0655 chi ∧
      Fin15AnchoredAtom0663 chi ∧
      Fin15AnchoredAtom0671 chi ∧
      Fin15AnchoredAtom0707 chi ∧
      Fin15AnchoredAtom1498 chi)) ∨
      ((Fin15AnchoredAtom2500 chi ∧
      ¬Fin15AnchoredAtom0656 chi) ∨
      (Fin15AnchoredAtom2500 chi ∧
      ¬Fin15AnchoredAtom0657 chi))) ∨
      (((Fin15AnchoredAtom2500 chi ∧
      ¬Fin15AnchoredAtom0672 chi) ∨
      (Fin15AnchoredAtom2500 chi ∧
      ¬Fin15AnchoredAtom0708 chi)) ∨
      ((Fin15AnchoredAtom2500 chi ∧
      ¬Fin15AnchoredAtom1499 chi) ∨
      (¬Fin15AnchoredAtom2500 chi ∧
      Fin15AnchoredAtom0656 chi ∧
      Fin15AnchoredAtom0657 chi ∧
      Fin15AnchoredAtom0672 chi ∧
      Fin15AnchoredAtom0708 chi ∧
      Fin15AnchoredAtom1499 chi))))) ∨
      (((((Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom0656 chi) ∨
      (Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom0658 chi)) ∨
      ((Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom0673 chi) ∨
      (Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom0709 chi))) ∨
      (((Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom1500 chi) ∨
      (¬Fin15AnchoredAtom2501 chi ∧
      Fin15AnchoredAtom0656 chi ∧
      Fin15AnchoredAtom0658 chi ∧
      Fin15AnchoredAtom0673 chi ∧
      Fin15AnchoredAtom0709 chi ∧
      Fin15AnchoredAtom1500 chi)) ∨
      ((Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom0656 chi) ∨
      (Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom0659 chi)))) ∨
      ((((Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom0674 chi) ∨
      (Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom0710 chi)) ∨
      ((Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom1501 chi) ∨
      (¬Fin15AnchoredAtom2502 chi ∧
      Fin15AnchoredAtom0656 chi ∧
      Fin15AnchoredAtom0659 chi ∧
      Fin15AnchoredAtom0674 chi ∧
      Fin15AnchoredAtom0710 chi ∧
      Fin15AnchoredAtom1501 chi))) ∨
      (((Fin15AnchoredAtom2503 chi ∧
      ¬Fin15AnchoredAtom0656 chi) ∨
      (¬Fin15AnchoredAtom2503 chi ∧
      Fin15AnchoredAtom0656 chi ∧
      Fin15AnchoredAtom0660 chi ∧
      Fin15AnchoredAtom0675 chi ∧
      Fin15AnchoredAtom0711 chi ∧
      Fin15AnchoredAtom1502 chi)) ∨
      ((Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom0656 chi) ∨
      (Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom0661 chi)))))) ∨
      ((((((Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom0676 chi) ∨
      (Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom0712 chi)) ∨
      ((Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom1503 chi) ∨
      (¬Fin15AnchoredAtom2504 chi ∧
      Fin15AnchoredAtom0656 chi ∧
      Fin15AnchoredAtom0661 chi ∧
      Fin15AnchoredAtom0676 chi ∧
      Fin15AnchoredAtom0712 chi ∧
      Fin15AnchoredAtom1503 chi))) ∨
      (((Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom0656 chi) ∨
      (Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom0662 chi)) ∨
      ((Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom0677 chi) ∨
      (Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom0713 chi)))) ∨
      ((((Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom1504 chi) ∨
      (¬Fin15AnchoredAtom2505 chi ∧
      Fin15AnchoredAtom0656 chi ∧
      Fin15AnchoredAtom0662 chi ∧
      Fin15AnchoredAtom0677 chi ∧
      Fin15AnchoredAtom0713 chi ∧
      Fin15AnchoredAtom1504 chi)) ∨
      ((Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom0656 chi) ∨
      (Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom0663 chi))) ∨
      (((Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom0678 chi) ∨
      (Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom0714 chi)) ∨
      ((Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom1505 chi) ∨
      (¬Fin15AnchoredAtom2506 chi ∧
      Fin15AnchoredAtom0656 chi ∧
      Fin15AnchoredAtom0663 chi ∧
      Fin15AnchoredAtom0678 chi ∧
      Fin15AnchoredAtom0714 chi ∧
      Fin15AnchoredAtom1505 chi))))) ∨
      (((((Fin15AnchoredAtom2507 chi ∧
      ¬Fin15AnchoredAtom0657 chi) ∨
      (Fin15AnchoredAtom2507 chi ∧
      ¬Fin15AnchoredAtom0658 chi)) ∨
      ((Fin15AnchoredAtom2507 chi ∧
      ¬Fin15AnchoredAtom0679 chi) ∨
      (Fin15AnchoredAtom2507 chi ∧
      ¬Fin15AnchoredAtom0715 chi))) ∨
      (((Fin15AnchoredAtom2507 chi ∧
      ¬Fin15AnchoredAtom1506 chi) ∨
      (¬Fin15AnchoredAtom2507 chi ∧
      Fin15AnchoredAtom0657 chi ∧
      Fin15AnchoredAtom0658 chi ∧
      Fin15AnchoredAtom0679 chi ∧
      Fin15AnchoredAtom0715 chi ∧
      Fin15AnchoredAtom1506 chi)) ∨
      ((Fin15AnchoredAtom2508 chi ∧
      ¬Fin15AnchoredAtom0657 chi) ∨
      (Fin15AnchoredAtom2508 chi ∧
      ¬Fin15AnchoredAtom0659 chi)))) ∨
      ((((Fin15AnchoredAtom2508 chi ∧
      ¬Fin15AnchoredAtom0680 chi) ∨
      (Fin15AnchoredAtom2508 chi ∧
      ¬Fin15AnchoredAtom0716 chi)) ∨
      ((Fin15AnchoredAtom2508 chi ∧
      ¬Fin15AnchoredAtom1507 chi) ∨
      (¬Fin15AnchoredAtom2508 chi ∧
      Fin15AnchoredAtom0657 chi ∧
      Fin15AnchoredAtom0659 chi ∧
      Fin15AnchoredAtom0680 chi ∧
      Fin15AnchoredAtom0716 chi ∧
      Fin15AnchoredAtom1507 chi))) ∨
      (((Fin15AnchoredAtom2510 chi ∧
      ¬Fin15AnchoredAtom0657 chi) ∨
      (Fin15AnchoredAtom2510 chi ∧
      ¬Fin15AnchoredAtom0661 chi)) ∨
      ((Fin15AnchoredAtom2510 chi ∧
      ¬Fin15AnchoredAtom0682 chi) ∨
      (Fin15AnchoredAtom2510 chi ∧
      ¬Fin15AnchoredAtom0718 chi)))))))) ∨
      (((((((Fin15AnchoredAtom2510 chi ∧
      ¬Fin15AnchoredAtom1509 chi) ∨
      ((¬Fin15AnchoredAtom2510 chi ∧
      Fin15AnchoredAtom0657 chi ∧
      Fin15AnchoredAtom0661 chi ∧
      Fin15AnchoredAtom0682 chi ∧
      Fin15AnchoredAtom0718 chi ∧
      Fin15AnchoredAtom1509 chi) ∨
      (Fin15AnchoredAtom2511 chi ∧
      ¬Fin15AnchoredAtom0657 chi))) ∨
      (((Fin15AnchoredAtom2511 chi ∧
      ¬Fin15AnchoredAtom0662 chi) ∨
      (Fin15AnchoredAtom2511 chi ∧
      ¬Fin15AnchoredAtom0683 chi)) ∨
      ((Fin15AnchoredAtom2511 chi ∧
      ¬Fin15AnchoredAtom0719 chi) ∨
      (Fin15AnchoredAtom2511 chi ∧
      ¬Fin15AnchoredAtom1510 chi)))) ∨
      ((((¬Fin15AnchoredAtom2511 chi ∧
      Fin15AnchoredAtom0657 chi ∧
      Fin15AnchoredAtom0662 chi ∧
      Fin15AnchoredAtom0683 chi ∧
      Fin15AnchoredAtom0719 chi ∧
      Fin15AnchoredAtom1510 chi) ∨
      (Fin15AnchoredAtom2512 chi ∧
      ¬Fin15AnchoredAtom0657 chi)) ∨
      ((Fin15AnchoredAtom2512 chi ∧
      ¬Fin15AnchoredAtom0663 chi) ∨
      (Fin15AnchoredAtom2512 chi ∧
      ¬Fin15AnchoredAtom0684 chi))) ∨
      (((Fin15AnchoredAtom2512 chi ∧
      ¬Fin15AnchoredAtom0720 chi) ∨
      (Fin15AnchoredAtom2512 chi ∧
      ¬Fin15AnchoredAtom1511 chi)) ∨
      ((¬Fin15AnchoredAtom2512 chi ∧
      Fin15AnchoredAtom0657 chi ∧
      Fin15AnchoredAtom0663 chi ∧
      Fin15AnchoredAtom0684 chi ∧
      Fin15AnchoredAtom0720 chi ∧
      Fin15AnchoredAtom1511 chi) ∨
      (Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom0658 chi))))) ∨
      (((((Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom0659 chi) ∨
      (Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom0685 chi)) ∨
      ((Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom0721 chi) ∨
      (Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom1512 chi))) ∨
      (((¬Fin15AnchoredAtom2513 chi ∧
      Fin15AnchoredAtom0658 chi ∧
      Fin15AnchoredAtom0659 chi ∧
      Fin15AnchoredAtom0685 chi ∧
      Fin15AnchoredAtom0721 chi ∧
      Fin15AnchoredAtom1512 chi) ∨
      (Fin15AnchoredAtom2514 chi ∧
      ¬Fin15AnchoredAtom0658 chi)) ∨
      ((Fin15AnchoredAtom2514 chi ∧
      ¬Fin15AnchoredAtom0660 chi) ∨
      (Fin15AnchoredAtom2514 chi ∧
      ¬Fin15AnchoredAtom0686 chi)))) ∨
      ((((Fin15AnchoredAtom2514 chi ∧
      ¬Fin15AnchoredAtom0722 chi) ∨
      (Fin15AnchoredAtom2514 chi ∧
      ¬Fin15AnchoredAtom1513 chi)) ∨
      ((¬Fin15AnchoredAtom2514 chi ∧
      Fin15AnchoredAtom0658 chi ∧
      Fin15AnchoredAtom0660 chi ∧
      Fin15AnchoredAtom0686 chi ∧
      Fin15AnchoredAtom0722 chi ∧
      Fin15AnchoredAtom1513 chi) ∨
      (Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom0658 chi))) ∨
      (((Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom0661 chi) ∨
      (Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom0687 chi)) ∨
      ((Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom0723 chi) ∨
      (Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom1514 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom2515 chi ∧
      Fin15AnchoredAtom0658 chi ∧
      Fin15AnchoredAtom0661 chi ∧
      Fin15AnchoredAtom0687 chi ∧
      Fin15AnchoredAtom0723 chi ∧
      Fin15AnchoredAtom1514 chi) ∨
      (Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom0658 chi)) ∨
      ((Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom0662 chi) ∨
      (Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom0688 chi))) ∨
      (((Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom0724 chi) ∨
      (Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom1515 chi)) ∨
      ((¬Fin15AnchoredAtom2516 chi ∧
      Fin15AnchoredAtom0658 chi ∧
      Fin15AnchoredAtom0662 chi ∧
      Fin15AnchoredAtom0688 chi ∧
      Fin15AnchoredAtom0724 chi ∧
      Fin15AnchoredAtom1515 chi) ∨
      (Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom0658 chi)))) ∨
      ((((Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom0663 chi) ∨
      (Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom0689 chi)) ∨
      ((Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom0725 chi) ∨
      (Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom1516 chi))) ∨
      (((¬Fin15AnchoredAtom2517 chi ∧
      Fin15AnchoredAtom0658 chi ∧
      Fin15AnchoredAtom0663 chi ∧
      Fin15AnchoredAtom0689 chi ∧
      Fin15AnchoredAtom0725 chi ∧
      Fin15AnchoredAtom1516 chi) ∨
      (Fin15AnchoredAtom2518 chi ∧
      ¬Fin15AnchoredAtom0659 chi)) ∨
      ((Fin15AnchoredAtom2518 chi ∧
      ¬Fin15AnchoredAtom0660 chi) ∨
      (Fin15AnchoredAtom2518 chi ∧
      ¬Fin15AnchoredAtom0690 chi))))) ∨
      (((((Fin15AnchoredAtom2518 chi ∧
      ¬Fin15AnchoredAtom0726 chi) ∨
      (Fin15AnchoredAtom2518 chi ∧
      ¬Fin15AnchoredAtom1517 chi)) ∨
      ((¬Fin15AnchoredAtom2518 chi ∧
      Fin15AnchoredAtom0659 chi ∧
      Fin15AnchoredAtom0660 chi ∧
      Fin15AnchoredAtom0690 chi ∧
      Fin15AnchoredAtom0726 chi ∧
      Fin15AnchoredAtom1517 chi) ∨
      (Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom0659 chi))) ∨
      (((Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom0661 chi) ∨
      (Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom0691 chi)) ∨
      ((Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom0727 chi) ∨
      (Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom1518 chi)))) ∨
      ((((¬Fin15AnchoredAtom2519 chi ∧
      Fin15AnchoredAtom0659 chi ∧
      Fin15AnchoredAtom0661 chi ∧
      Fin15AnchoredAtom0691 chi ∧
      Fin15AnchoredAtom0727 chi ∧
      Fin15AnchoredAtom1518 chi) ∨
      (Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom0659 chi)) ∨
      ((Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom0662 chi) ∨
      (Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom0692 chi))) ∨
      (((Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom0728 chi) ∨
      (Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom1519 chi)) ∨
      ((¬Fin15AnchoredAtom2520 chi ∧
      Fin15AnchoredAtom0659 chi ∧
      Fin15AnchoredAtom0662 chi ∧
      Fin15AnchoredAtom0692 chi ∧
      Fin15AnchoredAtom0728 chi ∧
      Fin15AnchoredAtom1519 chi) ∨
      (Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom0659 chi))))))) ∨
      ((((((Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom0663 chi) ∨
      ((Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom0693 chi) ∨
      (Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom0729 chi))) ∨
      (((Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom1520 chi) ∨
      (¬Fin15AnchoredAtom2521 chi ∧
      Fin15AnchoredAtom0659 chi ∧
      Fin15AnchoredAtom0663 chi ∧
      Fin15AnchoredAtom0693 chi ∧
      Fin15AnchoredAtom0729 chi ∧
      Fin15AnchoredAtom1520 chi)) ∨
      ((Fin15AnchoredAtom2522 chi ∧
      ¬Fin15AnchoredAtom0660 chi) ∨
      (Fin15AnchoredAtom2522 chi ∧
      ¬Fin15AnchoredAtom0661 chi)))) ∨
      ((((Fin15AnchoredAtom2522 chi ∧
      ¬Fin15AnchoredAtom0694 chi) ∨
      (Fin15AnchoredAtom2522 chi ∧
      ¬Fin15AnchoredAtom0730 chi)) ∨
      ((Fin15AnchoredAtom2522 chi ∧
      ¬Fin15AnchoredAtom1521 chi) ∨
      (¬Fin15AnchoredAtom2522 chi ∧
      Fin15AnchoredAtom0660 chi ∧
      Fin15AnchoredAtom0661 chi ∧
      Fin15AnchoredAtom0694 chi ∧
      Fin15AnchoredAtom0730 chi ∧
      Fin15AnchoredAtom1521 chi))) ∨
      (((Fin15AnchoredAtom2523 chi ∧
      ¬Fin15AnchoredAtom1522 chi) ∨
      (¬Fin15AnchoredAtom2523 chi ∧
      Fin15AnchoredAtom0660 chi ∧
      Fin15AnchoredAtom0662 chi ∧
      Fin15AnchoredAtom0695 chi ∧
      Fin15AnchoredAtom0731 chi ∧
      Fin15AnchoredAtom1522 chi)) ∨
      ((Fin15AnchoredAtom2524 chi ∧
      ¬Fin15AnchoredAtom0660 chi) ∨
      (Fin15AnchoredAtom2524 chi ∧
      ¬Fin15AnchoredAtom1523 chi))))) ∨
      (((((¬Fin15AnchoredAtom2524 chi ∧
      Fin15AnchoredAtom0660 chi ∧
      Fin15AnchoredAtom0663 chi ∧
      Fin15AnchoredAtom0696 chi ∧
      Fin15AnchoredAtom0732 chi ∧
      Fin15AnchoredAtom1523 chi) ∨
      (Fin15AnchoredAtom2525 chi ∧
      ¬Fin15AnchoredAtom0661 chi)) ∨
      ((Fin15AnchoredAtom2525 chi ∧
      ¬Fin15AnchoredAtom0662 chi) ∨
      (Fin15AnchoredAtom2525 chi ∧
      ¬Fin15AnchoredAtom0697 chi))) ∨
      (((Fin15AnchoredAtom2525 chi ∧
      ¬Fin15AnchoredAtom0733 chi) ∨
      (Fin15AnchoredAtom2525 chi ∧
      ¬Fin15AnchoredAtom1524 chi)) ∨
      ((¬Fin15AnchoredAtom2525 chi ∧
      Fin15AnchoredAtom0661 chi ∧
      Fin15AnchoredAtom0662 chi ∧
      Fin15AnchoredAtom0697 chi ∧
      Fin15AnchoredAtom0733 chi ∧
      Fin15AnchoredAtom1524 chi) ∨
      (Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom0661 chi)))) ∨
      ((((Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom0663 chi) ∨
      (Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom0698 chi)) ∨
      ((Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom0734 chi) ∨
      (Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom1525 chi))) ∨
      (((¬Fin15AnchoredAtom2526 chi ∧
      Fin15AnchoredAtom0661 chi ∧
      Fin15AnchoredAtom0663 chi ∧
      Fin15AnchoredAtom0698 chi ∧
      Fin15AnchoredAtom0734 chi ∧
      Fin15AnchoredAtom1525 chi) ∨
      (Fin15AnchoredAtom2527 chi ∧
      ¬Fin15AnchoredAtom0662 chi)) ∨
      ((Fin15AnchoredAtom2527 chi ∧
      ¬Fin15AnchoredAtom0663 chi) ∨
      (Fin15AnchoredAtom2527 chi ∧
      ¬Fin15AnchoredAtom0699 chi)))))) ∨
      ((((((Fin15AnchoredAtom2527 chi ∧
      ¬Fin15AnchoredAtom0735 chi) ∨
      (Fin15AnchoredAtom2527 chi ∧
      ¬Fin15AnchoredAtom1526 chi)) ∨
      ((¬Fin15AnchoredAtom2527 chi ∧
      Fin15AnchoredAtom0662 chi ∧
      Fin15AnchoredAtom0663 chi ∧
      Fin15AnchoredAtom0699 chi ∧
      Fin15AnchoredAtom0735 chi ∧
      Fin15AnchoredAtom1526 chi) ∨
      (Fin15AnchoredAtom2528 chi ∧
      ¬Fin15AnchoredAtom0664 chi))) ∨
      (((Fin15AnchoredAtom2528 chi ∧
      ¬Fin15AnchoredAtom0665 chi) ∨
      (Fin15AnchoredAtom2528 chi ∧
      ¬Fin15AnchoredAtom0672 chi)) ∨
      ((Fin15AnchoredAtom2528 chi ∧
      ¬Fin15AnchoredAtom0736 chi) ∨
      (Fin15AnchoredAtom2528 chi ∧
      ¬Fin15AnchoredAtom1527 chi)))) ∨
      ((((¬Fin15AnchoredAtom2528 chi ∧
      Fin15AnchoredAtom0664 chi ∧
      Fin15AnchoredAtom0665 chi ∧
      Fin15AnchoredAtom0672 chi ∧
      Fin15AnchoredAtom0736 chi ∧
      Fin15AnchoredAtom1527 chi) ∨
      (Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom0664 chi)) ∨
      ((Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom0666 chi) ∨
      (Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom0673 chi))) ∨
      (((Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom0737 chi) ∨
      (Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom1528 chi)) ∨
      ((¬Fin15AnchoredAtom2529 chi ∧
      Fin15AnchoredAtom0664 chi ∧
      Fin15AnchoredAtom0666 chi ∧
      Fin15AnchoredAtom0673 chi ∧
      Fin15AnchoredAtom0737 chi ∧
      Fin15AnchoredAtom1528 chi) ∨
      (Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom0664 chi))))) ∨
      (((((Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom0667 chi) ∨
      (Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom0674 chi)) ∨
      ((Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom0738 chi) ∨
      (Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom1529 chi))) ∨
      (((¬Fin15AnchoredAtom2530 chi ∧
      Fin15AnchoredAtom0664 chi ∧
      Fin15AnchoredAtom0667 chi ∧
      Fin15AnchoredAtom0674 chi ∧
      Fin15AnchoredAtom0738 chi ∧
      Fin15AnchoredAtom1529 chi) ∨
      (Fin15AnchoredAtom2531 chi ∧
      ¬Fin15AnchoredAtom0664 chi)) ∨
      ((Fin15AnchoredAtom2531 chi ∧
      ¬Fin15AnchoredAtom0668 chi) ∨
      (Fin15AnchoredAtom2531 chi ∧
      ¬Fin15AnchoredAtom0675 chi)))) ∨
      ((((Fin15AnchoredAtom2531 chi ∧
      ¬Fin15AnchoredAtom0739 chi) ∨
      (Fin15AnchoredAtom2531 chi ∧
      ¬Fin15AnchoredAtom1530 chi)) ∨
      ((¬Fin15AnchoredAtom2531 chi ∧
      Fin15AnchoredAtom0664 chi ∧
      Fin15AnchoredAtom0668 chi ∧
      Fin15AnchoredAtom0675 chi ∧
      Fin15AnchoredAtom0739 chi ∧
      Fin15AnchoredAtom1530 chi) ∨
      (Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom0664 chi))) ∨
      (((Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom0669 chi) ∨
      (Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom0676 chi)) ∨
      ((Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom0740 chi) ∨
      (Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom1531 chi)))))))))) := by
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
                exact fin15Anchored_clause18677 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18678 chi hbad
                ·
                  exact fin15Anchored_clause18679 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18680 chi hbad
                ·
                  exact fin15Anchored_clause18681 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18682 chi hbad
                ·
                  exact fin15Anchored_clause18683 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18684 chi hbad
                ·
                  exact fin15Anchored_clause18685 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18686 chi hbad
                ·
                  exact fin15Anchored_clause18687 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18688 chi hbad
                ·
                  exact fin15Anchored_clause18689 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18690 chi hbad
                ·
                  exact fin15Anchored_clause18691 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18692 chi hbad
                ·
                  exact fin15Anchored_clause18693 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18694 chi hbad
                ·
                  exact fin15Anchored_clause18695 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18696 chi hbad
                ·
                  exact fin15Anchored_clause18697 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18698 chi hbad
                ·
                  exact fin15Anchored_clause18699 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18700 chi hbad
                ·
                  exact fin15Anchored_clause18701 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18702 chi hbad
                ·
                  exact fin15Anchored_clause18703 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18704 chi hbad
                ·
                  exact fin15Anchored_clause18705 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18706 chi hbad
                ·
                  exact fin15Anchored_clause18707 chi hbad
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
                  exact fin15Anchored_clause18708 chi hbad
                ·
                  exact fin15Anchored_clause18709 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18710 chi hbad
                ·
                  exact fin15Anchored_clause18711 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18712 chi hbad
                ·
                  exact fin15Anchored_clause18713 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18714 chi hbad
                ·
                  exact fin15Anchored_clause18715 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18716 chi hbad
                ·
                  exact fin15Anchored_clause18717 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18718 chi hbad
                ·
                  exact fin15Anchored_clause18719 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18720 chi hbad
                ·
                  exact fin15Anchored_clause18721 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18722 chi hbad
                ·
                  exact fin15Anchored_clause18723 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18724 chi hbad
                ·
                  exact fin15Anchored_clause18725 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18726 chi hbad
                ·
                  exact fin15Anchored_clause18727 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18728 chi hbad
                ·
                  exact fin15Anchored_clause18729 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18730 chi hbad
                ·
                  exact fin15Anchored_clause18731 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18732 chi hbad
                ·
                  exact fin15Anchored_clause18733 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18734 chi hbad
                ·
                  exact fin15Anchored_clause18735 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18736 chi hbad
                ·
                  exact fin15Anchored_clause18737 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18738 chi hbad
                ·
                  exact fin15Anchored_clause18739 chi hbad
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
                exact fin15Anchored_clause18740 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18741 chi hbad
                ·
                  exact fin15Anchored_clause18742 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18743 chi hbad
                ·
                  exact fin15Anchored_clause18744 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18745 chi hbad
                ·
                  exact fin15Anchored_clause18746 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18747 chi hbad
                ·
                  exact fin15Anchored_clause18748 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18749 chi hbad
                ·
                  exact fin15Anchored_clause18750 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18751 chi hbad
                ·
                  exact fin15Anchored_clause18752 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18753 chi hbad
                ·
                  exact fin15Anchored_clause18754 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18755 chi hbad
                ·
                  exact fin15Anchored_clause18756 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18757 chi hbad
                ·
                  exact fin15Anchored_clause18758 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18759 chi hbad
                ·
                  exact fin15Anchored_clause18760 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18761 chi hbad
                ·
                  exact fin15Anchored_clause18762 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18763 chi hbad
                ·
                  exact fin15Anchored_clause18764 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18765 chi hbad
                ·
                  exact fin15Anchored_clause18766 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18767 chi hbad
                ·
                  exact fin15Anchored_clause18768 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18769 chi hbad
                ·
                  exact fin15Anchored_clause18770 chi hbad
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
                  exact fin15Anchored_clause18771 chi hbad
                ·
                  exact fin15Anchored_clause18772 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18773 chi hbad
                ·
                  exact fin15Anchored_clause18774 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18775 chi hbad
                ·
                  exact fin15Anchored_clause18776 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18777 chi hbad
                ·
                  exact fin15Anchored_clause18778 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18779 chi hbad
                ·
                  exact fin15Anchored_clause18780 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18781 chi hbad
                ·
                  exact fin15Anchored_clause18782 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18783 chi hbad
                ·
                  exact fin15Anchored_clause18784 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18785 chi hbad
                ·
                  exact fin15Anchored_clause18786 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18787 chi hbad
                ·
                  exact fin15Anchored_clause18788 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18789 chi hbad
                ·
                  exact fin15Anchored_clause18790 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18791 chi hbad
                ·
                  exact fin15Anchored_clause18792 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18793 chi hbad
                ·
                  exact fin15Anchored_clause18794 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18795 chi hbad
                ·
                  exact fin15Anchored_clause18796 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18797 chi hbad
                ·
                  exact fin15Anchored_clause18798 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18799 chi hbad
                ·
                  exact fin15Anchored_clause18800 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18801 chi hbad
                ·
                  exact fin15Anchored_clause18802 chi hbad
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
                exact fin15Anchored_clause18803 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18804 chi hbad
                ·
                  exact fin15Anchored_clause18805 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18806 chi hbad
                ·
                  exact fin15Anchored_clause18807 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18808 chi hbad
                ·
                  exact fin15Anchored_clause18809 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18810 chi hbad
                ·
                  exact fin15Anchored_clause18811 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18812 chi hbad
                ·
                  exact fin15Anchored_clause18813 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18814 chi hbad
                ·
                  exact fin15Anchored_clause18815 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18816 chi hbad
                ·
                  exact fin15Anchored_clause18817 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18818 chi hbad
                ·
                  exact fin15Anchored_clause18819 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18820 chi hbad
                ·
                  exact fin15Anchored_clause18821 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18822 chi hbad
                ·
                  exact fin15Anchored_clause18823 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18824 chi hbad
                ·
                  exact fin15Anchored_clause18825 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18826 chi hbad
                ·
                  exact fin15Anchored_clause18827 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18828 chi hbad
                ·
                  exact fin15Anchored_clause18829 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18830 chi hbad
                ·
                  exact fin15Anchored_clause18831 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18832 chi hbad
                ·
                  exact fin15Anchored_clause18833 chi hbad
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
                  exact fin15Anchored_clause18834 chi hbad
                ·
                  exact fin15Anchored_clause18835 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18836 chi hbad
                ·
                  exact fin15Anchored_clause18837 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18838 chi hbad
                ·
                  exact fin15Anchored_clause18839 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18840 chi hbad
                ·
                  exact fin15Anchored_clause18841 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18842 chi hbad
                ·
                  exact fin15Anchored_clause18843 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18844 chi hbad
                ·
                  exact fin15Anchored_clause18845 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18846 chi hbad
                ·
                  exact fin15Anchored_clause18847 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18848 chi hbad
                ·
                  exact fin15Anchored_clause18849 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18850 chi hbad
                ·
                  exact fin15Anchored_clause18851 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18852 chi hbad
                ·
                  exact fin15Anchored_clause18853 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18854 chi hbad
                ·
                  exact fin15Anchored_clause18855 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18856 chi hbad
                ·
                  exact fin15Anchored_clause18857 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18858 chi hbad
                ·
                  exact fin15Anchored_clause18859 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18860 chi hbad
                ·
                  exact fin15Anchored_clause18861 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18862 chi hbad
                ·
                  exact fin15Anchored_clause18863 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18864 chi hbad
                ·
                  exact fin15Anchored_clause18865 chi hbad
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
                exact fin15Anchored_clause18866 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18867 chi hbad
                ·
                  exact fin15Anchored_clause18868 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18869 chi hbad
                ·
                  exact fin15Anchored_clause18870 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18871 chi hbad
                ·
                  exact fin15Anchored_clause18872 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18873 chi hbad
                ·
                  exact fin15Anchored_clause18874 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18875 chi hbad
                ·
                  exact fin15Anchored_clause18876 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18877 chi hbad
                ·
                  exact fin15Anchored_clause18878 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18879 chi hbad
                ·
                  exact fin15Anchored_clause18880 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18881 chi hbad
                ·
                  exact fin15Anchored_clause18882 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18883 chi hbad
                ·
                  exact fin15Anchored_clause18884 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18885 chi hbad
                ·
                  exact fin15Anchored_clause18886 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18887 chi hbad
                ·
                  exact fin15Anchored_clause18888 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18889 chi hbad
                ·
                  exact fin15Anchored_clause18890 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18891 chi hbad
                ·
                  exact fin15Anchored_clause18892 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18893 chi hbad
                ·
                  exact fin15Anchored_clause18894 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18895 chi hbad
                ·
                  exact fin15Anchored_clause18896 chi hbad
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
                  exact fin15Anchored_clause18897 chi hbad
                ·
                  exact fin15Anchored_clause18898 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18899 chi hbad
                ·
                  exact fin15Anchored_clause18900 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18901 chi hbad
                ·
                  exact fin15Anchored_clause18902 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18903 chi hbad
                ·
                  exact fin15Anchored_clause18904 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18905 chi hbad
                ·
                  exact fin15Anchored_clause18906 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18907 chi hbad
                ·
                  exact fin15Anchored_clause18908 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18909 chi hbad
                ·
                  exact fin15Anchored_clause18910 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18911 chi hbad
                ·
                  exact fin15Anchored_clause18912 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18913 chi hbad
                ·
                  exact fin15Anchored_clause18914 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18915 chi hbad
                ·
                  exact fin15Anchored_clause18916 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18917 chi hbad
                ·
                  exact fin15Anchored_clause18918 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18919 chi hbad
                ·
                  exact fin15Anchored_clause18920 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18921 chi hbad
                ·
                  exact fin15Anchored_clause18922 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18923 chi hbad
                ·
                  exact fin15Anchored_clause18924 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18925 chi hbad
                ·
                  exact fin15Anchored_clause18926 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18927 chi hbad
                ·
                  exact fin15Anchored_clause18928 chi hbad

end ErdosSzekeres

end
