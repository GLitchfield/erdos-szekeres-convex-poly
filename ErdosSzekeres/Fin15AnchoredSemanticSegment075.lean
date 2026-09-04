module

public import ErdosSzekeres.Fin15AnchoredClauseChunk147
public import ErdosSzekeres.Fin15AnchoredClauseChunk148
public import ErdosSzekeres.Fin15AnchoredClauseChunk149

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 075. -/

theorem fin15Anchored_rejectSemanticSegment075
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((¬Fin15AnchoredAtom2532 chi ∧
      Fin15AnchoredAtom0664 chi ∧
      Fin15AnchoredAtom0669 chi ∧
      Fin15AnchoredAtom0676 chi ∧
      Fin15AnchoredAtom0740 chi ∧
      Fin15AnchoredAtom1531 chi) ∨
      ((Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom0664 chi) ∨
      (Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom0670 chi))) ∨
      (((Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom0677 chi) ∨
      (Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom0741 chi)) ∨
      ((Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom1532 chi) ∨
      (¬Fin15AnchoredAtom2533 chi ∧
      Fin15AnchoredAtom0664 chi ∧
      Fin15AnchoredAtom0670 chi ∧
      Fin15AnchoredAtom0677 chi ∧
      Fin15AnchoredAtom0741 chi ∧
      Fin15AnchoredAtom1532 chi)))) ∨
      ((((Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom0664 chi) ∨
      (Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom0671 chi)) ∨
      ((Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom0678 chi) ∨
      (Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom0742 chi))) ∨
      (((Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom1533 chi) ∨
      (¬Fin15AnchoredAtom2534 chi ∧
      Fin15AnchoredAtom0664 chi ∧
      Fin15AnchoredAtom0671 chi ∧
      Fin15AnchoredAtom0678 chi ∧
      Fin15AnchoredAtom0742 chi ∧
      Fin15AnchoredAtom1533 chi)) ∨
      ((Fin15AnchoredAtom2535 chi ∧
      ¬Fin15AnchoredAtom0665 chi) ∨
      (Fin15AnchoredAtom2535 chi ∧
      ¬Fin15AnchoredAtom0666 chi))))) ∨
      (((((Fin15AnchoredAtom2535 chi ∧
      ¬Fin15AnchoredAtom0679 chi) ∨
      (Fin15AnchoredAtom2535 chi ∧
      ¬Fin15AnchoredAtom0743 chi)) ∨
      ((Fin15AnchoredAtom2535 chi ∧
      ¬Fin15AnchoredAtom1534 chi) ∨
      (¬Fin15AnchoredAtom2535 chi ∧
      Fin15AnchoredAtom0665 chi ∧
      Fin15AnchoredAtom0666 chi ∧
      Fin15AnchoredAtom0679 chi ∧
      Fin15AnchoredAtom0743 chi ∧
      Fin15AnchoredAtom1534 chi))) ∨
      (((Fin15AnchoredAtom2536 chi ∧
      ¬Fin15AnchoredAtom0665 chi) ∨
      (Fin15AnchoredAtom2536 chi ∧
      ¬Fin15AnchoredAtom0667 chi)) ∨
      ((Fin15AnchoredAtom2536 chi ∧
      ¬Fin15AnchoredAtom0680 chi) ∨
      (Fin15AnchoredAtom2536 chi ∧
      ¬Fin15AnchoredAtom0744 chi)))) ∨
      ((((Fin15AnchoredAtom2536 chi ∧
      ¬Fin15AnchoredAtom1535 chi) ∨
      (¬Fin15AnchoredAtom2536 chi ∧
      Fin15AnchoredAtom0665 chi ∧
      Fin15AnchoredAtom0667 chi ∧
      Fin15AnchoredAtom0680 chi ∧
      Fin15AnchoredAtom0744 chi ∧
      Fin15AnchoredAtom1535 chi)) ∨
      ((Fin15AnchoredAtom2538 chi ∧
      ¬Fin15AnchoredAtom0665 chi) ∨
      (Fin15AnchoredAtom2538 chi ∧
      ¬Fin15AnchoredAtom0669 chi))) ∨
      (((Fin15AnchoredAtom2538 chi ∧
      ¬Fin15AnchoredAtom0682 chi) ∨
      (Fin15AnchoredAtom2538 chi ∧
      ¬Fin15AnchoredAtom0746 chi)) ∨
      ((Fin15AnchoredAtom2538 chi ∧
      ¬Fin15AnchoredAtom1537 chi) ∨
      (¬Fin15AnchoredAtom2538 chi ∧
      Fin15AnchoredAtom0665 chi ∧
      Fin15AnchoredAtom0669 chi ∧
      Fin15AnchoredAtom0682 chi ∧
      Fin15AnchoredAtom0746 chi ∧
      Fin15AnchoredAtom1537 chi)))))) ∨
      ((((((Fin15AnchoredAtom2539 chi ∧
      ¬Fin15AnchoredAtom0665 chi) ∨
      (Fin15AnchoredAtom2539 chi ∧
      ¬Fin15AnchoredAtom0670 chi)) ∨
      ((Fin15AnchoredAtom2539 chi ∧
      ¬Fin15AnchoredAtom0683 chi) ∨
      (Fin15AnchoredAtom2539 chi ∧
      ¬Fin15AnchoredAtom0747 chi))) ∨
      (((Fin15AnchoredAtom2539 chi ∧
      ¬Fin15AnchoredAtom1538 chi) ∨
      (¬Fin15AnchoredAtom2539 chi ∧
      Fin15AnchoredAtom0665 chi ∧
      Fin15AnchoredAtom0670 chi ∧
      Fin15AnchoredAtom0683 chi ∧
      Fin15AnchoredAtom0747 chi ∧
      Fin15AnchoredAtom1538 chi)) ∨
      ((Fin15AnchoredAtom2540 chi ∧
      ¬Fin15AnchoredAtom0665 chi) ∨
      (Fin15AnchoredAtom2540 chi ∧
      ¬Fin15AnchoredAtom0671 chi)))) ∨
      ((((Fin15AnchoredAtom2540 chi ∧
      ¬Fin15AnchoredAtom0684 chi) ∨
      (Fin15AnchoredAtom2540 chi ∧
      ¬Fin15AnchoredAtom0748 chi)) ∨
      ((Fin15AnchoredAtom2540 chi ∧
      ¬Fin15AnchoredAtom1539 chi) ∨
      (¬Fin15AnchoredAtom2540 chi ∧
      Fin15AnchoredAtom0665 chi ∧
      Fin15AnchoredAtom0671 chi ∧
      Fin15AnchoredAtom0684 chi ∧
      Fin15AnchoredAtom0748 chi ∧
      Fin15AnchoredAtom1539 chi))) ∨
      (((Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom0666 chi) ∨
      (Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom0667 chi)) ∨
      ((Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom0685 chi) ∨
      (Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom0749 chi))))) ∨
      (((((Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom1540 chi) ∨
      (¬Fin15AnchoredAtom2541 chi ∧
      Fin15AnchoredAtom0666 chi ∧
      Fin15AnchoredAtom0667 chi ∧
      Fin15AnchoredAtom0685 chi ∧
      Fin15AnchoredAtom0749 chi ∧
      Fin15AnchoredAtom1540 chi)) ∨
      ((Fin15AnchoredAtom2542 chi ∧
      ¬Fin15AnchoredAtom0666 chi) ∨
      (Fin15AnchoredAtom2542 chi ∧
      ¬Fin15AnchoredAtom0668 chi))) ∨
      (((Fin15AnchoredAtom2542 chi ∧
      ¬Fin15AnchoredAtom0686 chi) ∨
      (Fin15AnchoredAtom2542 chi ∧
      ¬Fin15AnchoredAtom0750 chi)) ∨
      ((Fin15AnchoredAtom2542 chi ∧
      ¬Fin15AnchoredAtom1541 chi) ∨
      (¬Fin15AnchoredAtom2542 chi ∧
      Fin15AnchoredAtom0666 chi ∧
      Fin15AnchoredAtom0668 chi ∧
      Fin15AnchoredAtom0686 chi ∧
      Fin15AnchoredAtom0750 chi ∧
      Fin15AnchoredAtom1541 chi)))) ∨
      ((((Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom0666 chi) ∨
      (Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom0669 chi)) ∨
      ((Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom0687 chi) ∨
      (Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom0751 chi))) ∨
      (((Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom1542 chi) ∨
      (¬Fin15AnchoredAtom2543 chi ∧
      Fin15AnchoredAtom0666 chi ∧
      Fin15AnchoredAtom0669 chi ∧
      Fin15AnchoredAtom0687 chi ∧
      Fin15AnchoredAtom0751 chi ∧
      Fin15AnchoredAtom1542 chi)) ∨
      ((Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom0666 chi) ∨
      (Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom0670 chi))))))) ∨
      ((((((Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom0688 chi) ∨
      ((Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom0752 chi) ∨
      (Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom1543 chi))) ∨
      (((¬Fin15AnchoredAtom2544 chi ∧
      Fin15AnchoredAtom0666 chi ∧
      Fin15AnchoredAtom0670 chi ∧
      Fin15AnchoredAtom0688 chi ∧
      Fin15AnchoredAtom0752 chi ∧
      Fin15AnchoredAtom1543 chi) ∨
      (Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom0666 chi)) ∨
      ((Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom0671 chi) ∨
      (Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom0689 chi)))) ∨
      ((((Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom0753 chi) ∨
      (Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom1544 chi)) ∨
      ((¬Fin15AnchoredAtom2545 chi ∧
      Fin15AnchoredAtom0666 chi ∧
      Fin15AnchoredAtom0671 chi ∧
      Fin15AnchoredAtom0689 chi ∧
      Fin15AnchoredAtom0753 chi ∧
      Fin15AnchoredAtom1544 chi) ∨
      (Fin15AnchoredAtom2546 chi ∧
      ¬Fin15AnchoredAtom0667 chi))) ∨
      (((Fin15AnchoredAtom2546 chi ∧
      ¬Fin15AnchoredAtom0668 chi) ∨
      (Fin15AnchoredAtom2546 chi ∧
      ¬Fin15AnchoredAtom0690 chi)) ∨
      ((Fin15AnchoredAtom2546 chi ∧
      ¬Fin15AnchoredAtom0754 chi) ∨
      (Fin15AnchoredAtom2546 chi ∧
      ¬Fin15AnchoredAtom1545 chi))))) ∨
      (((((¬Fin15AnchoredAtom2546 chi ∧
      Fin15AnchoredAtom0667 chi ∧
      Fin15AnchoredAtom0668 chi ∧
      Fin15AnchoredAtom0690 chi ∧
      Fin15AnchoredAtom0754 chi ∧
      Fin15AnchoredAtom1545 chi) ∨
      (Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom0667 chi)) ∨
      ((Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom0669 chi) ∨
      (Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom0691 chi))) ∨
      (((Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom0755 chi) ∨
      (Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom1546 chi)) ∨
      ((¬Fin15AnchoredAtom2547 chi ∧
      Fin15AnchoredAtom0667 chi ∧
      Fin15AnchoredAtom0669 chi ∧
      Fin15AnchoredAtom0691 chi ∧
      Fin15AnchoredAtom0755 chi ∧
      Fin15AnchoredAtom1546 chi) ∨
      (Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom0667 chi)))) ∨
      ((((Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom0670 chi) ∨
      (Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom0692 chi)) ∨
      ((Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom0756 chi) ∨
      (Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom1547 chi))) ∨
      (((¬Fin15AnchoredAtom2548 chi ∧
      Fin15AnchoredAtom0667 chi ∧
      Fin15AnchoredAtom0670 chi ∧
      Fin15AnchoredAtom0692 chi ∧
      Fin15AnchoredAtom0756 chi ∧
      Fin15AnchoredAtom1547 chi) ∨
      (Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom0667 chi)) ∨
      ((Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom0671 chi) ∨
      (Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom0693 chi)))))) ∨
      ((((((Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom0757 chi) ∨
      (Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom1548 chi)) ∨
      ((¬Fin15AnchoredAtom2549 chi ∧
      Fin15AnchoredAtom0667 chi ∧
      Fin15AnchoredAtom0671 chi ∧
      Fin15AnchoredAtom0693 chi ∧
      Fin15AnchoredAtom0757 chi ∧
      Fin15AnchoredAtom1548 chi) ∨
      (Fin15AnchoredAtom2550 chi ∧
      ¬Fin15AnchoredAtom0668 chi))) ∨
      (((Fin15AnchoredAtom2550 chi ∧
      ¬Fin15AnchoredAtom0694 chi) ∨
      (Fin15AnchoredAtom2550 chi ∧
      ¬Fin15AnchoredAtom0758 chi)) ∨
      ((Fin15AnchoredAtom2550 chi ∧
      ¬Fin15AnchoredAtom1549 chi) ∨
      (¬Fin15AnchoredAtom2550 chi ∧
      Fin15AnchoredAtom0668 chi ∧
      Fin15AnchoredAtom0669 chi ∧
      Fin15AnchoredAtom0694 chi ∧
      Fin15AnchoredAtom0758 chi ∧
      Fin15AnchoredAtom1549 chi)))) ∨
      ((((Fin15AnchoredAtom2551 chi ∧
      ¬Fin15AnchoredAtom0668 chi) ∨
      (Fin15AnchoredAtom2551 chi ∧
      ¬Fin15AnchoredAtom0695 chi)) ∨
      ((Fin15AnchoredAtom2551 chi ∧
      ¬Fin15AnchoredAtom0759 chi) ∨
      (Fin15AnchoredAtom2551 chi ∧
      ¬Fin15AnchoredAtom1550 chi))) ∨
      (((¬Fin15AnchoredAtom2551 chi ∧
      Fin15AnchoredAtom0668 chi ∧
      Fin15AnchoredAtom0670 chi ∧
      Fin15AnchoredAtom0695 chi ∧
      Fin15AnchoredAtom0759 chi ∧
      Fin15AnchoredAtom1550 chi) ∨
      (Fin15AnchoredAtom2552 chi ∧
      ¬Fin15AnchoredAtom0668 chi)) ∨
      ((Fin15AnchoredAtom2552 chi ∧
      ¬Fin15AnchoredAtom0671 chi) ∨
      (Fin15AnchoredAtom2553 chi ∧
      ¬Fin15AnchoredAtom0669 chi))))) ∨
      (((((Fin15AnchoredAtom2553 chi ∧
      ¬Fin15AnchoredAtom0670 chi) ∨
      (Fin15AnchoredAtom2553 chi ∧
      ¬Fin15AnchoredAtom0697 chi)) ∨
      ((Fin15AnchoredAtom2553 chi ∧
      ¬Fin15AnchoredAtom0761 chi) ∨
      (Fin15AnchoredAtom2553 chi ∧
      ¬Fin15AnchoredAtom1552 chi))) ∨
      (((¬Fin15AnchoredAtom2553 chi ∧
      Fin15AnchoredAtom0669 chi ∧
      Fin15AnchoredAtom0670 chi ∧
      Fin15AnchoredAtom0697 chi ∧
      Fin15AnchoredAtom0761 chi ∧
      Fin15AnchoredAtom1552 chi) ∨
      (Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom0669 chi)) ∨
      ((Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom0671 chi) ∨
      (Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom0698 chi)))) ∨
      ((((Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom0762 chi) ∨
      (Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom1553 chi)) ∨
      ((¬Fin15AnchoredAtom2554 chi ∧
      Fin15AnchoredAtom0669 chi ∧
      Fin15AnchoredAtom0671 chi ∧
      Fin15AnchoredAtom0698 chi ∧
      Fin15AnchoredAtom0762 chi ∧
      Fin15AnchoredAtom1553 chi) ∨
      (Fin15AnchoredAtom2555 chi ∧
      ¬Fin15AnchoredAtom0670 chi))) ∨
      (((Fin15AnchoredAtom2555 chi ∧
      ¬Fin15AnchoredAtom0671 chi) ∨
      (Fin15AnchoredAtom2555 chi ∧
      ¬Fin15AnchoredAtom0699 chi)) ∨
      ((Fin15AnchoredAtom2555 chi ∧
      ¬Fin15AnchoredAtom0763 chi) ∨
      (Fin15AnchoredAtom2555 chi ∧
      ¬Fin15AnchoredAtom1554 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom2555 chi ∧
      Fin15AnchoredAtom0670 chi ∧
      Fin15AnchoredAtom0671 chi ∧
      Fin15AnchoredAtom0699 chi ∧
      Fin15AnchoredAtom0763 chi ∧
      Fin15AnchoredAtom1554 chi) ∨
      ((Fin15AnchoredAtom2556 chi ∧
      ¬Fin15AnchoredAtom0672 chi) ∨
      (Fin15AnchoredAtom2556 chi ∧
      ¬Fin15AnchoredAtom0673 chi))) ∨
      (((Fin15AnchoredAtom2556 chi ∧
      ¬Fin15AnchoredAtom0679 chi) ∨
      (Fin15AnchoredAtom2556 chi ∧
      ¬Fin15AnchoredAtom0764 chi)) ∨
      ((Fin15AnchoredAtom2556 chi ∧
      ¬Fin15AnchoredAtom1555 chi) ∨
      (¬Fin15AnchoredAtom2556 chi ∧
      Fin15AnchoredAtom0672 chi ∧
      Fin15AnchoredAtom0673 chi ∧
      Fin15AnchoredAtom0679 chi ∧
      Fin15AnchoredAtom0764 chi ∧
      Fin15AnchoredAtom1555 chi)))) ∨
      ((((Fin15AnchoredAtom2557 chi ∧
      ¬Fin15AnchoredAtom0672 chi) ∨
      (Fin15AnchoredAtom2557 chi ∧
      ¬Fin15AnchoredAtom0674 chi)) ∨
      ((Fin15AnchoredAtom2557 chi ∧
      ¬Fin15AnchoredAtom0680 chi) ∨
      (Fin15AnchoredAtom2557 chi ∧
      ¬Fin15AnchoredAtom0765 chi))) ∨
      (((Fin15AnchoredAtom2557 chi ∧
      ¬Fin15AnchoredAtom1556 chi) ∨
      (¬Fin15AnchoredAtom2557 chi ∧
      Fin15AnchoredAtom0672 chi ∧
      Fin15AnchoredAtom0674 chi ∧
      Fin15AnchoredAtom0680 chi ∧
      Fin15AnchoredAtom0765 chi ∧
      Fin15AnchoredAtom1556 chi)) ∨
      ((Fin15AnchoredAtom2559 chi ∧
      ¬Fin15AnchoredAtom0672 chi) ∨
      (Fin15AnchoredAtom2559 chi ∧
      ¬Fin15AnchoredAtom0676 chi))))) ∨
      (((((Fin15AnchoredAtom2559 chi ∧
      ¬Fin15AnchoredAtom0682 chi) ∨
      (Fin15AnchoredAtom2559 chi ∧
      ¬Fin15AnchoredAtom0767 chi)) ∨
      ((Fin15AnchoredAtom2559 chi ∧
      ¬Fin15AnchoredAtom1558 chi) ∨
      (¬Fin15AnchoredAtom2559 chi ∧
      Fin15AnchoredAtom0672 chi ∧
      Fin15AnchoredAtom0676 chi ∧
      Fin15AnchoredAtom0682 chi ∧
      Fin15AnchoredAtom0767 chi ∧
      Fin15AnchoredAtom1558 chi))) ∨
      (((Fin15AnchoredAtom2560 chi ∧
      ¬Fin15AnchoredAtom0672 chi) ∨
      (Fin15AnchoredAtom2560 chi ∧
      ¬Fin15AnchoredAtom0677 chi)) ∨
      ((Fin15AnchoredAtom2560 chi ∧
      ¬Fin15AnchoredAtom0683 chi) ∨
      (Fin15AnchoredAtom2560 chi ∧
      ¬Fin15AnchoredAtom0768 chi)))) ∨
      ((((Fin15AnchoredAtom2560 chi ∧
      ¬Fin15AnchoredAtom1559 chi) ∨
      (¬Fin15AnchoredAtom2560 chi ∧
      Fin15AnchoredAtom0672 chi ∧
      Fin15AnchoredAtom0677 chi ∧
      Fin15AnchoredAtom0683 chi ∧
      Fin15AnchoredAtom0768 chi ∧
      Fin15AnchoredAtom1559 chi)) ∨
      ((Fin15AnchoredAtom2561 chi ∧
      ¬Fin15AnchoredAtom0672 chi) ∨
      (Fin15AnchoredAtom2561 chi ∧
      ¬Fin15AnchoredAtom0678 chi))) ∨
      (((Fin15AnchoredAtom2561 chi ∧
      ¬Fin15AnchoredAtom0684 chi) ∨
      (Fin15AnchoredAtom2561 chi ∧
      ¬Fin15AnchoredAtom0769 chi)) ∨
      ((Fin15AnchoredAtom2561 chi ∧
      ¬Fin15AnchoredAtom1560 chi) ∨
      (¬Fin15AnchoredAtom2561 chi ∧
      Fin15AnchoredAtom0672 chi ∧
      Fin15AnchoredAtom0678 chi ∧
      Fin15AnchoredAtom0684 chi ∧
      Fin15AnchoredAtom0769 chi ∧
      Fin15AnchoredAtom1560 chi)))))) ∨
      ((((((Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom0673 chi) ∨
      (Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom0674 chi)) ∨
      ((Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom0685 chi) ∨
      (Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom0770 chi))) ∨
      (((Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom1561 chi) ∨
      (¬Fin15AnchoredAtom2562 chi ∧
      Fin15AnchoredAtom0673 chi ∧
      Fin15AnchoredAtom0674 chi ∧
      Fin15AnchoredAtom0685 chi ∧
      Fin15AnchoredAtom0770 chi ∧
      Fin15AnchoredAtom1561 chi)) ∨
      ((Fin15AnchoredAtom2563 chi ∧
      ¬Fin15AnchoredAtom0673 chi) ∨
      (Fin15AnchoredAtom2563 chi ∧
      ¬Fin15AnchoredAtom0675 chi)))) ∨
      ((((Fin15AnchoredAtom2563 chi ∧
      ¬Fin15AnchoredAtom0771 chi) ∨
      (Fin15AnchoredAtom2563 chi ∧
      ¬Fin15AnchoredAtom1562 chi)) ∨
      ((¬Fin15AnchoredAtom2563 chi ∧
      Fin15AnchoredAtom0673 chi ∧
      Fin15AnchoredAtom0675 chi ∧
      Fin15AnchoredAtom0686 chi ∧
      Fin15AnchoredAtom0771 chi ∧
      Fin15AnchoredAtom1562 chi) ∨
      (Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom0673 chi))) ∨
      (((Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom0676 chi) ∨
      (Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom0687 chi)) ∨
      ((Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom0772 chi) ∨
      (Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom1563 chi))))) ∨
      (((((¬Fin15AnchoredAtom2564 chi ∧
      Fin15AnchoredAtom0673 chi ∧
      Fin15AnchoredAtom0676 chi ∧
      Fin15AnchoredAtom0687 chi ∧
      Fin15AnchoredAtom0772 chi ∧
      Fin15AnchoredAtom1563 chi) ∨
      (Fin15AnchoredAtom2565 chi ∧
      ¬Fin15AnchoredAtom0673 chi)) ∨
      ((Fin15AnchoredAtom2565 chi ∧
      ¬Fin15AnchoredAtom0677 chi) ∨
      (Fin15AnchoredAtom2565 chi ∧
      ¬Fin15AnchoredAtom0688 chi))) ∨
      (((Fin15AnchoredAtom2565 chi ∧
      ¬Fin15AnchoredAtom0773 chi) ∨
      (Fin15AnchoredAtom2565 chi ∧
      ¬Fin15AnchoredAtom1564 chi)) ∨
      ((¬Fin15AnchoredAtom2565 chi ∧
      Fin15AnchoredAtom0673 chi ∧
      Fin15AnchoredAtom0677 chi ∧
      Fin15AnchoredAtom0688 chi ∧
      Fin15AnchoredAtom0773 chi ∧
      Fin15AnchoredAtom1564 chi) ∨
      (Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom0673 chi)))) ∨
      ((((Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom0678 chi) ∨
      (Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom0689 chi)) ∨
      ((Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom0774 chi) ∨
      (Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom1565 chi))) ∨
      (((¬Fin15AnchoredAtom2566 chi ∧
      Fin15AnchoredAtom0673 chi ∧
      Fin15AnchoredAtom0678 chi ∧
      Fin15AnchoredAtom0689 chi ∧
      Fin15AnchoredAtom0774 chi ∧
      Fin15AnchoredAtom1565 chi) ∨
      (Fin15AnchoredAtom2567 chi ∧
      ¬Fin15AnchoredAtom0674 chi)) ∨
      ((Fin15AnchoredAtom2567 chi ∧
      ¬Fin15AnchoredAtom0690 chi) ∨
      (Fin15AnchoredAtom2567 chi ∧
      ¬Fin15AnchoredAtom0775 chi))))))) ∨
      (((((((¬Fin15AnchoredAtom2567 chi ∧
      Fin15AnchoredAtom0674 chi ∧
      Fin15AnchoredAtom0675 chi ∧
      Fin15AnchoredAtom0690 chi ∧
      Fin15AnchoredAtom0775 chi ∧
      Fin15AnchoredAtom1566 chi) ∨
      (Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom0674 chi)) ∨
      ((Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom0676 chi) ∨
      (Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom0691 chi))) ∨
      (((Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom0776 chi) ∨
      (Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom1567 chi)) ∨
      ((¬Fin15AnchoredAtom2568 chi ∧
      Fin15AnchoredAtom0674 chi ∧
      Fin15AnchoredAtom0676 chi ∧
      Fin15AnchoredAtom0691 chi ∧
      Fin15AnchoredAtom0776 chi ∧
      Fin15AnchoredAtom1567 chi) ∨
      (Fin15AnchoredAtom2569 chi ∧
      ¬Fin15AnchoredAtom0674 chi)))) ∨
      ((((Fin15AnchoredAtom2569 chi ∧
      ¬Fin15AnchoredAtom0677 chi) ∨
      (Fin15AnchoredAtom2569 chi ∧
      ¬Fin15AnchoredAtom0692 chi)) ∨
      ((Fin15AnchoredAtom2569 chi ∧
      ¬Fin15AnchoredAtom0777 chi) ∨
      (Fin15AnchoredAtom2569 chi ∧
      ¬Fin15AnchoredAtom1568 chi))) ∨
      (((¬Fin15AnchoredAtom2569 chi ∧
      Fin15AnchoredAtom0674 chi ∧
      Fin15AnchoredAtom0677 chi ∧
      Fin15AnchoredAtom0692 chi ∧
      Fin15AnchoredAtom0777 chi ∧
      Fin15AnchoredAtom1568 chi) ∨
      (Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom0674 chi)) ∨
      ((Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom0678 chi) ∨
      (Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom0693 chi))))) ∨
      (((((Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom0778 chi) ∨
      (Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom1569 chi)) ∨
      ((¬Fin15AnchoredAtom2570 chi ∧
      Fin15AnchoredAtom0674 chi ∧
      Fin15AnchoredAtom0678 chi ∧
      Fin15AnchoredAtom0693 chi ∧
      Fin15AnchoredAtom0778 chi ∧
      Fin15AnchoredAtom1569 chi) ∨
      (Fin15AnchoredAtom2571 chi ∧
      ¬Fin15AnchoredAtom0675 chi))) ∨
      (((Fin15AnchoredAtom2571 chi ∧
      ¬Fin15AnchoredAtom0676 chi) ∨
      (Fin15AnchoredAtom2571 chi ∧
      ¬Fin15AnchoredAtom0694 chi)) ∨
      ((Fin15AnchoredAtom2571 chi ∧
      ¬Fin15AnchoredAtom0779 chi) ∨
      (Fin15AnchoredAtom2571 chi ∧
      ¬Fin15AnchoredAtom1570 chi)))) ∨
      ((((¬Fin15AnchoredAtom2571 chi ∧
      Fin15AnchoredAtom0675 chi ∧
      Fin15AnchoredAtom0676 chi ∧
      Fin15AnchoredAtom0694 chi ∧
      Fin15AnchoredAtom0779 chi ∧
      Fin15AnchoredAtom1570 chi) ∨
      (Fin15AnchoredAtom2572 chi ∧
      ¬Fin15AnchoredAtom0695 chi)) ∨
      ((Fin15AnchoredAtom2572 chi ∧
      ¬Fin15AnchoredAtom0780 chi) ∨
      (Fin15AnchoredAtom2573 chi ∧
      ¬Fin15AnchoredAtom0678 chi))) ∨
      (((Fin15AnchoredAtom2573 chi ∧
      ¬Fin15AnchoredAtom0696 chi) ∨
      (Fin15AnchoredAtom2573 chi ∧
      ¬Fin15AnchoredAtom0781 chi)) ∨
      ((Fin15AnchoredAtom2574 chi ∧
      ¬Fin15AnchoredAtom0676 chi) ∨
      (Fin15AnchoredAtom2574 chi ∧
      ¬Fin15AnchoredAtom0677 chi)))))) ∨
      ((((((Fin15AnchoredAtom2574 chi ∧
      ¬Fin15AnchoredAtom0697 chi) ∨
      (Fin15AnchoredAtom2574 chi ∧
      ¬Fin15AnchoredAtom0782 chi)) ∨
      ((Fin15AnchoredAtom2574 chi ∧
      ¬Fin15AnchoredAtom1573 chi) ∨
      (¬Fin15AnchoredAtom2574 chi ∧
      Fin15AnchoredAtom0676 chi ∧
      Fin15AnchoredAtom0677 chi ∧
      Fin15AnchoredAtom0697 chi ∧
      Fin15AnchoredAtom0782 chi ∧
      Fin15AnchoredAtom1573 chi))) ∨
      (((Fin15AnchoredAtom2575 chi ∧
      ¬Fin15AnchoredAtom0676 chi) ∨
      (Fin15AnchoredAtom2575 chi ∧
      ¬Fin15AnchoredAtom0678 chi)) ∨
      ((Fin15AnchoredAtom2575 chi ∧
      ¬Fin15AnchoredAtom0698 chi) ∨
      (Fin15AnchoredAtom2575 chi ∧
      ¬Fin15AnchoredAtom0783 chi)))) ∨
      ((((Fin15AnchoredAtom2575 chi ∧
      ¬Fin15AnchoredAtom1574 chi) ∨
      (¬Fin15AnchoredAtom2575 chi ∧
      Fin15AnchoredAtom0676 chi ∧
      Fin15AnchoredAtom0678 chi ∧
      Fin15AnchoredAtom0698 chi ∧
      Fin15AnchoredAtom0783 chi ∧
      Fin15AnchoredAtom1574 chi)) ∨
      ((Fin15AnchoredAtom2576 chi ∧
      ¬Fin15AnchoredAtom0677 chi) ∨
      (Fin15AnchoredAtom2576 chi ∧
      ¬Fin15AnchoredAtom0678 chi))) ∨
      (((Fin15AnchoredAtom2576 chi ∧
      ¬Fin15AnchoredAtom0699 chi) ∨
      (Fin15AnchoredAtom2576 chi ∧
      ¬Fin15AnchoredAtom0784 chi)) ∨
      ((Fin15AnchoredAtom2576 chi ∧
      ¬Fin15AnchoredAtom1575 chi) ∨
      (¬Fin15AnchoredAtom2576 chi ∧
      Fin15AnchoredAtom0677 chi ∧
      Fin15AnchoredAtom0678 chi ∧
      Fin15AnchoredAtom0699 chi ∧
      Fin15AnchoredAtom0784 chi ∧
      Fin15AnchoredAtom1575 chi))))) ∨
      (((((Fin15AnchoredAtom2577 chi ∧
      ¬Fin15AnchoredAtom0679 chi) ∨
      (Fin15AnchoredAtom2577 chi ∧
      ¬Fin15AnchoredAtom0680 chi)) ∨
      ((Fin15AnchoredAtom2577 chi ∧
      ¬Fin15AnchoredAtom0685 chi) ∨
      (Fin15AnchoredAtom2577 chi ∧
      ¬Fin15AnchoredAtom0785 chi))) ∨
      (((¬Fin15AnchoredAtom2577 chi ∧
      Fin15AnchoredAtom0679 chi ∧
      Fin15AnchoredAtom0680 chi ∧
      Fin15AnchoredAtom0685 chi ∧
      Fin15AnchoredAtom0785 chi ∧
      Fin15AnchoredAtom1576 chi) ∨
      (Fin15AnchoredAtom2579 chi ∧
      ¬Fin15AnchoredAtom0679 chi)) ∨
      ((Fin15AnchoredAtom2579 chi ∧
      ¬Fin15AnchoredAtom0682 chi) ∨
      (Fin15AnchoredAtom2579 chi ∧
      ¬Fin15AnchoredAtom0687 chi)))) ∨
      ((((Fin15AnchoredAtom2579 chi ∧
      ¬Fin15AnchoredAtom0787 chi) ∨
      (Fin15AnchoredAtom2579 chi ∧
      ¬Fin15AnchoredAtom1578 chi)) ∨
      ((¬Fin15AnchoredAtom2579 chi ∧
      Fin15AnchoredAtom0679 chi ∧
      Fin15AnchoredAtom0682 chi ∧
      Fin15AnchoredAtom0687 chi ∧
      Fin15AnchoredAtom0787 chi ∧
      Fin15AnchoredAtom1578 chi) ∨
      (Fin15AnchoredAtom2580 chi ∧
      ¬Fin15AnchoredAtom0679 chi))) ∨
      (((Fin15AnchoredAtom2580 chi ∧
      ¬Fin15AnchoredAtom0683 chi) ∨
      (Fin15AnchoredAtom2580 chi ∧
      ¬Fin15AnchoredAtom0688 chi)) ∨
      ((Fin15AnchoredAtom2580 chi ∧
      ¬Fin15AnchoredAtom0788 chi) ∨
      (¬Fin15AnchoredAtom2580 chi ∧
      Fin15AnchoredAtom0679 chi ∧
      Fin15AnchoredAtom0683 chi ∧
      Fin15AnchoredAtom0688 chi ∧
      Fin15AnchoredAtom0788 chi ∧
      Fin15AnchoredAtom1579 chi)))))))))) := by
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
                exact fin15Anchored_clause18929 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18930 chi hbad
                ·
                  exact fin15Anchored_clause18931 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18932 chi hbad
                ·
                  exact fin15Anchored_clause18933 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18934 chi hbad
                ·
                  exact fin15Anchored_clause18935 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18936 chi hbad
                ·
                  exact fin15Anchored_clause18937 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18938 chi hbad
                ·
                  exact fin15Anchored_clause18939 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18940 chi hbad
                ·
                  exact fin15Anchored_clause18941 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18942 chi hbad
                ·
                  exact fin15Anchored_clause18943 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18944 chi hbad
                ·
                  exact fin15Anchored_clause18945 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18946 chi hbad
                ·
                  exact fin15Anchored_clause18947 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18948 chi hbad
                ·
                  exact fin15Anchored_clause18949 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18950 chi hbad
                ·
                  exact fin15Anchored_clause18951 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18952 chi hbad
                ·
                  exact fin15Anchored_clause18953 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18954 chi hbad
                ·
                  exact fin15Anchored_clause18955 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18956 chi hbad
                ·
                  exact fin15Anchored_clause18957 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18958 chi hbad
                ·
                  exact fin15Anchored_clause18959 chi hbad
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
                  exact fin15Anchored_clause18960 chi hbad
                ·
                  exact fin15Anchored_clause18961 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18962 chi hbad
                ·
                  exact fin15Anchored_clause18963 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18964 chi hbad
                ·
                  exact fin15Anchored_clause18965 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18966 chi hbad
                ·
                  exact fin15Anchored_clause18967 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18968 chi hbad
                ·
                  exact fin15Anchored_clause18969 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18970 chi hbad
                ·
                  exact fin15Anchored_clause18971 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18972 chi hbad
                ·
                  exact fin15Anchored_clause18973 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18974 chi hbad
                ·
                  exact fin15Anchored_clause18975 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18976 chi hbad
                ·
                  exact fin15Anchored_clause18977 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18978 chi hbad
                ·
                  exact fin15Anchored_clause18979 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18980 chi hbad
                ·
                  exact fin15Anchored_clause18981 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18982 chi hbad
                ·
                  exact fin15Anchored_clause18983 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18984 chi hbad
                ·
                  exact fin15Anchored_clause18985 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18986 chi hbad
                ·
                  exact fin15Anchored_clause18987 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18988 chi hbad
                ·
                  exact fin15Anchored_clause18989 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18990 chi hbad
                ·
                  exact fin15Anchored_clause18991 chi hbad
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
                exact fin15Anchored_clause18992 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18993 chi hbad
                ·
                  exact fin15Anchored_clause18994 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18995 chi hbad
                ·
                  exact fin15Anchored_clause18996 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18997 chi hbad
                ·
                  exact fin15Anchored_clause18998 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause18999 chi hbad
                ·
                  exact fin15Anchored_clause19000 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19001 chi hbad
                ·
                  exact fin15Anchored_clause19002 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19003 chi hbad
                ·
                  exact fin15Anchored_clause19004 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19005 chi hbad
                ·
                  exact fin15Anchored_clause19006 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19007 chi hbad
                ·
                  exact fin15Anchored_clause19008 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19009 chi hbad
                ·
                  exact fin15Anchored_clause19010 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19011 chi hbad
                ·
                  exact fin15Anchored_clause19012 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19013 chi hbad
                ·
                  exact fin15Anchored_clause19014 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19015 chi hbad
                ·
                  exact fin15Anchored_clause19016 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19017 chi hbad
                ·
                  exact fin15Anchored_clause19018 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19019 chi hbad
                ·
                  exact fin15Anchored_clause19020 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19021 chi hbad
                ·
                  exact fin15Anchored_clause19022 chi hbad
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
                  exact fin15Anchored_clause19023 chi hbad
                ·
                  exact fin15Anchored_clause19024 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19025 chi hbad
                ·
                  exact fin15Anchored_clause19026 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19027 chi hbad
                ·
                  exact fin15Anchored_clause19028 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19029 chi hbad
                ·
                  exact fin15Anchored_clause19030 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19031 chi hbad
                ·
                  exact fin15Anchored_clause19032 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19033 chi hbad
                ·
                  exact fin15Anchored_clause19034 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19035 chi hbad
                ·
                  exact fin15Anchored_clause19036 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19037 chi hbad
                ·
                  exact fin15Anchored_clause19038 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19039 chi hbad
                ·
                  exact fin15Anchored_clause19040 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19041 chi hbad
                ·
                  exact fin15Anchored_clause19042 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19043 chi hbad
                ·
                  exact fin15Anchored_clause19044 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19045 chi hbad
                ·
                  exact fin15Anchored_clause19046 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19047 chi hbad
                ·
                  exact fin15Anchored_clause19048 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19049 chi hbad
                ·
                  exact fin15Anchored_clause19050 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19051 chi hbad
                ·
                  exact fin15Anchored_clause19052 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19053 chi hbad
                ·
                  exact fin15Anchored_clause19054 chi hbad
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
                exact fin15Anchored_clause19055 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19056 chi hbad
                ·
                  exact fin15Anchored_clause19057 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19058 chi hbad
                ·
                  exact fin15Anchored_clause19059 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19060 chi hbad
                ·
                  exact fin15Anchored_clause19061 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19062 chi hbad
                ·
                  exact fin15Anchored_clause19063 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19064 chi hbad
                ·
                  exact fin15Anchored_clause19065 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19066 chi hbad
                ·
                  exact fin15Anchored_clause19067 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19068 chi hbad
                ·
                  exact fin15Anchored_clause19069 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19070 chi hbad
                ·
                  exact fin15Anchored_clause19071 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19072 chi hbad
                ·
                  exact fin15Anchored_clause19073 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19074 chi hbad
                ·
                  exact fin15Anchored_clause19075 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19076 chi hbad
                ·
                  exact fin15Anchored_clause19077 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19078 chi hbad
                ·
                  exact fin15Anchored_clause19079 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19080 chi hbad
                ·
                  exact fin15Anchored_clause19081 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19082 chi hbad
                ·
                  exact fin15Anchored_clause19083 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19084 chi hbad
                ·
                  exact fin15Anchored_clause19085 chi hbad
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
                  exact fin15Anchored_clause19086 chi hbad
                ·
                  exact fin15Anchored_clause19087 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19088 chi hbad
                ·
                  exact fin15Anchored_clause19089 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19090 chi hbad
                ·
                  exact fin15Anchored_clause19091 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19092 chi hbad
                ·
                  exact fin15Anchored_clause19093 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19094 chi hbad
                ·
                  exact fin15Anchored_clause19095 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19096 chi hbad
                ·
                  exact fin15Anchored_clause19097 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19098 chi hbad
                ·
                  exact fin15Anchored_clause19099 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19100 chi hbad
                ·
                  exact fin15Anchored_clause19101 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19102 chi hbad
                ·
                  exact fin15Anchored_clause19103 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19104 chi hbad
                ·
                  exact fin15Anchored_clause19105 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19106 chi hbad
                ·
                  exact fin15Anchored_clause19107 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19108 chi hbad
                ·
                  exact fin15Anchored_clause19109 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19110 chi hbad
                ·
                  exact fin15Anchored_clause19111 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19112 chi hbad
                ·
                  exact fin15Anchored_clause19113 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19114 chi hbad
                ·
                  exact fin15Anchored_clause19115 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19116 chi hbad
                ·
                  exact fin15Anchored_clause19117 chi hbad
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
                  exact fin15Anchored_clause19118 chi hbad
                ·
                  exact fin15Anchored_clause19119 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19120 chi hbad
                ·
                  exact fin15Anchored_clause19121 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19122 chi hbad
                ·
                  exact fin15Anchored_clause19123 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19124 chi hbad
                ·
                  exact fin15Anchored_clause19125 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19126 chi hbad
                ·
                  exact fin15Anchored_clause19127 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19128 chi hbad
                ·
                  exact fin15Anchored_clause19129 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19130 chi hbad
                ·
                  exact fin15Anchored_clause19131 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19132 chi hbad
                ·
                  exact fin15Anchored_clause19133 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19134 chi hbad
                ·
                  exact fin15Anchored_clause19135 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19136 chi hbad
                ·
                  exact fin15Anchored_clause19137 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19138 chi hbad
                ·
                  exact fin15Anchored_clause19139 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19140 chi hbad
                ·
                  exact fin15Anchored_clause19141 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19142 chi hbad
                ·
                  exact fin15Anchored_clause19143 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19144 chi hbad
                ·
                  exact fin15Anchored_clause19145 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19146 chi hbad
                ·
                  exact fin15Anchored_clause19147 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19148 chi hbad
                ·
                  exact fin15Anchored_clause19149 chi hbad
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
                  exact fin15Anchored_clause19150 chi hbad
                ·
                  exact fin15Anchored_clause19151 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19152 chi hbad
                ·
                  exact fin15Anchored_clause19153 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19154 chi hbad
                ·
                  exact fin15Anchored_clause19155 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19156 chi hbad
                ·
                  exact fin15Anchored_clause19157 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19158 chi hbad
                ·
                  exact fin15Anchored_clause19159 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19160 chi hbad
                ·
                  exact fin15Anchored_clause19161 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19162 chi hbad
                ·
                  exact fin15Anchored_clause19163 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19164 chi hbad
                ·
                  exact fin15Anchored_clause19165 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19166 chi hbad
                ·
                  exact fin15Anchored_clause19167 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19168 chi hbad
                ·
                  exact fin15Anchored_clause19169 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19170 chi hbad
                ·
                  exact fin15Anchored_clause19171 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19172 chi hbad
                ·
                  exact fin15Anchored_clause19173 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19174 chi hbad
                ·
                  exact fin15Anchored_clause19175 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19176 chi hbad
                ·
                  exact fin15Anchored_clause19177 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19178 chi hbad
                ·
                  exact fin15Anchored_clause19179 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19180 chi hbad
                ·
                  exact fin15Anchored_clause19181 chi hbad

end ErdosSzekeres

end
