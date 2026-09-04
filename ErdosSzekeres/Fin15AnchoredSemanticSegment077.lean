module

public import ErdosSzekeres.Fin15AnchoredClauseChunk151
public import ErdosSzekeres.Fin15AnchoredClauseChunk152
public import ErdosSzekeres.Fin15AnchoredClauseChunk153

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 077. -/

theorem fin15Anchored_rejectSemanticSegment077
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom0728 chi) ∨
      ((Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom0756 chi) ∨
      (Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom1631 chi))) ∨
      (((¬Fin15AnchoredAtom2632 chi ∧
      Fin15AnchoredAtom0703 chi ∧
      Fin15AnchoredAtom0706 chi ∧
      Fin15AnchoredAtom0728 chi ∧
      Fin15AnchoredAtom0756 chi ∧
      Fin15AnchoredAtom1631 chi) ∨
      (Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom0703 chi)) ∨
      ((Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom0707 chi) ∨
      (Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom0729 chi)))) ∨
      ((((Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom0757 chi) ∨
      (Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom1632 chi)) ∨
      ((¬Fin15AnchoredAtom2633 chi ∧
      Fin15AnchoredAtom0703 chi ∧
      Fin15AnchoredAtom0707 chi ∧
      Fin15AnchoredAtom0729 chi ∧
      Fin15AnchoredAtom0757 chi ∧
      Fin15AnchoredAtom1632 chi) ∨
      (Fin15AnchoredAtom2634 chi ∧
      ¬Fin15AnchoredAtom0705 chi))) ∨
      (((Fin15AnchoredAtom2634 chi ∧
      ¬Fin15AnchoredAtom0730 chi) ∨
      (Fin15AnchoredAtom2634 chi ∧
      ¬Fin15AnchoredAtom0758 chi)) ∨
      ((Fin15AnchoredAtom2634 chi ∧
      ¬Fin15AnchoredAtom1633 chi) ∨
      (¬Fin15AnchoredAtom2634 chi ∧
      Fin15AnchoredAtom0704 chi ∧
      Fin15AnchoredAtom0705 chi ∧
      Fin15AnchoredAtom0730 chi ∧
      Fin15AnchoredAtom0758 chi ∧
      Fin15AnchoredAtom1633 chi))))) ∨
      (((((Fin15AnchoredAtom2635 chi ∧
      ¬Fin15AnchoredAtom1634 chi) ∨
      (¬Fin15AnchoredAtom2635 chi ∧
      Fin15AnchoredAtom0704 chi ∧
      Fin15AnchoredAtom0706 chi ∧
      Fin15AnchoredAtom0731 chi ∧
      Fin15AnchoredAtom0759 chi ∧
      Fin15AnchoredAtom1634 chi)) ∨
      ((Fin15AnchoredAtom2636 chi ∧
      ¬Fin15AnchoredAtom0707 chi) ∨
      (Fin15AnchoredAtom2636 chi ∧
      ¬Fin15AnchoredAtom0732 chi))) ∨
      (((Fin15AnchoredAtom2636 chi ∧
      ¬Fin15AnchoredAtom0760 chi) ∨
      (Fin15AnchoredAtom2636 chi ∧
      ¬Fin15AnchoredAtom1635 chi)) ∨
      ((¬Fin15AnchoredAtom2636 chi ∧
      Fin15AnchoredAtom0704 chi ∧
      Fin15AnchoredAtom0707 chi ∧
      Fin15AnchoredAtom0732 chi ∧
      Fin15AnchoredAtom0760 chi ∧
      Fin15AnchoredAtom1635 chi) ∨
      (Fin15AnchoredAtom2637 chi ∧
      ¬Fin15AnchoredAtom0705 chi)))) ∨
      ((((Fin15AnchoredAtom2637 chi ∧
      ¬Fin15AnchoredAtom0706 chi) ∨
      (Fin15AnchoredAtom2637 chi ∧
      ¬Fin15AnchoredAtom0733 chi)) ∨
      ((Fin15AnchoredAtom2637 chi ∧
      ¬Fin15AnchoredAtom0761 chi) ∨
      (Fin15AnchoredAtom2637 chi ∧
      ¬Fin15AnchoredAtom1636 chi))) ∨
      (((¬Fin15AnchoredAtom2637 chi ∧
      Fin15AnchoredAtom0705 chi ∧
      Fin15AnchoredAtom0706 chi ∧
      Fin15AnchoredAtom0733 chi ∧
      Fin15AnchoredAtom0761 chi ∧
      Fin15AnchoredAtom1636 chi) ∨
      (Fin15AnchoredAtom2638 chi ∧
      ¬Fin15AnchoredAtom0705 chi)) ∨
      ((Fin15AnchoredAtom2638 chi ∧
      ¬Fin15AnchoredAtom0707 chi) ∨
      (Fin15AnchoredAtom2638 chi ∧
      ¬Fin15AnchoredAtom0734 chi)))))) ∨
      ((((((Fin15AnchoredAtom2638 chi ∧
      ¬Fin15AnchoredAtom0762 chi) ∨
      (Fin15AnchoredAtom2638 chi ∧
      ¬Fin15AnchoredAtom1637 chi)) ∨
      ((¬Fin15AnchoredAtom2638 chi ∧
      Fin15AnchoredAtom0705 chi ∧
      Fin15AnchoredAtom0707 chi ∧
      Fin15AnchoredAtom0734 chi ∧
      Fin15AnchoredAtom0762 chi ∧
      Fin15AnchoredAtom1637 chi) ∨
      (Fin15AnchoredAtom2639 chi ∧
      ¬Fin15AnchoredAtom0706 chi))) ∨
      (((Fin15AnchoredAtom2639 chi ∧
      ¬Fin15AnchoredAtom0707 chi) ∨
      (Fin15AnchoredAtom2639 chi ∧
      ¬Fin15AnchoredAtom0735 chi)) ∨
      ((Fin15AnchoredAtom2639 chi ∧
      ¬Fin15AnchoredAtom0763 chi) ∨
      (Fin15AnchoredAtom2639 chi ∧
      ¬Fin15AnchoredAtom1638 chi)))) ∨
      ((((¬Fin15AnchoredAtom2639 chi ∧
      Fin15AnchoredAtom0706 chi ∧
      Fin15AnchoredAtom0707 chi ∧
      Fin15AnchoredAtom0735 chi ∧
      Fin15AnchoredAtom0763 chi ∧
      Fin15AnchoredAtom1638 chi) ∨
      (Fin15AnchoredAtom2640 chi ∧
      ¬Fin15AnchoredAtom0708 chi)) ∨
      ((Fin15AnchoredAtom2640 chi ∧
      ¬Fin15AnchoredAtom0709 chi) ∨
      (Fin15AnchoredAtom2640 chi ∧
      ¬Fin15AnchoredAtom0715 chi))) ∨
      (((Fin15AnchoredAtom2640 chi ∧
      ¬Fin15AnchoredAtom0764 chi) ∨
      (Fin15AnchoredAtom2640 chi ∧
      ¬Fin15AnchoredAtom1639 chi)) ∨
      ((¬Fin15AnchoredAtom2640 chi ∧
      Fin15AnchoredAtom0708 chi ∧
      Fin15AnchoredAtom0709 chi ∧
      Fin15AnchoredAtom0715 chi ∧
      Fin15AnchoredAtom0764 chi ∧
      Fin15AnchoredAtom1639 chi) ∨
      (Fin15AnchoredAtom2641 chi ∧
      ¬Fin15AnchoredAtom0708 chi))))) ∨
      (((((Fin15AnchoredAtom2641 chi ∧
      ¬Fin15AnchoredAtom0710 chi) ∨
      (Fin15AnchoredAtom2641 chi ∧
      ¬Fin15AnchoredAtom0716 chi)) ∨
      ((Fin15AnchoredAtom2641 chi ∧
      ¬Fin15AnchoredAtom0765 chi) ∨
      (¬Fin15AnchoredAtom2641 chi ∧
      Fin15AnchoredAtom0708 chi ∧
      Fin15AnchoredAtom0710 chi ∧
      Fin15AnchoredAtom0716 chi ∧
      Fin15AnchoredAtom0765 chi ∧
      Fin15AnchoredAtom1640 chi))) ∨
      (((Fin15AnchoredAtom2643 chi ∧
      ¬Fin15AnchoredAtom0708 chi) ∨
      (Fin15AnchoredAtom2643 chi ∧
      ¬Fin15AnchoredAtom0712 chi)) ∨
      ((Fin15AnchoredAtom2643 chi ∧
      ¬Fin15AnchoredAtom0718 chi) ∨
      (Fin15AnchoredAtom2643 chi ∧
      ¬Fin15AnchoredAtom0767 chi)))) ∨
      ((((¬Fin15AnchoredAtom2643 chi ∧
      Fin15AnchoredAtom0708 chi ∧
      Fin15AnchoredAtom0712 chi ∧
      Fin15AnchoredAtom0718 chi ∧
      Fin15AnchoredAtom0767 chi ∧
      Fin15AnchoredAtom1642 chi) ∨
      (Fin15AnchoredAtom2644 chi ∧
      ¬Fin15AnchoredAtom0708 chi)) ∨
      ((Fin15AnchoredAtom2644 chi ∧
      ¬Fin15AnchoredAtom0713 chi) ∨
      (Fin15AnchoredAtom2644 chi ∧
      ¬Fin15AnchoredAtom0719 chi))) ∨
      (((Fin15AnchoredAtom2644 chi ∧
      ¬Fin15AnchoredAtom0768 chi) ∨
      (Fin15AnchoredAtom2644 chi ∧
      ¬Fin15AnchoredAtom1643 chi)) ∨
      ((¬Fin15AnchoredAtom2644 chi ∧
      Fin15AnchoredAtom0708 chi ∧
      Fin15AnchoredAtom0713 chi ∧
      Fin15AnchoredAtom0719 chi ∧
      Fin15AnchoredAtom0768 chi ∧
      Fin15AnchoredAtom1643 chi) ∨
      (Fin15AnchoredAtom2645 chi ∧
      ¬Fin15AnchoredAtom0708 chi))))))) ∨
      ((((((Fin15AnchoredAtom2645 chi ∧
      ¬Fin15AnchoredAtom0714 chi) ∨
      ((Fin15AnchoredAtom2645 chi ∧
      ¬Fin15AnchoredAtom0720 chi) ∨
      (Fin15AnchoredAtom2645 chi ∧
      ¬Fin15AnchoredAtom0769 chi))) ∨
      (((Fin15AnchoredAtom2645 chi ∧
      ¬Fin15AnchoredAtom1644 chi) ∨
      (¬Fin15AnchoredAtom2645 chi ∧
      Fin15AnchoredAtom0708 chi ∧
      Fin15AnchoredAtom0714 chi ∧
      Fin15AnchoredAtom0720 chi ∧
      Fin15AnchoredAtom0769 chi ∧
      Fin15AnchoredAtom1644 chi)) ∨
      ((Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom0709 chi) ∨
      (Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom0710 chi)))) ∨
      ((((Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom0721 chi) ∨
      (Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom0770 chi)) ∨
      ((Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom1645 chi) ∨
      (¬Fin15AnchoredAtom2646 chi ∧
      Fin15AnchoredAtom0709 chi ∧
      Fin15AnchoredAtom0710 chi ∧
      Fin15AnchoredAtom0721 chi ∧
      Fin15AnchoredAtom0770 chi ∧
      Fin15AnchoredAtom1645 chi))) ∨
      (((Fin15AnchoredAtom2647 chi ∧
      ¬Fin15AnchoredAtom0711 chi) ∨
      (Fin15AnchoredAtom2647 chi ∧
      ¬Fin15AnchoredAtom0722 chi)) ∨
      ((Fin15AnchoredAtom2647 chi ∧
      ¬Fin15AnchoredAtom0771 chi) ∨
      (Fin15AnchoredAtom2647 chi ∧
      ¬Fin15AnchoredAtom1646 chi))))) ∨
      (((((¬Fin15AnchoredAtom2647 chi ∧
      Fin15AnchoredAtom0709 chi ∧
      Fin15AnchoredAtom0711 chi ∧
      Fin15AnchoredAtom0722 chi ∧
      Fin15AnchoredAtom0771 chi ∧
      Fin15AnchoredAtom1646 chi) ∨
      (Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom0709 chi)) ∨
      ((Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom0712 chi) ∨
      (Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom0723 chi))) ∨
      (((Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom0772 chi) ∨
      (Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom1647 chi)) ∨
      ((¬Fin15AnchoredAtom2648 chi ∧
      Fin15AnchoredAtom0709 chi ∧
      Fin15AnchoredAtom0712 chi ∧
      Fin15AnchoredAtom0723 chi ∧
      Fin15AnchoredAtom0772 chi ∧
      Fin15AnchoredAtom1647 chi) ∨
      (Fin15AnchoredAtom2649 chi ∧
      ¬Fin15AnchoredAtom0709 chi)))) ∨
      ((((Fin15AnchoredAtom2649 chi ∧
      ¬Fin15AnchoredAtom0713 chi) ∨
      (Fin15AnchoredAtom2649 chi ∧
      ¬Fin15AnchoredAtom0724 chi)) ∨
      ((Fin15AnchoredAtom2649 chi ∧
      ¬Fin15AnchoredAtom0773 chi) ∨
      (Fin15AnchoredAtom2649 chi ∧
      ¬Fin15AnchoredAtom1648 chi))) ∨
      (((¬Fin15AnchoredAtom2649 chi ∧
      Fin15AnchoredAtom0709 chi ∧
      Fin15AnchoredAtom0713 chi ∧
      Fin15AnchoredAtom0724 chi ∧
      Fin15AnchoredAtom0773 chi ∧
      Fin15AnchoredAtom1648 chi) ∨
      (Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom0709 chi)) ∨
      ((Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom0714 chi) ∨
      (Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom0725 chi)))))) ∨
      ((((((Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom0774 chi) ∨
      (Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom1649 chi)) ∨
      ((¬Fin15AnchoredAtom2650 chi ∧
      Fin15AnchoredAtom0709 chi ∧
      Fin15AnchoredAtom0714 chi ∧
      Fin15AnchoredAtom0725 chi ∧
      Fin15AnchoredAtom0774 chi ∧
      Fin15AnchoredAtom1649 chi) ∨
      (Fin15AnchoredAtom2651 chi ∧
      ¬Fin15AnchoredAtom0710 chi))) ∨
      (((Fin15AnchoredAtom2651 chi ∧
      ¬Fin15AnchoredAtom0711 chi) ∨
      (Fin15AnchoredAtom2651 chi ∧
      ¬Fin15AnchoredAtom0726 chi)) ∨
      ((Fin15AnchoredAtom2651 chi ∧
      ¬Fin15AnchoredAtom0775 chi) ∨
      (Fin15AnchoredAtom2651 chi ∧
      ¬Fin15AnchoredAtom1650 chi)))) ∨
      ((((¬Fin15AnchoredAtom2651 chi ∧
      Fin15AnchoredAtom0710 chi ∧
      Fin15AnchoredAtom0711 chi ∧
      Fin15AnchoredAtom0726 chi ∧
      Fin15AnchoredAtom0775 chi ∧
      Fin15AnchoredAtom1650 chi) ∨
      (Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom0710 chi)) ∨
      ((Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom0712 chi) ∨
      (Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom0727 chi))) ∨
      (((Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom0776 chi) ∨
      (Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom1651 chi)) ∨
      ((¬Fin15AnchoredAtom2652 chi ∧
      Fin15AnchoredAtom0710 chi ∧
      Fin15AnchoredAtom0712 chi ∧
      Fin15AnchoredAtom0727 chi ∧
      Fin15AnchoredAtom0776 chi ∧
      Fin15AnchoredAtom1651 chi) ∨
      (Fin15AnchoredAtom2653 chi ∧
      ¬Fin15AnchoredAtom0710 chi))))) ∨
      (((((Fin15AnchoredAtom2653 chi ∧
      ¬Fin15AnchoredAtom0713 chi) ∨
      (Fin15AnchoredAtom2653 chi ∧
      ¬Fin15AnchoredAtom0728 chi)) ∨
      ((Fin15AnchoredAtom2653 chi ∧
      ¬Fin15AnchoredAtom0777 chi) ∨
      (Fin15AnchoredAtom2653 chi ∧
      ¬Fin15AnchoredAtom1652 chi))) ∨
      (((¬Fin15AnchoredAtom2653 chi ∧
      Fin15AnchoredAtom0710 chi ∧
      Fin15AnchoredAtom0713 chi ∧
      Fin15AnchoredAtom0728 chi ∧
      Fin15AnchoredAtom0777 chi ∧
      Fin15AnchoredAtom1652 chi) ∨
      (Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom0710 chi)) ∨
      ((Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom0714 chi) ∨
      (Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom0729 chi)))) ∨
      ((((Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom0778 chi) ∨
      (Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom1653 chi)) ∨
      ((¬Fin15AnchoredAtom2654 chi ∧
      Fin15AnchoredAtom0710 chi ∧
      Fin15AnchoredAtom0714 chi ∧
      Fin15AnchoredAtom0729 chi ∧
      Fin15AnchoredAtom0778 chi ∧
      Fin15AnchoredAtom1653 chi) ∨
      (Fin15AnchoredAtom2655 chi ∧
      ¬Fin15AnchoredAtom0712 chi))) ∨
      (((Fin15AnchoredAtom2655 chi ∧
      ¬Fin15AnchoredAtom0730 chi) ∨
      (Fin15AnchoredAtom2655 chi ∧
      ¬Fin15AnchoredAtom0779 chi)) ∨
      ((¬Fin15AnchoredAtom2655 chi ∧
      Fin15AnchoredAtom0711 chi ∧
      Fin15AnchoredAtom0712 chi ∧
      Fin15AnchoredAtom0730 chi ∧
      Fin15AnchoredAtom0779 chi ∧
      Fin15AnchoredAtom1654 chi) ∨
      (Fin15AnchoredAtom2656 chi ∧
      ¬Fin15AnchoredAtom0713 chi)))))))) ∨
      (((((((Fin15AnchoredAtom2656 chi ∧
      ¬Fin15AnchoredAtom0780 chi) ∨
      ((Fin15AnchoredAtom2656 chi ∧
      ¬Fin15AnchoredAtom1655 chi) ∨
      (¬Fin15AnchoredAtom2656 chi ∧
      Fin15AnchoredAtom0711 chi ∧
      Fin15AnchoredAtom0713 chi ∧
      Fin15AnchoredAtom0731 chi ∧
      Fin15AnchoredAtom0780 chi ∧
      Fin15AnchoredAtom1655 chi))) ∨
      (((Fin15AnchoredAtom2657 chi ∧
      ¬Fin15AnchoredAtom0714 chi) ∨
      (Fin15AnchoredAtom2657 chi ∧
      ¬Fin15AnchoredAtom0732 chi)) ∨
      ((Fin15AnchoredAtom2657 chi ∧
      ¬Fin15AnchoredAtom0781 chi) ∨
      (Fin15AnchoredAtom2658 chi ∧
      ¬Fin15AnchoredAtom0712 chi)))) ∨
      ((((Fin15AnchoredAtom2658 chi ∧
      ¬Fin15AnchoredAtom0713 chi) ∨
      (Fin15AnchoredAtom2658 chi ∧
      ¬Fin15AnchoredAtom0733 chi)) ∨
      ((Fin15AnchoredAtom2658 chi ∧
      ¬Fin15AnchoredAtom0782 chi) ∨
      (Fin15AnchoredAtom2658 chi ∧
      ¬Fin15AnchoredAtom1657 chi))) ∨
      (((¬Fin15AnchoredAtom2658 chi ∧
      Fin15AnchoredAtom0712 chi ∧
      Fin15AnchoredAtom0713 chi ∧
      Fin15AnchoredAtom0733 chi ∧
      Fin15AnchoredAtom0782 chi ∧
      Fin15AnchoredAtom1657 chi) ∨
      (Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom0712 chi)) ∨
      ((Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom0714 chi) ∨
      (Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom0734 chi))))) ∨
      (((((Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom0783 chi) ∨
      (Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom1658 chi)) ∨
      ((¬Fin15AnchoredAtom2659 chi ∧
      Fin15AnchoredAtom0712 chi ∧
      Fin15AnchoredAtom0714 chi ∧
      Fin15AnchoredAtom0734 chi ∧
      Fin15AnchoredAtom0783 chi ∧
      Fin15AnchoredAtom1658 chi) ∨
      (Fin15AnchoredAtom2660 chi ∧
      ¬Fin15AnchoredAtom0713 chi))) ∨
      (((Fin15AnchoredAtom2660 chi ∧
      ¬Fin15AnchoredAtom0714 chi) ∨
      (Fin15AnchoredAtom2660 chi ∧
      ¬Fin15AnchoredAtom0735 chi)) ∨
      ((Fin15AnchoredAtom2660 chi ∧
      ¬Fin15AnchoredAtom0784 chi) ∨
      (Fin15AnchoredAtom2660 chi ∧
      ¬Fin15AnchoredAtom1659 chi)))) ∨
      ((((¬Fin15AnchoredAtom2660 chi ∧
      Fin15AnchoredAtom0713 chi ∧
      Fin15AnchoredAtom0714 chi ∧
      Fin15AnchoredAtom0735 chi ∧
      Fin15AnchoredAtom0784 chi ∧
      Fin15AnchoredAtom1659 chi) ∨
      (Fin15AnchoredAtom2661 chi ∧
      ¬Fin15AnchoredAtom0715 chi)) ∨
      ((Fin15AnchoredAtom2661 chi ∧
      ¬Fin15AnchoredAtom0716 chi) ∨
      (Fin15AnchoredAtom2661 chi ∧
      ¬Fin15AnchoredAtom0721 chi))) ∨
      (((Fin15AnchoredAtom2661 chi ∧
      ¬Fin15AnchoredAtom0785 chi) ∨
      (Fin15AnchoredAtom2661 chi ∧
      ¬Fin15AnchoredAtom1660 chi)) ∨
      ((¬Fin15AnchoredAtom2661 chi ∧
      Fin15AnchoredAtom0715 chi ∧
      Fin15AnchoredAtom0716 chi ∧
      Fin15AnchoredAtom0721 chi ∧
      Fin15AnchoredAtom0785 chi ∧
      Fin15AnchoredAtom1660 chi) ∨
      (Fin15AnchoredAtom2663 chi ∧
      ¬Fin15AnchoredAtom0715 chi)))))) ∨
      ((((((Fin15AnchoredAtom2663 chi ∧
      ¬Fin15AnchoredAtom0718 chi) ∨
      (Fin15AnchoredAtom2663 chi ∧
      ¬Fin15AnchoredAtom0723 chi)) ∨
      ((Fin15AnchoredAtom2663 chi ∧
      ¬Fin15AnchoredAtom0787 chi) ∨
      (Fin15AnchoredAtom2663 chi ∧
      ¬Fin15AnchoredAtom1662 chi))) ∨
      (((¬Fin15AnchoredAtom2663 chi ∧
      Fin15AnchoredAtom0715 chi ∧
      Fin15AnchoredAtom0718 chi ∧
      Fin15AnchoredAtom0723 chi ∧
      Fin15AnchoredAtom0787 chi ∧
      Fin15AnchoredAtom1662 chi) ∨
      (Fin15AnchoredAtom2664 chi ∧
      ¬Fin15AnchoredAtom0715 chi)) ∨
      ((Fin15AnchoredAtom2664 chi ∧
      ¬Fin15AnchoredAtom0724 chi) ∨
      (Fin15AnchoredAtom2664 chi ∧
      ¬Fin15AnchoredAtom0788 chi)))) ∨
      ((((Fin15AnchoredAtom2664 chi ∧
      ¬Fin15AnchoredAtom1663 chi) ∨
      (¬Fin15AnchoredAtom2664 chi ∧
      Fin15AnchoredAtom0715 chi ∧
      Fin15AnchoredAtom0719 chi ∧
      Fin15AnchoredAtom0724 chi ∧
      Fin15AnchoredAtom0788 chi ∧
      Fin15AnchoredAtom1663 chi)) ∨
      ((Fin15AnchoredAtom2665 chi ∧
      ¬Fin15AnchoredAtom0715 chi) ∨
      (Fin15AnchoredAtom2665 chi ∧
      ¬Fin15AnchoredAtom0720 chi))) ∨
      (((Fin15AnchoredAtom2665 chi ∧
      ¬Fin15AnchoredAtom0725 chi) ∨
      (Fin15AnchoredAtom2665 chi ∧
      ¬Fin15AnchoredAtom0789 chi)) ∨
      ((Fin15AnchoredAtom2665 chi ∧
      ¬Fin15AnchoredAtom1664 chi) ∨
      (¬Fin15AnchoredAtom2665 chi ∧
      Fin15AnchoredAtom0715 chi ∧
      Fin15AnchoredAtom0720 chi ∧
      Fin15AnchoredAtom0725 chi ∧
      Fin15AnchoredAtom0789 chi ∧
      Fin15AnchoredAtom1664 chi))))) ∨
      (((((Fin15AnchoredAtom2667 chi ∧
      ¬Fin15AnchoredAtom0716 chi) ∨
      (Fin15AnchoredAtom2667 chi ∧
      ¬Fin15AnchoredAtom0718 chi)) ∨
      ((Fin15AnchoredAtom2667 chi ∧
      ¬Fin15AnchoredAtom0727 chi) ∨
      (Fin15AnchoredAtom2667 chi ∧
      ¬Fin15AnchoredAtom0791 chi))) ∨
      (((Fin15AnchoredAtom2667 chi ∧
      ¬Fin15AnchoredAtom1666 chi) ∨
      (¬Fin15AnchoredAtom2667 chi ∧
      Fin15AnchoredAtom0716 chi ∧
      Fin15AnchoredAtom0718 chi ∧
      Fin15AnchoredAtom0727 chi ∧
      Fin15AnchoredAtom0791 chi ∧
      Fin15AnchoredAtom1666 chi)) ∨
      ((Fin15AnchoredAtom2668 chi ∧
      ¬Fin15AnchoredAtom0716 chi) ∨
      (Fin15AnchoredAtom2668 chi ∧
      ¬Fin15AnchoredAtom0728 chi)))) ∨
      ((((Fin15AnchoredAtom2668 chi ∧
      ¬Fin15AnchoredAtom0792 chi) ∨
      (Fin15AnchoredAtom2668 chi ∧
      ¬Fin15AnchoredAtom1667 chi)) ∨
      ((¬Fin15AnchoredAtom2668 chi ∧
      Fin15AnchoredAtom0716 chi ∧
      Fin15AnchoredAtom0719 chi ∧
      Fin15AnchoredAtom0728 chi ∧
      Fin15AnchoredAtom0792 chi ∧
      Fin15AnchoredAtom1667 chi) ∨
      (Fin15AnchoredAtom2669 chi ∧
      ¬Fin15AnchoredAtom0716 chi))) ∨
      (((Fin15AnchoredAtom2669 chi ∧
      ¬Fin15AnchoredAtom0720 chi) ∨
      (Fin15AnchoredAtom2669 chi ∧
      ¬Fin15AnchoredAtom0729 chi)) ∨
      ((Fin15AnchoredAtom2669 chi ∧
      ¬Fin15AnchoredAtom0793 chi) ∨
      (Fin15AnchoredAtom2669 chi ∧
      ¬Fin15AnchoredAtom1668 chi))))))) ∨
      (((((((¬Fin15AnchoredAtom2669 chi ∧
      Fin15AnchoredAtom0716 chi ∧
      Fin15AnchoredAtom0720 chi ∧
      Fin15AnchoredAtom0729 chi ∧
      Fin15AnchoredAtom0793 chi ∧
      Fin15AnchoredAtom1668 chi) ∨
      (Fin15AnchoredAtom2673 chi ∧
      ¬Fin15AnchoredAtom0718 chi)) ∨
      ((Fin15AnchoredAtom2673 chi ∧
      ¬Fin15AnchoredAtom0719 chi) ∨
      (Fin15AnchoredAtom2673 chi ∧
      ¬Fin15AnchoredAtom0733 chi))) ∨
      (((Fin15AnchoredAtom2673 chi ∧
      ¬Fin15AnchoredAtom0797 chi) ∨
      (¬Fin15AnchoredAtom2673 chi ∧
      Fin15AnchoredAtom0718 chi ∧
      Fin15AnchoredAtom0719 chi ∧
      Fin15AnchoredAtom0733 chi ∧
      Fin15AnchoredAtom0797 chi ∧
      Fin15AnchoredAtom1672 chi)) ∨
      ((Fin15AnchoredAtom2674 chi ∧
      ¬Fin15AnchoredAtom0718 chi) ∨
      (Fin15AnchoredAtom2674 chi ∧
      ¬Fin15AnchoredAtom0720 chi)))) ∨
      ((((Fin15AnchoredAtom2674 chi ∧
      ¬Fin15AnchoredAtom0734 chi) ∨
      (Fin15AnchoredAtom2674 chi ∧
      ¬Fin15AnchoredAtom0798 chi)) ∨
      ((Fin15AnchoredAtom2674 chi ∧
      ¬Fin15AnchoredAtom1673 chi) ∨
      (¬Fin15AnchoredAtom2674 chi ∧
      Fin15AnchoredAtom0718 chi ∧
      Fin15AnchoredAtom0720 chi ∧
      Fin15AnchoredAtom0734 chi ∧
      Fin15AnchoredAtom0798 chi ∧
      Fin15AnchoredAtom1673 chi))) ∨
      (((Fin15AnchoredAtom2675 chi ∧
      ¬Fin15AnchoredAtom0719 chi) ∨
      (Fin15AnchoredAtom2675 chi ∧
      ¬Fin15AnchoredAtom0720 chi)) ∨
      ((Fin15AnchoredAtom2675 chi ∧
      ¬Fin15AnchoredAtom0735 chi) ∨
      (Fin15AnchoredAtom2675 chi ∧
      ¬Fin15AnchoredAtom0799 chi))))) ∨
      (((((Fin15AnchoredAtom2675 chi ∧
      ¬Fin15AnchoredAtom1674 chi) ∨
      (¬Fin15AnchoredAtom2675 chi ∧
      Fin15AnchoredAtom0719 chi ∧
      Fin15AnchoredAtom0720 chi ∧
      Fin15AnchoredAtom0735 chi ∧
      Fin15AnchoredAtom0799 chi ∧
      Fin15AnchoredAtom1674 chi)) ∨
      ((Fin15AnchoredAtom2676 chi ∧
      ¬Fin15AnchoredAtom0800 chi) ∨
      (¬Fin15AnchoredAtom2676 chi ∧
      Fin15AnchoredAtom0721 chi ∧
      Fin15AnchoredAtom0722 chi ∧
      Fin15AnchoredAtom0726 chi ∧
      Fin15AnchoredAtom0800 chi ∧
      Fin15AnchoredAtom1675 chi))) ∨
      (((Fin15AnchoredAtom2677 chi ∧
      ¬Fin15AnchoredAtom0721 chi) ∨
      (Fin15AnchoredAtom2677 chi ∧
      ¬Fin15AnchoredAtom0723 chi)) ∨
      ((Fin15AnchoredAtom2677 chi ∧
      ¬Fin15AnchoredAtom0727 chi) ∨
      (Fin15AnchoredAtom2677 chi ∧
      ¬Fin15AnchoredAtom0801 chi)))) ∨
      ((((Fin15AnchoredAtom2677 chi ∧
      ¬Fin15AnchoredAtom1676 chi) ∨
      (¬Fin15AnchoredAtom2677 chi ∧
      Fin15AnchoredAtom0721 chi ∧
      Fin15AnchoredAtom0723 chi ∧
      Fin15AnchoredAtom0727 chi ∧
      Fin15AnchoredAtom0801 chi ∧
      Fin15AnchoredAtom1676 chi)) ∨
      ((Fin15AnchoredAtom2678 chi ∧
      ¬Fin15AnchoredAtom0721 chi) ∨
      (Fin15AnchoredAtom2678 chi ∧
      ¬Fin15AnchoredAtom0724 chi))) ∨
      (((Fin15AnchoredAtom2678 chi ∧
      ¬Fin15AnchoredAtom0728 chi) ∨
      (Fin15AnchoredAtom2678 chi ∧
      ¬Fin15AnchoredAtom0802 chi)) ∨
      ((Fin15AnchoredAtom2678 chi ∧
      ¬Fin15AnchoredAtom1677 chi) ∨
      (¬Fin15AnchoredAtom2678 chi ∧
      Fin15AnchoredAtom0721 chi ∧
      Fin15AnchoredAtom0724 chi ∧
      Fin15AnchoredAtom0728 chi ∧
      Fin15AnchoredAtom0802 chi ∧
      Fin15AnchoredAtom1677 chi)))))) ∨
      ((((((Fin15AnchoredAtom2679 chi ∧
      ¬Fin15AnchoredAtom0721 chi) ∨
      (Fin15AnchoredAtom2679 chi ∧
      ¬Fin15AnchoredAtom0725 chi)) ∨
      ((Fin15AnchoredAtom2679 chi ∧
      ¬Fin15AnchoredAtom0729 chi) ∨
      (Fin15AnchoredAtom2679 chi ∧
      ¬Fin15AnchoredAtom0803 chi))) ∨
      (((Fin15AnchoredAtom2679 chi ∧
      ¬Fin15AnchoredAtom1678 chi) ∨
      (¬Fin15AnchoredAtom2679 chi ∧
      Fin15AnchoredAtom0721 chi ∧
      Fin15AnchoredAtom0725 chi ∧
      Fin15AnchoredAtom0729 chi ∧
      Fin15AnchoredAtom0803 chi ∧
      Fin15AnchoredAtom1678 chi)) ∨
      ((Fin15AnchoredAtom2680 chi ∧
      ¬Fin15AnchoredAtom0722 chi) ∨
      (Fin15AnchoredAtom2680 chi ∧
      ¬Fin15AnchoredAtom0723 chi)))) ∨
      ((((Fin15AnchoredAtom2680 chi ∧
      ¬Fin15AnchoredAtom0730 chi) ∨
      (Fin15AnchoredAtom2680 chi ∧
      ¬Fin15AnchoredAtom0804 chi)) ∨
      ((Fin15AnchoredAtom2680 chi ∧
      ¬Fin15AnchoredAtom1679 chi) ∨
      (¬Fin15AnchoredAtom2680 chi ∧
      Fin15AnchoredAtom0722 chi ∧
      Fin15AnchoredAtom0723 chi ∧
      Fin15AnchoredAtom0730 chi ∧
      Fin15AnchoredAtom0804 chi ∧
      Fin15AnchoredAtom1679 chi))) ∨
      (((Fin15AnchoredAtom2681 chi ∧
      ¬Fin15AnchoredAtom0722 chi) ∨
      (Fin15AnchoredAtom2681 chi ∧
      ¬Fin15AnchoredAtom0805 chi)) ∨
      ((¬Fin15AnchoredAtom2681 chi ∧
      Fin15AnchoredAtom0722 chi ∧
      Fin15AnchoredAtom0724 chi ∧
      Fin15AnchoredAtom0731 chi ∧
      Fin15AnchoredAtom0805 chi ∧
      Fin15AnchoredAtom1680 chi) ∨
      (Fin15AnchoredAtom2682 chi ∧
      ¬Fin15AnchoredAtom0722 chi))))) ∨
      (((((Fin15AnchoredAtom2682 chi ∧
      ¬Fin15AnchoredAtom0732 chi) ∨
      (Fin15AnchoredAtom2682 chi ∧
      ¬Fin15AnchoredAtom0806 chi)) ∨
      ((Fin15AnchoredAtom2682 chi ∧
      ¬Fin15AnchoredAtom1681 chi) ∨
      (Fin15AnchoredAtom2683 chi ∧
      ¬Fin15AnchoredAtom0723 chi))) ∨
      (((Fin15AnchoredAtom2683 chi ∧
      ¬Fin15AnchoredAtom0724 chi) ∨
      (Fin15AnchoredAtom2683 chi ∧
      ¬Fin15AnchoredAtom0733 chi)) ∨
      ((Fin15AnchoredAtom2683 chi ∧
      ¬Fin15AnchoredAtom0807 chi) ∨
      (Fin15AnchoredAtom2683 chi ∧
      ¬Fin15AnchoredAtom1682 chi)))) ∨
      ((((¬Fin15AnchoredAtom2683 chi ∧
      Fin15AnchoredAtom0723 chi ∧
      Fin15AnchoredAtom0724 chi ∧
      Fin15AnchoredAtom0733 chi ∧
      Fin15AnchoredAtom0807 chi ∧
      Fin15AnchoredAtom1682 chi) ∨
      (Fin15AnchoredAtom2684 chi ∧
      ¬Fin15AnchoredAtom0723 chi)) ∨
      ((Fin15AnchoredAtom2684 chi ∧
      ¬Fin15AnchoredAtom0725 chi) ∨
      (Fin15AnchoredAtom2684 chi ∧
      ¬Fin15AnchoredAtom0734 chi))) ∨
      (((Fin15AnchoredAtom2684 chi ∧
      ¬Fin15AnchoredAtom0808 chi) ∨
      (Fin15AnchoredAtom2684 chi ∧
      ¬Fin15AnchoredAtom1683 chi)) ∨
      ((¬Fin15AnchoredAtom2684 chi ∧
      Fin15AnchoredAtom0723 chi ∧
      Fin15AnchoredAtom0725 chi ∧
      Fin15AnchoredAtom0734 chi ∧
      Fin15AnchoredAtom0808 chi ∧
      Fin15AnchoredAtom1683 chi) ∨
      (Fin15AnchoredAtom2685 chi ∧
      ¬Fin15AnchoredAtom0724 chi)))))))))) := by
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
                exact fin15Anchored_clause19434 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19435 chi hbad
                ·
                  exact fin15Anchored_clause19436 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19437 chi hbad
                ·
                  exact fin15Anchored_clause19438 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19439 chi hbad
                ·
                  exact fin15Anchored_clause19440 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19441 chi hbad
                ·
                  exact fin15Anchored_clause19442 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19443 chi hbad
                ·
                  exact fin15Anchored_clause19444 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19445 chi hbad
                ·
                  exact fin15Anchored_clause19446 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19447 chi hbad
                ·
                  exact fin15Anchored_clause19448 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19449 chi hbad
                ·
                  exact fin15Anchored_clause19450 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19451 chi hbad
                ·
                  exact fin15Anchored_clause19452 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19453 chi hbad
                ·
                  exact fin15Anchored_clause19454 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19455 chi hbad
                ·
                  exact fin15Anchored_clause19456 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19457 chi hbad
                ·
                  exact fin15Anchored_clause19458 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19459 chi hbad
                ·
                  exact fin15Anchored_clause19460 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19461 chi hbad
                ·
                  exact fin15Anchored_clause19462 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19463 chi hbad
                ·
                  exact fin15Anchored_clause19464 chi hbad
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
                  exact fin15Anchored_clause19465 chi hbad
                ·
                  exact fin15Anchored_clause19466 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19467 chi hbad
                ·
                  exact fin15Anchored_clause19468 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19469 chi hbad
                ·
                  exact fin15Anchored_clause19470 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19471 chi hbad
                ·
                  exact fin15Anchored_clause19472 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19473 chi hbad
                ·
                  exact fin15Anchored_clause19474 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19475 chi hbad
                ·
                  exact fin15Anchored_clause19476 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19477 chi hbad
                ·
                  exact fin15Anchored_clause19478 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19479 chi hbad
                ·
                  exact fin15Anchored_clause19480 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19481 chi hbad
                ·
                  exact fin15Anchored_clause19482 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19483 chi hbad
                ·
                  exact fin15Anchored_clause19484 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19485 chi hbad
                ·
                  exact fin15Anchored_clause19486 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19487 chi hbad
                ·
                  exact fin15Anchored_clause19488 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19489 chi hbad
                ·
                  exact fin15Anchored_clause19490 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19491 chi hbad
                ·
                  exact fin15Anchored_clause19492 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19493 chi hbad
                ·
                  exact fin15Anchored_clause19494 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19495 chi hbad
                ·
                  exact fin15Anchored_clause19496 chi hbad
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
                exact fin15Anchored_clause19497 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19498 chi hbad
                ·
                  exact fin15Anchored_clause19499 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19500 chi hbad
                ·
                  exact fin15Anchored_clause19501 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19502 chi hbad
                ·
                  exact fin15Anchored_clause19503 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19504 chi hbad
                ·
                  exact fin15Anchored_clause19505 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19506 chi hbad
                ·
                  exact fin15Anchored_clause19507 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19508 chi hbad
                ·
                  exact fin15Anchored_clause19509 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19510 chi hbad
                ·
                  exact fin15Anchored_clause19511 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19512 chi hbad
                ·
                  exact fin15Anchored_clause19513 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19514 chi hbad
                ·
                  exact fin15Anchored_clause19515 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19516 chi hbad
                ·
                  exact fin15Anchored_clause19517 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19518 chi hbad
                ·
                  exact fin15Anchored_clause19519 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19520 chi hbad
                ·
                  exact fin15Anchored_clause19521 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19522 chi hbad
                ·
                  exact fin15Anchored_clause19523 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19524 chi hbad
                ·
                  exact fin15Anchored_clause19525 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19526 chi hbad
                ·
                  exact fin15Anchored_clause19527 chi hbad
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
                  exact fin15Anchored_clause19528 chi hbad
                ·
                  exact fin15Anchored_clause19529 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19530 chi hbad
                ·
                  exact fin15Anchored_clause19531 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19532 chi hbad
                ·
                  exact fin15Anchored_clause19533 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19534 chi hbad
                ·
                  exact fin15Anchored_clause19535 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19536 chi hbad
                ·
                  exact fin15Anchored_clause19537 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19538 chi hbad
                ·
                  exact fin15Anchored_clause19539 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19540 chi hbad
                ·
                  exact fin15Anchored_clause19541 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19542 chi hbad
                ·
                  exact fin15Anchored_clause19543 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19544 chi hbad
                ·
                  exact fin15Anchored_clause19545 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19546 chi hbad
                ·
                  exact fin15Anchored_clause19547 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19548 chi hbad
                ·
                  exact fin15Anchored_clause19549 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19550 chi hbad
                ·
                  exact fin15Anchored_clause19551 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19552 chi hbad
                ·
                  exact fin15Anchored_clause19553 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19554 chi hbad
                ·
                  exact fin15Anchored_clause19555 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19556 chi hbad
                ·
                  exact fin15Anchored_clause19557 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19558 chi hbad
                ·
                  exact fin15Anchored_clause19559 chi hbad
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
                exact fin15Anchored_clause19560 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19561 chi hbad
                ·
                  exact fin15Anchored_clause19562 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19563 chi hbad
                ·
                  exact fin15Anchored_clause19564 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19565 chi hbad
                ·
                  exact fin15Anchored_clause19566 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19567 chi hbad
                ·
                  exact fin15Anchored_clause19568 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19569 chi hbad
                ·
                  exact fin15Anchored_clause19570 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19571 chi hbad
                ·
                  exact fin15Anchored_clause19572 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19573 chi hbad
                ·
                  exact fin15Anchored_clause19574 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19575 chi hbad
                ·
                  exact fin15Anchored_clause19576 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19577 chi hbad
                ·
                  exact fin15Anchored_clause19578 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19579 chi hbad
                ·
                  exact fin15Anchored_clause19580 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19581 chi hbad
                ·
                  exact fin15Anchored_clause19582 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19583 chi hbad
                ·
                  exact fin15Anchored_clause19584 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19585 chi hbad
                ·
                  exact fin15Anchored_clause19586 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19587 chi hbad
                ·
                  exact fin15Anchored_clause19588 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19589 chi hbad
                ·
                  exact fin15Anchored_clause19590 chi hbad
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
                  exact fin15Anchored_clause19591 chi hbad
                ·
                  exact fin15Anchored_clause19592 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19593 chi hbad
                ·
                  exact fin15Anchored_clause19594 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19595 chi hbad
                ·
                  exact fin15Anchored_clause19596 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19597 chi hbad
                ·
                  exact fin15Anchored_clause19598 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19599 chi hbad
                ·
                  exact fin15Anchored_clause19600 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19601 chi hbad
                ·
                  exact fin15Anchored_clause19602 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19603 chi hbad
                ·
                  exact fin15Anchored_clause19604 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19605 chi hbad
                ·
                  exact fin15Anchored_clause19606 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19607 chi hbad
                ·
                  exact fin15Anchored_clause19608 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19609 chi hbad
                ·
                  exact fin15Anchored_clause19610 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19611 chi hbad
                ·
                  exact fin15Anchored_clause19612 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19613 chi hbad
                ·
                  exact fin15Anchored_clause19614 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19615 chi hbad
                ·
                  exact fin15Anchored_clause19616 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19617 chi hbad
                ·
                  exact fin15Anchored_clause19618 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19619 chi hbad
                ·
                  exact fin15Anchored_clause19620 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19621 chi hbad
                ·
                  exact fin15Anchored_clause19622 chi hbad
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
                  exact fin15Anchored_clause19623 chi hbad
                ·
                  exact fin15Anchored_clause19624 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19625 chi hbad
                ·
                  exact fin15Anchored_clause19626 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19627 chi hbad
                ·
                  exact fin15Anchored_clause19628 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19629 chi hbad
                ·
                  exact fin15Anchored_clause19630 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19631 chi hbad
                ·
                  exact fin15Anchored_clause19632 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19633 chi hbad
                ·
                  exact fin15Anchored_clause19634 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19635 chi hbad
                ·
                  exact fin15Anchored_clause19636 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19637 chi hbad
                ·
                  exact fin15Anchored_clause19638 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19639 chi hbad
                ·
                  exact fin15Anchored_clause19640 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19641 chi hbad
                ·
                  exact fin15Anchored_clause19642 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19643 chi hbad
                ·
                  exact fin15Anchored_clause19644 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19645 chi hbad
                ·
                  exact fin15Anchored_clause19646 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19647 chi hbad
                ·
                  exact fin15Anchored_clause19648 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19649 chi hbad
                ·
                  exact fin15Anchored_clause19650 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19651 chi hbad
                ·
                  exact fin15Anchored_clause19652 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19653 chi hbad
                ·
                  exact fin15Anchored_clause19654 chi hbad
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
                  exact fin15Anchored_clause19655 chi hbad
                ·
                  exact fin15Anchored_clause19656 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19657 chi hbad
                ·
                  exact fin15Anchored_clause19658 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19659 chi hbad
                ·
                  exact fin15Anchored_clause19660 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19661 chi hbad
                ·
                  exact fin15Anchored_clause19662 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19663 chi hbad
                ·
                  exact fin15Anchored_clause19664 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19665 chi hbad
                ·
                  exact fin15Anchored_clause19666 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19667 chi hbad
                ·
                  exact fin15Anchored_clause19668 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19669 chi hbad
                ·
                  exact fin15Anchored_clause19670 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19671 chi hbad
                ·
                  exact fin15Anchored_clause19672 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19673 chi hbad
                ·
                  exact fin15Anchored_clause19674 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19675 chi hbad
                ·
                  exact fin15Anchored_clause19676 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19677 chi hbad
                ·
                  exact fin15Anchored_clause19678 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19679 chi hbad
                ·
                  exact fin15Anchored_clause19680 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19681 chi hbad
                ·
                  exact fin15Anchored_clause19682 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19683 chi hbad
                ·
                  exact fin15Anchored_clause19684 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19685 chi hbad
                ·
                  exact fin15Anchored_clause19686 chi hbad

end ErdosSzekeres

end
