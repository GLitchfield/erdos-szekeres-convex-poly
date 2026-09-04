module

public import ErdosSzekeres.Fin15AnchoredClauseChunk153
public import ErdosSzekeres.Fin15AnchoredClauseChunk154
public import ErdosSzekeres.Fin15AnchoredClauseChunk155

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 078. -/

theorem fin15Anchored_rejectSemanticSegment078
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom2685 chi ∧
      ¬Fin15AnchoredAtom0725 chi) ∨
      ((Fin15AnchoredAtom2685 chi ∧
      ¬Fin15AnchoredAtom0735 chi) ∨
      (Fin15AnchoredAtom2685 chi ∧
      ¬Fin15AnchoredAtom0809 chi))) ∨
      (((Fin15AnchoredAtom2685 chi ∧
      ¬Fin15AnchoredAtom1684 chi) ∨
      (¬Fin15AnchoredAtom2685 chi ∧
      Fin15AnchoredAtom0724 chi ∧
      Fin15AnchoredAtom0725 chi ∧
      Fin15AnchoredAtom0735 chi ∧
      Fin15AnchoredAtom0809 chi ∧
      Fin15AnchoredAtom1684 chi)) ∨
      ((Fin15AnchoredAtom2686 chi ∧
      ¬Fin15AnchoredAtom0726 chi) ∨
      (Fin15AnchoredAtom2686 chi ∧
      ¬Fin15AnchoredAtom0727 chi)))) ∨
      ((((Fin15AnchoredAtom2686 chi ∧
      ¬Fin15AnchoredAtom0730 chi) ∨
      (Fin15AnchoredAtom2686 chi ∧
      ¬Fin15AnchoredAtom0810 chi)) ∨
      ((Fin15AnchoredAtom2686 chi ∧
      ¬Fin15AnchoredAtom1685 chi) ∨
      (¬Fin15AnchoredAtom2686 chi ∧
      Fin15AnchoredAtom0726 chi ∧
      Fin15AnchoredAtom0727 chi ∧
      Fin15AnchoredAtom0730 chi ∧
      Fin15AnchoredAtom0810 chi ∧
      Fin15AnchoredAtom1685 chi))) ∨
      (((Fin15AnchoredAtom2687 chi ∧
      ¬Fin15AnchoredAtom0726 chi) ∨
      (Fin15AnchoredAtom2687 chi ∧
      ¬Fin15AnchoredAtom0728 chi)) ∨
      ((Fin15AnchoredAtom2687 chi ∧
      ¬Fin15AnchoredAtom0731 chi) ∨
      (Fin15AnchoredAtom2687 chi ∧
      ¬Fin15AnchoredAtom0811 chi))))) ∨
      (((((Fin15AnchoredAtom2687 chi ∧
      ¬Fin15AnchoredAtom1686 chi) ∨
      (¬Fin15AnchoredAtom2687 chi ∧
      Fin15AnchoredAtom0726 chi ∧
      Fin15AnchoredAtom0728 chi ∧
      Fin15AnchoredAtom0731 chi ∧
      Fin15AnchoredAtom0811 chi ∧
      Fin15AnchoredAtom1686 chi)) ∨
      ((Fin15AnchoredAtom2688 chi ∧
      ¬Fin15AnchoredAtom0729 chi) ∨
      (Fin15AnchoredAtom2688 chi ∧
      ¬Fin15AnchoredAtom0812 chi))) ∨
      (((Fin15AnchoredAtom2688 chi ∧
      ¬Fin15AnchoredAtom1687 chi) ∨
      (¬Fin15AnchoredAtom2688 chi ∧
      Fin15AnchoredAtom0726 chi ∧
      Fin15AnchoredAtom0729 chi ∧
      Fin15AnchoredAtom0732 chi ∧
      Fin15AnchoredAtom0812 chi ∧
      Fin15AnchoredAtom1687 chi)) ∨
      ((Fin15AnchoredAtom2689 chi ∧
      ¬Fin15AnchoredAtom0727 chi) ∨
      (Fin15AnchoredAtom2689 chi ∧
      ¬Fin15AnchoredAtom0728 chi)))) ∨
      ((((Fin15AnchoredAtom2689 chi ∧
      ¬Fin15AnchoredAtom0733 chi) ∨
      (Fin15AnchoredAtom2689 chi ∧
      ¬Fin15AnchoredAtom0813 chi)) ∨
      ((Fin15AnchoredAtom2689 chi ∧
      ¬Fin15AnchoredAtom1688 chi) ∨
      (¬Fin15AnchoredAtom2689 chi ∧
      Fin15AnchoredAtom0727 chi ∧
      Fin15AnchoredAtom0728 chi ∧
      Fin15AnchoredAtom0733 chi ∧
      Fin15AnchoredAtom0813 chi ∧
      Fin15AnchoredAtom1688 chi))) ∨
      (((Fin15AnchoredAtom2690 chi ∧
      ¬Fin15AnchoredAtom0727 chi) ∨
      (Fin15AnchoredAtom2690 chi ∧
      ¬Fin15AnchoredAtom0729 chi)) ∨
      ((Fin15AnchoredAtom2690 chi ∧
      ¬Fin15AnchoredAtom0734 chi) ∨
      (Fin15AnchoredAtom2690 chi ∧
      ¬Fin15AnchoredAtom0814 chi)))))) ∨
      ((((((Fin15AnchoredAtom2690 chi ∧
      ¬Fin15AnchoredAtom1689 chi) ∨
      (¬Fin15AnchoredAtom2690 chi ∧
      Fin15AnchoredAtom0727 chi ∧
      Fin15AnchoredAtom0729 chi ∧
      Fin15AnchoredAtom0734 chi ∧
      Fin15AnchoredAtom0814 chi ∧
      Fin15AnchoredAtom1689 chi)) ∨
      ((Fin15AnchoredAtom2691 chi ∧
      ¬Fin15AnchoredAtom0728 chi) ∨
      (Fin15AnchoredAtom2691 chi ∧
      ¬Fin15AnchoredAtom0729 chi))) ∨
      (((Fin15AnchoredAtom2691 chi ∧
      ¬Fin15AnchoredAtom0735 chi) ∨
      (Fin15AnchoredAtom2691 chi ∧
      ¬Fin15AnchoredAtom0815 chi)) ∨
      ((Fin15AnchoredAtom2691 chi ∧
      ¬Fin15AnchoredAtom1690 chi) ∨
      (¬Fin15AnchoredAtom2691 chi ∧
      Fin15AnchoredAtom0728 chi ∧
      Fin15AnchoredAtom0729 chi ∧
      Fin15AnchoredAtom0735 chi ∧
      Fin15AnchoredAtom0815 chi ∧
      Fin15AnchoredAtom1690 chi)))) ∨
      ((((Fin15AnchoredAtom2692 chi ∧
      ¬Fin15AnchoredAtom0730 chi) ∨
      (Fin15AnchoredAtom2692 chi ∧
      ¬Fin15AnchoredAtom0731 chi)) ∨
      ((Fin15AnchoredAtom2692 chi ∧
      ¬Fin15AnchoredAtom0733 chi) ∨
      (Fin15AnchoredAtom2692 chi ∧
      ¬Fin15AnchoredAtom0816 chi))) ∨
      (((Fin15AnchoredAtom2692 chi ∧
      ¬Fin15AnchoredAtom1691 chi) ∨
      (¬Fin15AnchoredAtom2692 chi ∧
      Fin15AnchoredAtom0730 chi ∧
      Fin15AnchoredAtom0731 chi ∧
      Fin15AnchoredAtom0733 chi ∧
      Fin15AnchoredAtom0816 chi ∧
      Fin15AnchoredAtom1691 chi)) ∨
      ((Fin15AnchoredAtom2693 chi ∧
      ¬Fin15AnchoredAtom0730 chi) ∨
      (Fin15AnchoredAtom2693 chi ∧
      ¬Fin15AnchoredAtom0732 chi))))) ∨
      (((((Fin15AnchoredAtom2693 chi ∧
      ¬Fin15AnchoredAtom0734 chi) ∨
      (Fin15AnchoredAtom2693 chi ∧
      ¬Fin15AnchoredAtom0817 chi)) ∨
      ((¬Fin15AnchoredAtom2693 chi ∧
      Fin15AnchoredAtom0730 chi ∧
      Fin15AnchoredAtom0732 chi ∧
      Fin15AnchoredAtom0734 chi ∧
      Fin15AnchoredAtom0817 chi ∧
      Fin15AnchoredAtom1692 chi) ∨
      (Fin15AnchoredAtom2694 chi ∧
      ¬Fin15AnchoredAtom0731 chi))) ∨
      (((Fin15AnchoredAtom2694 chi ∧
      ¬Fin15AnchoredAtom0732 chi) ∨
      (Fin15AnchoredAtom2694 chi ∧
      ¬Fin15AnchoredAtom0735 chi)) ∨
      ((Fin15AnchoredAtom2694 chi ∧
      ¬Fin15AnchoredAtom1693 chi) ∨
      (¬Fin15AnchoredAtom2694 chi ∧
      Fin15AnchoredAtom0731 chi ∧
      Fin15AnchoredAtom0732 chi ∧
      Fin15AnchoredAtom0735 chi ∧
      Fin15AnchoredAtom0818 chi ∧
      Fin15AnchoredAtom1693 chi)))) ∨
      ((((Fin15AnchoredAtom2695 chi ∧
      ¬Fin15AnchoredAtom0733 chi) ∨
      (Fin15AnchoredAtom2695 chi ∧
      ¬Fin15AnchoredAtom0734 chi)) ∨
      ((Fin15AnchoredAtom2695 chi ∧
      ¬Fin15AnchoredAtom0735 chi) ∨
      (Fin15AnchoredAtom2695 chi ∧
      ¬Fin15AnchoredAtom0819 chi))) ∨
      (((Fin15AnchoredAtom2695 chi ∧
      ¬Fin15AnchoredAtom1694 chi) ∨
      (¬Fin15AnchoredAtom2695 chi ∧
      Fin15AnchoredAtom0733 chi ∧
      Fin15AnchoredAtom0734 chi ∧
      Fin15AnchoredAtom0735 chi ∧
      Fin15AnchoredAtom0819 chi ∧
      Fin15AnchoredAtom1694 chi)) ∨
      ((Fin15AnchoredAtom2696 chi ∧
      ¬Fin15AnchoredAtom0736 chi) ∨
      (Fin15AnchoredAtom2696 chi ∧
      ¬Fin15AnchoredAtom0737 chi))))))) ∨
      ((((((Fin15AnchoredAtom2696 chi ∧
      ¬Fin15AnchoredAtom0743 chi) ∨
      ((Fin15AnchoredAtom2696 chi ∧
      ¬Fin15AnchoredAtom0764 chi) ∨
      (Fin15AnchoredAtom2696 chi ∧
      ¬Fin15AnchoredAtom1695 chi))) ∨
      (((¬Fin15AnchoredAtom2696 chi ∧
      Fin15AnchoredAtom0736 chi ∧
      Fin15AnchoredAtom0737 chi ∧
      Fin15AnchoredAtom0743 chi ∧
      Fin15AnchoredAtom0764 chi ∧
      Fin15AnchoredAtom1695 chi) ∨
      (Fin15AnchoredAtom2697 chi ∧
      ¬Fin15AnchoredAtom0736 chi)) ∨
      ((Fin15AnchoredAtom2697 chi ∧
      ¬Fin15AnchoredAtom0738 chi) ∨
      (Fin15AnchoredAtom2697 chi ∧
      ¬Fin15AnchoredAtom0744 chi)))) ∨
      ((((Fin15AnchoredAtom2697 chi ∧
      ¬Fin15AnchoredAtom0765 chi) ∨
      (Fin15AnchoredAtom2697 chi ∧
      ¬Fin15AnchoredAtom1696 chi)) ∨
      ((¬Fin15AnchoredAtom2697 chi ∧
      Fin15AnchoredAtom0736 chi ∧
      Fin15AnchoredAtom0738 chi ∧
      Fin15AnchoredAtom0744 chi ∧
      Fin15AnchoredAtom0765 chi ∧
      Fin15AnchoredAtom1696 chi) ∨
      (Fin15AnchoredAtom2699 chi ∧
      ¬Fin15AnchoredAtom0736 chi))) ∨
      (((Fin15AnchoredAtom2699 chi ∧
      ¬Fin15AnchoredAtom0740 chi) ∨
      (Fin15AnchoredAtom2699 chi ∧
      ¬Fin15AnchoredAtom0746 chi)) ∨
      ((Fin15AnchoredAtom2699 chi ∧
      ¬Fin15AnchoredAtom0767 chi) ∨
      (¬Fin15AnchoredAtom2699 chi ∧
      Fin15AnchoredAtom0736 chi ∧
      Fin15AnchoredAtom0740 chi ∧
      Fin15AnchoredAtom0746 chi ∧
      Fin15AnchoredAtom0767 chi ∧
      Fin15AnchoredAtom1698 chi))))) ∨
      (((((Fin15AnchoredAtom2700 chi ∧
      ¬Fin15AnchoredAtom0736 chi) ∨
      (Fin15AnchoredAtom2700 chi ∧
      ¬Fin15AnchoredAtom0741 chi)) ∨
      ((Fin15AnchoredAtom2700 chi ∧
      ¬Fin15AnchoredAtom0747 chi) ∨
      (Fin15AnchoredAtom2700 chi ∧
      ¬Fin15AnchoredAtom0768 chi))) ∨
      (((Fin15AnchoredAtom2700 chi ∧
      ¬Fin15AnchoredAtom1699 chi) ∨
      (¬Fin15AnchoredAtom2700 chi ∧
      Fin15AnchoredAtom0736 chi ∧
      Fin15AnchoredAtom0741 chi ∧
      Fin15AnchoredAtom0747 chi ∧
      Fin15AnchoredAtom0768 chi ∧
      Fin15AnchoredAtom1699 chi)) ∨
      ((Fin15AnchoredAtom2701 chi ∧
      ¬Fin15AnchoredAtom0736 chi) ∨
      (Fin15AnchoredAtom2701 chi ∧
      ¬Fin15AnchoredAtom0742 chi)))) ∨
      ((((Fin15AnchoredAtom2701 chi ∧
      ¬Fin15AnchoredAtom0748 chi) ∨
      (Fin15AnchoredAtom2701 chi ∧
      ¬Fin15AnchoredAtom0769 chi)) ∨
      ((Fin15AnchoredAtom2701 chi ∧
      ¬Fin15AnchoredAtom1700 chi) ∨
      (¬Fin15AnchoredAtom2701 chi ∧
      Fin15AnchoredAtom0736 chi ∧
      Fin15AnchoredAtom0742 chi ∧
      Fin15AnchoredAtom0748 chi ∧
      Fin15AnchoredAtom0769 chi ∧
      Fin15AnchoredAtom1700 chi))) ∨
      (((Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom0737 chi) ∨
      (Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom0738 chi)) ∨
      ((Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom0749 chi) ∨
      (Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom0770 chi)))))) ∨
      ((((((Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom1701 chi) ∨
      (¬Fin15AnchoredAtom2702 chi ∧
      Fin15AnchoredAtom0737 chi ∧
      Fin15AnchoredAtom0738 chi ∧
      Fin15AnchoredAtom0749 chi ∧
      Fin15AnchoredAtom0770 chi ∧
      Fin15AnchoredAtom1701 chi)) ∨
      ((Fin15AnchoredAtom2703 chi ∧
      ¬Fin15AnchoredAtom0737 chi) ∨
      (Fin15AnchoredAtom2703 chi ∧
      ¬Fin15AnchoredAtom0739 chi))) ∨
      (((Fin15AnchoredAtom2703 chi ∧
      ¬Fin15AnchoredAtom0750 chi) ∨
      (Fin15AnchoredAtom2703 chi ∧
      ¬Fin15AnchoredAtom0771 chi)) ∨
      ((Fin15AnchoredAtom2703 chi ∧
      ¬Fin15AnchoredAtom1702 chi) ∨
      (¬Fin15AnchoredAtom2703 chi ∧
      Fin15AnchoredAtom0737 chi ∧
      Fin15AnchoredAtom0739 chi ∧
      Fin15AnchoredAtom0750 chi ∧
      Fin15AnchoredAtom0771 chi ∧
      Fin15AnchoredAtom1702 chi)))) ∨
      ((((Fin15AnchoredAtom2704 chi ∧
      ¬Fin15AnchoredAtom0737 chi) ∨
      (Fin15AnchoredAtom2704 chi ∧
      ¬Fin15AnchoredAtom0740 chi)) ∨
      ((Fin15AnchoredAtom2704 chi ∧
      ¬Fin15AnchoredAtom0751 chi) ∨
      (Fin15AnchoredAtom2704 chi ∧
      ¬Fin15AnchoredAtom0772 chi))) ∨
      (((Fin15AnchoredAtom2704 chi ∧
      ¬Fin15AnchoredAtom1703 chi) ∨
      (¬Fin15AnchoredAtom2704 chi ∧
      Fin15AnchoredAtom0737 chi ∧
      Fin15AnchoredAtom0740 chi ∧
      Fin15AnchoredAtom0751 chi ∧
      Fin15AnchoredAtom0772 chi ∧
      Fin15AnchoredAtom1703 chi)) ∨
      ((Fin15AnchoredAtom2705 chi ∧
      ¬Fin15AnchoredAtom0737 chi) ∨
      (Fin15AnchoredAtom2705 chi ∧
      ¬Fin15AnchoredAtom0741 chi))))) ∨
      (((((Fin15AnchoredAtom2705 chi ∧
      ¬Fin15AnchoredAtom0752 chi) ∨
      (Fin15AnchoredAtom2705 chi ∧
      ¬Fin15AnchoredAtom0773 chi)) ∨
      ((Fin15AnchoredAtom2705 chi ∧
      ¬Fin15AnchoredAtom1704 chi) ∨
      (¬Fin15AnchoredAtom2705 chi ∧
      Fin15AnchoredAtom0737 chi ∧
      Fin15AnchoredAtom0741 chi ∧
      Fin15AnchoredAtom0752 chi ∧
      Fin15AnchoredAtom0773 chi ∧
      Fin15AnchoredAtom1704 chi))) ∨
      (((Fin15AnchoredAtom2706 chi ∧
      ¬Fin15AnchoredAtom0737 chi) ∨
      (Fin15AnchoredAtom2706 chi ∧
      ¬Fin15AnchoredAtom0742 chi)) ∨
      ((Fin15AnchoredAtom2706 chi ∧
      ¬Fin15AnchoredAtom0753 chi) ∨
      (Fin15AnchoredAtom2706 chi ∧
      ¬Fin15AnchoredAtom0774 chi)))) ∨
      ((((Fin15AnchoredAtom2706 chi ∧
      ¬Fin15AnchoredAtom1705 chi) ∨
      (¬Fin15AnchoredAtom2706 chi ∧
      Fin15AnchoredAtom0737 chi ∧
      Fin15AnchoredAtom0742 chi ∧
      Fin15AnchoredAtom0753 chi ∧
      Fin15AnchoredAtom0774 chi ∧
      Fin15AnchoredAtom1705 chi)) ∨
      ((Fin15AnchoredAtom2707 chi ∧
      ¬Fin15AnchoredAtom0738 chi) ∨
      (Fin15AnchoredAtom2707 chi ∧
      ¬Fin15AnchoredAtom0739 chi))) ∨
      (((Fin15AnchoredAtom2707 chi ∧
      ¬Fin15AnchoredAtom0775 chi) ∨
      (¬Fin15AnchoredAtom2707 chi ∧
      Fin15AnchoredAtom0738 chi ∧
      Fin15AnchoredAtom0739 chi ∧
      Fin15AnchoredAtom0754 chi ∧
      Fin15AnchoredAtom0775 chi ∧
      Fin15AnchoredAtom1706 chi)) ∨
      ((Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom0738 chi) ∨
      (Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom0740 chi)))))))) ∨
      (((((((Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom0755 chi) ∨
      ((Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom0776 chi) ∨
      (Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom1707 chi))) ∨
      (((¬Fin15AnchoredAtom2708 chi ∧
      Fin15AnchoredAtom0738 chi ∧
      Fin15AnchoredAtom0740 chi ∧
      Fin15AnchoredAtom0755 chi ∧
      Fin15AnchoredAtom0776 chi ∧
      Fin15AnchoredAtom1707 chi) ∨
      (Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom0738 chi)) ∨
      ((Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom0741 chi) ∨
      (Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom0756 chi)))) ∨
      ((((Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom0777 chi) ∨
      (Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom1708 chi)) ∨
      ((¬Fin15AnchoredAtom2709 chi ∧
      Fin15AnchoredAtom0738 chi ∧
      Fin15AnchoredAtom0741 chi ∧
      Fin15AnchoredAtom0756 chi ∧
      Fin15AnchoredAtom0777 chi ∧
      Fin15AnchoredAtom1708 chi) ∨
      (Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom0738 chi))) ∨
      (((Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom0742 chi) ∨
      (Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom0757 chi)) ∨
      ((Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom0778 chi) ∨
      (Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom1709 chi))))) ∨
      (((((¬Fin15AnchoredAtom2710 chi ∧
      Fin15AnchoredAtom0738 chi ∧
      Fin15AnchoredAtom0742 chi ∧
      Fin15AnchoredAtom0757 chi ∧
      Fin15AnchoredAtom0778 chi ∧
      Fin15AnchoredAtom1709 chi) ∨
      (Fin15AnchoredAtom2711 chi ∧
      ¬Fin15AnchoredAtom0739 chi)) ∨
      ((Fin15AnchoredAtom2711 chi ∧
      ¬Fin15AnchoredAtom0740 chi) ∨
      (Fin15AnchoredAtom2711 chi ∧
      ¬Fin15AnchoredAtom0779 chi))) ∨
      (((¬Fin15AnchoredAtom2711 chi ∧
      Fin15AnchoredAtom0739 chi ∧
      Fin15AnchoredAtom0740 chi ∧
      Fin15AnchoredAtom0758 chi ∧
      Fin15AnchoredAtom0779 chi ∧
      Fin15AnchoredAtom1710 chi) ∨
      (Fin15AnchoredAtom2712 chi ∧
      ¬Fin15AnchoredAtom0739 chi)) ∨
      ((Fin15AnchoredAtom2712 chi ∧
      ¬Fin15AnchoredAtom0741 chi) ∨
      (Fin15AnchoredAtom2712 chi ∧
      ¬Fin15AnchoredAtom0759 chi)))) ∨
      ((((Fin15AnchoredAtom2712 chi ∧
      ¬Fin15AnchoredAtom0780 chi) ∨
      (Fin15AnchoredAtom2712 chi ∧
      ¬Fin15AnchoredAtom1711 chi)) ∨
      ((¬Fin15AnchoredAtom2712 chi ∧
      Fin15AnchoredAtom0739 chi ∧
      Fin15AnchoredAtom0741 chi ∧
      Fin15AnchoredAtom0759 chi ∧
      Fin15AnchoredAtom0780 chi ∧
      Fin15AnchoredAtom1711 chi) ∨
      (Fin15AnchoredAtom2713 chi ∧
      ¬Fin15AnchoredAtom0742 chi))) ∨
      (((Fin15AnchoredAtom2713 chi ∧
      ¬Fin15AnchoredAtom0781 chi) ∨
      (¬Fin15AnchoredAtom2713 chi ∧
      Fin15AnchoredAtom0739 chi ∧
      Fin15AnchoredAtom0742 chi ∧
      Fin15AnchoredAtom0760 chi ∧
      Fin15AnchoredAtom0781 chi ∧
      Fin15AnchoredAtom1712 chi)) ∨
      ((Fin15AnchoredAtom2714 chi ∧
      ¬Fin15AnchoredAtom0740 chi) ∨
      (Fin15AnchoredAtom2714 chi ∧
      ¬Fin15AnchoredAtom0741 chi)))))) ∨
      ((((((Fin15AnchoredAtom2714 chi ∧
      ¬Fin15AnchoredAtom0761 chi) ∨
      (Fin15AnchoredAtom2714 chi ∧
      ¬Fin15AnchoredAtom0782 chi)) ∨
      ((Fin15AnchoredAtom2714 chi ∧
      ¬Fin15AnchoredAtom1713 chi) ∨
      (¬Fin15AnchoredAtom2714 chi ∧
      Fin15AnchoredAtom0740 chi ∧
      Fin15AnchoredAtom0741 chi ∧
      Fin15AnchoredAtom0761 chi ∧
      Fin15AnchoredAtom0782 chi ∧
      Fin15AnchoredAtom1713 chi))) ∨
      (((Fin15AnchoredAtom2715 chi ∧
      ¬Fin15AnchoredAtom0740 chi) ∨
      (Fin15AnchoredAtom2715 chi ∧
      ¬Fin15AnchoredAtom0742 chi)) ∨
      ((Fin15AnchoredAtom2715 chi ∧
      ¬Fin15AnchoredAtom0762 chi) ∨
      (Fin15AnchoredAtom2715 chi ∧
      ¬Fin15AnchoredAtom0783 chi)))) ∨
      ((((Fin15AnchoredAtom2715 chi ∧
      ¬Fin15AnchoredAtom1714 chi) ∨
      (¬Fin15AnchoredAtom2715 chi ∧
      Fin15AnchoredAtom0740 chi ∧
      Fin15AnchoredAtom0742 chi ∧
      Fin15AnchoredAtom0762 chi ∧
      Fin15AnchoredAtom0783 chi ∧
      Fin15AnchoredAtom1714 chi)) ∨
      ((Fin15AnchoredAtom2716 chi ∧
      ¬Fin15AnchoredAtom0741 chi) ∨
      (Fin15AnchoredAtom2716 chi ∧
      ¬Fin15AnchoredAtom0742 chi))) ∨
      (((Fin15AnchoredAtom2716 chi ∧
      ¬Fin15AnchoredAtom0763 chi) ∨
      (Fin15AnchoredAtom2716 chi ∧
      ¬Fin15AnchoredAtom0784 chi)) ∨
      ((Fin15AnchoredAtom2716 chi ∧
      ¬Fin15AnchoredAtom1715 chi) ∨
      (¬Fin15AnchoredAtom2716 chi ∧
      Fin15AnchoredAtom0741 chi ∧
      Fin15AnchoredAtom0742 chi ∧
      Fin15AnchoredAtom0763 chi ∧
      Fin15AnchoredAtom0784 chi ∧
      Fin15AnchoredAtom1715 chi))))) ∨
      (((((Fin15AnchoredAtom2717 chi ∧
      ¬Fin15AnchoredAtom0743 chi) ∨
      (Fin15AnchoredAtom2717 chi ∧
      ¬Fin15AnchoredAtom0744 chi)) ∨
      ((Fin15AnchoredAtom2717 chi ∧
      ¬Fin15AnchoredAtom0749 chi) ∨
      (Fin15AnchoredAtom2717 chi ∧
      ¬Fin15AnchoredAtom0785 chi))) ∨
      (((Fin15AnchoredAtom2717 chi ∧
      ¬Fin15AnchoredAtom1716 chi) ∨
      (¬Fin15AnchoredAtom2717 chi ∧
      Fin15AnchoredAtom0743 chi ∧
      Fin15AnchoredAtom0744 chi ∧
      Fin15AnchoredAtom0749 chi ∧
      Fin15AnchoredAtom0785 chi ∧
      Fin15AnchoredAtom1716 chi)) ∨
      ((Fin15AnchoredAtom2719 chi ∧
      ¬Fin15AnchoredAtom0743 chi) ∨
      (Fin15AnchoredAtom2719 chi ∧
      ¬Fin15AnchoredAtom0746 chi)))) ∨
      ((((Fin15AnchoredAtom2719 chi ∧
      ¬Fin15AnchoredAtom0751 chi) ∨
      (Fin15AnchoredAtom2719 chi ∧
      ¬Fin15AnchoredAtom0787 chi)) ∨
      ((Fin15AnchoredAtom2719 chi ∧
      ¬Fin15AnchoredAtom1718 chi) ∨
      (¬Fin15AnchoredAtom2719 chi ∧
      Fin15AnchoredAtom0743 chi ∧
      Fin15AnchoredAtom0746 chi ∧
      Fin15AnchoredAtom0751 chi ∧
      Fin15AnchoredAtom0787 chi ∧
      Fin15AnchoredAtom1718 chi))) ∨
      (((Fin15AnchoredAtom2720 chi ∧
      ¬Fin15AnchoredAtom0743 chi) ∨
      (Fin15AnchoredAtom2720 chi ∧
      ¬Fin15AnchoredAtom0747 chi)) ∨
      ((Fin15AnchoredAtom2720 chi ∧
      ¬Fin15AnchoredAtom0752 chi) ∨
      (Fin15AnchoredAtom2720 chi ∧
      ¬Fin15AnchoredAtom0788 chi))))))) ∨
      ((((((Fin15AnchoredAtom2720 chi ∧
      ¬Fin15AnchoredAtom1719 chi) ∨
      ((¬Fin15AnchoredAtom2720 chi ∧
      Fin15AnchoredAtom0743 chi ∧
      Fin15AnchoredAtom0747 chi ∧
      Fin15AnchoredAtom0752 chi ∧
      Fin15AnchoredAtom0788 chi ∧
      Fin15AnchoredAtom1719 chi) ∨
      (Fin15AnchoredAtom2721 chi ∧
      ¬Fin15AnchoredAtom0743 chi))) ∨
      (((Fin15AnchoredAtom2721 chi ∧
      ¬Fin15AnchoredAtom0748 chi) ∨
      (Fin15AnchoredAtom2721 chi ∧
      ¬Fin15AnchoredAtom0753 chi)) ∨
      ((Fin15AnchoredAtom2721 chi ∧
      ¬Fin15AnchoredAtom0789 chi) ∨
      (Fin15AnchoredAtom2721 chi ∧
      ¬Fin15AnchoredAtom1720 chi)))) ∨
      ((((¬Fin15AnchoredAtom2721 chi ∧
      Fin15AnchoredAtom0743 chi ∧
      Fin15AnchoredAtom0748 chi ∧
      Fin15AnchoredAtom0753 chi ∧
      Fin15AnchoredAtom0789 chi ∧
      Fin15AnchoredAtom1720 chi) ∨
      (Fin15AnchoredAtom2723 chi ∧
      ¬Fin15AnchoredAtom0744 chi)) ∨
      ((Fin15AnchoredAtom2723 chi ∧
      ¬Fin15AnchoredAtom0746 chi) ∨
      (Fin15AnchoredAtom2723 chi ∧
      ¬Fin15AnchoredAtom0755 chi))) ∨
      (((Fin15AnchoredAtom2723 chi ∧
      ¬Fin15AnchoredAtom0791 chi) ∨
      (Fin15AnchoredAtom2723 chi ∧
      ¬Fin15AnchoredAtom1722 chi)) ∨
      ((¬Fin15AnchoredAtom2723 chi ∧
      Fin15AnchoredAtom0744 chi ∧
      Fin15AnchoredAtom0746 chi ∧
      Fin15AnchoredAtom0755 chi ∧
      Fin15AnchoredAtom0791 chi ∧
      Fin15AnchoredAtom1722 chi) ∨
      (Fin15AnchoredAtom2724 chi ∧
      ¬Fin15AnchoredAtom0744 chi))))) ∨
      (((((Fin15AnchoredAtom2724 chi ∧
      ¬Fin15AnchoredAtom0747 chi) ∨
      (Fin15AnchoredAtom2724 chi ∧
      ¬Fin15AnchoredAtom0756 chi)) ∨
      ((Fin15AnchoredAtom2724 chi ∧
      ¬Fin15AnchoredAtom0792 chi) ∨
      (¬Fin15AnchoredAtom2724 chi ∧
      Fin15AnchoredAtom0744 chi ∧
      Fin15AnchoredAtom0747 chi ∧
      Fin15AnchoredAtom0756 chi ∧
      Fin15AnchoredAtom0792 chi ∧
      Fin15AnchoredAtom1723 chi))) ∨
      (((Fin15AnchoredAtom2725 chi ∧
      ¬Fin15AnchoredAtom0744 chi) ∨
      (Fin15AnchoredAtom2725 chi ∧
      ¬Fin15AnchoredAtom0748 chi)) ∨
      ((Fin15AnchoredAtom2725 chi ∧
      ¬Fin15AnchoredAtom0757 chi) ∨
      (Fin15AnchoredAtom2725 chi ∧
      ¬Fin15AnchoredAtom0793 chi)))) ∨
      ((((Fin15AnchoredAtom2725 chi ∧
      ¬Fin15AnchoredAtom1724 chi) ∨
      (¬Fin15AnchoredAtom2725 chi ∧
      Fin15AnchoredAtom0744 chi ∧
      Fin15AnchoredAtom0748 chi ∧
      Fin15AnchoredAtom0757 chi ∧
      Fin15AnchoredAtom0793 chi ∧
      Fin15AnchoredAtom1724 chi)) ∨
      ((Fin15AnchoredAtom2729 chi ∧
      ¬Fin15AnchoredAtom0746 chi) ∨
      (Fin15AnchoredAtom2729 chi ∧
      ¬Fin15AnchoredAtom0747 chi))) ∨
      (((Fin15AnchoredAtom2729 chi ∧
      ¬Fin15AnchoredAtom0761 chi) ∨
      (Fin15AnchoredAtom2729 chi ∧
      ¬Fin15AnchoredAtom0797 chi)) ∨
      ((Fin15AnchoredAtom2729 chi ∧
      ¬Fin15AnchoredAtom1728 chi) ∨
      (¬Fin15AnchoredAtom2729 chi ∧
      Fin15AnchoredAtom0746 chi ∧
      Fin15AnchoredAtom0747 chi ∧
      Fin15AnchoredAtom0761 chi ∧
      Fin15AnchoredAtom0797 chi ∧
      Fin15AnchoredAtom1728 chi)))))) ∨
      ((((((Fin15AnchoredAtom2730 chi ∧
      ¬Fin15AnchoredAtom0746 chi) ∨
      (Fin15AnchoredAtom2730 chi ∧
      ¬Fin15AnchoredAtom0748 chi)) ∨
      ((Fin15AnchoredAtom2730 chi ∧
      ¬Fin15AnchoredAtom0762 chi) ∨
      (Fin15AnchoredAtom2730 chi ∧
      ¬Fin15AnchoredAtom0798 chi))) ∨
      (((Fin15AnchoredAtom2730 chi ∧
      ¬Fin15AnchoredAtom1729 chi) ∨
      (¬Fin15AnchoredAtom2730 chi ∧
      Fin15AnchoredAtom0746 chi ∧
      Fin15AnchoredAtom0748 chi ∧
      Fin15AnchoredAtom0762 chi ∧
      Fin15AnchoredAtom0798 chi ∧
      Fin15AnchoredAtom1729 chi)) ∨
      ((Fin15AnchoredAtom2731 chi ∧
      ¬Fin15AnchoredAtom0747 chi) ∨
      (Fin15AnchoredAtom2731 chi ∧
      ¬Fin15AnchoredAtom0748 chi)))) ∨
      ((((Fin15AnchoredAtom2731 chi ∧
      ¬Fin15AnchoredAtom0763 chi) ∨
      (Fin15AnchoredAtom2731 chi ∧
      ¬Fin15AnchoredAtom0799 chi)) ∨
      ((Fin15AnchoredAtom2731 chi ∧
      ¬Fin15AnchoredAtom1730 chi) ∨
      (¬Fin15AnchoredAtom2731 chi ∧
      Fin15AnchoredAtom0747 chi ∧
      Fin15AnchoredAtom0748 chi ∧
      Fin15AnchoredAtom0763 chi ∧
      Fin15AnchoredAtom0799 chi ∧
      Fin15AnchoredAtom1730 chi))) ∨
      (((Fin15AnchoredAtom2732 chi ∧
      ¬Fin15AnchoredAtom0749 chi) ∨
      (Fin15AnchoredAtom2732 chi ∧
      ¬Fin15AnchoredAtom0750 chi)) ∨
      ((Fin15AnchoredAtom2732 chi ∧
      ¬Fin15AnchoredAtom0754 chi) ∨
      (Fin15AnchoredAtom2732 chi ∧
      ¬Fin15AnchoredAtom0800 chi))))) ∨
      (((((Fin15AnchoredAtom2732 chi ∧
      ¬Fin15AnchoredAtom1731 chi) ∨
      (¬Fin15AnchoredAtom2732 chi ∧
      Fin15AnchoredAtom0749 chi ∧
      Fin15AnchoredAtom0750 chi ∧
      Fin15AnchoredAtom0754 chi ∧
      Fin15AnchoredAtom0800 chi ∧
      Fin15AnchoredAtom1731 chi)) ∨
      ((Fin15AnchoredAtom2733 chi ∧
      ¬Fin15AnchoredAtom0749 chi) ∨
      (Fin15AnchoredAtom2733 chi ∧
      ¬Fin15AnchoredAtom0751 chi))) ∨
      (((Fin15AnchoredAtom2733 chi ∧
      ¬Fin15AnchoredAtom0755 chi) ∨
      (Fin15AnchoredAtom2733 chi ∧
      ¬Fin15AnchoredAtom0801 chi)) ∨
      ((Fin15AnchoredAtom2733 chi ∧
      ¬Fin15AnchoredAtom1732 chi) ∨
      (¬Fin15AnchoredAtom2733 chi ∧
      Fin15AnchoredAtom0749 chi ∧
      Fin15AnchoredAtom0751 chi ∧
      Fin15AnchoredAtom0755 chi ∧
      Fin15AnchoredAtom0801 chi ∧
      Fin15AnchoredAtom1732 chi)))) ∨
      ((((Fin15AnchoredAtom2734 chi ∧
      ¬Fin15AnchoredAtom0749 chi) ∨
      (Fin15AnchoredAtom2734 chi ∧
      ¬Fin15AnchoredAtom0752 chi)) ∨
      ((Fin15AnchoredAtom2734 chi ∧
      ¬Fin15AnchoredAtom0756 chi) ∨
      (Fin15AnchoredAtom2734 chi ∧
      ¬Fin15AnchoredAtom0802 chi))) ∨
      (((Fin15AnchoredAtom2734 chi ∧
      ¬Fin15AnchoredAtom1733 chi) ∨
      (¬Fin15AnchoredAtom2734 chi ∧
      Fin15AnchoredAtom0749 chi ∧
      Fin15AnchoredAtom0752 chi ∧
      Fin15AnchoredAtom0756 chi ∧
      Fin15AnchoredAtom0802 chi ∧
      Fin15AnchoredAtom1733 chi)) ∨
      ((Fin15AnchoredAtom2735 chi ∧
      ¬Fin15AnchoredAtom0749 chi) ∨
      (Fin15AnchoredAtom2735 chi ∧
      ¬Fin15AnchoredAtom0753 chi)))))))))) := by
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
                exact fin15Anchored_clause19687 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19688 chi hbad
                ·
                  exact fin15Anchored_clause19689 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19690 chi hbad
                ·
                  exact fin15Anchored_clause19691 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19692 chi hbad
                ·
                  exact fin15Anchored_clause19693 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19694 chi hbad
                ·
                  exact fin15Anchored_clause19695 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19696 chi hbad
                ·
                  exact fin15Anchored_clause19697 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19698 chi hbad
                ·
                  exact fin15Anchored_clause19699 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19700 chi hbad
                ·
                  exact fin15Anchored_clause19701 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19702 chi hbad
                ·
                  exact fin15Anchored_clause19703 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19704 chi hbad
                ·
                  exact fin15Anchored_clause19705 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19706 chi hbad
                ·
                  exact fin15Anchored_clause19707 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19708 chi hbad
                ·
                  exact fin15Anchored_clause19709 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19710 chi hbad
                ·
                  exact fin15Anchored_clause19711 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19712 chi hbad
                ·
                  exact fin15Anchored_clause19713 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19714 chi hbad
                ·
                  exact fin15Anchored_clause19715 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19716 chi hbad
                ·
                  exact fin15Anchored_clause19717 chi hbad
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
                  exact fin15Anchored_clause19718 chi hbad
                ·
                  exact fin15Anchored_clause19719 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19720 chi hbad
                ·
                  exact fin15Anchored_clause19721 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19722 chi hbad
                ·
                  exact fin15Anchored_clause19723 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19724 chi hbad
                ·
                  exact fin15Anchored_clause19725 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19726 chi hbad
                ·
                  exact fin15Anchored_clause19727 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19728 chi hbad
                ·
                  exact fin15Anchored_clause19729 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19730 chi hbad
                ·
                  exact fin15Anchored_clause19731 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19732 chi hbad
                ·
                  exact fin15Anchored_clause19733 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19734 chi hbad
                ·
                  exact fin15Anchored_clause19735 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19736 chi hbad
                ·
                  exact fin15Anchored_clause19737 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19738 chi hbad
                ·
                  exact fin15Anchored_clause19739 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19740 chi hbad
                ·
                  exact fin15Anchored_clause19741 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19742 chi hbad
                ·
                  exact fin15Anchored_clause19743 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19744 chi hbad
                ·
                  exact fin15Anchored_clause19745 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19746 chi hbad
                ·
                  exact fin15Anchored_clause19747 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19748 chi hbad
                ·
                  exact fin15Anchored_clause19749 chi hbad
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
                exact fin15Anchored_clause19750 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19751 chi hbad
                ·
                  exact fin15Anchored_clause19752 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19753 chi hbad
                ·
                  exact fin15Anchored_clause19754 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19755 chi hbad
                ·
                  exact fin15Anchored_clause19756 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19757 chi hbad
                ·
                  exact fin15Anchored_clause19758 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19759 chi hbad
                ·
                  exact fin15Anchored_clause19760 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19761 chi hbad
                ·
                  exact fin15Anchored_clause19762 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19763 chi hbad
                ·
                  exact fin15Anchored_clause19764 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19765 chi hbad
                ·
                  exact fin15Anchored_clause19766 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19767 chi hbad
                ·
                  exact fin15Anchored_clause19768 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19769 chi hbad
                ·
                  exact fin15Anchored_clause19770 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19771 chi hbad
                ·
                  exact fin15Anchored_clause19772 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19773 chi hbad
                ·
                  exact fin15Anchored_clause19774 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19775 chi hbad
                ·
                  exact fin15Anchored_clause19776 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19777 chi hbad
                ·
                  exact fin15Anchored_clause19778 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19779 chi hbad
                ·
                  exact fin15Anchored_clause19780 chi hbad
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
                  exact fin15Anchored_clause19781 chi hbad
                ·
                  exact fin15Anchored_clause19782 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19783 chi hbad
                ·
                  exact fin15Anchored_clause19784 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19785 chi hbad
                ·
                  exact fin15Anchored_clause19786 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19787 chi hbad
                ·
                  exact fin15Anchored_clause19788 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19789 chi hbad
                ·
                  exact fin15Anchored_clause19790 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19791 chi hbad
                ·
                  exact fin15Anchored_clause19792 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19793 chi hbad
                ·
                  exact fin15Anchored_clause19794 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19795 chi hbad
                ·
                  exact fin15Anchored_clause19796 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19797 chi hbad
                ·
                  exact fin15Anchored_clause19798 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19799 chi hbad
                ·
                  exact fin15Anchored_clause19800 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19801 chi hbad
                ·
                  exact fin15Anchored_clause19802 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19803 chi hbad
                ·
                  exact fin15Anchored_clause19804 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19805 chi hbad
                ·
                  exact fin15Anchored_clause19806 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19807 chi hbad
                ·
                  exact fin15Anchored_clause19808 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19809 chi hbad
                ·
                  exact fin15Anchored_clause19810 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19811 chi hbad
                ·
                  exact fin15Anchored_clause19812 chi hbad
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
                exact fin15Anchored_clause19813 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19814 chi hbad
                ·
                  exact fin15Anchored_clause19815 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19816 chi hbad
                ·
                  exact fin15Anchored_clause19817 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19818 chi hbad
                ·
                  exact fin15Anchored_clause19819 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19820 chi hbad
                ·
                  exact fin15Anchored_clause19821 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19822 chi hbad
                ·
                  exact fin15Anchored_clause19823 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19824 chi hbad
                ·
                  exact fin15Anchored_clause19825 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19826 chi hbad
                ·
                  exact fin15Anchored_clause19827 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19828 chi hbad
                ·
                  exact fin15Anchored_clause19829 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19830 chi hbad
                ·
                  exact fin15Anchored_clause19831 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19832 chi hbad
                ·
                  exact fin15Anchored_clause19833 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19834 chi hbad
                ·
                  exact fin15Anchored_clause19835 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19836 chi hbad
                ·
                  exact fin15Anchored_clause19837 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19838 chi hbad
                ·
                  exact fin15Anchored_clause19839 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19840 chi hbad
                ·
                  exact fin15Anchored_clause19841 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19842 chi hbad
                ·
                  exact fin15Anchored_clause19843 chi hbad
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
                  exact fin15Anchored_clause19844 chi hbad
                ·
                  exact fin15Anchored_clause19845 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19846 chi hbad
                ·
                  exact fin15Anchored_clause19847 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19848 chi hbad
                ·
                  exact fin15Anchored_clause19849 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19850 chi hbad
                ·
                  exact fin15Anchored_clause19851 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19852 chi hbad
                ·
                  exact fin15Anchored_clause19853 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19854 chi hbad
                ·
                  exact fin15Anchored_clause19855 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19856 chi hbad
                ·
                  exact fin15Anchored_clause19857 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19858 chi hbad
                ·
                  exact fin15Anchored_clause19859 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19860 chi hbad
                ·
                  exact fin15Anchored_clause19861 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19862 chi hbad
                ·
                  exact fin15Anchored_clause19863 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19864 chi hbad
                ·
                  exact fin15Anchored_clause19865 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19866 chi hbad
                ·
                  exact fin15Anchored_clause19867 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19868 chi hbad
                ·
                  exact fin15Anchored_clause19869 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19870 chi hbad
                ·
                  exact fin15Anchored_clause19871 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19872 chi hbad
                ·
                  exact fin15Anchored_clause19873 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19874 chi hbad
                ·
                  exact fin15Anchored_clause19875 chi hbad
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
                exact fin15Anchored_clause19876 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19877 chi hbad
                ·
                  exact fin15Anchored_clause19878 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19879 chi hbad
                ·
                  exact fin15Anchored_clause19880 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19881 chi hbad
                ·
                  exact fin15Anchored_clause19882 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19883 chi hbad
                ·
                  exact fin15Anchored_clause19884 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19885 chi hbad
                ·
                  exact fin15Anchored_clause19886 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19887 chi hbad
                ·
                  exact fin15Anchored_clause19888 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19889 chi hbad
                ·
                  exact fin15Anchored_clause19890 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19891 chi hbad
                ·
                  exact fin15Anchored_clause19892 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19893 chi hbad
                ·
                  exact fin15Anchored_clause19894 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19895 chi hbad
                ·
                  exact fin15Anchored_clause19896 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19897 chi hbad
                ·
                  exact fin15Anchored_clause19898 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19899 chi hbad
                ·
                  exact fin15Anchored_clause19900 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19901 chi hbad
                ·
                  exact fin15Anchored_clause19902 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19903 chi hbad
                ·
                  exact fin15Anchored_clause19904 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19905 chi hbad
                ·
                  exact fin15Anchored_clause19906 chi hbad
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
                  exact fin15Anchored_clause19907 chi hbad
                ·
                  exact fin15Anchored_clause19908 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19909 chi hbad
                ·
                  exact fin15Anchored_clause19910 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19911 chi hbad
                ·
                  exact fin15Anchored_clause19912 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19913 chi hbad
                ·
                  exact fin15Anchored_clause19914 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19915 chi hbad
                ·
                  exact fin15Anchored_clause19916 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19917 chi hbad
                ·
                  exact fin15Anchored_clause19918 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19919 chi hbad
                ·
                  exact fin15Anchored_clause19920 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19921 chi hbad
                ·
                  exact fin15Anchored_clause19922 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19923 chi hbad
                ·
                  exact fin15Anchored_clause19924 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19925 chi hbad
                ·
                  exact fin15Anchored_clause19926 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19927 chi hbad
                ·
                  exact fin15Anchored_clause19928 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19929 chi hbad
                ·
                  exact fin15Anchored_clause19930 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19931 chi hbad
                ·
                  exact fin15Anchored_clause19932 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19933 chi hbad
                ·
                  exact fin15Anchored_clause19934 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19935 chi hbad
                ·
                  exact fin15Anchored_clause19936 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19937 chi hbad
                ·
                  exact fin15Anchored_clause19938 chi hbad

end ErdosSzekeres

end
