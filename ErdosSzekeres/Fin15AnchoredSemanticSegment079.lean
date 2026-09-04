module

public import ErdosSzekeres.Fin15AnchoredClauseChunk155
public import ErdosSzekeres.Fin15AnchoredClauseChunk156
public import ErdosSzekeres.Fin15AnchoredClauseChunk157

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 079. -/

theorem fin15Anchored_rejectSemanticSegment079
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom2735 chi ∧
      ¬Fin15AnchoredAtom0757 chi) ∨
      ((Fin15AnchoredAtom2735 chi ∧
      ¬Fin15AnchoredAtom0803 chi) ∨
      (Fin15AnchoredAtom2735 chi ∧
      ¬Fin15AnchoredAtom1734 chi))) ∨
      (((¬Fin15AnchoredAtom2735 chi ∧
      Fin15AnchoredAtom0749 chi ∧
      Fin15AnchoredAtom0753 chi ∧
      Fin15AnchoredAtom0757 chi ∧
      Fin15AnchoredAtom0803 chi ∧
      Fin15AnchoredAtom1734 chi) ∨
      (Fin15AnchoredAtom2736 chi ∧
      ¬Fin15AnchoredAtom0750 chi)) ∨
      ((Fin15AnchoredAtom2736 chi ∧
      ¬Fin15AnchoredAtom0751 chi) ∨
      (Fin15AnchoredAtom2736 chi ∧
      ¬Fin15AnchoredAtom0804 chi)))) ∨
      ((((¬Fin15AnchoredAtom2736 chi ∧
      Fin15AnchoredAtom0750 chi ∧
      Fin15AnchoredAtom0751 chi ∧
      Fin15AnchoredAtom0758 chi ∧
      Fin15AnchoredAtom0804 chi ∧
      Fin15AnchoredAtom1735 chi) ∨
      (Fin15AnchoredAtom2737 chi ∧
      ¬Fin15AnchoredAtom0750 chi)) ∨
      ((Fin15AnchoredAtom2737 chi ∧
      ¬Fin15AnchoredAtom0752 chi) ∨
      (Fin15AnchoredAtom2737 chi ∧
      ¬Fin15AnchoredAtom0805 chi))) ∨
      (((Fin15AnchoredAtom2738 chi ∧
      ¬Fin15AnchoredAtom0750 chi) ∨
      (Fin15AnchoredAtom2738 chi ∧
      ¬Fin15AnchoredAtom0753 chi)) ∨
      ((Fin15AnchoredAtom2738 chi ∧
      ¬Fin15AnchoredAtom0760 chi) ∨
      (Fin15AnchoredAtom2738 chi ∧
      ¬Fin15AnchoredAtom0806 chi))))) ∨
      (((((Fin15AnchoredAtom2738 chi ∧
      ¬Fin15AnchoredAtom1737 chi) ∨
      (¬Fin15AnchoredAtom2738 chi ∧
      Fin15AnchoredAtom0750 chi ∧
      Fin15AnchoredAtom0753 chi ∧
      Fin15AnchoredAtom0760 chi ∧
      Fin15AnchoredAtom0806 chi ∧
      Fin15AnchoredAtom1737 chi)) ∨
      ((Fin15AnchoredAtom2739 chi ∧
      ¬Fin15AnchoredAtom0751 chi) ∨
      (Fin15AnchoredAtom2739 chi ∧
      ¬Fin15AnchoredAtom0752 chi))) ∨
      (((Fin15AnchoredAtom2739 chi ∧
      ¬Fin15AnchoredAtom0761 chi) ∨
      (Fin15AnchoredAtom2739 chi ∧
      ¬Fin15AnchoredAtom0807 chi)) ∨
      ((Fin15AnchoredAtom2739 chi ∧
      ¬Fin15AnchoredAtom1738 chi) ∨
      (¬Fin15AnchoredAtom2739 chi ∧
      Fin15AnchoredAtom0751 chi ∧
      Fin15AnchoredAtom0752 chi ∧
      Fin15AnchoredAtom0761 chi ∧
      Fin15AnchoredAtom0807 chi ∧
      Fin15AnchoredAtom1738 chi)))) ∨
      ((((Fin15AnchoredAtom2740 chi ∧
      ¬Fin15AnchoredAtom0751 chi) ∨
      (Fin15AnchoredAtom2740 chi ∧
      ¬Fin15AnchoredAtom0753 chi)) ∨
      ((Fin15AnchoredAtom2740 chi ∧
      ¬Fin15AnchoredAtom0762 chi) ∨
      (Fin15AnchoredAtom2740 chi ∧
      ¬Fin15AnchoredAtom0808 chi))) ∨
      (((Fin15AnchoredAtom2740 chi ∧
      ¬Fin15AnchoredAtom1739 chi) ∨
      (¬Fin15AnchoredAtom2740 chi ∧
      Fin15AnchoredAtom0751 chi ∧
      Fin15AnchoredAtom0753 chi ∧
      Fin15AnchoredAtom0762 chi ∧
      Fin15AnchoredAtom0808 chi ∧
      Fin15AnchoredAtom1739 chi)) ∨
      ((Fin15AnchoredAtom2741 chi ∧
      ¬Fin15AnchoredAtom0752 chi) ∨
      (Fin15AnchoredAtom2741 chi ∧
      ¬Fin15AnchoredAtom0753 chi)))))) ∨
      ((((((Fin15AnchoredAtom2741 chi ∧
      ¬Fin15AnchoredAtom0763 chi) ∨
      (Fin15AnchoredAtom2741 chi ∧
      ¬Fin15AnchoredAtom0809 chi)) ∨
      ((Fin15AnchoredAtom2741 chi ∧
      ¬Fin15AnchoredAtom1740 chi) ∨
      (¬Fin15AnchoredAtom2741 chi ∧
      Fin15AnchoredAtom0752 chi ∧
      Fin15AnchoredAtom0753 chi ∧
      Fin15AnchoredAtom0763 chi ∧
      Fin15AnchoredAtom0809 chi ∧
      Fin15AnchoredAtom1740 chi))) ∨
      (((Fin15AnchoredAtom2742 chi ∧
      ¬Fin15AnchoredAtom0755 chi) ∨
      (Fin15AnchoredAtom2742 chi ∧
      ¬Fin15AnchoredAtom0810 chi)) ∨
      ((¬Fin15AnchoredAtom2742 chi ∧
      Fin15AnchoredAtom0754 chi ∧
      Fin15AnchoredAtom0755 chi ∧
      Fin15AnchoredAtom0758 chi ∧
      Fin15AnchoredAtom0810 chi ∧
      Fin15AnchoredAtom1741 chi) ∨
      (Fin15AnchoredAtom2743 chi ∧
      ¬Fin15AnchoredAtom0754 chi)))) ∨
      ((((Fin15AnchoredAtom2743 chi ∧
      ¬Fin15AnchoredAtom0756 chi) ∨
      (Fin15AnchoredAtom2743 chi ∧
      ¬Fin15AnchoredAtom0759 chi)) ∨
      ((Fin15AnchoredAtom2743 chi ∧
      ¬Fin15AnchoredAtom0811 chi) ∨
      (Fin15AnchoredAtom2743 chi ∧
      ¬Fin15AnchoredAtom1742 chi))) ∨
      (((¬Fin15AnchoredAtom2743 chi ∧
      Fin15AnchoredAtom0754 chi ∧
      Fin15AnchoredAtom0756 chi ∧
      Fin15AnchoredAtom0759 chi ∧
      Fin15AnchoredAtom0811 chi ∧
      Fin15AnchoredAtom1742 chi) ∨
      (Fin15AnchoredAtom2744 chi ∧
      ¬Fin15AnchoredAtom0754 chi)) ∨
      ((Fin15AnchoredAtom2744 chi ∧
      ¬Fin15AnchoredAtom0757 chi) ∨
      (Fin15AnchoredAtom2744 chi ∧
      ¬Fin15AnchoredAtom0760 chi))))) ∨
      (((((Fin15AnchoredAtom2744 chi ∧
      ¬Fin15AnchoredAtom0812 chi) ∨
      (Fin15AnchoredAtom2744 chi ∧
      ¬Fin15AnchoredAtom1743 chi)) ∨
      ((¬Fin15AnchoredAtom2744 chi ∧
      Fin15AnchoredAtom0754 chi ∧
      Fin15AnchoredAtom0757 chi ∧
      Fin15AnchoredAtom0760 chi ∧
      Fin15AnchoredAtom0812 chi ∧
      Fin15AnchoredAtom1743 chi) ∨
      (Fin15AnchoredAtom2745 chi ∧
      ¬Fin15AnchoredAtom0755 chi))) ∨
      (((Fin15AnchoredAtom2745 chi ∧
      ¬Fin15AnchoredAtom0756 chi) ∨
      (Fin15AnchoredAtom2745 chi ∧
      ¬Fin15AnchoredAtom0761 chi)) ∨
      ((Fin15AnchoredAtom2745 chi ∧
      ¬Fin15AnchoredAtom0813 chi) ∨
      (Fin15AnchoredAtom2745 chi ∧
      ¬Fin15AnchoredAtom1744 chi)))) ∨
      ((((¬Fin15AnchoredAtom2745 chi ∧
      Fin15AnchoredAtom0755 chi ∧
      Fin15AnchoredAtom0756 chi ∧
      Fin15AnchoredAtom0761 chi ∧
      Fin15AnchoredAtom0813 chi ∧
      Fin15AnchoredAtom1744 chi) ∨
      (Fin15AnchoredAtom2746 chi ∧
      ¬Fin15AnchoredAtom0755 chi)) ∨
      ((Fin15AnchoredAtom2746 chi ∧
      ¬Fin15AnchoredAtom0757 chi) ∨
      (Fin15AnchoredAtom2746 chi ∧
      ¬Fin15AnchoredAtom0762 chi))) ∨
      (((Fin15AnchoredAtom2746 chi ∧
      ¬Fin15AnchoredAtom0814 chi) ∨
      (Fin15AnchoredAtom2746 chi ∧
      ¬Fin15AnchoredAtom1745 chi)) ∨
      ((¬Fin15AnchoredAtom2746 chi ∧
      Fin15AnchoredAtom0755 chi ∧
      Fin15AnchoredAtom0757 chi ∧
      Fin15AnchoredAtom0762 chi ∧
      Fin15AnchoredAtom0814 chi ∧
      Fin15AnchoredAtom1745 chi) ∨
      (Fin15AnchoredAtom2747 chi ∧
      ¬Fin15AnchoredAtom0756 chi))))))) ∨
      ((((((Fin15AnchoredAtom2747 chi ∧
      ¬Fin15AnchoredAtom0757 chi) ∨
      ((Fin15AnchoredAtom2747 chi ∧
      ¬Fin15AnchoredAtom0763 chi) ∨
      (Fin15AnchoredAtom2747 chi ∧
      ¬Fin15AnchoredAtom0815 chi))) ∨
      (((Fin15AnchoredAtom2747 chi ∧
      ¬Fin15AnchoredAtom1746 chi) ∨
      (¬Fin15AnchoredAtom2747 chi ∧
      Fin15AnchoredAtom0756 chi ∧
      Fin15AnchoredAtom0757 chi ∧
      Fin15AnchoredAtom0763 chi ∧
      Fin15AnchoredAtom0815 chi ∧
      Fin15AnchoredAtom1746 chi)) ∨
      ((Fin15AnchoredAtom2748 chi ∧
      ¬Fin15AnchoredAtom0758 chi) ∨
      (Fin15AnchoredAtom2748 chi ∧
      ¬Fin15AnchoredAtom0761 chi)))) ∨
      ((((Fin15AnchoredAtom2748 chi ∧
      ¬Fin15AnchoredAtom0816 chi) ∨
      (Fin15AnchoredAtom2748 chi ∧
      ¬Fin15AnchoredAtom1747 chi)) ∨
      ((¬Fin15AnchoredAtom2748 chi ∧
      Fin15AnchoredAtom0758 chi ∧
      Fin15AnchoredAtom0759 chi ∧
      Fin15AnchoredAtom0761 chi ∧
      Fin15AnchoredAtom0816 chi ∧
      Fin15AnchoredAtom1747 chi) ∨
      (Fin15AnchoredAtom2749 chi ∧
      ¬Fin15AnchoredAtom0762 chi))) ∨
      (((¬Fin15AnchoredAtom2749 chi ∧
      Fin15AnchoredAtom0758 chi ∧
      Fin15AnchoredAtom0760 chi ∧
      Fin15AnchoredAtom0762 chi ∧
      Fin15AnchoredAtom0817 chi ∧
      Fin15AnchoredAtom1748 chi) ∨
      (Fin15AnchoredAtom2751 chi ∧
      ¬Fin15AnchoredAtom0761 chi)) ∨
      ((Fin15AnchoredAtom2751 chi ∧
      ¬Fin15AnchoredAtom0762 chi) ∨
      (Fin15AnchoredAtom2751 chi ∧
      ¬Fin15AnchoredAtom0763 chi))))) ∨
      (((((Fin15AnchoredAtom2751 chi ∧
      ¬Fin15AnchoredAtom0819 chi) ∨
      (Fin15AnchoredAtom2751 chi ∧
      ¬Fin15AnchoredAtom1750 chi)) ∨
      ((¬Fin15AnchoredAtom2751 chi ∧
      Fin15AnchoredAtom0761 chi ∧
      Fin15AnchoredAtom0762 chi ∧
      Fin15AnchoredAtom0763 chi ∧
      Fin15AnchoredAtom0819 chi ∧
      Fin15AnchoredAtom1750 chi) ∨
      (Fin15AnchoredAtom2752 chi ∧
      ¬Fin15AnchoredAtom0764 chi))) ∨
      (((Fin15AnchoredAtom2752 chi ∧
      ¬Fin15AnchoredAtom0765 chi) ∨
      (Fin15AnchoredAtom2752 chi ∧
      ¬Fin15AnchoredAtom0770 chi)) ∨
      ((Fin15AnchoredAtom2752 chi ∧
      ¬Fin15AnchoredAtom0785 chi) ∨
      (Fin15AnchoredAtom2752 chi ∧
      ¬Fin15AnchoredAtom1751 chi)))) ∨
      ((((¬Fin15AnchoredAtom2752 chi ∧
      Fin15AnchoredAtom0764 chi ∧
      Fin15AnchoredAtom0765 chi ∧
      Fin15AnchoredAtom0770 chi ∧
      Fin15AnchoredAtom0785 chi ∧
      Fin15AnchoredAtom1751 chi) ∨
      (Fin15AnchoredAtom2754 chi ∧
      ¬Fin15AnchoredAtom0764 chi)) ∨
      ((Fin15AnchoredAtom2754 chi ∧
      ¬Fin15AnchoredAtom0767 chi) ∨
      (Fin15AnchoredAtom2754 chi ∧
      ¬Fin15AnchoredAtom0772 chi))) ∨
      (((Fin15AnchoredAtom2754 chi ∧
      ¬Fin15AnchoredAtom0787 chi) ∨
      (Fin15AnchoredAtom2754 chi ∧
      ¬Fin15AnchoredAtom1753 chi)) ∨
      ((¬Fin15AnchoredAtom2754 chi ∧
      Fin15AnchoredAtom0764 chi ∧
      Fin15AnchoredAtom0767 chi ∧
      Fin15AnchoredAtom0772 chi ∧
      Fin15AnchoredAtom0787 chi ∧
      Fin15AnchoredAtom1753 chi) ∨
      (Fin15AnchoredAtom2755 chi ∧
      ¬Fin15AnchoredAtom0764 chi)))))) ∨
      ((((((Fin15AnchoredAtom2755 chi ∧
      ¬Fin15AnchoredAtom0773 chi) ∨
      (Fin15AnchoredAtom2755 chi ∧
      ¬Fin15AnchoredAtom0788 chi)) ∨
      ((Fin15AnchoredAtom2755 chi ∧
      ¬Fin15AnchoredAtom1754 chi) ∨
      (¬Fin15AnchoredAtom2755 chi ∧
      Fin15AnchoredAtom0764 chi ∧
      Fin15AnchoredAtom0768 chi ∧
      Fin15AnchoredAtom0773 chi ∧
      Fin15AnchoredAtom0788 chi ∧
      Fin15AnchoredAtom1754 chi))) ∨
      (((Fin15AnchoredAtom2756 chi ∧
      ¬Fin15AnchoredAtom0764 chi) ∨
      (Fin15AnchoredAtom2756 chi ∧
      ¬Fin15AnchoredAtom0769 chi)) ∨
      ((Fin15AnchoredAtom2756 chi ∧
      ¬Fin15AnchoredAtom0774 chi) ∨
      (Fin15AnchoredAtom2756 chi ∧
      ¬Fin15AnchoredAtom0789 chi)))) ∨
      ((((Fin15AnchoredAtom2756 chi ∧
      ¬Fin15AnchoredAtom1755 chi) ∨
      (¬Fin15AnchoredAtom2756 chi ∧
      Fin15AnchoredAtom0764 chi ∧
      Fin15AnchoredAtom0769 chi ∧
      Fin15AnchoredAtom0774 chi ∧
      Fin15AnchoredAtom0789 chi ∧
      Fin15AnchoredAtom1755 chi)) ∨
      ((Fin15AnchoredAtom2758 chi ∧
      ¬Fin15AnchoredAtom0765 chi) ∨
      (Fin15AnchoredAtom2758 chi ∧
      ¬Fin15AnchoredAtom0767 chi))) ∨
      (((Fin15AnchoredAtom2758 chi ∧
      ¬Fin15AnchoredAtom0776 chi) ∨
      (Fin15AnchoredAtom2758 chi ∧
      ¬Fin15AnchoredAtom0791 chi)) ∨
      ((Fin15AnchoredAtom2758 chi ∧
      ¬Fin15AnchoredAtom1757 chi) ∨
      (¬Fin15AnchoredAtom2758 chi ∧
      Fin15AnchoredAtom0765 chi ∧
      Fin15AnchoredAtom0767 chi ∧
      Fin15AnchoredAtom0776 chi ∧
      Fin15AnchoredAtom0791 chi ∧
      Fin15AnchoredAtom1757 chi))))) ∨
      (((((Fin15AnchoredAtom2759 chi ∧
      ¬Fin15AnchoredAtom0765 chi) ∨
      (Fin15AnchoredAtom2759 chi ∧
      ¬Fin15AnchoredAtom0768 chi)) ∨
      ((Fin15AnchoredAtom2759 chi ∧
      ¬Fin15AnchoredAtom0777 chi) ∨
      (Fin15AnchoredAtom2759 chi ∧
      ¬Fin15AnchoredAtom0792 chi))) ∨
      (((Fin15AnchoredAtom2759 chi ∧
      ¬Fin15AnchoredAtom1758 chi) ∨
      (¬Fin15AnchoredAtom2759 chi ∧
      Fin15AnchoredAtom0765 chi ∧
      Fin15AnchoredAtom0768 chi ∧
      Fin15AnchoredAtom0777 chi ∧
      Fin15AnchoredAtom0792 chi ∧
      Fin15AnchoredAtom1758 chi)) ∨
      ((Fin15AnchoredAtom2760 chi ∧
      ¬Fin15AnchoredAtom0765 chi) ∨
      (Fin15AnchoredAtom2760 chi ∧
      ¬Fin15AnchoredAtom0769 chi)))) ∨
      ((((Fin15AnchoredAtom2760 chi ∧
      ¬Fin15AnchoredAtom0778 chi) ∨
      (Fin15AnchoredAtom2760 chi ∧
      ¬Fin15AnchoredAtom0793 chi)) ∨
      ((Fin15AnchoredAtom2760 chi ∧
      ¬Fin15AnchoredAtom1759 chi) ∨
      (¬Fin15AnchoredAtom2760 chi ∧
      Fin15AnchoredAtom0765 chi ∧
      Fin15AnchoredAtom0769 chi ∧
      Fin15AnchoredAtom0778 chi ∧
      Fin15AnchoredAtom0793 chi ∧
      Fin15AnchoredAtom1759 chi))) ∨
      (((Fin15AnchoredAtom2764 chi ∧
      ¬Fin15AnchoredAtom0767 chi) ∨
      (Fin15AnchoredAtom2764 chi ∧
      ¬Fin15AnchoredAtom0768 chi)) ∨
      ((Fin15AnchoredAtom2764 chi ∧
      ¬Fin15AnchoredAtom0782 chi) ∨
      (Fin15AnchoredAtom2764 chi ∧
      ¬Fin15AnchoredAtom0797 chi)))))))) ∨
      (((((((Fin15AnchoredAtom2764 chi ∧
      ¬Fin15AnchoredAtom1763 chi) ∨
      ((¬Fin15AnchoredAtom2764 chi ∧
      Fin15AnchoredAtom0767 chi ∧
      Fin15AnchoredAtom0768 chi ∧
      Fin15AnchoredAtom0782 chi ∧
      Fin15AnchoredAtom0797 chi ∧
      Fin15AnchoredAtom1763 chi) ∨
      (Fin15AnchoredAtom2765 chi ∧
      ¬Fin15AnchoredAtom0767 chi))) ∨
      (((Fin15AnchoredAtom2765 chi ∧
      ¬Fin15AnchoredAtom0769 chi) ∨
      (Fin15AnchoredAtom2765 chi ∧
      ¬Fin15AnchoredAtom0783 chi)) ∨
      ((Fin15AnchoredAtom2765 chi ∧
      ¬Fin15AnchoredAtom0798 chi) ∨
      (Fin15AnchoredAtom2765 chi ∧
      ¬Fin15AnchoredAtom1764 chi)))) ∨
      ((((¬Fin15AnchoredAtom2765 chi ∧
      Fin15AnchoredAtom0767 chi ∧
      Fin15AnchoredAtom0769 chi ∧
      Fin15AnchoredAtom0783 chi ∧
      Fin15AnchoredAtom0798 chi ∧
      Fin15AnchoredAtom1764 chi) ∨
      (Fin15AnchoredAtom2766 chi ∧
      ¬Fin15AnchoredAtom0768 chi)) ∨
      ((Fin15AnchoredAtom2766 chi ∧
      ¬Fin15AnchoredAtom0769 chi) ∨
      (Fin15AnchoredAtom2766 chi ∧
      ¬Fin15AnchoredAtom0784 chi))) ∨
      (((Fin15AnchoredAtom2766 chi ∧
      ¬Fin15AnchoredAtom0799 chi) ∨
      (Fin15AnchoredAtom2766 chi ∧
      ¬Fin15AnchoredAtom1765 chi)) ∨
      ((¬Fin15AnchoredAtom2766 chi ∧
      Fin15AnchoredAtom0768 chi ∧
      Fin15AnchoredAtom0769 chi ∧
      Fin15AnchoredAtom0784 chi ∧
      Fin15AnchoredAtom0799 chi ∧
      Fin15AnchoredAtom1765 chi) ∨
      (Fin15AnchoredAtom2767 chi ∧
      ¬Fin15AnchoredAtom0770 chi))))) ∨
      (((((Fin15AnchoredAtom2767 chi ∧
      ¬Fin15AnchoredAtom0771 chi) ∨
      (Fin15AnchoredAtom2767 chi ∧
      ¬Fin15AnchoredAtom0775 chi)) ∨
      ((Fin15AnchoredAtom2767 chi ∧
      ¬Fin15AnchoredAtom0800 chi) ∨
      (Fin15AnchoredAtom2767 chi ∧
      ¬Fin15AnchoredAtom1766 chi))) ∨
      (((¬Fin15AnchoredAtom2767 chi ∧
      Fin15AnchoredAtom0770 chi ∧
      Fin15AnchoredAtom0771 chi ∧
      Fin15AnchoredAtom0775 chi ∧
      Fin15AnchoredAtom0800 chi ∧
      Fin15AnchoredAtom1766 chi) ∨
      (Fin15AnchoredAtom2768 chi ∧
      ¬Fin15AnchoredAtom0770 chi)) ∨
      ((Fin15AnchoredAtom2768 chi ∧
      ¬Fin15AnchoredAtom0772 chi) ∨
      (Fin15AnchoredAtom2768 chi ∧
      ¬Fin15AnchoredAtom0776 chi)))) ∨
      ((((Fin15AnchoredAtom2768 chi ∧
      ¬Fin15AnchoredAtom0801 chi) ∨
      (Fin15AnchoredAtom2768 chi ∧
      ¬Fin15AnchoredAtom1767 chi)) ∨
      ((¬Fin15AnchoredAtom2768 chi ∧
      Fin15AnchoredAtom0770 chi ∧
      Fin15AnchoredAtom0772 chi ∧
      Fin15AnchoredAtom0776 chi ∧
      Fin15AnchoredAtom0801 chi ∧
      Fin15AnchoredAtom1767 chi) ∨
      (Fin15AnchoredAtom2769 chi ∧
      ¬Fin15AnchoredAtom0770 chi))) ∨
      (((Fin15AnchoredAtom2769 chi ∧
      ¬Fin15AnchoredAtom0773 chi) ∨
      (Fin15AnchoredAtom2769 chi ∧
      ¬Fin15AnchoredAtom0777 chi)) ∨
      ((Fin15AnchoredAtom2769 chi ∧
      ¬Fin15AnchoredAtom0802 chi) ∨
      (Fin15AnchoredAtom2769 chi ∧
      ¬Fin15AnchoredAtom1768 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom2769 chi ∧
      Fin15AnchoredAtom0770 chi ∧
      Fin15AnchoredAtom0773 chi ∧
      Fin15AnchoredAtom0777 chi ∧
      Fin15AnchoredAtom0802 chi ∧
      Fin15AnchoredAtom1768 chi) ∨
      (Fin15AnchoredAtom2770 chi ∧
      ¬Fin15AnchoredAtom0770 chi)) ∨
      ((Fin15AnchoredAtom2770 chi ∧
      ¬Fin15AnchoredAtom0774 chi) ∨
      (Fin15AnchoredAtom2770 chi ∧
      ¬Fin15AnchoredAtom0778 chi))) ∨
      (((Fin15AnchoredAtom2770 chi ∧
      ¬Fin15AnchoredAtom0803 chi) ∨
      (Fin15AnchoredAtom2770 chi ∧
      ¬Fin15AnchoredAtom1769 chi)) ∨
      ((¬Fin15AnchoredAtom2770 chi ∧
      Fin15AnchoredAtom0770 chi ∧
      Fin15AnchoredAtom0774 chi ∧
      Fin15AnchoredAtom0778 chi ∧
      Fin15AnchoredAtom0803 chi ∧
      Fin15AnchoredAtom1769 chi) ∨
      (Fin15AnchoredAtom2771 chi ∧
      ¬Fin15AnchoredAtom0771 chi)))) ∨
      ((((Fin15AnchoredAtom2771 chi ∧
      ¬Fin15AnchoredAtom0772 chi) ∨
      (Fin15AnchoredAtom2771 chi ∧
      ¬Fin15AnchoredAtom0779 chi)) ∨
      ((Fin15AnchoredAtom2771 chi ∧
      ¬Fin15AnchoredAtom0804 chi) ∨
      (¬Fin15AnchoredAtom2771 chi ∧
      Fin15AnchoredAtom0771 chi ∧
      Fin15AnchoredAtom0772 chi ∧
      Fin15AnchoredAtom0779 chi ∧
      Fin15AnchoredAtom0804 chi ∧
      Fin15AnchoredAtom1770 chi))) ∨
      (((Fin15AnchoredAtom2772 chi ∧
      ¬Fin15AnchoredAtom0771 chi) ∨
      (Fin15AnchoredAtom2772 chi ∧
      ¬Fin15AnchoredAtom0780 chi)) ∨
      ((Fin15AnchoredAtom2772 chi ∧
      ¬Fin15AnchoredAtom0805 chi) ∨
      (Fin15AnchoredAtom2772 chi ∧
      ¬Fin15AnchoredAtom1771 chi))))) ∨
      (((((¬Fin15AnchoredAtom2772 chi ∧
      Fin15AnchoredAtom0771 chi ∧
      Fin15AnchoredAtom0773 chi ∧
      Fin15AnchoredAtom0780 chi ∧
      Fin15AnchoredAtom0805 chi ∧
      Fin15AnchoredAtom1771 chi) ∨
      (Fin15AnchoredAtom2773 chi ∧
      ¬Fin15AnchoredAtom0774 chi)) ∨
      ((Fin15AnchoredAtom2773 chi ∧
      ¬Fin15AnchoredAtom0806 chi) ∨
      (Fin15AnchoredAtom2774 chi ∧
      ¬Fin15AnchoredAtom0772 chi))) ∨
      (((Fin15AnchoredAtom2774 chi ∧
      ¬Fin15AnchoredAtom0773 chi) ∨
      (Fin15AnchoredAtom2774 chi ∧
      ¬Fin15AnchoredAtom0782 chi)) ∨
      ((Fin15AnchoredAtom2774 chi ∧
      ¬Fin15AnchoredAtom0807 chi) ∨
      (Fin15AnchoredAtom2774 chi ∧
      ¬Fin15AnchoredAtom1773 chi)))) ∨
      ((((¬Fin15AnchoredAtom2774 chi ∧
      Fin15AnchoredAtom0772 chi ∧
      Fin15AnchoredAtom0773 chi ∧
      Fin15AnchoredAtom0782 chi ∧
      Fin15AnchoredAtom0807 chi ∧
      Fin15AnchoredAtom1773 chi) ∨
      (Fin15AnchoredAtom2775 chi ∧
      ¬Fin15AnchoredAtom0772 chi)) ∨
      ((Fin15AnchoredAtom2775 chi ∧
      ¬Fin15AnchoredAtom0774 chi) ∨
      (Fin15AnchoredAtom2775 chi ∧
      ¬Fin15AnchoredAtom0783 chi))) ∨
      (((Fin15AnchoredAtom2775 chi ∧
      ¬Fin15AnchoredAtom0808 chi) ∨
      (Fin15AnchoredAtom2775 chi ∧
      ¬Fin15AnchoredAtom1774 chi)) ∨
      ((¬Fin15AnchoredAtom2775 chi ∧
      Fin15AnchoredAtom0772 chi ∧
      Fin15AnchoredAtom0774 chi ∧
      Fin15AnchoredAtom0783 chi ∧
      Fin15AnchoredAtom0808 chi ∧
      Fin15AnchoredAtom1774 chi) ∨
      (Fin15AnchoredAtom2776 chi ∧
      ¬Fin15AnchoredAtom0773 chi))))))) ∨
      (((((((Fin15AnchoredAtom2776 chi ∧
      ¬Fin15AnchoredAtom0774 chi) ∨
      (Fin15AnchoredAtom2776 chi ∧
      ¬Fin15AnchoredAtom0784 chi)) ∨
      ((Fin15AnchoredAtom2776 chi ∧
      ¬Fin15AnchoredAtom0809 chi) ∨
      (Fin15AnchoredAtom2776 chi ∧
      ¬Fin15AnchoredAtom1775 chi))) ∨
      (((¬Fin15AnchoredAtom2776 chi ∧
      Fin15AnchoredAtom0773 chi ∧
      Fin15AnchoredAtom0774 chi ∧
      Fin15AnchoredAtom0784 chi ∧
      Fin15AnchoredAtom0809 chi ∧
      Fin15AnchoredAtom1775 chi) ∨
      (Fin15AnchoredAtom2777 chi ∧
      ¬Fin15AnchoredAtom0775 chi)) ∨
      ((Fin15AnchoredAtom2777 chi ∧
      ¬Fin15AnchoredAtom0776 chi) ∨
      (Fin15AnchoredAtom2777 chi ∧
      ¬Fin15AnchoredAtom0810 chi)))) ∨
      ((((Fin15AnchoredAtom2777 chi ∧
      ¬Fin15AnchoredAtom1776 chi) ∨
      (¬Fin15AnchoredAtom2777 chi ∧
      Fin15AnchoredAtom0775 chi ∧
      Fin15AnchoredAtom0776 chi ∧
      Fin15AnchoredAtom0779 chi ∧
      Fin15AnchoredAtom0810 chi ∧
      Fin15AnchoredAtom1776 chi)) ∨
      ((Fin15AnchoredAtom2778 chi ∧
      ¬Fin15AnchoredAtom0775 chi) ∨
      (Fin15AnchoredAtom2778 chi ∧
      ¬Fin15AnchoredAtom0777 chi))) ∨
      (((Fin15AnchoredAtom2778 chi ∧
      ¬Fin15AnchoredAtom0780 chi) ∨
      (Fin15AnchoredAtom2778 chi ∧
      ¬Fin15AnchoredAtom0811 chi)) ∨
      ((Fin15AnchoredAtom2778 chi ∧
      ¬Fin15AnchoredAtom1777 chi) ∨
      (¬Fin15AnchoredAtom2778 chi ∧
      Fin15AnchoredAtom0775 chi ∧
      Fin15AnchoredAtom0777 chi ∧
      Fin15AnchoredAtom0780 chi ∧
      Fin15AnchoredAtom0811 chi ∧
      Fin15AnchoredAtom1777 chi))))) ∨
      (((((Fin15AnchoredAtom2779 chi ∧
      ¬Fin15AnchoredAtom0775 chi) ∨
      (Fin15AnchoredAtom2779 chi ∧
      ¬Fin15AnchoredAtom0778 chi)) ∨
      ((Fin15AnchoredAtom2779 chi ∧
      ¬Fin15AnchoredAtom0812 chi) ∨
      (Fin15AnchoredAtom2779 chi ∧
      ¬Fin15AnchoredAtom1778 chi))) ∨
      (((¬Fin15AnchoredAtom2779 chi ∧
      Fin15AnchoredAtom0775 chi ∧
      Fin15AnchoredAtom0778 chi ∧
      Fin15AnchoredAtom0781 chi ∧
      Fin15AnchoredAtom0812 chi ∧
      Fin15AnchoredAtom1778 chi) ∨
      (Fin15AnchoredAtom2780 chi ∧
      ¬Fin15AnchoredAtom0776 chi)) ∨
      ((Fin15AnchoredAtom2780 chi ∧
      ¬Fin15AnchoredAtom0777 chi) ∨
      (Fin15AnchoredAtom2780 chi ∧
      ¬Fin15AnchoredAtom0782 chi)))) ∨
      ((((Fin15AnchoredAtom2780 chi ∧
      ¬Fin15AnchoredAtom0813 chi) ∨
      (Fin15AnchoredAtom2780 chi ∧
      ¬Fin15AnchoredAtom1779 chi)) ∨
      ((¬Fin15AnchoredAtom2780 chi ∧
      Fin15AnchoredAtom0776 chi ∧
      Fin15AnchoredAtom0777 chi ∧
      Fin15AnchoredAtom0782 chi ∧
      Fin15AnchoredAtom0813 chi ∧
      Fin15AnchoredAtom1779 chi) ∨
      (Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom0776 chi))) ∨
      (((Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom0778 chi) ∨
      (Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom0783 chi)) ∨
      ((Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom0814 chi) ∨
      (Fin15AnchoredAtom2781 chi ∧
      ¬Fin15AnchoredAtom1780 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom2781 chi ∧
      Fin15AnchoredAtom0776 chi ∧
      Fin15AnchoredAtom0778 chi ∧
      Fin15AnchoredAtom0783 chi ∧
      Fin15AnchoredAtom0814 chi ∧
      Fin15AnchoredAtom1780 chi) ∨
      (Fin15AnchoredAtom2782 chi ∧
      ¬Fin15AnchoredAtom0777 chi)) ∨
      ((Fin15AnchoredAtom2782 chi ∧
      ¬Fin15AnchoredAtom0778 chi) ∨
      (Fin15AnchoredAtom2782 chi ∧
      ¬Fin15AnchoredAtom0784 chi))) ∨
      (((Fin15AnchoredAtom2782 chi ∧
      ¬Fin15AnchoredAtom0815 chi) ∨
      (Fin15AnchoredAtom2782 chi ∧
      ¬Fin15AnchoredAtom1781 chi)) ∨
      ((¬Fin15AnchoredAtom2782 chi ∧
      Fin15AnchoredAtom0777 chi ∧
      Fin15AnchoredAtom0778 chi ∧
      Fin15AnchoredAtom0784 chi ∧
      Fin15AnchoredAtom0815 chi ∧
      Fin15AnchoredAtom1781 chi) ∨
      (Fin15AnchoredAtom2783 chi ∧
      ¬Fin15AnchoredAtom0782 chi)))) ∨
      ((((Fin15AnchoredAtom2783 chi ∧
      ¬Fin15AnchoredAtom0816 chi) ∨
      (¬Fin15AnchoredAtom2783 chi ∧
      Fin15AnchoredAtom0779 chi ∧
      Fin15AnchoredAtom0780 chi ∧
      Fin15AnchoredAtom0782 chi ∧
      Fin15AnchoredAtom0816 chi ∧
      Fin15AnchoredAtom1782 chi)) ∨
      ((Fin15AnchoredAtom2784 chi ∧
      ¬Fin15AnchoredAtom0781 chi) ∨
      (Fin15AnchoredAtom2784 chi ∧
      ¬Fin15AnchoredAtom0783 chi))) ∨
      (((Fin15AnchoredAtom2784 chi ∧
      ¬Fin15AnchoredAtom0817 chi) ∨
      (Fin15AnchoredAtom2784 chi ∧
      ¬Fin15AnchoredAtom1783 chi)) ∨
      ((¬Fin15AnchoredAtom2784 chi ∧
      Fin15AnchoredAtom0779 chi ∧
      Fin15AnchoredAtom0781 chi ∧
      Fin15AnchoredAtom0783 chi ∧
      Fin15AnchoredAtom0817 chi ∧
      Fin15AnchoredAtom1783 chi) ∨
      (Fin15AnchoredAtom2785 chi ∧
      ¬Fin15AnchoredAtom0780 chi))))) ∨
      (((((Fin15AnchoredAtom2785 chi ∧
      ¬Fin15AnchoredAtom0784 chi) ∨
      (Fin15AnchoredAtom2786 chi ∧
      ¬Fin15AnchoredAtom0782 chi)) ∨
      ((Fin15AnchoredAtom2786 chi ∧
      ¬Fin15AnchoredAtom0783 chi) ∨
      (Fin15AnchoredAtom2786 chi ∧
      ¬Fin15AnchoredAtom0784 chi))) ∨
      (((Fin15AnchoredAtom2786 chi ∧
      ¬Fin15AnchoredAtom0819 chi) ∨
      (Fin15AnchoredAtom2786 chi ∧
      ¬Fin15AnchoredAtom1785 chi)) ∨
      ((¬Fin15AnchoredAtom2786 chi ∧
      Fin15AnchoredAtom0782 chi ∧
      Fin15AnchoredAtom0783 chi ∧
      Fin15AnchoredAtom0784 chi ∧
      Fin15AnchoredAtom0819 chi ∧
      Fin15AnchoredAtom1785 chi) ∨
      (Fin15AnchoredAtom2788 chi ∧
      ¬Fin15AnchoredAtom0785 chi)))) ∨
      ((((Fin15AnchoredAtom2788 chi ∧
      ¬Fin15AnchoredAtom0787 chi) ∨
      (Fin15AnchoredAtom2788 chi ∧
      ¬Fin15AnchoredAtom0791 chi)) ∨
      ((Fin15AnchoredAtom2788 chi ∧
      ¬Fin15AnchoredAtom0801 chi) ∨
      (Fin15AnchoredAtom2788 chi ∧
      ¬Fin15AnchoredAtom1787 chi))) ∨
      (((¬Fin15AnchoredAtom2788 chi ∧
      Fin15AnchoredAtom0785 chi ∧
      Fin15AnchoredAtom0787 chi ∧
      Fin15AnchoredAtom0791 chi ∧
      Fin15AnchoredAtom0801 chi ∧
      Fin15AnchoredAtom1787 chi) ∨
      (Fin15AnchoredAtom2789 chi ∧
      ¬Fin15AnchoredAtom0785 chi)) ∨
      ((Fin15AnchoredAtom2789 chi ∧
      ¬Fin15AnchoredAtom0788 chi) ∨
      (Fin15AnchoredAtom2789 chi ∧
      ¬Fin15AnchoredAtom0792 chi)))))))))) := by
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
                exact fin15Anchored_clause19939 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19940 chi hbad
                ·
                  exact fin15Anchored_clause19941 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19942 chi hbad
                ·
                  exact fin15Anchored_clause19943 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19944 chi hbad
                ·
                  exact fin15Anchored_clause19945 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19946 chi hbad
                ·
                  exact fin15Anchored_clause19947 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19948 chi hbad
                ·
                  exact fin15Anchored_clause19949 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19950 chi hbad
                ·
                  exact fin15Anchored_clause19951 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19952 chi hbad
                ·
                  exact fin15Anchored_clause19953 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19954 chi hbad
                ·
                  exact fin15Anchored_clause19955 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19956 chi hbad
                ·
                  exact fin15Anchored_clause19957 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19958 chi hbad
                ·
                  exact fin15Anchored_clause19959 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19960 chi hbad
                ·
                  exact fin15Anchored_clause19961 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19962 chi hbad
                ·
                  exact fin15Anchored_clause19963 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19964 chi hbad
                ·
                  exact fin15Anchored_clause19965 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19966 chi hbad
                ·
                  exact fin15Anchored_clause19967 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19968 chi hbad
                ·
                  exact fin15Anchored_clause19969 chi hbad
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
                  exact fin15Anchored_clause19970 chi hbad
                ·
                  exact fin15Anchored_clause19971 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19972 chi hbad
                ·
                  exact fin15Anchored_clause19973 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19974 chi hbad
                ·
                  exact fin15Anchored_clause19975 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19976 chi hbad
                ·
                  exact fin15Anchored_clause19977 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19978 chi hbad
                ·
                  exact fin15Anchored_clause19979 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19980 chi hbad
                ·
                  exact fin15Anchored_clause19981 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19982 chi hbad
                ·
                  exact fin15Anchored_clause19983 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19984 chi hbad
                ·
                  exact fin15Anchored_clause19985 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19986 chi hbad
                ·
                  exact fin15Anchored_clause19987 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19988 chi hbad
                ·
                  exact fin15Anchored_clause19989 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19990 chi hbad
                ·
                  exact fin15Anchored_clause19991 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19992 chi hbad
                ·
                  exact fin15Anchored_clause19993 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19994 chi hbad
                ·
                  exact fin15Anchored_clause19995 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19996 chi hbad
                ·
                  exact fin15Anchored_clause19997 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19998 chi hbad
                ·
                  exact fin15Anchored_clause19999 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20000 chi hbad
                ·
                  exact fin15Anchored_clause20001 chi hbad
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
                exact fin15Anchored_clause20002 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20003 chi hbad
                ·
                  exact fin15Anchored_clause20004 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20005 chi hbad
                ·
                  exact fin15Anchored_clause20006 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20007 chi hbad
                ·
                  exact fin15Anchored_clause20008 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20009 chi hbad
                ·
                  exact fin15Anchored_clause20010 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20011 chi hbad
                ·
                  exact fin15Anchored_clause20012 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20013 chi hbad
                ·
                  exact fin15Anchored_clause20014 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20015 chi hbad
                ·
                  exact fin15Anchored_clause20016 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20017 chi hbad
                ·
                  exact fin15Anchored_clause20018 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20019 chi hbad
                ·
                  exact fin15Anchored_clause20020 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20021 chi hbad
                ·
                  exact fin15Anchored_clause20022 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20023 chi hbad
                ·
                  exact fin15Anchored_clause20024 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20025 chi hbad
                ·
                  exact fin15Anchored_clause20026 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20027 chi hbad
                ·
                  exact fin15Anchored_clause20028 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20029 chi hbad
                ·
                  exact fin15Anchored_clause20030 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20031 chi hbad
                ·
                  exact fin15Anchored_clause20032 chi hbad
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
                  exact fin15Anchored_clause20033 chi hbad
                ·
                  exact fin15Anchored_clause20034 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20035 chi hbad
                ·
                  exact fin15Anchored_clause20036 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20037 chi hbad
                ·
                  exact fin15Anchored_clause20038 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20039 chi hbad
                ·
                  exact fin15Anchored_clause20040 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20041 chi hbad
                ·
                  exact fin15Anchored_clause20042 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20043 chi hbad
                ·
                  exact fin15Anchored_clause20044 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20045 chi hbad
                ·
                  exact fin15Anchored_clause20046 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20047 chi hbad
                ·
                  exact fin15Anchored_clause20048 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20049 chi hbad
                ·
                  exact fin15Anchored_clause20050 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20051 chi hbad
                ·
                  exact fin15Anchored_clause20052 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20053 chi hbad
                ·
                  exact fin15Anchored_clause20054 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20055 chi hbad
                ·
                  exact fin15Anchored_clause20056 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20057 chi hbad
                ·
                  exact fin15Anchored_clause20058 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20059 chi hbad
                ·
                  exact fin15Anchored_clause20060 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20061 chi hbad
                ·
                  exact fin15Anchored_clause20062 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20063 chi hbad
                ·
                  exact fin15Anchored_clause20064 chi hbad
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
                exact fin15Anchored_clause20065 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20066 chi hbad
                ·
                  exact fin15Anchored_clause20067 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20068 chi hbad
                ·
                  exact fin15Anchored_clause20069 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20070 chi hbad
                ·
                  exact fin15Anchored_clause20071 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20072 chi hbad
                ·
                  exact fin15Anchored_clause20073 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20074 chi hbad
                ·
                  exact fin15Anchored_clause20075 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20076 chi hbad
                ·
                  exact fin15Anchored_clause20077 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20078 chi hbad
                ·
                  exact fin15Anchored_clause20079 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20080 chi hbad
                ·
                  exact fin15Anchored_clause20081 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20082 chi hbad
                ·
                  exact fin15Anchored_clause20083 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20084 chi hbad
                ·
                  exact fin15Anchored_clause20085 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20086 chi hbad
                ·
                  exact fin15Anchored_clause20087 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20088 chi hbad
                ·
                  exact fin15Anchored_clause20089 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20090 chi hbad
                ·
                  exact fin15Anchored_clause20091 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20092 chi hbad
                ·
                  exact fin15Anchored_clause20093 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20094 chi hbad
                ·
                  exact fin15Anchored_clause20095 chi hbad
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
                  exact fin15Anchored_clause20096 chi hbad
                ·
                  exact fin15Anchored_clause20097 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20098 chi hbad
                ·
                  exact fin15Anchored_clause20099 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20100 chi hbad
                ·
                  exact fin15Anchored_clause20101 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20102 chi hbad
                ·
                  exact fin15Anchored_clause20103 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20104 chi hbad
                ·
                  exact fin15Anchored_clause20105 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20106 chi hbad
                ·
                  exact fin15Anchored_clause20107 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20108 chi hbad
                ·
                  exact fin15Anchored_clause20109 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20110 chi hbad
                ·
                  exact fin15Anchored_clause20111 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20112 chi hbad
                ·
                  exact fin15Anchored_clause20113 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20114 chi hbad
                ·
                  exact fin15Anchored_clause20115 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20116 chi hbad
                ·
                  exact fin15Anchored_clause20117 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20118 chi hbad
                ·
                  exact fin15Anchored_clause20119 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20120 chi hbad
                ·
                  exact fin15Anchored_clause20121 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20122 chi hbad
                ·
                  exact fin15Anchored_clause20123 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20124 chi hbad
                ·
                  exact fin15Anchored_clause20125 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20126 chi hbad
                ·
                  exact fin15Anchored_clause20127 chi hbad
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
                  exact fin15Anchored_clause20128 chi hbad
                ·
                  exact fin15Anchored_clause20129 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20130 chi hbad
                ·
                  exact fin15Anchored_clause20131 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20132 chi hbad
                ·
                  exact fin15Anchored_clause20133 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20134 chi hbad
                ·
                  exact fin15Anchored_clause20135 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20136 chi hbad
                ·
                  exact fin15Anchored_clause20137 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20138 chi hbad
                ·
                  exact fin15Anchored_clause20139 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20140 chi hbad
                ·
                  exact fin15Anchored_clause20141 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20142 chi hbad
                ·
                  exact fin15Anchored_clause20143 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20144 chi hbad
                ·
                  exact fin15Anchored_clause20145 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20146 chi hbad
                ·
                  exact fin15Anchored_clause20147 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20148 chi hbad
                ·
                  exact fin15Anchored_clause20149 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20150 chi hbad
                ·
                  exact fin15Anchored_clause20151 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20152 chi hbad
                ·
                  exact fin15Anchored_clause20153 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20154 chi hbad
                ·
                  exact fin15Anchored_clause20155 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20156 chi hbad
                ·
                  exact fin15Anchored_clause20157 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20158 chi hbad
                ·
                  exact fin15Anchored_clause20159 chi hbad
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
                  exact fin15Anchored_clause20160 chi hbad
                ·
                  exact fin15Anchored_clause20161 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20162 chi hbad
                ·
                  exact fin15Anchored_clause20163 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20164 chi hbad
                ·
                  exact fin15Anchored_clause20165 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20166 chi hbad
                ·
                  exact fin15Anchored_clause20167 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20168 chi hbad
                ·
                  exact fin15Anchored_clause20169 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20170 chi hbad
                ·
                  exact fin15Anchored_clause20171 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20172 chi hbad
                ·
                  exact fin15Anchored_clause20173 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20174 chi hbad
                ·
                  exact fin15Anchored_clause20175 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20176 chi hbad
                ·
                  exact fin15Anchored_clause20177 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20178 chi hbad
                ·
                  exact fin15Anchored_clause20179 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20180 chi hbad
                ·
                  exact fin15Anchored_clause20181 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20182 chi hbad
                ·
                  exact fin15Anchored_clause20183 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20184 chi hbad
                ·
                  exact fin15Anchored_clause20185 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20186 chi hbad
                ·
                  exact fin15Anchored_clause20187 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20188 chi hbad
                ·
                  exact fin15Anchored_clause20189 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20190 chi hbad
                ·
                  exact fin15Anchored_clause20191 chi hbad

end ErdosSzekeres

end
