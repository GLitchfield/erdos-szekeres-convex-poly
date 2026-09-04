module

public import ErdosSzekeres.Fin15AnchoredClauseChunk157
public import ErdosSzekeres.Fin15AnchoredClauseChunk158
public import ErdosSzekeres.Fin15AnchoredClauseChunk159

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 080. -/

theorem fin15Anchored_rejectSemanticSegment080
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom2789 chi ∧
      ¬Fin15AnchoredAtom0802 chi) ∨
      ((¬Fin15AnchoredAtom2789 chi ∧
      Fin15AnchoredAtom0785 chi ∧
      Fin15AnchoredAtom0788 chi ∧
      Fin15AnchoredAtom0792 chi ∧
      Fin15AnchoredAtom0802 chi ∧
      Fin15AnchoredAtom1788 chi) ∨
      (Fin15AnchoredAtom2790 chi ∧
      ¬Fin15AnchoredAtom0785 chi))) ∨
      (((Fin15AnchoredAtom2790 chi ∧
      ¬Fin15AnchoredAtom0789 chi) ∨
      (Fin15AnchoredAtom2790 chi ∧
      ¬Fin15AnchoredAtom0793 chi)) ∨
      ((Fin15AnchoredAtom2790 chi ∧
      ¬Fin15AnchoredAtom0803 chi) ∨
      (¬Fin15AnchoredAtom2790 chi ∧
      Fin15AnchoredAtom0785 chi ∧
      Fin15AnchoredAtom0789 chi ∧
      Fin15AnchoredAtom0793 chi ∧
      Fin15AnchoredAtom0803 chi ∧
      Fin15AnchoredAtom1789 chi)))) ∨
      ((((Fin15AnchoredAtom2794 chi ∧
      ¬Fin15AnchoredAtom0787 chi) ∨
      (Fin15AnchoredAtom2794 chi ∧
      ¬Fin15AnchoredAtom0788 chi)) ∨
      ((Fin15AnchoredAtom2794 chi ∧
      ¬Fin15AnchoredAtom0797 chi) ∨
      (Fin15AnchoredAtom2794 chi ∧
      ¬Fin15AnchoredAtom0807 chi))) ∨
      (((Fin15AnchoredAtom2794 chi ∧
      ¬Fin15AnchoredAtom1793 chi) ∨
      (¬Fin15AnchoredAtom2794 chi ∧
      Fin15AnchoredAtom0787 chi ∧
      Fin15AnchoredAtom0788 chi ∧
      Fin15AnchoredAtom0797 chi ∧
      Fin15AnchoredAtom0807 chi ∧
      Fin15AnchoredAtom1793 chi)) ∨
      ((Fin15AnchoredAtom2795 chi ∧
      ¬Fin15AnchoredAtom0787 chi) ∨
      (Fin15AnchoredAtom2795 chi ∧
      ¬Fin15AnchoredAtom0789 chi))))) ∨
      (((((Fin15AnchoredAtom2795 chi ∧
      ¬Fin15AnchoredAtom0798 chi) ∨
      (Fin15AnchoredAtom2795 chi ∧
      ¬Fin15AnchoredAtom0808 chi)) ∨
      ((Fin15AnchoredAtom2795 chi ∧
      ¬Fin15AnchoredAtom1794 chi) ∨
      (¬Fin15AnchoredAtom2795 chi ∧
      Fin15AnchoredAtom0787 chi ∧
      Fin15AnchoredAtom0789 chi ∧
      Fin15AnchoredAtom0798 chi ∧
      Fin15AnchoredAtom0808 chi ∧
      Fin15AnchoredAtom1794 chi))) ∨
      (((Fin15AnchoredAtom2796 chi ∧
      ¬Fin15AnchoredAtom0788 chi) ∨
      (Fin15AnchoredAtom2796 chi ∧
      ¬Fin15AnchoredAtom0789 chi)) ∨
      ((Fin15AnchoredAtom2796 chi ∧
      ¬Fin15AnchoredAtom0799 chi) ∨
      (Fin15AnchoredAtom2796 chi ∧
      ¬Fin15AnchoredAtom0809 chi)))) ∨
      ((((Fin15AnchoredAtom2796 chi ∧
      ¬Fin15AnchoredAtom1795 chi) ∨
      (¬Fin15AnchoredAtom2796 chi ∧
      Fin15AnchoredAtom0788 chi ∧
      Fin15AnchoredAtom0789 chi ∧
      Fin15AnchoredAtom0799 chi ∧
      Fin15AnchoredAtom0809 chi ∧
      Fin15AnchoredAtom1795 chi)) ∨
      ((Fin15AnchoredAtom2800 chi ∧
      ¬Fin15AnchoredAtom0791 chi) ∨
      (Fin15AnchoredAtom2800 chi ∧
      ¬Fin15AnchoredAtom0792 chi))) ∨
      (((Fin15AnchoredAtom2800 chi ∧
      ¬Fin15AnchoredAtom0797 chi) ∨
      (Fin15AnchoredAtom2800 chi ∧
      ¬Fin15AnchoredAtom0813 chi)) ∨
      ((¬Fin15AnchoredAtom2800 chi ∧
      Fin15AnchoredAtom0791 chi ∧
      Fin15AnchoredAtom0792 chi ∧
      Fin15AnchoredAtom0797 chi ∧
      Fin15AnchoredAtom0813 chi ∧
      Fin15AnchoredAtom1799 chi) ∨
      (Fin15AnchoredAtom2801 chi ∧
      ¬Fin15AnchoredAtom0791 chi)))))) ∨
      ((((((Fin15AnchoredAtom2801 chi ∧
      ¬Fin15AnchoredAtom0793 chi) ∨
      (Fin15AnchoredAtom2801 chi ∧
      ¬Fin15AnchoredAtom0798 chi)) ∨
      ((Fin15AnchoredAtom2801 chi ∧
      ¬Fin15AnchoredAtom0814 chi) ∨
      (Fin15AnchoredAtom2801 chi ∧
      ¬Fin15AnchoredAtom1800 chi))) ∨
      (((¬Fin15AnchoredAtom2801 chi ∧
      Fin15AnchoredAtom0791 chi ∧
      Fin15AnchoredAtom0793 chi ∧
      Fin15AnchoredAtom0798 chi ∧
      Fin15AnchoredAtom0814 chi ∧
      Fin15AnchoredAtom1800 chi) ∨
      (Fin15AnchoredAtom2802 chi ∧
      ¬Fin15AnchoredAtom0792 chi)) ∨
      ((Fin15AnchoredAtom2802 chi ∧
      ¬Fin15AnchoredAtom0793 chi) ∨
      (Fin15AnchoredAtom2802 chi ∧
      ¬Fin15AnchoredAtom0799 chi)))) ∨
      ((((Fin15AnchoredAtom2802 chi ∧
      ¬Fin15AnchoredAtom0815 chi) ∨
      (Fin15AnchoredAtom2802 chi ∧
      ¬Fin15AnchoredAtom1801 chi)) ∨
      ((¬Fin15AnchoredAtom2802 chi ∧
      Fin15AnchoredAtom0792 chi ∧
      Fin15AnchoredAtom0793 chi ∧
      Fin15AnchoredAtom0799 chi ∧
      Fin15AnchoredAtom0815 chi ∧
      Fin15AnchoredAtom1801 chi) ∨
      (Fin15AnchoredAtom2806 chi ∧
      ¬Fin15AnchoredAtom0797 chi))) ∨
      (((Fin15AnchoredAtom2806 chi ∧
      ¬Fin15AnchoredAtom0798 chi) ∨
      (Fin15AnchoredAtom2806 chi ∧
      ¬Fin15AnchoredAtom0799 chi)) ∨
      ((Fin15AnchoredAtom2806 chi ∧
      ¬Fin15AnchoredAtom0819 chi) ∨
      (¬Fin15AnchoredAtom2806 chi ∧
      Fin15AnchoredAtom0797 chi ∧
      Fin15AnchoredAtom0798 chi ∧
      Fin15AnchoredAtom0799 chi ∧
      Fin15AnchoredAtom0819 chi ∧
      Fin15AnchoredAtom1805 chi))))) ∨
      (((((Fin15AnchoredAtom2807 chi ∧
      ¬Fin15AnchoredAtom0800 chi) ∨
      (Fin15AnchoredAtom2807 chi ∧
      ¬Fin15AnchoredAtom0801 chi)) ∨
      ((Fin15AnchoredAtom2807 chi ∧
      ¬Fin15AnchoredAtom0804 chi) ∨
      (Fin15AnchoredAtom2807 chi ∧
      ¬Fin15AnchoredAtom0810 chi))) ∨
      (((Fin15AnchoredAtom2807 chi ∧
      ¬Fin15AnchoredAtom1806 chi) ∨
      (¬Fin15AnchoredAtom2807 chi ∧
      Fin15AnchoredAtom0800 chi ∧
      Fin15AnchoredAtom0801 chi ∧
      Fin15AnchoredAtom0804 chi ∧
      Fin15AnchoredAtom0810 chi ∧
      Fin15AnchoredAtom1806 chi)) ∨
      ((Fin15AnchoredAtom2808 chi ∧
      ¬Fin15AnchoredAtom0800 chi) ∨
      (Fin15AnchoredAtom2808 chi ∧
      ¬Fin15AnchoredAtom0802 chi)))) ∨
      ((((Fin15AnchoredAtom2808 chi ∧
      ¬Fin15AnchoredAtom0805 chi) ∨
      (Fin15AnchoredAtom2808 chi ∧
      ¬Fin15AnchoredAtom0811 chi)) ∨
      ((Fin15AnchoredAtom2808 chi ∧
      ¬Fin15AnchoredAtom1807 chi) ∨
      (¬Fin15AnchoredAtom2808 chi ∧
      Fin15AnchoredAtom0800 chi ∧
      Fin15AnchoredAtom0802 chi ∧
      Fin15AnchoredAtom0805 chi ∧
      Fin15AnchoredAtom0811 chi ∧
      Fin15AnchoredAtom1807 chi))) ∨
      (((Fin15AnchoredAtom2809 chi ∧
      ¬Fin15AnchoredAtom0800 chi) ∨
      (Fin15AnchoredAtom2809 chi ∧
      ¬Fin15AnchoredAtom0803 chi)) ∨
      ((Fin15AnchoredAtom2809 chi ∧
      ¬Fin15AnchoredAtom0806 chi) ∨
      (Fin15AnchoredAtom2809 chi ∧
      ¬Fin15AnchoredAtom0812 chi))))))) ∨
      ((((((Fin15AnchoredAtom2809 chi ∧
      ¬Fin15AnchoredAtom1808 chi) ∨
      ((¬Fin15AnchoredAtom2809 chi ∧
      Fin15AnchoredAtom0800 chi ∧
      Fin15AnchoredAtom0803 chi ∧
      Fin15AnchoredAtom0806 chi ∧
      Fin15AnchoredAtom0812 chi ∧
      Fin15AnchoredAtom1808 chi) ∨
      (Fin15AnchoredAtom2810 chi ∧
      ¬Fin15AnchoredAtom0801 chi))) ∨
      (((Fin15AnchoredAtom2810 chi ∧
      ¬Fin15AnchoredAtom0802 chi) ∨
      (Fin15AnchoredAtom2810 chi ∧
      ¬Fin15AnchoredAtom0807 chi)) ∨
      ((Fin15AnchoredAtom2810 chi ∧
      ¬Fin15AnchoredAtom0813 chi) ∨
      (Fin15AnchoredAtom2810 chi ∧
      ¬Fin15AnchoredAtom1809 chi)))) ∨
      ((((¬Fin15AnchoredAtom2810 chi ∧
      Fin15AnchoredAtom0801 chi ∧
      Fin15AnchoredAtom0802 chi ∧
      Fin15AnchoredAtom0807 chi ∧
      Fin15AnchoredAtom0813 chi ∧
      Fin15AnchoredAtom1809 chi) ∨
      (Fin15AnchoredAtom2811 chi ∧
      ¬Fin15AnchoredAtom0801 chi)) ∨
      ((Fin15AnchoredAtom2811 chi ∧
      ¬Fin15AnchoredAtom0803 chi) ∨
      (Fin15AnchoredAtom2811 chi ∧
      ¬Fin15AnchoredAtom0808 chi))) ∨
      (((Fin15AnchoredAtom2811 chi ∧
      ¬Fin15AnchoredAtom0814 chi) ∨
      (Fin15AnchoredAtom2811 chi ∧
      ¬Fin15AnchoredAtom1810 chi)) ∨
      ((¬Fin15AnchoredAtom2811 chi ∧
      Fin15AnchoredAtom0801 chi ∧
      Fin15AnchoredAtom0803 chi ∧
      Fin15AnchoredAtom0808 chi ∧
      Fin15AnchoredAtom0814 chi ∧
      Fin15AnchoredAtom1810 chi) ∨
      (Fin15AnchoredAtom2812 chi ∧
      ¬Fin15AnchoredAtom0802 chi))))) ∨
      (((((Fin15AnchoredAtom2812 chi ∧
      ¬Fin15AnchoredAtom0803 chi) ∨
      (Fin15AnchoredAtom2812 chi ∧
      ¬Fin15AnchoredAtom0809 chi)) ∨
      ((Fin15AnchoredAtom2812 chi ∧
      ¬Fin15AnchoredAtom0815 chi) ∨
      (Fin15AnchoredAtom2812 chi ∧
      ¬Fin15AnchoredAtom1811 chi))) ∨
      (((¬Fin15AnchoredAtom2812 chi ∧
      Fin15AnchoredAtom0802 chi ∧
      Fin15AnchoredAtom0803 chi ∧
      Fin15AnchoredAtom0809 chi ∧
      Fin15AnchoredAtom0815 chi ∧
      Fin15AnchoredAtom1811 chi) ∨
      (Fin15AnchoredAtom2813 chi ∧
      ¬Fin15AnchoredAtom0807 chi)) ∨
      ((¬Fin15AnchoredAtom2813 chi ∧
      Fin15AnchoredAtom0804 chi ∧
      Fin15AnchoredAtom0805 chi ∧
      Fin15AnchoredAtom0807 chi ∧
      Fin15AnchoredAtom0816 chi ∧
      Fin15AnchoredAtom1812 chi) ∨
      (Fin15AnchoredAtom2814 chi ∧
      ¬Fin15AnchoredAtom0808 chi)))) ∨
      ((((Fin15AnchoredAtom2814 chi ∧
      ¬Fin15AnchoredAtom0817 chi) ∨
      (¬Fin15AnchoredAtom2814 chi ∧
      Fin15AnchoredAtom0804 chi ∧
      Fin15AnchoredAtom0806 chi ∧
      Fin15AnchoredAtom0808 chi ∧
      Fin15AnchoredAtom0817 chi ∧
      Fin15AnchoredAtom1813 chi)) ∨
      ((Fin15AnchoredAtom2815 chi ∧
      ¬Fin15AnchoredAtom0805 chi) ∨
      (Fin15AnchoredAtom2815 chi ∧
      ¬Fin15AnchoredAtom0806 chi))) ∨
      (((Fin15AnchoredAtom2815 chi ∧
      ¬Fin15AnchoredAtom0809 chi) ∨
      (Fin15AnchoredAtom2815 chi ∧
      ¬Fin15AnchoredAtom0818 chi)) ∨
      ((Fin15AnchoredAtom2815 chi ∧
      ¬Fin15AnchoredAtom1814 chi) ∨
      (¬Fin15AnchoredAtom2815 chi ∧
      Fin15AnchoredAtom0805 chi ∧
      Fin15AnchoredAtom0806 chi ∧
      Fin15AnchoredAtom0809 chi ∧
      Fin15AnchoredAtom0818 chi ∧
      Fin15AnchoredAtom1814 chi)))))) ∨
      ((((((Fin15AnchoredAtom2816 chi ∧
      ¬Fin15AnchoredAtom0807 chi) ∨
      (Fin15AnchoredAtom2816 chi ∧
      ¬Fin15AnchoredAtom0808 chi)) ∨
      ((Fin15AnchoredAtom2816 chi ∧
      ¬Fin15AnchoredAtom0809 chi) ∨
      (Fin15AnchoredAtom2816 chi ∧
      ¬Fin15AnchoredAtom0819 chi))) ∨
      (((Fin15AnchoredAtom2816 chi ∧
      ¬Fin15AnchoredAtom1815 chi) ∨
      (¬Fin15AnchoredAtom2816 chi ∧
      Fin15AnchoredAtom0807 chi ∧
      Fin15AnchoredAtom0808 chi ∧
      Fin15AnchoredAtom0809 chi ∧
      Fin15AnchoredAtom0819 chi ∧
      Fin15AnchoredAtom1815 chi)) ∨
      ((Fin15AnchoredAtom2817 chi ∧
      ¬Fin15AnchoredAtom0810 chi) ∨
      (Fin15AnchoredAtom2817 chi ∧
      ¬Fin15AnchoredAtom0811 chi)))) ∨
      ((((Fin15AnchoredAtom2817 chi ∧
      ¬Fin15AnchoredAtom0813 chi) ∨
      (Fin15AnchoredAtom2817 chi ∧
      ¬Fin15AnchoredAtom0816 chi)) ∨
      ((Fin15AnchoredAtom2817 chi ∧
      ¬Fin15AnchoredAtom1816 chi) ∨
      (¬Fin15AnchoredAtom2817 chi ∧
      Fin15AnchoredAtom0810 chi ∧
      Fin15AnchoredAtom0811 chi ∧
      Fin15AnchoredAtom0813 chi ∧
      Fin15AnchoredAtom0816 chi ∧
      Fin15AnchoredAtom1816 chi))) ∨
      (((Fin15AnchoredAtom2818 chi ∧
      ¬Fin15AnchoredAtom0810 chi) ∨
      (Fin15AnchoredAtom2818 chi ∧
      ¬Fin15AnchoredAtom0812 chi)) ∨
      ((Fin15AnchoredAtom2818 chi ∧
      ¬Fin15AnchoredAtom0814 chi) ∨
      (Fin15AnchoredAtom2818 chi ∧
      ¬Fin15AnchoredAtom0817 chi))))) ∨
      (((((Fin15AnchoredAtom2818 chi ∧
      ¬Fin15AnchoredAtom1817 chi) ∨
      (¬Fin15AnchoredAtom2818 chi ∧
      Fin15AnchoredAtom0810 chi ∧
      Fin15AnchoredAtom0812 chi ∧
      Fin15AnchoredAtom0814 chi ∧
      Fin15AnchoredAtom0817 chi ∧
      Fin15AnchoredAtom1817 chi)) ∨
      ((Fin15AnchoredAtom2819 chi ∧
      ¬Fin15AnchoredAtom0811 chi) ∨
      (Fin15AnchoredAtom2819 chi ∧
      ¬Fin15AnchoredAtom0812 chi))) ∨
      (((Fin15AnchoredAtom2819 chi ∧
      ¬Fin15AnchoredAtom0815 chi) ∨
      (Fin15AnchoredAtom2819 chi ∧
      ¬Fin15AnchoredAtom1818 chi)) ∨
      ((¬Fin15AnchoredAtom2819 chi ∧
      Fin15AnchoredAtom0811 chi ∧
      Fin15AnchoredAtom0812 chi ∧
      Fin15AnchoredAtom0815 chi ∧
      Fin15AnchoredAtom0818 chi ∧
      Fin15AnchoredAtom1818 chi) ∨
      (Fin15AnchoredAtom2820 chi ∧
      ¬Fin15AnchoredAtom0813 chi)))) ∨
      ((((Fin15AnchoredAtom2820 chi ∧
      ¬Fin15AnchoredAtom0814 chi) ∨
      (Fin15AnchoredAtom2820 chi ∧
      ¬Fin15AnchoredAtom0815 chi)) ∨
      ((Fin15AnchoredAtom2820 chi ∧
      ¬Fin15AnchoredAtom0819 chi) ∨
      (Fin15AnchoredAtom2820 chi ∧
      ¬Fin15AnchoredAtom1819 chi))) ∨
      (((¬Fin15AnchoredAtom2820 chi ∧
      Fin15AnchoredAtom0813 chi ∧
      Fin15AnchoredAtom0814 chi ∧
      Fin15AnchoredAtom0815 chi ∧
      Fin15AnchoredAtom0819 chi ∧
      Fin15AnchoredAtom1819 chi) ∨
      (Fin15AnchoredAtom2821 chi ∧
      ¬Fin15AnchoredAtom0816 chi)) ∨
      ((Fin15AnchoredAtom2821 chi ∧
      ¬Fin15AnchoredAtom0819 chi) ∨
      (Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom0820 chi)))))))) ∨
      (((((((Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom0821 chi) ∨
      ((Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom0831 chi) ∨
      (Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom0886 chi))) ∨
      (((Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom1106 chi) ∨
      (¬Fin15AnchoredAtom2822 chi ∧
      Fin15AnchoredAtom0820 chi ∧
      Fin15AnchoredAtom0821 chi ∧
      Fin15AnchoredAtom0831 chi ∧
      Fin15AnchoredAtom0886 chi ∧
      Fin15AnchoredAtom1106 chi)) ∨
      ((Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom0820 chi) ∨
      (Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom0822 chi)))) ∨
      ((((Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom0832 chi) ∨
      (Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom0887 chi)) ∨
      ((Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom1107 chi) ∨
      (¬Fin15AnchoredAtom2823 chi ∧
      Fin15AnchoredAtom0820 chi ∧
      Fin15AnchoredAtom0822 chi ∧
      Fin15AnchoredAtom0832 chi ∧
      Fin15AnchoredAtom0887 chi ∧
      Fin15AnchoredAtom1107 chi))) ∨
      (((Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom0820 chi) ∨
      (Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom0823 chi)) ∨
      ((Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom0833 chi) ∨
      (Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom0888 chi))))) ∨
      (((((Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom1108 chi) ∨
      (¬Fin15AnchoredAtom2824 chi ∧
      Fin15AnchoredAtom0820 chi ∧
      Fin15AnchoredAtom0823 chi ∧
      Fin15AnchoredAtom0833 chi ∧
      Fin15AnchoredAtom0888 chi ∧
      Fin15AnchoredAtom1108 chi)) ∨
      ((Fin15AnchoredAtom2825 chi ∧
      ¬Fin15AnchoredAtom0889 chi) ∨
      (Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom0820 chi))) ∨
      (((Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom0825 chi) ∨
      (Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom0835 chi)) ∨
      ((Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom0890 chi) ∨
      (Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom1110 chi)))) ∨
      ((((¬Fin15AnchoredAtom2826 chi ∧
      Fin15AnchoredAtom0820 chi ∧
      Fin15AnchoredAtom0825 chi ∧
      Fin15AnchoredAtom0835 chi ∧
      Fin15AnchoredAtom0890 chi ∧
      Fin15AnchoredAtom1110 chi) ∨
      (Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom0820 chi)) ∨
      ((Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom0826 chi) ∨
      (Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom0836 chi))) ∨
      (((Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom0891 chi) ∨
      (Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom1111 chi)) ∨
      ((¬Fin15AnchoredAtom2827 chi ∧
      Fin15AnchoredAtom0820 chi ∧
      Fin15AnchoredAtom0826 chi ∧
      Fin15AnchoredAtom0836 chi ∧
      Fin15AnchoredAtom0891 chi ∧
      Fin15AnchoredAtom1111 chi) ∨
      (¬Fin15AnchoredAtom2828 chi ∧
      Fin15AnchoredAtom0820 chi ∧
      Fin15AnchoredAtom0827 chi ∧
      Fin15AnchoredAtom0837 chi ∧
      Fin15AnchoredAtom0892 chi ∧
      Fin15AnchoredAtom1112 chi)))))) ∨
      ((((((Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom0820 chi) ∨
      (Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom0828 chi)) ∨
      ((Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom0838 chi) ∨
      (Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom0893 chi))) ∨
      (((Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom1113 chi) ∨
      (¬Fin15AnchoredAtom2829 chi ∧
      Fin15AnchoredAtom0820 chi ∧
      Fin15AnchoredAtom0828 chi ∧
      Fin15AnchoredAtom0838 chi ∧
      Fin15AnchoredAtom0893 chi ∧
      Fin15AnchoredAtom1113 chi)) ∨
      ((Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom0820 chi) ∨
      (Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom0829 chi)))) ∨
      ((((Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom0839 chi) ∨
      (Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom0894 chi)) ∨
      ((Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom1114 chi) ∨
      (¬Fin15AnchoredAtom2830 chi ∧
      Fin15AnchoredAtom0820 chi ∧
      Fin15AnchoredAtom0829 chi ∧
      Fin15AnchoredAtom0839 chi ∧
      Fin15AnchoredAtom0894 chi ∧
      Fin15AnchoredAtom1114 chi))) ∨
      (((Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom0820 chi) ∨
      (Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom0830 chi)) ∨
      ((Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom0840 chi) ∨
      (Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom0895 chi))))) ∨
      (((((Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom1115 chi) ∨
      (¬Fin15AnchoredAtom2831 chi ∧
      Fin15AnchoredAtom0820 chi ∧
      Fin15AnchoredAtom0830 chi ∧
      Fin15AnchoredAtom0840 chi ∧
      Fin15AnchoredAtom0895 chi ∧
      Fin15AnchoredAtom1115 chi)) ∨
      ((Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom0821 chi) ∨
      (Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom0822 chi))) ∨
      (((Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom0841 chi) ∨
      (Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom0896 chi)) ∨
      ((Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom1116 chi) ∨
      (¬Fin15AnchoredAtom2832 chi ∧
      Fin15AnchoredAtom0821 chi ∧
      Fin15AnchoredAtom0822 chi ∧
      Fin15AnchoredAtom0841 chi ∧
      Fin15AnchoredAtom0896 chi ∧
      Fin15AnchoredAtom1116 chi)))) ∨
      ((((Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom0821 chi) ∨
      (Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom0823 chi)) ∨
      ((Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom0842 chi) ∨
      (Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom0897 chi))) ∨
      (((Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom1117 chi) ∨
      (¬Fin15AnchoredAtom2833 chi ∧
      Fin15AnchoredAtom0821 chi ∧
      Fin15AnchoredAtom0823 chi ∧
      Fin15AnchoredAtom0842 chi ∧
      Fin15AnchoredAtom0897 chi ∧
      Fin15AnchoredAtom1117 chi)) ∨
      ((Fin15AnchoredAtom2834 chi ∧
      ¬Fin15AnchoredAtom1118 chi) ∨
      (¬Fin15AnchoredAtom2834 chi ∧
      Fin15AnchoredAtom0821 chi ∧
      Fin15AnchoredAtom0824 chi ∧
      Fin15AnchoredAtom0843 chi ∧
      Fin15AnchoredAtom0898 chi ∧
      Fin15AnchoredAtom1118 chi))))))) ∨
      ((((((Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom0821 chi) ∨
      ((Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom0825 chi) ∨
      (Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom0844 chi))) ∨
      (((Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom0899 chi) ∨
      (Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom1119 chi)) ∨
      ((¬Fin15AnchoredAtom2835 chi ∧
      Fin15AnchoredAtom0821 chi ∧
      Fin15AnchoredAtom0825 chi ∧
      Fin15AnchoredAtom0844 chi ∧
      Fin15AnchoredAtom0899 chi ∧
      Fin15AnchoredAtom1119 chi) ∨
      (Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom0821 chi)))) ∨
      ((((Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom0826 chi) ∨
      (Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom0845 chi)) ∨
      ((Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom0900 chi) ∨
      (Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom1120 chi))) ∨
      (((¬Fin15AnchoredAtom2836 chi ∧
      Fin15AnchoredAtom0821 chi ∧
      Fin15AnchoredAtom0826 chi ∧
      Fin15AnchoredAtom0845 chi ∧
      Fin15AnchoredAtom0900 chi ∧
      Fin15AnchoredAtom1120 chi) ∨
      (Fin15AnchoredAtom2837 chi ∧
      ¬Fin15AnchoredAtom0821 chi)) ∨
      ((Fin15AnchoredAtom2837 chi ∧
      ¬Fin15AnchoredAtom1121 chi) ∨
      (¬Fin15AnchoredAtom2837 chi ∧
      Fin15AnchoredAtom0821 chi ∧
      Fin15AnchoredAtom0827 chi ∧
      Fin15AnchoredAtom0846 chi ∧
      Fin15AnchoredAtom0901 chi ∧
      Fin15AnchoredAtom1121 chi))))) ∨
      (((((Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom0821 chi) ∨
      (Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom0828 chi)) ∨
      ((Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom0847 chi) ∨
      (Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom0902 chi))) ∨
      (((Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom1122 chi) ∨
      (¬Fin15AnchoredAtom2838 chi ∧
      Fin15AnchoredAtom0821 chi ∧
      Fin15AnchoredAtom0828 chi ∧
      Fin15AnchoredAtom0847 chi ∧
      Fin15AnchoredAtom0902 chi ∧
      Fin15AnchoredAtom1122 chi)) ∨
      ((Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom0821 chi) ∨
      (Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom0829 chi)))) ∨
      ((((Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom0848 chi) ∨
      (Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom0903 chi)) ∨
      ((Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom1123 chi) ∨
      (¬Fin15AnchoredAtom2839 chi ∧
      Fin15AnchoredAtom0821 chi ∧
      Fin15AnchoredAtom0829 chi ∧
      Fin15AnchoredAtom0848 chi ∧
      Fin15AnchoredAtom0903 chi ∧
      Fin15AnchoredAtom1123 chi))) ∨
      (((Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom0821 chi) ∨
      (Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom0830 chi)) ∨
      ((Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom0849 chi) ∨
      (Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom0904 chi)))))) ∨
      ((((((Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom1124 chi) ∨
      (¬Fin15AnchoredAtom2840 chi ∧
      Fin15AnchoredAtom0821 chi ∧
      Fin15AnchoredAtom0830 chi ∧
      Fin15AnchoredAtom0849 chi ∧
      Fin15AnchoredAtom0904 chi ∧
      Fin15AnchoredAtom1124 chi)) ∨
      ((Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom0822 chi) ∨
      (Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom0823 chi))) ∨
      (((Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom0850 chi) ∨
      (Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom0905 chi)) ∨
      ((Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom1125 chi) ∨
      (¬Fin15AnchoredAtom2841 chi ∧
      Fin15AnchoredAtom0822 chi ∧
      Fin15AnchoredAtom0823 chi ∧
      Fin15AnchoredAtom0850 chi ∧
      Fin15AnchoredAtom0905 chi ∧
      Fin15AnchoredAtom1125 chi)))) ∨
      ((((Fin15AnchoredAtom2842 chi ∧
      ¬Fin15AnchoredAtom0822 chi) ∨
      (Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom0822 chi)) ∨
      ((Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom0825 chi) ∨
      (Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom0852 chi))) ∨
      (((Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom0907 chi) ∨
      (Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom1127 chi)) ∨
      ((¬Fin15AnchoredAtom2843 chi ∧
      Fin15AnchoredAtom0822 chi ∧
      Fin15AnchoredAtom0825 chi ∧
      Fin15AnchoredAtom0852 chi ∧
      Fin15AnchoredAtom0907 chi ∧
      Fin15AnchoredAtom1127 chi) ∨
      (Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom0822 chi))))) ∨
      (((((Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom0826 chi) ∨
      (Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom0853 chi)) ∨
      ((Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom0908 chi) ∨
      (Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom1128 chi))) ∨
      (((¬Fin15AnchoredAtom2844 chi ∧
      Fin15AnchoredAtom0822 chi ∧
      Fin15AnchoredAtom0826 chi ∧
      Fin15AnchoredAtom0853 chi ∧
      Fin15AnchoredAtom0908 chi ∧
      Fin15AnchoredAtom1128 chi) ∨
      (Fin15AnchoredAtom2845 chi ∧
      ¬Fin15AnchoredAtom0822 chi)) ∨
      ((Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom0822 chi) ∨
      (Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom0828 chi)))) ∨
      ((((Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom0855 chi) ∨
      (Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom0910 chi)) ∨
      ((Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom1130 chi) ∨
      (¬Fin15AnchoredAtom2846 chi ∧
      Fin15AnchoredAtom0822 chi ∧
      Fin15AnchoredAtom0828 chi ∧
      Fin15AnchoredAtom0855 chi ∧
      Fin15AnchoredAtom0910 chi ∧
      Fin15AnchoredAtom1130 chi))) ∨
      (((Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom0822 chi) ∨
      (Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom0829 chi)) ∨
      ((Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom0856 chi) ∨
      (Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom0911 chi)))))))))) := by
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
                exact fin15Anchored_clause20192 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20193 chi hbad
                ·
                  exact fin15Anchored_clause20194 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20195 chi hbad
                ·
                  exact fin15Anchored_clause20196 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20197 chi hbad
                ·
                  exact fin15Anchored_clause20198 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20199 chi hbad
                ·
                  exact fin15Anchored_clause20200 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20201 chi hbad
                ·
                  exact fin15Anchored_clause20202 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20203 chi hbad
                ·
                  exact fin15Anchored_clause20204 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20205 chi hbad
                ·
                  exact fin15Anchored_clause20206 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20207 chi hbad
                ·
                  exact fin15Anchored_clause20208 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20209 chi hbad
                ·
                  exact fin15Anchored_clause20210 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20211 chi hbad
                ·
                  exact fin15Anchored_clause20212 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20213 chi hbad
                ·
                  exact fin15Anchored_clause20214 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20215 chi hbad
                ·
                  exact fin15Anchored_clause20216 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20217 chi hbad
                ·
                  exact fin15Anchored_clause20218 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20219 chi hbad
                ·
                  exact fin15Anchored_clause20220 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20221 chi hbad
                ·
                  exact fin15Anchored_clause20222 chi hbad
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
                  exact fin15Anchored_clause20223 chi hbad
                ·
                  exact fin15Anchored_clause20224 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20225 chi hbad
                ·
                  exact fin15Anchored_clause20226 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20227 chi hbad
                ·
                  exact fin15Anchored_clause20228 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20229 chi hbad
                ·
                  exact fin15Anchored_clause20230 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20231 chi hbad
                ·
                  exact fin15Anchored_clause20232 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20233 chi hbad
                ·
                  exact fin15Anchored_clause20234 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20235 chi hbad
                ·
                  exact fin15Anchored_clause20236 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20237 chi hbad
                ·
                  exact fin15Anchored_clause20238 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20239 chi hbad
                ·
                  exact fin15Anchored_clause20240 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20241 chi hbad
                ·
                  exact fin15Anchored_clause20242 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20243 chi hbad
                ·
                  exact fin15Anchored_clause20244 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20245 chi hbad
                ·
                  exact fin15Anchored_clause20246 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20247 chi hbad
                ·
                  exact fin15Anchored_clause20248 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20249 chi hbad
                ·
                  exact fin15Anchored_clause20250 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20251 chi hbad
                ·
                  exact fin15Anchored_clause20252 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20253 chi hbad
                ·
                  exact fin15Anchored_clause20254 chi hbad
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
                exact fin15Anchored_clause20255 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20256 chi hbad
                ·
                  exact fin15Anchored_clause20257 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20258 chi hbad
                ·
                  exact fin15Anchored_clause20259 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20260 chi hbad
                ·
                  exact fin15Anchored_clause20261 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20262 chi hbad
                ·
                  exact fin15Anchored_clause20263 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20264 chi hbad
                ·
                  exact fin15Anchored_clause20265 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20266 chi hbad
                ·
                  exact fin15Anchored_clause20267 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20268 chi hbad
                ·
                  exact fin15Anchored_clause20269 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20270 chi hbad
                ·
                  exact fin15Anchored_clause20271 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20272 chi hbad
                ·
                  exact fin15Anchored_clause20273 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20274 chi hbad
                ·
                  exact fin15Anchored_clause20275 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20276 chi hbad
                ·
                  exact fin15Anchored_clause20277 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20278 chi hbad
                ·
                  exact fin15Anchored_clause20279 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20280 chi hbad
                ·
                  exact fin15Anchored_clause20281 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20282 chi hbad
                ·
                  exact fin15Anchored_clause20283 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20284 chi hbad
                ·
                  exact fin15Anchored_clause20285 chi hbad
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
                  exact fin15Anchored_clause20286 chi hbad
                ·
                  exact fin15Anchored_clause20287 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20288 chi hbad
                ·
                  exact fin15Anchored_clause20289 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20290 chi hbad
                ·
                  exact fin15Anchored_clause20291 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20292 chi hbad
                ·
                  exact fin15Anchored_clause20293 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20294 chi hbad
                ·
                  exact fin15Anchored_clause20295 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20296 chi hbad
                ·
                  exact fin15Anchored_clause20297 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20298 chi hbad
                ·
                  exact fin15Anchored_clause20299 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20300 chi hbad
                ·
                  exact fin15Anchored_clause20301 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20302 chi hbad
                ·
                  exact fin15Anchored_clause20303 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20304 chi hbad
                ·
                  exact fin15Anchored_clause20305 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20306 chi hbad
                ·
                  exact fin15Anchored_clause20307 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20308 chi hbad
                ·
                  exact fin15Anchored_clause20309 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20310 chi hbad
                ·
                  exact fin15Anchored_clause20311 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20312 chi hbad
                ·
                  exact fin15Anchored_clause20313 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20314 chi hbad
                ·
                  exact fin15Anchored_clause20315 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20316 chi hbad
                ·
                  exact fin15Anchored_clause20317 chi hbad
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
                exact fin15Anchored_clause20318 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20319 chi hbad
                ·
                  exact fin15Anchored_clause20320 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20321 chi hbad
                ·
                  exact fin15Anchored_clause20322 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20323 chi hbad
                ·
                  exact fin15Anchored_clause20324 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20325 chi hbad
                ·
                  exact fin15Anchored_clause20326 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20327 chi hbad
                ·
                  exact fin15Anchored_clause20328 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20329 chi hbad
                ·
                  exact fin15Anchored_clause20330 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20331 chi hbad
                ·
                  exact fin15Anchored_clause20332 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20333 chi hbad
                ·
                  exact fin15Anchored_clause20334 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20335 chi hbad
                ·
                  exact fin15Anchored_clause20336 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20337 chi hbad
                ·
                  exact fin15Anchored_clause20338 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20339 chi hbad
                ·
                  exact fin15Anchored_clause20340 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20341 chi hbad
                ·
                  exact fin15Anchored_clause20342 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20343 chi hbad
                ·
                  exact fin15Anchored_clause20344 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20345 chi hbad
                ·
                  exact fin15Anchored_clause20346 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20347 chi hbad
                ·
                  exact fin15Anchored_clause20348 chi hbad
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
                  exact fin15Anchored_clause20349 chi hbad
                ·
                  exact fin15Anchored_clause20350 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20351 chi hbad
                ·
                  exact fin15Anchored_clause20352 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20353 chi hbad
                ·
                  exact fin15Anchored_clause20354 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20355 chi hbad
                ·
                  exact fin15Anchored_clause20356 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20357 chi hbad
                ·
                  exact fin15Anchored_clause20358 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20359 chi hbad
                ·
                  exact fin15Anchored_clause20360 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20361 chi hbad
                ·
                  exact fin15Anchored_clause20362 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20363 chi hbad
                ·
                  exact fin15Anchored_clause20364 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20365 chi hbad
                ·
                  exact fin15Anchored_clause20366 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20367 chi hbad
                ·
                  exact fin15Anchored_clause20368 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20369 chi hbad
                ·
                  exact fin15Anchored_clause20370 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20371 chi hbad
                ·
                  exact fin15Anchored_clause20372 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20373 chi hbad
                ·
                  exact fin15Anchored_clause20374 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20375 chi hbad
                ·
                  exact fin15Anchored_clause20376 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20377 chi hbad
                ·
                  exact fin15Anchored_clause20378 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20379 chi hbad
                ·
                  exact fin15Anchored_clause20380 chi hbad
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
                exact fin15Anchored_clause20381 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20382 chi hbad
                ·
                  exact fin15Anchored_clause20383 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20384 chi hbad
                ·
                  exact fin15Anchored_clause20385 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20386 chi hbad
                ·
                  exact fin15Anchored_clause20387 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20388 chi hbad
                ·
                  exact fin15Anchored_clause20389 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20390 chi hbad
                ·
                  exact fin15Anchored_clause20391 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20392 chi hbad
                ·
                  exact fin15Anchored_clause20393 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20394 chi hbad
                ·
                  exact fin15Anchored_clause20395 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20396 chi hbad
                ·
                  exact fin15Anchored_clause20397 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20398 chi hbad
                ·
                  exact fin15Anchored_clause20399 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20400 chi hbad
                ·
                  exact fin15Anchored_clause20401 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20402 chi hbad
                ·
                  exact fin15Anchored_clause20403 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20404 chi hbad
                ·
                  exact fin15Anchored_clause20405 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20406 chi hbad
                ·
                  exact fin15Anchored_clause20407 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20408 chi hbad
                ·
                  exact fin15Anchored_clause20409 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20410 chi hbad
                ·
                  exact fin15Anchored_clause20411 chi hbad
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
                  exact fin15Anchored_clause20412 chi hbad
                ·
                  exact fin15Anchored_clause20413 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20414 chi hbad
                ·
                  exact fin15Anchored_clause20415 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20416 chi hbad
                ·
                  exact fin15Anchored_clause20417 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20418 chi hbad
                ·
                  exact fin15Anchored_clause20419 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20420 chi hbad
                ·
                  exact fin15Anchored_clause20421 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20422 chi hbad
                ·
                  exact fin15Anchored_clause20423 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20424 chi hbad
                ·
                  exact fin15Anchored_clause20425 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20426 chi hbad
                ·
                  exact fin15Anchored_clause20427 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20428 chi hbad
                ·
                  exact fin15Anchored_clause20429 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20430 chi hbad
                ·
                  exact fin15Anchored_clause20431 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20432 chi hbad
                ·
                  exact fin15Anchored_clause20433 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20434 chi hbad
                ·
                  exact fin15Anchored_clause20435 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20436 chi hbad
                ·
                  exact fin15Anchored_clause20437 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20438 chi hbad
                ·
                  exact fin15Anchored_clause20439 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20440 chi hbad
                ·
                  exact fin15Anchored_clause20441 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20442 chi hbad
                ·
                  exact fin15Anchored_clause20443 chi hbad

end ErdosSzekeres

end
