module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk082

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 107. -/

theorem predecessorHalfFin13_rejectSemanticSegment107
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom2096 chi ∧
      ¬PredecessorHalfFin13Atom0820 chi) ∨
      ((PredecessorHalfFin13Atom2096 chi ∧
      ¬PredecessorHalfFin13Atom0824 chi) ∨
      (PredecessorHalfFin13Atom2096 chi ∧
      ¬PredecessorHalfFin13Atom0829 chi))) ∨
      ((PredecessorHalfFin13Atom2096 chi ∧
      ¬PredecessorHalfFin13Atom0844 chi) ∨
      ((PredecessorHalfFin13Atom2096 chi ∧
      ¬PredecessorHalfFin13Atom0935 chi) ∨
      (PredecessorHalfFin13Atom2097 chi ∧
      ¬PredecessorHalfFin13Atom0820 chi)))) ∨
      (((PredecessorHalfFin13Atom2097 chi ∧
      ¬PredecessorHalfFin13Atom0825 chi) ∨
      ((PredecessorHalfFin13Atom2097 chi ∧
      ¬PredecessorHalfFin13Atom0830 chi) ∨
      (PredecessorHalfFin13Atom2097 chi ∧
      ¬PredecessorHalfFin13Atom0845 chi))) ∨
      ((PredecessorHalfFin13Atom2097 chi ∧
      ¬PredecessorHalfFin13Atom0936 chi) ∨
      ((¬PredecessorHalfFin13Atom2097 chi ∧
      PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0825 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0845 chi ∧
      PredecessorHalfFin13Atom0936 chi) ∨
      (PredecessorHalfFin13Atom2098 chi ∧
      ¬PredecessorHalfFin13Atom0821 chi))))) ∨
      ((((PredecessorHalfFin13Atom2098 chi ∧
      ¬PredecessorHalfFin13Atom0822 chi) ∨
      ((PredecessorHalfFin13Atom2098 chi ∧
      ¬PredecessorHalfFin13Atom0831 chi) ∨
      (PredecessorHalfFin13Atom2098 chi ∧
      ¬PredecessorHalfFin13Atom0846 chi))) ∨
      ((PredecessorHalfFin13Atom2098 chi ∧
      ¬PredecessorHalfFin13Atom0937 chi) ∨
      ((¬PredecessorHalfFin13Atom2098 chi ∧
      PredecessorHalfFin13Atom0821 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0846 chi ∧
      PredecessorHalfFin13Atom0937 chi) ∨
      (PredecessorHalfFin13Atom2099 chi ∧
      ¬PredecessorHalfFin13Atom0821 chi)))) ∨
      (((PredecessorHalfFin13Atom2099 chi ∧
      ¬PredecessorHalfFin13Atom0823 chi) ∨
      ((PredecessorHalfFin13Atom2099 chi ∧
      ¬PredecessorHalfFin13Atom0832 chi) ∨
      (PredecessorHalfFin13Atom2099 chi ∧
      ¬PredecessorHalfFin13Atom0847 chi))) ∨
      ((PredecessorHalfFin13Atom2099 chi ∧
      ¬PredecessorHalfFin13Atom0938 chi) ∨
      ((¬PredecessorHalfFin13Atom2099 chi ∧
      PredecessorHalfFin13Atom0821 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0847 chi ∧
      PredecessorHalfFin13Atom0938 chi) ∨
      (PredecessorHalfFin13Atom2100 chi ∧
      ¬PredecessorHalfFin13Atom0821 chi)))))) ∨
      (((((PredecessorHalfFin13Atom2100 chi ∧
      ¬PredecessorHalfFin13Atom0824 chi) ∨
      ((PredecessorHalfFin13Atom2100 chi ∧
      ¬PredecessorHalfFin13Atom0833 chi) ∨
      (PredecessorHalfFin13Atom2100 chi ∧
      ¬PredecessorHalfFin13Atom0848 chi))) ∨
      ((PredecessorHalfFin13Atom2100 chi ∧
      ¬PredecessorHalfFin13Atom0939 chi) ∨
      ((PredecessorHalfFin13Atom2101 chi ∧
      ¬PredecessorHalfFin13Atom0821 chi) ∨
      (PredecessorHalfFin13Atom2101 chi ∧
      ¬PredecessorHalfFin13Atom0825 chi)))) ∨
      (((PredecessorHalfFin13Atom2101 chi ∧
      ¬PredecessorHalfFin13Atom0834 chi) ∨
      ((PredecessorHalfFin13Atom2101 chi ∧
      ¬PredecessorHalfFin13Atom0849 chi) ∨
      (PredecessorHalfFin13Atom2101 chi ∧
      ¬PredecessorHalfFin13Atom0940 chi))) ∨
      ((¬PredecessorHalfFin13Atom2101 chi ∧
      PredecessorHalfFin13Atom0821 chi ∧
      PredecessorHalfFin13Atom0825 chi ∧
      PredecessorHalfFin13Atom0834 chi ∧
      PredecessorHalfFin13Atom0849 chi ∧
      PredecessorHalfFin13Atom0940 chi) ∨
      ((PredecessorHalfFin13Atom2102 chi ∧
      ¬PredecessorHalfFin13Atom0822 chi) ∨
      (PredecessorHalfFin13Atom2102 chi ∧
      ¬PredecessorHalfFin13Atom0823 chi))))) ∨
      ((((PredecessorHalfFin13Atom2102 chi ∧
      ¬PredecessorHalfFin13Atom0835 chi) ∨
      ((PredecessorHalfFin13Atom2102 chi ∧
      ¬PredecessorHalfFin13Atom0850 chi) ∨
      (PredecessorHalfFin13Atom2102 chi ∧
      ¬PredecessorHalfFin13Atom0941 chi))) ∨
      ((¬PredecessorHalfFin13Atom2102 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0850 chi ∧
      PredecessorHalfFin13Atom0941 chi) ∨
      ((PredecessorHalfFin13Atom2103 chi ∧
      ¬PredecessorHalfFin13Atom0822 chi) ∨
      (PredecessorHalfFin13Atom2103 chi ∧
      ¬PredecessorHalfFin13Atom0824 chi)))) ∨
      (((PredecessorHalfFin13Atom2103 chi ∧
      ¬PredecessorHalfFin13Atom0851 chi) ∨
      ((PredecessorHalfFin13Atom2103 chi ∧
      ¬PredecessorHalfFin13Atom0942 chi) ∨
      (¬PredecessorHalfFin13Atom2103 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0824 chi ∧
      PredecessorHalfFin13Atom0836 chi ∧
      PredecessorHalfFin13Atom0851 chi ∧
      PredecessorHalfFin13Atom0942 chi))) ∨
      (((PredecessorHalfFin13Atom2104 chi ∧
      ¬PredecessorHalfFin13Atom0822 chi) ∨
      (PredecessorHalfFin13Atom2104 chi ∧
      ¬PredecessorHalfFin13Atom0825 chi)) ∨
      ((PredecessorHalfFin13Atom2104 chi ∧
      ¬PredecessorHalfFin13Atom0837 chi) ∨
      (PredecessorHalfFin13Atom2104 chi ∧
      ¬PredecessorHalfFin13Atom0852 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom2104 chi ∧
      ¬PredecessorHalfFin13Atom0943 chi) ∨
      ((¬PredecessorHalfFin13Atom2104 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0825 chi ∧
      PredecessorHalfFin13Atom0837 chi ∧
      PredecessorHalfFin13Atom0852 chi ∧
      PredecessorHalfFin13Atom0943 chi) ∨
      (PredecessorHalfFin13Atom2105 chi ∧
      ¬PredecessorHalfFin13Atom0823 chi))) ∨
      ((PredecessorHalfFin13Atom2105 chi ∧
      ¬PredecessorHalfFin13Atom0824 chi) ∨
      ((PredecessorHalfFin13Atom2105 chi ∧
      ¬PredecessorHalfFin13Atom0838 chi) ∨
      (PredecessorHalfFin13Atom2105 chi ∧
      ¬PredecessorHalfFin13Atom0853 chi)))) ∨
      (((PredecessorHalfFin13Atom2105 chi ∧
      ¬PredecessorHalfFin13Atom0944 chi) ∨
      ((PredecessorHalfFin13Atom2106 chi ∧
      ¬PredecessorHalfFin13Atom0823 chi) ∨
      (PredecessorHalfFin13Atom2106 chi ∧
      ¬PredecessorHalfFin13Atom0825 chi))) ∨
      ((PredecessorHalfFin13Atom2106 chi ∧
      ¬PredecessorHalfFin13Atom0839 chi) ∨
      ((PredecessorHalfFin13Atom2106 chi ∧
      ¬PredecessorHalfFin13Atom0854 chi) ∨
      (PredecessorHalfFin13Atom2106 chi ∧
      ¬PredecessorHalfFin13Atom0945 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom2106 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0825 chi ∧
      PredecessorHalfFin13Atom0839 chi ∧
      PredecessorHalfFin13Atom0854 chi ∧
      PredecessorHalfFin13Atom0945 chi) ∨
      ((PredecessorHalfFin13Atom2107 chi ∧
      ¬PredecessorHalfFin13Atom0824 chi) ∨
      (PredecessorHalfFin13Atom2107 chi ∧
      ¬PredecessorHalfFin13Atom0825 chi))) ∨
      ((PredecessorHalfFin13Atom2107 chi ∧
      ¬PredecessorHalfFin13Atom0840 chi) ∨
      ((PredecessorHalfFin13Atom2107 chi ∧
      ¬PredecessorHalfFin13Atom0855 chi) ∨
      (PredecessorHalfFin13Atom2107 chi ∧
      ¬PredecessorHalfFin13Atom0946 chi)))) ∨
      (((PredecessorHalfFin13Atom2108 chi ∧
      ¬PredecessorHalfFin13Atom0826 chi) ∨
      ((PredecessorHalfFin13Atom2108 chi ∧
      ¬PredecessorHalfFin13Atom0827 chi) ∨
      (PredecessorHalfFin13Atom2108 chi ∧
      ¬PredecessorHalfFin13Atom0831 chi))) ∨
      (((PredecessorHalfFin13Atom2108 chi ∧
      ¬PredecessorHalfFin13Atom0856 chi) ∨
      (PredecessorHalfFin13Atom2108 chi ∧
      ¬PredecessorHalfFin13Atom0947 chi)) ∨
      ((¬PredecessorHalfFin13Atom2108 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0856 chi ∧
      PredecessorHalfFin13Atom0947 chi) ∨
      (PredecessorHalfFin13Atom2109 chi ∧
      ¬PredecessorHalfFin13Atom0826 chi)))))) ∨
      (((((PredecessorHalfFin13Atom2109 chi ∧
      ¬PredecessorHalfFin13Atom0828 chi) ∨
      ((PredecessorHalfFin13Atom2109 chi ∧
      ¬PredecessorHalfFin13Atom0832 chi) ∨
      (PredecessorHalfFin13Atom2109 chi ∧
      ¬PredecessorHalfFin13Atom0857 chi))) ∨
      ((PredecessorHalfFin13Atom2109 chi ∧
      ¬PredecessorHalfFin13Atom0948 chi) ∨
      ((¬PredecessorHalfFin13Atom2109 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0857 chi ∧
      PredecessorHalfFin13Atom0948 chi) ∨
      (PredecessorHalfFin13Atom2110 chi ∧
      ¬PredecessorHalfFin13Atom0826 chi)))) ∨
      (((PredecessorHalfFin13Atom2110 chi ∧
      ¬PredecessorHalfFin13Atom0829 chi) ∨
      ((PredecessorHalfFin13Atom2110 chi ∧
      ¬PredecessorHalfFin13Atom0833 chi) ∨
      (PredecessorHalfFin13Atom2110 chi ∧
      ¬PredecessorHalfFin13Atom0858 chi))) ∨
      ((PredecessorHalfFin13Atom2110 chi ∧
      ¬PredecessorHalfFin13Atom0949 chi) ∨
      ((¬PredecessorHalfFin13Atom2110 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0829 chi ∧
      PredecessorHalfFin13Atom0833 chi ∧
      PredecessorHalfFin13Atom0858 chi ∧
      PredecessorHalfFin13Atom0949 chi) ∨
      (PredecessorHalfFin13Atom2111 chi ∧
      ¬PredecessorHalfFin13Atom0826 chi))))) ∨
      ((((PredecessorHalfFin13Atom2111 chi ∧
      ¬PredecessorHalfFin13Atom0830 chi) ∨
      ((PredecessorHalfFin13Atom2111 chi ∧
      ¬PredecessorHalfFin13Atom0834 chi) ∨
      (PredecessorHalfFin13Atom2111 chi ∧
      ¬PredecessorHalfFin13Atom0859 chi))) ∨
      ((PredecessorHalfFin13Atom2111 chi ∧
      ¬PredecessorHalfFin13Atom0950 chi) ∨
      ((¬PredecessorHalfFin13Atom2111 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0834 chi ∧
      PredecessorHalfFin13Atom0859 chi ∧
      PredecessorHalfFin13Atom0950 chi) ∨
      (PredecessorHalfFin13Atom2112 chi ∧
      ¬PredecessorHalfFin13Atom0827 chi)))) ∨
      (((PredecessorHalfFin13Atom2112 chi ∧
      ¬PredecessorHalfFin13Atom0828 chi) ∨
      ((PredecessorHalfFin13Atom2112 chi ∧
      ¬PredecessorHalfFin13Atom0835 chi) ∨
      (PredecessorHalfFin13Atom2112 chi ∧
      ¬PredecessorHalfFin13Atom0860 chi))) ∨
      (((PredecessorHalfFin13Atom2112 chi ∧
      ¬PredecessorHalfFin13Atom0951 chi) ∨
      (¬PredecessorHalfFin13Atom2112 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0860 chi ∧
      PredecessorHalfFin13Atom0951 chi)) ∨
      ((PredecessorHalfFin13Atom2113 chi ∧
      ¬PredecessorHalfFin13Atom0827 chi) ∨
      (PredecessorHalfFin13Atom2113 chi ∧
      ¬PredecessorHalfFin13Atom0829 chi))))))))) := by
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
              exact predecessorHalfFin13_clause23725 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23726 chi hbad
              ·
                exact predecessorHalfFin13_clause23727 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23728 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23729 chi hbad
              ·
                exact predecessorHalfFin13_clause23731 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23732 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23733 chi hbad
              ·
                exact predecessorHalfFin13_clause23734 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23735 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23736 chi hbad
              ·
                exact predecessorHalfFin13_clause23737 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23738 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23739 chi hbad
              ·
                exact predecessorHalfFin13_clause23740 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23741 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23742 chi hbad
              ·
                exact predecessorHalfFin13_clause23743 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23744 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23745 chi hbad
              ·
                exact predecessorHalfFin13_clause23746 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23747 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23748 chi hbad
              ·
                exact predecessorHalfFin13_clause23749 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23750 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23751 chi hbad
              ·
                exact predecessorHalfFin13_clause23752 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23753 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23755 chi hbad
              ·
                exact predecessorHalfFin13_clause23756 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23757 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23758 chi hbad
              ·
                exact predecessorHalfFin13_clause23759 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23760 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23761 chi hbad
              ·
                exact predecessorHalfFin13_clause23762 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23763 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23764 chi hbad
              ·
                exact predecessorHalfFin13_clause23765 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23766 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23767 chi hbad
              ·
                exact predecessorHalfFin13_clause23768 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23770 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23771 chi hbad
              ·
                exact predecessorHalfFin13_clause23772 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23773 chi hbad
              ·
                exact predecessorHalfFin13_clause23774 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23775 chi hbad
              ·
                exact predecessorHalfFin13_clause23776 chi hbad
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
              exact predecessorHalfFin13_clause23777 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23778 chi hbad
              ·
                exact predecessorHalfFin13_clause23779 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23780 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23781 chi hbad
              ·
                exact predecessorHalfFin13_clause23782 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23783 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23785 chi hbad
              ·
                exact predecessorHalfFin13_clause23786 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23787 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23788 chi hbad
              ·
                exact predecessorHalfFin13_clause23789 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23790 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23791 chi hbad
              ·
                exact predecessorHalfFin13_clause23792 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23793 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23794 chi hbad
              ·
                exact predecessorHalfFin13_clause23795 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23797 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23798 chi hbad
              ·
                exact predecessorHalfFin13_clause23799 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23800 chi hbad
              ·
                exact predecessorHalfFin13_clause23801 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23802 chi hbad
              ·
                exact predecessorHalfFin13_clause23803 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23804 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23805 chi hbad
              ·
                exact predecessorHalfFin13_clause23806 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23807 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23808 chi hbad
              ·
                exact predecessorHalfFin13_clause23809 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23810 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23811 chi hbad
              ·
                exact predecessorHalfFin13_clause23812 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23813 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23814 chi hbad
              ·
                exact predecessorHalfFin13_clause23815 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23816 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23817 chi hbad
              ·
                exact predecessorHalfFin13_clause23818 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23819 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23820 chi hbad
              ·
                exact predecessorHalfFin13_clause23821 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23822 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23823 chi hbad
              ·
                exact predecessorHalfFin13_clause23824 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23825 chi hbad
              ·
                exact predecessorHalfFin13_clause23826 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23827 chi hbad
              ·
                exact predecessorHalfFin13_clause23828 chi hbad

end ErdosSzekeres

end
