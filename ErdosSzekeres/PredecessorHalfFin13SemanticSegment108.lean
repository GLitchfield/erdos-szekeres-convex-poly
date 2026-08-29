module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk082
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk083

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 108. -/

theorem predecessorHalfFin13_rejectSemanticSegment108
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom2113 chi ∧
      ¬PredecessorHalfFin13Atom0836 chi) ∨
      ((PredecessorHalfFin13Atom2113 chi ∧
      ¬PredecessorHalfFin13Atom0861 chi) ∨
      (PredecessorHalfFin13Atom2113 chi ∧
      ¬PredecessorHalfFin13Atom0952 chi))) ∨
      ((¬PredecessorHalfFin13Atom2113 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0829 chi ∧
      PredecessorHalfFin13Atom0836 chi ∧
      PredecessorHalfFin13Atom0861 chi ∧
      PredecessorHalfFin13Atom0952 chi) ∨
      ((PredecessorHalfFin13Atom2114 chi ∧
      ¬PredecessorHalfFin13Atom0827 chi) ∨
      (PredecessorHalfFin13Atom2114 chi ∧
      ¬PredecessorHalfFin13Atom0830 chi)))) ∨
      (((PredecessorHalfFin13Atom2114 chi ∧
      ¬PredecessorHalfFin13Atom0837 chi) ∨
      ((PredecessorHalfFin13Atom2114 chi ∧
      ¬PredecessorHalfFin13Atom0862 chi) ∨
      (PredecessorHalfFin13Atom2114 chi ∧
      ¬PredecessorHalfFin13Atom0953 chi))) ∨
      ((¬PredecessorHalfFin13Atom2114 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0837 chi ∧
      PredecessorHalfFin13Atom0862 chi ∧
      PredecessorHalfFin13Atom0953 chi) ∨
      ((PredecessorHalfFin13Atom2115 chi ∧
      ¬PredecessorHalfFin13Atom0828 chi) ∨
      (PredecessorHalfFin13Atom2115 chi ∧
      ¬PredecessorHalfFin13Atom0829 chi))))) ∨
      ((((PredecessorHalfFin13Atom2115 chi ∧
      ¬PredecessorHalfFin13Atom0838 chi) ∨
      ((PredecessorHalfFin13Atom2115 chi ∧
      ¬PredecessorHalfFin13Atom0863 chi) ∨
      (PredecessorHalfFin13Atom2115 chi ∧
      ¬PredecessorHalfFin13Atom0954 chi))) ∨
      ((¬PredecessorHalfFin13Atom2115 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0829 chi ∧
      PredecessorHalfFin13Atom0838 chi ∧
      PredecessorHalfFin13Atom0863 chi ∧
      PredecessorHalfFin13Atom0954 chi) ∨
      ((PredecessorHalfFin13Atom2116 chi ∧
      ¬PredecessorHalfFin13Atom0828 chi) ∨
      (PredecessorHalfFin13Atom2116 chi ∧
      ¬PredecessorHalfFin13Atom0830 chi)))) ∨
      (((PredecessorHalfFin13Atom2116 chi ∧
      ¬PredecessorHalfFin13Atom0839 chi) ∨
      ((PredecessorHalfFin13Atom2116 chi ∧
      ¬PredecessorHalfFin13Atom0864 chi) ∨
      (PredecessorHalfFin13Atom2116 chi ∧
      ¬PredecessorHalfFin13Atom0955 chi))) ∨
      ((¬PredecessorHalfFin13Atom2116 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0839 chi ∧
      PredecessorHalfFin13Atom0864 chi ∧
      PredecessorHalfFin13Atom0955 chi) ∨
      ((PredecessorHalfFin13Atom2117 chi ∧
      ¬PredecessorHalfFin13Atom0830 chi) ∨
      (PredecessorHalfFin13Atom2117 chi ∧
      ¬PredecessorHalfFin13Atom0865 chi)))))) ∨
      (((((PredecessorHalfFin13Atom2117 chi ∧
      ¬PredecessorHalfFin13Atom0956 chi) ∨
      ((PredecessorHalfFin13Atom2118 chi ∧
      ¬PredecessorHalfFin13Atom0831 chi) ∨
      (PredecessorHalfFin13Atom2118 chi ∧
      ¬PredecessorHalfFin13Atom0832 chi))) ∨
      ((PredecessorHalfFin13Atom2118 chi ∧
      ¬PredecessorHalfFin13Atom0835 chi) ∨
      ((PredecessorHalfFin13Atom2118 chi ∧
      ¬PredecessorHalfFin13Atom0866 chi) ∨
      (PredecessorHalfFin13Atom2118 chi ∧
      ¬PredecessorHalfFin13Atom0957 chi)))) ∨
      (((¬PredecessorHalfFin13Atom2118 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0866 chi ∧
      PredecessorHalfFin13Atom0957 chi) ∨
      ((PredecessorHalfFin13Atom2119 chi ∧
      ¬PredecessorHalfFin13Atom0831 chi) ∨
      (PredecessorHalfFin13Atom2119 chi ∧
      ¬PredecessorHalfFin13Atom0833 chi))) ∨
      ((PredecessorHalfFin13Atom2119 chi ∧
      ¬PredecessorHalfFin13Atom0836 chi) ∨
      ((PredecessorHalfFin13Atom2119 chi ∧
      ¬PredecessorHalfFin13Atom0867 chi) ∨
      (PredecessorHalfFin13Atom2119 chi ∧
      ¬PredecessorHalfFin13Atom0958 chi))))) ∨
      ((((PredecessorHalfFin13Atom2120 chi ∧
      ¬PredecessorHalfFin13Atom0831 chi) ∨
      ((PredecessorHalfFin13Atom2120 chi ∧
      ¬PredecessorHalfFin13Atom0834 chi) ∨
      (PredecessorHalfFin13Atom2120 chi ∧
      ¬PredecessorHalfFin13Atom0837 chi))) ∨
      ((PredecessorHalfFin13Atom2120 chi ∧
      ¬PredecessorHalfFin13Atom0868 chi) ∨
      ((PredecessorHalfFin13Atom2120 chi ∧
      ¬PredecessorHalfFin13Atom0959 chi) ∨
      (¬PredecessorHalfFin13Atom2120 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0834 chi ∧
      PredecessorHalfFin13Atom0837 chi ∧
      PredecessorHalfFin13Atom0868 chi ∧
      PredecessorHalfFin13Atom0959 chi)))) ∨
      (((PredecessorHalfFin13Atom2121 chi ∧
      ¬PredecessorHalfFin13Atom0832 chi) ∨
      ((PredecessorHalfFin13Atom2121 chi ∧
      ¬PredecessorHalfFin13Atom0833 chi) ∨
      (PredecessorHalfFin13Atom2121 chi ∧
      ¬PredecessorHalfFin13Atom0838 chi))) ∨
      (((PredecessorHalfFin13Atom2121 chi ∧
      ¬PredecessorHalfFin13Atom0869 chi) ∨
      (PredecessorHalfFin13Atom2121 chi ∧
      ¬PredecessorHalfFin13Atom0960 chi)) ∨
      ((¬PredecessorHalfFin13Atom2121 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0833 chi ∧
      PredecessorHalfFin13Atom0838 chi ∧
      PredecessorHalfFin13Atom0869 chi ∧
      PredecessorHalfFin13Atom0960 chi) ∨
      (PredecessorHalfFin13Atom2122 chi ∧
      ¬PredecessorHalfFin13Atom0832 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom2122 chi ∧
      ¬PredecessorHalfFin13Atom0834 chi) ∨
      ((PredecessorHalfFin13Atom2122 chi ∧
      ¬PredecessorHalfFin13Atom0839 chi) ∨
      (PredecessorHalfFin13Atom2122 chi ∧
      ¬PredecessorHalfFin13Atom0870 chi))) ∨
      ((PredecessorHalfFin13Atom2122 chi ∧
      ¬PredecessorHalfFin13Atom0961 chi) ∨
      ((¬PredecessorHalfFin13Atom2122 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0834 chi ∧
      PredecessorHalfFin13Atom0839 chi ∧
      PredecessorHalfFin13Atom0870 chi ∧
      PredecessorHalfFin13Atom0961 chi) ∨
      (PredecessorHalfFin13Atom2123 chi ∧
      ¬PredecessorHalfFin13Atom0834 chi)))) ∨
      (((PredecessorHalfFin13Atom2123 chi ∧
      ¬PredecessorHalfFin13Atom0840 chi) ∨
      ((PredecessorHalfFin13Atom2123 chi ∧
      ¬PredecessorHalfFin13Atom0871 chi) ∨
      (PredecessorHalfFin13Atom2123 chi ∧
      ¬PredecessorHalfFin13Atom0962 chi))) ∨
      ((PredecessorHalfFin13Atom2124 chi ∧
      ¬PredecessorHalfFin13Atom0835 chi) ∨
      ((PredecessorHalfFin13Atom2124 chi ∧
      ¬PredecessorHalfFin13Atom0836 chi) ∨
      (PredecessorHalfFin13Atom2124 chi ∧
      ¬PredecessorHalfFin13Atom0838 chi))))) ∨
      ((((PredecessorHalfFin13Atom2124 chi ∧
      ¬PredecessorHalfFin13Atom0872 chi) ∨
      ((PredecessorHalfFin13Atom2124 chi ∧
      ¬PredecessorHalfFin13Atom0963 chi) ∨
      (¬PredecessorHalfFin13Atom2124 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0836 chi ∧
      PredecessorHalfFin13Atom0838 chi ∧
      PredecessorHalfFin13Atom0872 chi ∧
      PredecessorHalfFin13Atom0963 chi))) ∨
      ((PredecessorHalfFin13Atom2125 chi ∧
      ¬PredecessorHalfFin13Atom0835 chi) ∨
      ((PredecessorHalfFin13Atom2125 chi ∧
      ¬PredecessorHalfFin13Atom0837 chi) ∨
      (PredecessorHalfFin13Atom2125 chi ∧
      ¬PredecessorHalfFin13Atom0839 chi)))) ∨
      (((PredecessorHalfFin13Atom2125 chi ∧
      ¬PredecessorHalfFin13Atom0873 chi) ∨
      ((PredecessorHalfFin13Atom2125 chi ∧
      ¬PredecessorHalfFin13Atom0964 chi) ∨
      (¬PredecessorHalfFin13Atom2125 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0837 chi ∧
      PredecessorHalfFin13Atom0839 chi ∧
      PredecessorHalfFin13Atom0873 chi ∧
      PredecessorHalfFin13Atom0964 chi))) ∨
      ((PredecessorHalfFin13Atom2126 chi ∧
      ¬PredecessorHalfFin13Atom0836 chi) ∨
      ((PredecessorHalfFin13Atom2126 chi ∧
      ¬PredecessorHalfFin13Atom0837 chi) ∨
      (PredecessorHalfFin13Atom2126 chi ∧
      ¬PredecessorHalfFin13Atom0840 chi)))))) ∨
      (((((PredecessorHalfFin13Atom2126 chi ∧
      ¬PredecessorHalfFin13Atom0874 chi) ∨
      ((PredecessorHalfFin13Atom2126 chi ∧
      ¬PredecessorHalfFin13Atom0965 chi) ∨
      (PredecessorHalfFin13Atom2127 chi ∧
      ¬PredecessorHalfFin13Atom0838 chi))) ∨
      ((PredecessorHalfFin13Atom2127 chi ∧
      ¬PredecessorHalfFin13Atom0839 chi) ∨
      ((PredecessorHalfFin13Atom2127 chi ∧
      ¬PredecessorHalfFin13Atom0875 chi) ∨
      (PredecessorHalfFin13Atom2127 chi ∧
      ¬PredecessorHalfFin13Atom0966 chi)))) ∨
      (((PredecessorHalfFin13Atom2128 chi ∧
      ¬PredecessorHalfFin13Atom0841 chi) ∨
      ((PredecessorHalfFin13Atom2128 chi ∧
      ¬PredecessorHalfFin13Atom0842 chi) ∨
      (PredecessorHalfFin13Atom2128 chi ∧
      ¬PredecessorHalfFin13Atom0846 chi))) ∨
      ((PredecessorHalfFin13Atom2128 chi ∧
      ¬PredecessorHalfFin13Atom0856 chi) ∨
      ((PredecessorHalfFin13Atom2128 chi ∧
      ¬PredecessorHalfFin13Atom0967 chi) ∨
      (¬PredecessorHalfFin13Atom2128 chi ∧
      PredecessorHalfFin13Atom0841 chi ∧
      PredecessorHalfFin13Atom0842 chi ∧
      PredecessorHalfFin13Atom0846 chi ∧
      PredecessorHalfFin13Atom0856 chi ∧
      PredecessorHalfFin13Atom0967 chi))))) ∨
      ((((PredecessorHalfFin13Atom2129 chi ∧
      ¬PredecessorHalfFin13Atom0841 chi) ∨
      ((PredecessorHalfFin13Atom2129 chi ∧
      ¬PredecessorHalfFin13Atom0843 chi) ∨
      (PredecessorHalfFin13Atom2129 chi ∧
      ¬PredecessorHalfFin13Atom0847 chi))) ∨
      ((PredecessorHalfFin13Atom2129 chi ∧
      ¬PredecessorHalfFin13Atom0857 chi) ∨
      ((PredecessorHalfFin13Atom2129 chi ∧
      ¬PredecessorHalfFin13Atom0968 chi) ∨
      (¬PredecessorHalfFin13Atom2129 chi ∧
      PredecessorHalfFin13Atom0841 chi ∧
      PredecessorHalfFin13Atom0843 chi ∧
      PredecessorHalfFin13Atom0847 chi ∧
      PredecessorHalfFin13Atom0857 chi ∧
      PredecessorHalfFin13Atom0968 chi)))) ∨
      (((PredecessorHalfFin13Atom2130 chi ∧
      ¬PredecessorHalfFin13Atom0841 chi) ∨
      ((PredecessorHalfFin13Atom2130 chi ∧
      ¬PredecessorHalfFin13Atom0844 chi) ∨
      (PredecessorHalfFin13Atom2130 chi ∧
      ¬PredecessorHalfFin13Atom0848 chi))) ∨
      (((PredecessorHalfFin13Atom2130 chi ∧
      ¬PredecessorHalfFin13Atom0858 chi) ∨
      (PredecessorHalfFin13Atom2130 chi ∧
      ¬PredecessorHalfFin13Atom0969 chi)) ∨
      ((¬PredecessorHalfFin13Atom2130 chi ∧
      PredecessorHalfFin13Atom0841 chi ∧
      PredecessorHalfFin13Atom0844 chi ∧
      PredecessorHalfFin13Atom0848 chi ∧
      PredecessorHalfFin13Atom0858 chi ∧
      PredecessorHalfFin13Atom0969 chi) ∨
      (PredecessorHalfFin13Atom2131 chi ∧
      ¬PredecessorHalfFin13Atom0841 chi))))))))) := by
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
              exact predecessorHalfFin13_clause23829 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23830 chi hbad
              ·
                exact predecessorHalfFin13_clause23831 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23832 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23833 chi hbad
              ·
                exact predecessorHalfFin13_clause23834 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23835 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23836 chi hbad
              ·
                exact predecessorHalfFin13_clause23837 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23838 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23839 chi hbad
              ·
                exact predecessorHalfFin13_clause23840 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23841 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23842 chi hbad
              ·
                exact predecessorHalfFin13_clause23843 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23844 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23845 chi hbad
              ·
                exact predecessorHalfFin13_clause23846 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23847 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23848 chi hbad
              ·
                exact predecessorHalfFin13_clause23849 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23850 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23852 chi hbad
              ·
                exact predecessorHalfFin13_clause23854 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23855 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23857 chi hbad
              ·
                exact predecessorHalfFin13_clause23858 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23859 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23860 chi hbad
              ·
                exact predecessorHalfFin13_clause23861 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23862 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23863 chi hbad
              ·
                exact predecessorHalfFin13_clause23864 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23865 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23866 chi hbad
              ·
                exact predecessorHalfFin13_clause23867 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23869 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23870 chi hbad
              ·
                exact predecessorHalfFin13_clause23871 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23872 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23873 chi hbad
              ·
                exact predecessorHalfFin13_clause23874 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23875 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23876 chi hbad
              ·
                exact predecessorHalfFin13_clause23877 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23878 chi hbad
              ·
                exact predecessorHalfFin13_clause23879 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23880 chi hbad
              ·
                exact predecessorHalfFin13_clause23881 chi hbad
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
              exact predecessorHalfFin13_clause23882 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23883 chi hbad
              ·
                exact predecessorHalfFin13_clause23884 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23885 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23886 chi hbad
              ·
                exact predecessorHalfFin13_clause23888 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23889 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23890 chi hbad
              ·
                exact predecessorHalfFin13_clause23891 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23893 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23894 chi hbad
              ·
                exact predecessorHalfFin13_clause23895 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23896 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23897 chi hbad
              ·
                exact predecessorHalfFin13_clause23898 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23899 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23900 chi hbad
              ·
                exact predecessorHalfFin13_clause23901 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23902 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23903 chi hbad
              ·
                exact predecessorHalfFin13_clause23904 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23905 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23906 chi hbad
              ·
                exact predecessorHalfFin13_clause23907 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23908 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23909 chi hbad
              ·
                exact predecessorHalfFin13_clause23911 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23912 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23914 chi hbad
              ·
                exact predecessorHalfFin13_clause23915 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23917 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23918 chi hbad
              ·
                exact predecessorHalfFin13_clause23919 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23920 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23921 chi hbad
              ·
                exact predecessorHalfFin13_clause23922 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23923 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23924 chi hbad
              ·
                exact predecessorHalfFin13_clause23925 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23926 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23927 chi hbad
              ·
                exact predecessorHalfFin13_clause23928 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23929 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23930 chi hbad
              ·
                exact predecessorHalfFin13_clause23931 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23932 chi hbad
              ·
                exact predecessorHalfFin13_clause23933 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23934 chi hbad
              ·
                exact predecessorHalfFin13_clause23935 chi hbad

end ErdosSzekeres

end
