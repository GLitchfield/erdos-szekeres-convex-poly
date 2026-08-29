module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk083
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk084

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 109. -/

theorem predecessorHalfFin13_rejectSemanticSegment109
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom2131 chi ∧
      ¬PredecessorHalfFin13Atom0845 chi) ∨
      ((PredecessorHalfFin13Atom2131 chi ∧
      ¬PredecessorHalfFin13Atom0849 chi) ∨
      (PredecessorHalfFin13Atom2131 chi ∧
      ¬PredecessorHalfFin13Atom0859 chi))) ∨
      ((PredecessorHalfFin13Atom2131 chi ∧
      ¬PredecessorHalfFin13Atom0970 chi) ∨
      ((¬PredecessorHalfFin13Atom2131 chi ∧
      PredecessorHalfFin13Atom0841 chi ∧
      PredecessorHalfFin13Atom0845 chi ∧
      PredecessorHalfFin13Atom0849 chi ∧
      PredecessorHalfFin13Atom0859 chi ∧
      PredecessorHalfFin13Atom0970 chi) ∨
      (PredecessorHalfFin13Atom2132 chi ∧
      ¬PredecessorHalfFin13Atom0842 chi)))) ∨
      (((PredecessorHalfFin13Atom2132 chi ∧
      ¬PredecessorHalfFin13Atom0843 chi) ∨
      ((PredecessorHalfFin13Atom2132 chi ∧
      ¬PredecessorHalfFin13Atom0850 chi) ∨
      (PredecessorHalfFin13Atom2132 chi ∧
      ¬PredecessorHalfFin13Atom0860 chi))) ∨
      ((PredecessorHalfFin13Atom2132 chi ∧
      ¬PredecessorHalfFin13Atom0971 chi) ∨
      ((¬PredecessorHalfFin13Atom2132 chi ∧
      PredecessorHalfFin13Atom0842 chi ∧
      PredecessorHalfFin13Atom0843 chi ∧
      PredecessorHalfFin13Atom0850 chi ∧
      PredecessorHalfFin13Atom0860 chi ∧
      PredecessorHalfFin13Atom0971 chi) ∨
      (PredecessorHalfFin13Atom2133 chi ∧
      ¬PredecessorHalfFin13Atom0842 chi))))) ∨
      ((((PredecessorHalfFin13Atom2133 chi ∧
      ¬PredecessorHalfFin13Atom0844 chi) ∨
      ((PredecessorHalfFin13Atom2133 chi ∧
      ¬PredecessorHalfFin13Atom0851 chi) ∨
      (PredecessorHalfFin13Atom2133 chi ∧
      ¬PredecessorHalfFin13Atom0861 chi))) ∨
      ((PredecessorHalfFin13Atom2133 chi ∧
      ¬PredecessorHalfFin13Atom0972 chi) ∨
      ((¬PredecessorHalfFin13Atom2133 chi ∧
      PredecessorHalfFin13Atom0842 chi ∧
      PredecessorHalfFin13Atom0844 chi ∧
      PredecessorHalfFin13Atom0851 chi ∧
      PredecessorHalfFin13Atom0861 chi ∧
      PredecessorHalfFin13Atom0972 chi) ∨
      (PredecessorHalfFin13Atom2134 chi ∧
      ¬PredecessorHalfFin13Atom0842 chi)))) ∨
      (((PredecessorHalfFin13Atom2134 chi ∧
      ¬PredecessorHalfFin13Atom0845 chi) ∨
      ((PredecessorHalfFin13Atom2134 chi ∧
      ¬PredecessorHalfFin13Atom0852 chi) ∨
      (PredecessorHalfFin13Atom2134 chi ∧
      ¬PredecessorHalfFin13Atom0862 chi))) ∨
      ((PredecessorHalfFin13Atom2134 chi ∧
      ¬PredecessorHalfFin13Atom0973 chi) ∨
      ((¬PredecessorHalfFin13Atom2134 chi ∧
      PredecessorHalfFin13Atom0842 chi ∧
      PredecessorHalfFin13Atom0845 chi ∧
      PredecessorHalfFin13Atom0852 chi ∧
      PredecessorHalfFin13Atom0862 chi ∧
      PredecessorHalfFin13Atom0973 chi) ∨
      (PredecessorHalfFin13Atom2135 chi ∧
      ¬PredecessorHalfFin13Atom0843 chi)))))) ∨
      (((((PredecessorHalfFin13Atom2135 chi ∧
      ¬PredecessorHalfFin13Atom0844 chi) ∨
      ((PredecessorHalfFin13Atom2135 chi ∧
      ¬PredecessorHalfFin13Atom0853 chi) ∨
      (PredecessorHalfFin13Atom2135 chi ∧
      ¬PredecessorHalfFin13Atom0863 chi))) ∨
      ((PredecessorHalfFin13Atom2135 chi ∧
      ¬PredecessorHalfFin13Atom0974 chi) ∨
      ((PredecessorHalfFin13Atom2136 chi ∧
      ¬PredecessorHalfFin13Atom0843 chi) ∨
      (PredecessorHalfFin13Atom2136 chi ∧
      ¬PredecessorHalfFin13Atom0845 chi)))) ∨
      (((PredecessorHalfFin13Atom2136 chi ∧
      ¬PredecessorHalfFin13Atom0854 chi) ∨
      ((PredecessorHalfFin13Atom2136 chi ∧
      ¬PredecessorHalfFin13Atom0864 chi) ∨
      (PredecessorHalfFin13Atom2136 chi ∧
      ¬PredecessorHalfFin13Atom0975 chi))) ∨
      ((¬PredecessorHalfFin13Atom2136 chi ∧
      PredecessorHalfFin13Atom0843 chi ∧
      PredecessorHalfFin13Atom0845 chi ∧
      PredecessorHalfFin13Atom0854 chi ∧
      PredecessorHalfFin13Atom0864 chi ∧
      PredecessorHalfFin13Atom0975 chi) ∨
      ((PredecessorHalfFin13Atom2137 chi ∧
      ¬PredecessorHalfFin13Atom0844 chi) ∨
      (PredecessorHalfFin13Atom2137 chi ∧
      ¬PredecessorHalfFin13Atom0845 chi))))) ∨
      ((((PredecessorHalfFin13Atom2137 chi ∧
      ¬PredecessorHalfFin13Atom0976 chi) ∨
      ((PredecessorHalfFin13Atom2138 chi ∧
      ¬PredecessorHalfFin13Atom0846 chi) ∨
      (PredecessorHalfFin13Atom2138 chi ∧
      ¬PredecessorHalfFin13Atom0847 chi))) ∨
      ((PredecessorHalfFin13Atom2138 chi ∧
      ¬PredecessorHalfFin13Atom0850 chi) ∨
      ((PredecessorHalfFin13Atom2138 chi ∧
      ¬PredecessorHalfFin13Atom0866 chi) ∨
      (PredecessorHalfFin13Atom2138 chi ∧
      ¬PredecessorHalfFin13Atom0977 chi)))) ∨
      (((¬PredecessorHalfFin13Atom2138 chi ∧
      PredecessorHalfFin13Atom0846 chi ∧
      PredecessorHalfFin13Atom0847 chi ∧
      PredecessorHalfFin13Atom0850 chi ∧
      PredecessorHalfFin13Atom0866 chi ∧
      PredecessorHalfFin13Atom0977 chi) ∨
      ((PredecessorHalfFin13Atom2139 chi ∧
      ¬PredecessorHalfFin13Atom0846 chi) ∨
      (PredecessorHalfFin13Atom2139 chi ∧
      ¬PredecessorHalfFin13Atom0848 chi))) ∨
      (((PredecessorHalfFin13Atom2139 chi ∧
      ¬PredecessorHalfFin13Atom0851 chi) ∨
      (PredecessorHalfFin13Atom2139 chi ∧
      ¬PredecessorHalfFin13Atom0867 chi)) ∨
      ((PredecessorHalfFin13Atom2139 chi ∧
      ¬PredecessorHalfFin13Atom0978 chi) ∨
      (¬PredecessorHalfFin13Atom2139 chi ∧
      PredecessorHalfFin13Atom0846 chi ∧
      PredecessorHalfFin13Atom0848 chi ∧
      PredecessorHalfFin13Atom0851 chi ∧
      PredecessorHalfFin13Atom0867 chi ∧
      PredecessorHalfFin13Atom0978 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom2140 chi ∧
      ¬PredecessorHalfFin13Atom0846 chi) ∨
      ((PredecessorHalfFin13Atom2140 chi ∧
      ¬PredecessorHalfFin13Atom0849 chi) ∨
      (PredecessorHalfFin13Atom2140 chi ∧
      ¬PredecessorHalfFin13Atom0852 chi))) ∨
      ((PredecessorHalfFin13Atom2140 chi ∧
      ¬PredecessorHalfFin13Atom0868 chi) ∨
      ((PredecessorHalfFin13Atom2140 chi ∧
      ¬PredecessorHalfFin13Atom0979 chi) ∨
      (¬PredecessorHalfFin13Atom2140 chi ∧
      PredecessorHalfFin13Atom0846 chi ∧
      PredecessorHalfFin13Atom0849 chi ∧
      PredecessorHalfFin13Atom0852 chi ∧
      PredecessorHalfFin13Atom0868 chi ∧
      PredecessorHalfFin13Atom0979 chi)))) ∨
      (((PredecessorHalfFin13Atom2141 chi ∧
      ¬PredecessorHalfFin13Atom0847 chi) ∨
      ((PredecessorHalfFin13Atom2141 chi ∧
      ¬PredecessorHalfFin13Atom0848 chi) ∨
      (PredecessorHalfFin13Atom2141 chi ∧
      ¬PredecessorHalfFin13Atom0853 chi))) ∨
      ((PredecessorHalfFin13Atom2141 chi ∧
      ¬PredecessorHalfFin13Atom0869 chi) ∨
      ((PredecessorHalfFin13Atom2141 chi ∧
      ¬PredecessorHalfFin13Atom0980 chi) ∨
      (¬PredecessorHalfFin13Atom2141 chi ∧
      PredecessorHalfFin13Atom0847 chi ∧
      PredecessorHalfFin13Atom0848 chi ∧
      PredecessorHalfFin13Atom0853 chi ∧
      PredecessorHalfFin13Atom0869 chi ∧
      PredecessorHalfFin13Atom0980 chi))))) ∨
      ((((PredecessorHalfFin13Atom2142 chi ∧
      ¬PredecessorHalfFin13Atom0847 chi) ∨
      ((PredecessorHalfFin13Atom2142 chi ∧
      ¬PredecessorHalfFin13Atom0849 chi) ∨
      (PredecessorHalfFin13Atom2142 chi ∧
      ¬PredecessorHalfFin13Atom0854 chi))) ∨
      ((PredecessorHalfFin13Atom2142 chi ∧
      ¬PredecessorHalfFin13Atom0870 chi) ∨
      ((PredecessorHalfFin13Atom2142 chi ∧
      ¬PredecessorHalfFin13Atom0981 chi) ∨
      (¬PredecessorHalfFin13Atom2142 chi ∧
      PredecessorHalfFin13Atom0847 chi ∧
      PredecessorHalfFin13Atom0849 chi ∧
      PredecessorHalfFin13Atom0854 chi ∧
      PredecessorHalfFin13Atom0870 chi ∧
      PredecessorHalfFin13Atom0981 chi)))) ∨
      (((PredecessorHalfFin13Atom2143 chi ∧
      ¬PredecessorHalfFin13Atom0848 chi) ∨
      ((PredecessorHalfFin13Atom2143 chi ∧
      ¬PredecessorHalfFin13Atom0849 chi) ∨
      (PredecessorHalfFin13Atom2143 chi ∧
      ¬PredecessorHalfFin13Atom0855 chi))) ∨
      (((PredecessorHalfFin13Atom2143 chi ∧
      ¬PredecessorHalfFin13Atom0982 chi) ∨
      (PredecessorHalfFin13Atom2144 chi ∧
      ¬PredecessorHalfFin13Atom0850 chi)) ∨
      ((PredecessorHalfFin13Atom2144 chi ∧
      ¬PredecessorHalfFin13Atom0851 chi) ∨
      (PredecessorHalfFin13Atom2144 chi ∧
      ¬PredecessorHalfFin13Atom0853 chi)))))) ∨
      (((((PredecessorHalfFin13Atom2144 chi ∧
      ¬PredecessorHalfFin13Atom0872 chi) ∨
      ((PredecessorHalfFin13Atom2144 chi ∧
      ¬PredecessorHalfFin13Atom0983 chi) ∨
      (PredecessorHalfFin13Atom2145 chi ∧
      ¬PredecessorHalfFin13Atom0850 chi))) ∨
      ((PredecessorHalfFin13Atom2145 chi ∧
      ¬PredecessorHalfFin13Atom0852 chi) ∨
      ((PredecessorHalfFin13Atom2145 chi ∧
      ¬PredecessorHalfFin13Atom0854 chi) ∨
      (PredecessorHalfFin13Atom2145 chi ∧
      ¬PredecessorHalfFin13Atom0873 chi)))) ∨
      (((PredecessorHalfFin13Atom2145 chi ∧
      ¬PredecessorHalfFin13Atom0984 chi) ∨
      ((¬PredecessorHalfFin13Atom2145 chi ∧
      PredecessorHalfFin13Atom0850 chi ∧
      PredecessorHalfFin13Atom0852 chi ∧
      PredecessorHalfFin13Atom0854 chi ∧
      PredecessorHalfFin13Atom0873 chi ∧
      PredecessorHalfFin13Atom0984 chi) ∨
      (PredecessorHalfFin13Atom2146 chi ∧
      ¬PredecessorHalfFin13Atom0851 chi))) ∨
      ((PredecessorHalfFin13Atom2146 chi ∧
      ¬PredecessorHalfFin13Atom0852 chi) ∨
      ((PredecessorHalfFin13Atom2146 chi ∧
      ¬PredecessorHalfFin13Atom0874 chi) ∨
      (PredecessorHalfFin13Atom2146 chi ∧
      ¬PredecessorHalfFin13Atom0985 chi))))) ∨
      ((((PredecessorHalfFin13Atom2147 chi ∧
      ¬PredecessorHalfFin13Atom0853 chi) ∨
      ((PredecessorHalfFin13Atom2147 chi ∧
      ¬PredecessorHalfFin13Atom0854 chi) ∨
      (PredecessorHalfFin13Atom2147 chi ∧
      ¬PredecessorHalfFin13Atom0855 chi))) ∨
      ((PredecessorHalfFin13Atom2147 chi ∧
      ¬PredecessorHalfFin13Atom0875 chi) ∨
      ((PredecessorHalfFin13Atom2147 chi ∧
      ¬PredecessorHalfFin13Atom0986 chi) ∨
      (PredecessorHalfFin13Atom2148 chi ∧
      ¬PredecessorHalfFin13Atom0856 chi)))) ∨
      (((PredecessorHalfFin13Atom2148 chi ∧
      ¬PredecessorHalfFin13Atom0857 chi) ∨
      ((PredecessorHalfFin13Atom2148 chi ∧
      ¬PredecessorHalfFin13Atom0860 chi) ∨
      (PredecessorHalfFin13Atom2148 chi ∧
      ¬PredecessorHalfFin13Atom0866 chi))) ∨
      (((PredecessorHalfFin13Atom2148 chi ∧
      ¬PredecessorHalfFin13Atom0987 chi) ∨
      (¬PredecessorHalfFin13Atom2148 chi ∧
      PredecessorHalfFin13Atom0856 chi ∧
      PredecessorHalfFin13Atom0857 chi ∧
      PredecessorHalfFin13Atom0860 chi ∧
      PredecessorHalfFin13Atom0866 chi ∧
      PredecessorHalfFin13Atom0987 chi)) ∨
      ((PredecessorHalfFin13Atom2149 chi ∧
      ¬PredecessorHalfFin13Atom0856 chi) ∨
      (PredecessorHalfFin13Atom2149 chi ∧
      ¬PredecessorHalfFin13Atom0858 chi))))))))) := by
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
              exact predecessorHalfFin13_clause23936 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23937 chi hbad
              ·
                exact predecessorHalfFin13_clause23938 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23939 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23940 chi hbad
              ·
                exact predecessorHalfFin13_clause23941 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23942 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23943 chi hbad
              ·
                exact predecessorHalfFin13_clause23944 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23945 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23946 chi hbad
              ·
                exact predecessorHalfFin13_clause23947 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23948 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23949 chi hbad
              ·
                exact predecessorHalfFin13_clause23950 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23951 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23952 chi hbad
              ·
                exact predecessorHalfFin13_clause23953 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23954 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23955 chi hbad
              ·
                exact predecessorHalfFin13_clause23956 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23957 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23958 chi hbad
              ·
                exact predecessorHalfFin13_clause23959 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23960 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23961 chi hbad
              ·
                exact predecessorHalfFin13_clause23962 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23963 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23965 chi hbad
              ·
                exact predecessorHalfFin13_clause23966 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23967 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23968 chi hbad
              ·
                exact predecessorHalfFin13_clause23969 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23970 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23971 chi hbad
              ·
                exact predecessorHalfFin13_clause23972 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23975 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23977 chi hbad
              ·
                exact predecessorHalfFin13_clause23978 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23979 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23980 chi hbad
              ·
                exact predecessorHalfFin13_clause23981 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23982 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23983 chi hbad
              ·
                exact predecessorHalfFin13_clause23984 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23985 chi hbad
              ·
                exact predecessorHalfFin13_clause23986 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23987 chi hbad
              ·
                exact predecessorHalfFin13_clause23988 chi hbad
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
              exact predecessorHalfFin13_clause23989 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23990 chi hbad
              ·
                exact predecessorHalfFin13_clause23991 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23992 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23993 chi hbad
              ·
                exact predecessorHalfFin13_clause23994 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23995 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23996 chi hbad
              ·
                exact predecessorHalfFin13_clause23997 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23998 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23999 chi hbad
              ·
                exact predecessorHalfFin13_clause24000 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24001 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24002 chi hbad
              ·
                exact predecessorHalfFin13_clause24003 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24004 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24005 chi hbad
              ·
                exact predecessorHalfFin13_clause24006 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24007 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24008 chi hbad
              ·
                exact predecessorHalfFin13_clause24009 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24011 chi hbad
              ·
                exact predecessorHalfFin13_clause24013 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24014 chi hbad
              ·
                exact predecessorHalfFin13_clause24015 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24016 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24017 chi hbad
              ·
                exact predecessorHalfFin13_clause24019 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24020 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24021 chi hbad
              ·
                exact predecessorHalfFin13_clause24022 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24023 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24024 chi hbad
              ·
                exact predecessorHalfFin13_clause24025 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24026 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24028 chi hbad
              ·
                exact predecessorHalfFin13_clause24029 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24031 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24032 chi hbad
              ·
                exact predecessorHalfFin13_clause24033 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24034 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24035 chi hbad
              ·
                exact predecessorHalfFin13_clause24037 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24038 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24039 chi hbad
              ·
                exact predecessorHalfFin13_clause24040 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24041 chi hbad
              ·
                exact predecessorHalfFin13_clause24042 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24043 chi hbad
              ·
                exact predecessorHalfFin13_clause24044 chi hbad

end ErdosSzekeres

end
