module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk084
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk085

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 110. -/

theorem predecessorHalfFin13_rejectSemanticSegment110
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom2149 chi ∧
      ¬PredecessorHalfFin13Atom0861 chi) ∨
      ((PredecessorHalfFin13Atom2149 chi ∧
      ¬PredecessorHalfFin13Atom0867 chi) ∨
      (PredecessorHalfFin13Atom2149 chi ∧
      ¬PredecessorHalfFin13Atom0988 chi))) ∨
      ((¬PredecessorHalfFin13Atom2149 chi ∧
      PredecessorHalfFin13Atom0856 chi ∧
      PredecessorHalfFin13Atom0858 chi ∧
      PredecessorHalfFin13Atom0861 chi ∧
      PredecessorHalfFin13Atom0867 chi ∧
      PredecessorHalfFin13Atom0988 chi) ∨
      ((PredecessorHalfFin13Atom2150 chi ∧
      ¬PredecessorHalfFin13Atom0856 chi) ∨
      (PredecessorHalfFin13Atom2150 chi ∧
      ¬PredecessorHalfFin13Atom0859 chi)))) ∨
      (((PredecessorHalfFin13Atom2150 chi ∧
      ¬PredecessorHalfFin13Atom0862 chi) ∨
      ((PredecessorHalfFin13Atom2150 chi ∧
      ¬PredecessorHalfFin13Atom0868 chi) ∨
      (PredecessorHalfFin13Atom2150 chi ∧
      ¬PredecessorHalfFin13Atom0989 chi))) ∨
      ((¬PredecessorHalfFin13Atom2150 chi ∧
      PredecessorHalfFin13Atom0856 chi ∧
      PredecessorHalfFin13Atom0859 chi ∧
      PredecessorHalfFin13Atom0862 chi ∧
      PredecessorHalfFin13Atom0868 chi ∧
      PredecessorHalfFin13Atom0989 chi) ∨
      ((PredecessorHalfFin13Atom2151 chi ∧
      ¬PredecessorHalfFin13Atom0857 chi) ∨
      (PredecessorHalfFin13Atom2151 chi ∧
      ¬PredecessorHalfFin13Atom0858 chi))))) ∨
      ((((PredecessorHalfFin13Atom2151 chi ∧
      ¬PredecessorHalfFin13Atom0863 chi) ∨
      ((PredecessorHalfFin13Atom2151 chi ∧
      ¬PredecessorHalfFin13Atom0869 chi) ∨
      (PredecessorHalfFin13Atom2151 chi ∧
      ¬PredecessorHalfFin13Atom0990 chi))) ∨
      ((PredecessorHalfFin13Atom2152 chi ∧
      ¬PredecessorHalfFin13Atom0857 chi) ∨
      ((PredecessorHalfFin13Atom2152 chi ∧
      ¬PredecessorHalfFin13Atom0859 chi) ∨
      (PredecessorHalfFin13Atom2152 chi ∧
      ¬PredecessorHalfFin13Atom0864 chi)))) ∨
      (((PredecessorHalfFin13Atom2152 chi ∧
      ¬PredecessorHalfFin13Atom0870 chi) ∨
      ((PredecessorHalfFin13Atom2152 chi ∧
      ¬PredecessorHalfFin13Atom0991 chi) ∨
      (¬PredecessorHalfFin13Atom2152 chi ∧
      PredecessorHalfFin13Atom0857 chi ∧
      PredecessorHalfFin13Atom0859 chi ∧
      PredecessorHalfFin13Atom0864 chi ∧
      PredecessorHalfFin13Atom0870 chi ∧
      PredecessorHalfFin13Atom0991 chi))) ∨
      ((PredecessorHalfFin13Atom2153 chi ∧
      ¬PredecessorHalfFin13Atom0858 chi) ∨
      ((PredecessorHalfFin13Atom2153 chi ∧
      ¬PredecessorHalfFin13Atom0859 chi) ∨
      (PredecessorHalfFin13Atom2153 chi ∧
      ¬PredecessorHalfFin13Atom0992 chi)))))) ∨
      (((((PredecessorHalfFin13Atom2154 chi ∧
      ¬PredecessorHalfFin13Atom0860 chi) ∨
      ((PredecessorHalfFin13Atom2154 chi ∧
      ¬PredecessorHalfFin13Atom0861 chi) ∨
      (PredecessorHalfFin13Atom2154 chi ∧
      ¬PredecessorHalfFin13Atom0863 chi))) ∨
      ((PredecessorHalfFin13Atom2154 chi ∧
      ¬PredecessorHalfFin13Atom0872 chi) ∨
      ((PredecessorHalfFin13Atom2154 chi ∧
      ¬PredecessorHalfFin13Atom0993 chi) ∨
      (¬PredecessorHalfFin13Atom2154 chi ∧
      PredecessorHalfFin13Atom0860 chi ∧
      PredecessorHalfFin13Atom0861 chi ∧
      PredecessorHalfFin13Atom0863 chi ∧
      PredecessorHalfFin13Atom0872 chi ∧
      PredecessorHalfFin13Atom0993 chi)))) ∨
      (((PredecessorHalfFin13Atom2155 chi ∧
      ¬PredecessorHalfFin13Atom0860 chi) ∨
      ((PredecessorHalfFin13Atom2155 chi ∧
      ¬PredecessorHalfFin13Atom0862 chi) ∨
      (PredecessorHalfFin13Atom2155 chi ∧
      ¬PredecessorHalfFin13Atom0864 chi))) ∨
      ((PredecessorHalfFin13Atom2155 chi ∧
      ¬PredecessorHalfFin13Atom0873 chi) ∨
      ((PredecessorHalfFin13Atom2155 chi ∧
      ¬PredecessorHalfFin13Atom0994 chi) ∨
      (¬PredecessorHalfFin13Atom2155 chi ∧
      PredecessorHalfFin13Atom0860 chi ∧
      PredecessorHalfFin13Atom0862 chi ∧
      PredecessorHalfFin13Atom0864 chi ∧
      PredecessorHalfFin13Atom0873 chi ∧
      PredecessorHalfFin13Atom0994 chi))))) ∨
      ((((PredecessorHalfFin13Atom2156 chi ∧
      ¬PredecessorHalfFin13Atom0862 chi) ∨
      ((PredecessorHalfFin13Atom2156 chi ∧
      ¬PredecessorHalfFin13Atom0865 chi) ∨
      (PredecessorHalfFin13Atom2156 chi ∧
      ¬PredecessorHalfFin13Atom0874 chi))) ∨
      ((PredecessorHalfFin13Atom2156 chi ∧
      ¬PredecessorHalfFin13Atom0995 chi) ∨
      ((PredecessorHalfFin13Atom2157 chi ∧
      ¬PredecessorHalfFin13Atom0864 chi) ∨
      (PredecessorHalfFin13Atom2157 chi ∧
      ¬PredecessorHalfFin13Atom0865 chi)))) ∨
      (((PredecessorHalfFin13Atom2157 chi ∧
      ¬PredecessorHalfFin13Atom0875 chi) ∨
      ((PredecessorHalfFin13Atom2157 chi ∧
      ¬PredecessorHalfFin13Atom0996 chi) ∨
      (PredecessorHalfFin13Atom2158 chi ∧
      ¬PredecessorHalfFin13Atom0866 chi))) ∨
      (((PredecessorHalfFin13Atom2158 chi ∧
      ¬PredecessorHalfFin13Atom0867 chi) ∨
      (PredecessorHalfFin13Atom2158 chi ∧
      ¬PredecessorHalfFin13Atom0869 chi)) ∨
      ((PredecessorHalfFin13Atom2158 chi ∧
      ¬PredecessorHalfFin13Atom0872 chi) ∨
      (PredecessorHalfFin13Atom2158 chi ∧
      ¬PredecessorHalfFin13Atom0997 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom2159 chi ∧
      ¬PredecessorHalfFin13Atom0866 chi) ∨
      ((PredecessorHalfFin13Atom2159 chi ∧
      ¬PredecessorHalfFin13Atom0868 chi) ∨
      (PredecessorHalfFin13Atom2159 chi ∧
      ¬PredecessorHalfFin13Atom0870 chi))) ∨
      ((PredecessorHalfFin13Atom2159 chi ∧
      ¬PredecessorHalfFin13Atom0873 chi) ∨
      ((PredecessorHalfFin13Atom2159 chi ∧
      ¬PredecessorHalfFin13Atom0998 chi) ∨
      (¬PredecessorHalfFin13Atom2159 chi ∧
      PredecessorHalfFin13Atom0866 chi ∧
      PredecessorHalfFin13Atom0868 chi ∧
      PredecessorHalfFin13Atom0870 chi ∧
      PredecessorHalfFin13Atom0873 chi ∧
      PredecessorHalfFin13Atom0998 chi)))) ∨
      (((PredecessorHalfFin13Atom2160 chi ∧
      ¬PredecessorHalfFin13Atom0867 chi) ∨
      ((PredecessorHalfFin13Atom2160 chi ∧
      ¬PredecessorHalfFin13Atom0868 chi) ∨
      (PredecessorHalfFin13Atom2160 chi ∧
      ¬PredecessorHalfFin13Atom0999 chi))) ∨
      ((PredecessorHalfFin13Atom2161 chi ∧
      ¬PredecessorHalfFin13Atom0869 chi) ∨
      ((PredecessorHalfFin13Atom2161 chi ∧
      ¬PredecessorHalfFin13Atom0870 chi) ∨
      (PredecessorHalfFin13Atom2161 chi ∧
      ¬PredecessorHalfFin13Atom0875 chi))))) ∨
      ((((PredecessorHalfFin13Atom2161 chi ∧
      ¬PredecessorHalfFin13Atom1000 chi) ∨
      ((PredecessorHalfFin13Atom2162 chi ∧
      ¬PredecessorHalfFin13Atom0872 chi) ∨
      (PredecessorHalfFin13Atom2162 chi ∧
      ¬PredecessorHalfFin13Atom0873 chi))) ∨
      ((PredecessorHalfFin13Atom2162 chi ∧
      ¬PredecessorHalfFin13Atom0874 chi) ∨
      ((PredecessorHalfFin13Atom2162 chi ∧
      ¬PredecessorHalfFin13Atom0875 chi) ∨
      (PredecessorHalfFin13Atom2163 chi ∧
      ¬PredecessorHalfFin13Atom0876 chi)))) ∨
      (((PredecessorHalfFin13Atom2163 chi ∧
      ¬PredecessorHalfFin13Atom0877 chi) ∨
      ((PredecessorHalfFin13Atom2163 chi ∧
      ¬PredecessorHalfFin13Atom0882 chi) ∨
      (PredecessorHalfFin13Atom2163 chi ∧
      ¬PredecessorHalfFin13Atom0897 chi))) ∨
      ((PredecessorHalfFin13Atom2163 chi ∧
      ¬PredecessorHalfFin13Atom0932 chi) ∨
      ((¬PredecessorHalfFin13Atom2163 chi ∧
      PredecessorHalfFin13Atom0876 chi ∧
      PredecessorHalfFin13Atom0877 chi ∧
      PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0897 chi ∧
      PredecessorHalfFin13Atom0932 chi) ∨
      (PredecessorHalfFin13Atom2164 chi ∧
      ¬PredecessorHalfFin13Atom0876 chi)))))) ∨
      (((((PredecessorHalfFin13Atom2164 chi ∧
      ¬PredecessorHalfFin13Atom0878 chi) ∨
      ((PredecessorHalfFin13Atom2164 chi ∧
      ¬PredecessorHalfFin13Atom0883 chi) ∨
      (PredecessorHalfFin13Atom2164 chi ∧
      ¬PredecessorHalfFin13Atom0898 chi))) ∨
      ((PredecessorHalfFin13Atom2164 chi ∧
      ¬PredecessorHalfFin13Atom0933 chi) ∨
      ((¬PredecessorHalfFin13Atom2164 chi ∧
      PredecessorHalfFin13Atom0876 chi ∧
      PredecessorHalfFin13Atom0878 chi ∧
      PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0898 chi ∧
      PredecessorHalfFin13Atom0933 chi) ∨
      (PredecessorHalfFin13Atom2165 chi ∧
      ¬PredecessorHalfFin13Atom0876 chi)))) ∨
      (((PredecessorHalfFin13Atom2165 chi ∧
      ¬PredecessorHalfFin13Atom0879 chi) ∨
      ((PredecessorHalfFin13Atom2165 chi ∧
      ¬PredecessorHalfFin13Atom0884 chi) ∨
      (PredecessorHalfFin13Atom2165 chi ∧
      ¬PredecessorHalfFin13Atom0899 chi))) ∨
      ((PredecessorHalfFin13Atom2165 chi ∧
      ¬PredecessorHalfFin13Atom0934 chi) ∨
      ((¬PredecessorHalfFin13Atom2165 chi ∧
      PredecessorHalfFin13Atom0876 chi ∧
      PredecessorHalfFin13Atom0879 chi ∧
      PredecessorHalfFin13Atom0884 chi ∧
      PredecessorHalfFin13Atom0899 chi ∧
      PredecessorHalfFin13Atom0934 chi) ∨
      (PredecessorHalfFin13Atom2166 chi ∧
      ¬PredecessorHalfFin13Atom0876 chi))))) ∨
      ((((PredecessorHalfFin13Atom2166 chi ∧
      ¬PredecessorHalfFin13Atom0880 chi) ∨
      ((PredecessorHalfFin13Atom2166 chi ∧
      ¬PredecessorHalfFin13Atom0885 chi) ∨
      (PredecessorHalfFin13Atom2166 chi ∧
      ¬PredecessorHalfFin13Atom0900 chi))) ∨
      ((PredecessorHalfFin13Atom2166 chi ∧
      ¬PredecessorHalfFin13Atom0935 chi) ∨
      ((PredecessorHalfFin13Atom2167 chi ∧
      ¬PredecessorHalfFin13Atom0876 chi) ∨
      (PredecessorHalfFin13Atom2167 chi ∧
      ¬PredecessorHalfFin13Atom0881 chi)))) ∨
      (((PredecessorHalfFin13Atom2167 chi ∧
      ¬PredecessorHalfFin13Atom0886 chi) ∨
      ((PredecessorHalfFin13Atom2167 chi ∧
      ¬PredecessorHalfFin13Atom0901 chi) ∨
      (PredecessorHalfFin13Atom2167 chi ∧
      ¬PredecessorHalfFin13Atom0936 chi))) ∨
      (((¬PredecessorHalfFin13Atom2167 chi ∧
      PredecessorHalfFin13Atom0876 chi ∧
      PredecessorHalfFin13Atom0881 chi ∧
      PredecessorHalfFin13Atom0886 chi ∧
      PredecessorHalfFin13Atom0901 chi ∧
      PredecessorHalfFin13Atom0936 chi) ∨
      (PredecessorHalfFin13Atom2168 chi ∧
      ¬PredecessorHalfFin13Atom0877 chi)) ∨
      ((PredecessorHalfFin13Atom2168 chi ∧
      ¬PredecessorHalfFin13Atom0878 chi) ∨
      (PredecessorHalfFin13Atom2168 chi ∧
      ¬PredecessorHalfFin13Atom0887 chi))))))))) := by
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
              exact predecessorHalfFin13_clause24045 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24046 chi hbad
              ·
                exact predecessorHalfFin13_clause24047 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24048 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24049 chi hbad
              ·
                exact predecessorHalfFin13_clause24050 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24051 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24052 chi hbad
              ·
                exact predecessorHalfFin13_clause24053 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24054 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24055 chi hbad
              ·
                exact predecessorHalfFin13_clause24056 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24057 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24058 chi hbad
              ·
                exact predecessorHalfFin13_clause24059 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24061 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24062 chi hbad
              ·
                exact predecessorHalfFin13_clause24063 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24064 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24065 chi hbad
              ·
                exact predecessorHalfFin13_clause24066 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24067 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24068 chi hbad
              ·
                exact predecessorHalfFin13_clause24071 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24073 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24074 chi hbad
              ·
                exact predecessorHalfFin13_clause24075 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24076 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24077 chi hbad
              ·
                exact predecessorHalfFin13_clause24078 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24079 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24080 chi hbad
              ·
                exact predecessorHalfFin13_clause24081 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24082 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24083 chi hbad
              ·
                exact predecessorHalfFin13_clause24084 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24086 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24087 chi hbad
              ·
                exact predecessorHalfFin13_clause24088 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24089 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24092 chi hbad
              ·
                exact predecessorHalfFin13_clause24093 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24094 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24095 chi hbad
              ·
                exact predecessorHalfFin13_clause24097 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24098 chi hbad
              ·
                exact predecessorHalfFin13_clause24099 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24100 chi hbad
              ·
                exact predecessorHalfFin13_clause24101 chi hbad
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
              exact predecessorHalfFin13_clause24103 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24104 chi hbad
              ·
                exact predecessorHalfFin13_clause24105 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24106 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24107 chi hbad
              ·
                exact predecessorHalfFin13_clause24108 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24109 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24110 chi hbad
              ·
                exact predecessorHalfFin13_clause24113 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24115 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24116 chi hbad
              ·
                exact predecessorHalfFin13_clause24118 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24119 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24121 chi hbad
              ·
                exact predecessorHalfFin13_clause24122 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24123 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24124 chi hbad
              ·
                exact predecessorHalfFin13_clause24127 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24128 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24129 chi hbad
              ·
                exact predecessorHalfFin13_clause24130 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24131 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24132 chi hbad
              ·
                exact predecessorHalfFin13_clause24133 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24134 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24135 chi hbad
              ·
                exact predecessorHalfFin13_clause24136 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24137 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24138 chi hbad
              ·
                exact predecessorHalfFin13_clause24139 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24140 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24141 chi hbad
              ·
                exact predecessorHalfFin13_clause24142 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24143 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24144 chi hbad
              ·
                exact predecessorHalfFin13_clause24145 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24146 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24147 chi hbad
              ·
                exact predecessorHalfFin13_clause24148 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24149 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24151 chi hbad
              ·
                exact predecessorHalfFin13_clause24152 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24153 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24154 chi hbad
              ·
                exact predecessorHalfFin13_clause24155 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24156 chi hbad
              ·
                exact predecessorHalfFin13_clause24157 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24158 chi hbad
              ·
                exact predecessorHalfFin13_clause24159 chi hbad

end ErdosSzekeres

end
