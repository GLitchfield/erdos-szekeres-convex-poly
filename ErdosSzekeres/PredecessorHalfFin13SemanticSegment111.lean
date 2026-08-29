module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk085
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk086

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 111. -/

theorem predecessorHalfFin13_rejectSemanticSegment111
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom2168 chi ∧
      ¬PredecessorHalfFin13Atom0902 chi) ∨
      ((PredecessorHalfFin13Atom2168 chi ∧
      ¬PredecessorHalfFin13Atom0937 chi) ∨
      (¬PredecessorHalfFin13Atom2168 chi ∧
      PredecessorHalfFin13Atom0877 chi ∧
      PredecessorHalfFin13Atom0878 chi ∧
      PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0902 chi ∧
      PredecessorHalfFin13Atom0937 chi))) ∨
      ((PredecessorHalfFin13Atom2169 chi ∧
      ¬PredecessorHalfFin13Atom0877 chi) ∨
      ((PredecessorHalfFin13Atom2169 chi ∧
      ¬PredecessorHalfFin13Atom0879 chi) ∨
      (PredecessorHalfFin13Atom2169 chi ∧
      ¬PredecessorHalfFin13Atom0888 chi)))) ∨
      (((PredecessorHalfFin13Atom2169 chi ∧
      ¬PredecessorHalfFin13Atom0903 chi) ∨
      ((PredecessorHalfFin13Atom2169 chi ∧
      ¬PredecessorHalfFin13Atom0938 chi) ∨
      (¬PredecessorHalfFin13Atom2169 chi ∧
      PredecessorHalfFin13Atom0877 chi ∧
      PredecessorHalfFin13Atom0879 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0938 chi))) ∨
      ((PredecessorHalfFin13Atom2170 chi ∧
      ¬PredecessorHalfFin13Atom0877 chi) ∨
      ((PredecessorHalfFin13Atom2170 chi ∧
      ¬PredecessorHalfFin13Atom0880 chi) ∨
      (PredecessorHalfFin13Atom2170 chi ∧
      ¬PredecessorHalfFin13Atom0889 chi))))) ∨
      ((((PredecessorHalfFin13Atom2170 chi ∧
      ¬PredecessorHalfFin13Atom0904 chi) ∨
      ((PredecessorHalfFin13Atom2170 chi ∧
      ¬PredecessorHalfFin13Atom0939 chi) ∨
      (¬PredecessorHalfFin13Atom2170 chi ∧
      PredecessorHalfFin13Atom0877 chi ∧
      PredecessorHalfFin13Atom0880 chi ∧
      PredecessorHalfFin13Atom0889 chi ∧
      PredecessorHalfFin13Atom0904 chi ∧
      PredecessorHalfFin13Atom0939 chi))) ∨
      ((PredecessorHalfFin13Atom2171 chi ∧
      ¬PredecessorHalfFin13Atom0877 chi) ∨
      ((PredecessorHalfFin13Atom2171 chi ∧
      ¬PredecessorHalfFin13Atom0881 chi) ∨
      (PredecessorHalfFin13Atom2171 chi ∧
      ¬PredecessorHalfFin13Atom0890 chi)))) ∨
      (((PredecessorHalfFin13Atom2171 chi ∧
      ¬PredecessorHalfFin13Atom0905 chi) ∨
      ((PredecessorHalfFin13Atom2171 chi ∧
      ¬PredecessorHalfFin13Atom0940 chi) ∨
      (¬PredecessorHalfFin13Atom2171 chi ∧
      PredecessorHalfFin13Atom0877 chi ∧
      PredecessorHalfFin13Atom0881 chi ∧
      PredecessorHalfFin13Atom0890 chi ∧
      PredecessorHalfFin13Atom0905 chi ∧
      PredecessorHalfFin13Atom0940 chi))) ∨
      ((PredecessorHalfFin13Atom2172 chi ∧
      ¬PredecessorHalfFin13Atom0878 chi) ∨
      ((PredecessorHalfFin13Atom2172 chi ∧
      ¬PredecessorHalfFin13Atom0879 chi) ∨
      (PredecessorHalfFin13Atom2172 chi ∧
      ¬PredecessorHalfFin13Atom0891 chi)))))) ∨
      (((((PredecessorHalfFin13Atom2172 chi ∧
      ¬PredecessorHalfFin13Atom0906 chi) ∨
      ((PredecessorHalfFin13Atom2172 chi ∧
      ¬PredecessorHalfFin13Atom0941 chi) ∨
      (¬PredecessorHalfFin13Atom2172 chi ∧
      PredecessorHalfFin13Atom0878 chi ∧
      PredecessorHalfFin13Atom0879 chi ∧
      PredecessorHalfFin13Atom0891 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0941 chi))) ∨
      ((PredecessorHalfFin13Atom2173 chi ∧
      ¬PredecessorHalfFin13Atom0878 chi) ∨
      ((PredecessorHalfFin13Atom2173 chi ∧
      ¬PredecessorHalfFin13Atom0880 chi) ∨
      (PredecessorHalfFin13Atom2173 chi ∧
      ¬PredecessorHalfFin13Atom0892 chi)))) ∨
      (((PredecessorHalfFin13Atom2173 chi ∧
      ¬PredecessorHalfFin13Atom0907 chi) ∨
      ((PredecessorHalfFin13Atom2173 chi ∧
      ¬PredecessorHalfFin13Atom0942 chi) ∨
      (PredecessorHalfFin13Atom2174 chi ∧
      ¬PredecessorHalfFin13Atom0878 chi))) ∨
      ((PredecessorHalfFin13Atom2174 chi ∧
      ¬PredecessorHalfFin13Atom0881 chi) ∨
      ((PredecessorHalfFin13Atom2174 chi ∧
      ¬PredecessorHalfFin13Atom0893 chi) ∨
      (PredecessorHalfFin13Atom2174 chi ∧
      ¬PredecessorHalfFin13Atom0908 chi))))) ∨
      ((((PredecessorHalfFin13Atom2174 chi ∧
      ¬PredecessorHalfFin13Atom0943 chi) ∨
      ((¬PredecessorHalfFin13Atom2174 chi ∧
      PredecessorHalfFin13Atom0878 chi ∧
      PredecessorHalfFin13Atom0881 chi ∧
      PredecessorHalfFin13Atom0893 chi ∧
      PredecessorHalfFin13Atom0908 chi ∧
      PredecessorHalfFin13Atom0943 chi) ∨
      (PredecessorHalfFin13Atom2175 chi ∧
      ¬PredecessorHalfFin13Atom0879 chi))) ∨
      ((PredecessorHalfFin13Atom2175 chi ∧
      ¬PredecessorHalfFin13Atom0880 chi) ∨
      ((PredecessorHalfFin13Atom2175 chi ∧
      ¬PredecessorHalfFin13Atom0894 chi) ∨
      (PredecessorHalfFin13Atom2175 chi ∧
      ¬PredecessorHalfFin13Atom0909 chi)))) ∨
      (((PredecessorHalfFin13Atom2175 chi ∧
      ¬PredecessorHalfFin13Atom0944 chi) ∨
      ((¬PredecessorHalfFin13Atom2175 chi ∧
      PredecessorHalfFin13Atom0879 chi ∧
      PredecessorHalfFin13Atom0880 chi ∧
      PredecessorHalfFin13Atom0894 chi ∧
      PredecessorHalfFin13Atom0909 chi ∧
      PredecessorHalfFin13Atom0944 chi) ∨
      (PredecessorHalfFin13Atom2176 chi ∧
      ¬PredecessorHalfFin13Atom0879 chi))) ∨
      (((PredecessorHalfFin13Atom2176 chi ∧
      ¬PredecessorHalfFin13Atom0881 chi) ∨
      (PredecessorHalfFin13Atom2176 chi ∧
      ¬PredecessorHalfFin13Atom0895 chi)) ∨
      ((PredecessorHalfFin13Atom2176 chi ∧
      ¬PredecessorHalfFin13Atom0910 chi) ∨
      (PredecessorHalfFin13Atom2176 chi ∧
      ¬PredecessorHalfFin13Atom0945 chi))))))) ∨
      ((((((¬PredecessorHalfFin13Atom2176 chi ∧
      PredecessorHalfFin13Atom0879 chi ∧
      PredecessorHalfFin13Atom0881 chi ∧
      PredecessorHalfFin13Atom0895 chi ∧
      PredecessorHalfFin13Atom0910 chi ∧
      PredecessorHalfFin13Atom0945 chi) ∨
      ((PredecessorHalfFin13Atom2177 chi ∧
      ¬PredecessorHalfFin13Atom0880 chi) ∨
      (PredecessorHalfFin13Atom2177 chi ∧
      ¬PredecessorHalfFin13Atom0881 chi))) ∨
      ((PredecessorHalfFin13Atom2177 chi ∧
      ¬PredecessorHalfFin13Atom0896 chi) ∨
      ((PredecessorHalfFin13Atom2177 chi ∧
      ¬PredecessorHalfFin13Atom0911 chi) ∨
      (PredecessorHalfFin13Atom2177 chi ∧
      ¬PredecessorHalfFin13Atom0946 chi)))) ∨
      (((PredecessorHalfFin13Atom2178 chi ∧
      ¬PredecessorHalfFin13Atom0882 chi) ∨
      ((PredecessorHalfFin13Atom2178 chi ∧
      ¬PredecessorHalfFin13Atom0883 chi) ∨
      (PredecessorHalfFin13Atom2178 chi ∧
      ¬PredecessorHalfFin13Atom0887 chi))) ∨
      ((PredecessorHalfFin13Atom2178 chi ∧
      ¬PredecessorHalfFin13Atom0912 chi) ∨
      ((PredecessorHalfFin13Atom2178 chi ∧
      ¬PredecessorHalfFin13Atom0947 chi) ∨
      (¬PredecessorHalfFin13Atom2178 chi ∧
      PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0947 chi))))) ∨
      ((((PredecessorHalfFin13Atom2179 chi ∧
      ¬PredecessorHalfFin13Atom0882 chi) ∨
      ((PredecessorHalfFin13Atom2179 chi ∧
      ¬PredecessorHalfFin13Atom0884 chi) ∨
      (PredecessorHalfFin13Atom2179 chi ∧
      ¬PredecessorHalfFin13Atom0888 chi))) ∨
      ((PredecessorHalfFin13Atom2179 chi ∧
      ¬PredecessorHalfFin13Atom0913 chi) ∨
      ((PredecessorHalfFin13Atom2179 chi ∧
      ¬PredecessorHalfFin13Atom0948 chi) ∨
      (¬PredecessorHalfFin13Atom2179 chi ∧
      PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0884 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0913 chi ∧
      PredecessorHalfFin13Atom0948 chi)))) ∨
      (((PredecessorHalfFin13Atom2180 chi ∧
      ¬PredecessorHalfFin13Atom0882 chi) ∨
      ((PredecessorHalfFin13Atom2180 chi ∧
      ¬PredecessorHalfFin13Atom0885 chi) ∨
      (PredecessorHalfFin13Atom2180 chi ∧
      ¬PredecessorHalfFin13Atom0889 chi))) ∨
      (((PredecessorHalfFin13Atom2180 chi ∧
      ¬PredecessorHalfFin13Atom0914 chi) ∨
      (PredecessorHalfFin13Atom2180 chi ∧
      ¬PredecessorHalfFin13Atom0949 chi)) ∨
      ((¬PredecessorHalfFin13Atom2180 chi ∧
      PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0885 chi ∧
      PredecessorHalfFin13Atom0889 chi ∧
      PredecessorHalfFin13Atom0914 chi ∧
      PredecessorHalfFin13Atom0949 chi) ∨
      (PredecessorHalfFin13Atom2181 chi ∧
      ¬PredecessorHalfFin13Atom0882 chi)))))) ∨
      (((((PredecessorHalfFin13Atom2181 chi ∧
      ¬PredecessorHalfFin13Atom0886 chi) ∨
      ((PredecessorHalfFin13Atom2181 chi ∧
      ¬PredecessorHalfFin13Atom0890 chi) ∨
      (PredecessorHalfFin13Atom2181 chi ∧
      ¬PredecessorHalfFin13Atom0915 chi))) ∨
      ((PredecessorHalfFin13Atom2181 chi ∧
      ¬PredecessorHalfFin13Atom0950 chi) ∨
      ((¬PredecessorHalfFin13Atom2181 chi ∧
      PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0886 chi ∧
      PredecessorHalfFin13Atom0890 chi ∧
      PredecessorHalfFin13Atom0915 chi ∧
      PredecessorHalfFin13Atom0950 chi) ∨
      (PredecessorHalfFin13Atom2182 chi ∧
      ¬PredecessorHalfFin13Atom0883 chi)))) ∨
      (((PredecessorHalfFin13Atom2182 chi ∧
      ¬PredecessorHalfFin13Atom0884 chi) ∨
      ((PredecessorHalfFin13Atom2182 chi ∧
      ¬PredecessorHalfFin13Atom0891 chi) ∨
      (PredecessorHalfFin13Atom2182 chi ∧
      ¬PredecessorHalfFin13Atom0916 chi))) ∨
      ((PredecessorHalfFin13Atom2182 chi ∧
      ¬PredecessorHalfFin13Atom0951 chi) ∨
      ((¬PredecessorHalfFin13Atom2182 chi ∧
      PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0884 chi ∧
      PredecessorHalfFin13Atom0891 chi ∧
      PredecessorHalfFin13Atom0916 chi ∧
      PredecessorHalfFin13Atom0951 chi) ∨
      (PredecessorHalfFin13Atom2183 chi ∧
      ¬PredecessorHalfFin13Atom0883 chi))))) ∨
      ((((PredecessorHalfFin13Atom2183 chi ∧
      ¬PredecessorHalfFin13Atom0885 chi) ∨
      ((PredecessorHalfFin13Atom2183 chi ∧
      ¬PredecessorHalfFin13Atom0892 chi) ∨
      (PredecessorHalfFin13Atom2183 chi ∧
      ¬PredecessorHalfFin13Atom0917 chi))) ∨
      ((PredecessorHalfFin13Atom2183 chi ∧
      ¬PredecessorHalfFin13Atom0952 chi) ∨
      ((¬PredecessorHalfFin13Atom2183 chi ∧
      PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0885 chi ∧
      PredecessorHalfFin13Atom0892 chi ∧
      PredecessorHalfFin13Atom0917 chi ∧
      PredecessorHalfFin13Atom0952 chi) ∨
      (PredecessorHalfFin13Atom2184 chi ∧
      ¬PredecessorHalfFin13Atom0883 chi)))) ∨
      (((PredecessorHalfFin13Atom2184 chi ∧
      ¬PredecessorHalfFin13Atom0886 chi) ∨
      ((PredecessorHalfFin13Atom2184 chi ∧
      ¬PredecessorHalfFin13Atom0893 chi) ∨
      (PredecessorHalfFin13Atom2184 chi ∧
      ¬PredecessorHalfFin13Atom0918 chi))) ∨
      (((PredecessorHalfFin13Atom2184 chi ∧
      ¬PredecessorHalfFin13Atom0953 chi) ∨
      (¬PredecessorHalfFin13Atom2184 chi ∧
      PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0886 chi ∧
      PredecessorHalfFin13Atom0893 chi ∧
      PredecessorHalfFin13Atom0918 chi ∧
      PredecessorHalfFin13Atom0953 chi)) ∨
      ((PredecessorHalfFin13Atom2185 chi ∧
      ¬PredecessorHalfFin13Atom0884 chi) ∨
      (PredecessorHalfFin13Atom2185 chi ∧
      ¬PredecessorHalfFin13Atom0885 chi))))))))) := by
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
              exact predecessorHalfFin13_clause24160 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24161 chi hbad
              ·
                exact predecessorHalfFin13_clause24162 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24163 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24164 chi hbad
              ·
                exact predecessorHalfFin13_clause24165 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24166 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24167 chi hbad
              ·
                exact predecessorHalfFin13_clause24168 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24169 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24170 chi hbad
              ·
                exact predecessorHalfFin13_clause24171 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24172 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24173 chi hbad
              ·
                exact predecessorHalfFin13_clause24174 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24175 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24176 chi hbad
              ·
                exact predecessorHalfFin13_clause24177 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24178 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24179 chi hbad
              ·
                exact predecessorHalfFin13_clause24180 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24181 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24182 chi hbad
              ·
                exact predecessorHalfFin13_clause24183 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24184 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24185 chi hbad
              ·
                exact predecessorHalfFin13_clause24186 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24187 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24188 chi hbad
              ·
                exact predecessorHalfFin13_clause24189 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24190 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24191 chi hbad
              ·
                exact predecessorHalfFin13_clause24193 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24194 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24195 chi hbad
              ·
                exact predecessorHalfFin13_clause24196 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24197 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24198 chi hbad
              ·
                exact predecessorHalfFin13_clause24199 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24200 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24201 chi hbad
              ·
                exact predecessorHalfFin13_clause24202 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24203 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24204 chi hbad
              ·
                exact predecessorHalfFin13_clause24205 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24206 chi hbad
              ·
                exact predecessorHalfFin13_clause24207 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24208 chi hbad
              ·
                exact predecessorHalfFin13_clause24209 chi hbad
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
              exact predecessorHalfFin13_clause24210 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24211 chi hbad
              ·
                exact predecessorHalfFin13_clause24212 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24213 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24214 chi hbad
              ·
                exact predecessorHalfFin13_clause24215 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24217 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24218 chi hbad
              ·
                exact predecessorHalfFin13_clause24219 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24220 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24221 chi hbad
              ·
                exact predecessorHalfFin13_clause24222 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24223 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24224 chi hbad
              ·
                exact predecessorHalfFin13_clause24225 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24226 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24227 chi hbad
              ·
                exact predecessorHalfFin13_clause24228 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24229 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24230 chi hbad
              ·
                exact predecessorHalfFin13_clause24231 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24232 chi hbad
              ·
                exact predecessorHalfFin13_clause24233 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24234 chi hbad
              ·
                exact predecessorHalfFin13_clause24235 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24236 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24237 chi hbad
              ·
                exact predecessorHalfFin13_clause24238 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24239 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24240 chi hbad
              ·
                exact predecessorHalfFin13_clause24241 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24242 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24243 chi hbad
              ·
                exact predecessorHalfFin13_clause24244 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24245 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24246 chi hbad
              ·
                exact predecessorHalfFin13_clause24247 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24248 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24249 chi hbad
              ·
                exact predecessorHalfFin13_clause24250 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24251 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24252 chi hbad
              ·
                exact predecessorHalfFin13_clause24253 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24254 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24255 chi hbad
              ·
                exact predecessorHalfFin13_clause24256 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24257 chi hbad
              ·
                exact predecessorHalfFin13_clause24258 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24259 chi hbad
              ·
                exact predecessorHalfFin13_clause24260 chi hbad

end ErdosSzekeres

end
