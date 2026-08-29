module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk086

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 112. -/

theorem predecessorHalfFin13_rejectSemanticSegment112
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom2185 chi ∧
      ¬PredecessorHalfFin13Atom0894 chi) ∨
      ((PredecessorHalfFin13Atom2185 chi ∧
      ¬PredecessorHalfFin13Atom0919 chi) ∨
      (PredecessorHalfFin13Atom2185 chi ∧
      ¬PredecessorHalfFin13Atom0954 chi))) ∨
      ((PredecessorHalfFin13Atom2186 chi ∧
      ¬PredecessorHalfFin13Atom0884 chi) ∨
      ((PredecessorHalfFin13Atom2186 chi ∧
      ¬PredecessorHalfFin13Atom0886 chi) ∨
      (PredecessorHalfFin13Atom2186 chi ∧
      ¬PredecessorHalfFin13Atom0895 chi)))) ∨
      (((PredecessorHalfFin13Atom2186 chi ∧
      ¬PredecessorHalfFin13Atom0920 chi) ∨
      ((PredecessorHalfFin13Atom2186 chi ∧
      ¬PredecessorHalfFin13Atom0955 chi) ∨
      (¬PredecessorHalfFin13Atom2186 chi ∧
      PredecessorHalfFin13Atom0884 chi ∧
      PredecessorHalfFin13Atom0886 chi ∧
      PredecessorHalfFin13Atom0895 chi ∧
      PredecessorHalfFin13Atom0920 chi ∧
      PredecessorHalfFin13Atom0955 chi))) ∨
      ((PredecessorHalfFin13Atom2187 chi ∧
      ¬PredecessorHalfFin13Atom0886 chi) ∨
      ((PredecessorHalfFin13Atom2187 chi ∧
      ¬PredecessorHalfFin13Atom0921 chi) ∨
      (PredecessorHalfFin13Atom2187 chi ∧
      ¬PredecessorHalfFin13Atom0956 chi))))) ∨
      ((((PredecessorHalfFin13Atom2188 chi ∧
      ¬PredecessorHalfFin13Atom0887 chi) ∨
      ((PredecessorHalfFin13Atom2188 chi ∧
      ¬PredecessorHalfFin13Atom0888 chi) ∨
      (PredecessorHalfFin13Atom2188 chi ∧
      ¬PredecessorHalfFin13Atom0891 chi))) ∨
      ((PredecessorHalfFin13Atom2188 chi ∧
      ¬PredecessorHalfFin13Atom0922 chi) ∨
      ((PredecessorHalfFin13Atom2188 chi ∧
      ¬PredecessorHalfFin13Atom0957 chi) ∨
      (¬PredecessorHalfFin13Atom2188 chi ∧
      PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0891 chi ∧
      PredecessorHalfFin13Atom0922 chi ∧
      PredecessorHalfFin13Atom0957 chi)))) ∨
      (((PredecessorHalfFin13Atom2189 chi ∧
      ¬PredecessorHalfFin13Atom0887 chi) ∨
      ((PredecessorHalfFin13Atom2189 chi ∧
      ¬PredecessorHalfFin13Atom0889 chi) ∨
      (PredecessorHalfFin13Atom2189 chi ∧
      ¬PredecessorHalfFin13Atom0892 chi))) ∨
      ((PredecessorHalfFin13Atom2189 chi ∧
      ¬PredecessorHalfFin13Atom0923 chi) ∨
      ((PredecessorHalfFin13Atom2189 chi ∧
      ¬PredecessorHalfFin13Atom0958 chi) ∨
      (¬PredecessorHalfFin13Atom2189 chi ∧
      PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0889 chi ∧
      PredecessorHalfFin13Atom0892 chi ∧
      PredecessorHalfFin13Atom0923 chi ∧
      PredecessorHalfFin13Atom0958 chi)))))) ∨
      (((((PredecessorHalfFin13Atom2190 chi ∧
      ¬PredecessorHalfFin13Atom0887 chi) ∨
      ((PredecessorHalfFin13Atom2190 chi ∧
      ¬PredecessorHalfFin13Atom0890 chi) ∨
      (PredecessorHalfFin13Atom2190 chi ∧
      ¬PredecessorHalfFin13Atom0893 chi))) ∨
      ((PredecessorHalfFin13Atom2190 chi ∧
      ¬PredecessorHalfFin13Atom0924 chi) ∨
      ((PredecessorHalfFin13Atom2190 chi ∧
      ¬PredecessorHalfFin13Atom0959 chi) ∨
      (¬PredecessorHalfFin13Atom2190 chi ∧
      PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0890 chi ∧
      PredecessorHalfFin13Atom0893 chi ∧
      PredecessorHalfFin13Atom0924 chi ∧
      PredecessorHalfFin13Atom0959 chi)))) ∨
      (((PredecessorHalfFin13Atom2191 chi ∧
      ¬PredecessorHalfFin13Atom0888 chi) ∨
      ((PredecessorHalfFin13Atom2191 chi ∧
      ¬PredecessorHalfFin13Atom0889 chi) ∨
      (PredecessorHalfFin13Atom2191 chi ∧
      ¬PredecessorHalfFin13Atom0894 chi))) ∨
      ((PredecessorHalfFin13Atom2191 chi ∧
      ¬PredecessorHalfFin13Atom0925 chi) ∨
      ((PredecessorHalfFin13Atom2191 chi ∧
      ¬PredecessorHalfFin13Atom0960 chi) ∨
      (¬PredecessorHalfFin13Atom2191 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0889 chi ∧
      PredecessorHalfFin13Atom0894 chi ∧
      PredecessorHalfFin13Atom0925 chi ∧
      PredecessorHalfFin13Atom0960 chi))))) ∨
      ((((PredecessorHalfFin13Atom2192 chi ∧
      ¬PredecessorHalfFin13Atom0888 chi) ∨
      ((PredecessorHalfFin13Atom2192 chi ∧
      ¬PredecessorHalfFin13Atom0890 chi) ∨
      (PredecessorHalfFin13Atom2192 chi ∧
      ¬PredecessorHalfFin13Atom0895 chi))) ∨
      ((PredecessorHalfFin13Atom2192 chi ∧
      ¬PredecessorHalfFin13Atom0926 chi) ∨
      ((PredecessorHalfFin13Atom2192 chi ∧
      ¬PredecessorHalfFin13Atom0961 chi) ∨
      (¬PredecessorHalfFin13Atom2192 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0890 chi ∧
      PredecessorHalfFin13Atom0895 chi ∧
      PredecessorHalfFin13Atom0926 chi ∧
      PredecessorHalfFin13Atom0961 chi)))) ∨
      (((PredecessorHalfFin13Atom2193 chi ∧
      ¬PredecessorHalfFin13Atom0890 chi) ∨
      ((PredecessorHalfFin13Atom2193 chi ∧
      ¬PredecessorHalfFin13Atom0927 chi) ∨
      (PredecessorHalfFin13Atom2193 chi ∧
      ¬PredecessorHalfFin13Atom0962 chi))) ∨
      (((PredecessorHalfFin13Atom2194 chi ∧
      ¬PredecessorHalfFin13Atom0891 chi) ∨
      (PredecessorHalfFin13Atom2194 chi ∧
      ¬PredecessorHalfFin13Atom0892 chi)) ∨
      ((PredecessorHalfFin13Atom2194 chi ∧
      ¬PredecessorHalfFin13Atom0894 chi) ∨
      (PredecessorHalfFin13Atom2194 chi ∧
      ¬PredecessorHalfFin13Atom0928 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom2194 chi ∧
      ¬PredecessorHalfFin13Atom0963 chi) ∨
      ((PredecessorHalfFin13Atom2195 chi ∧
      ¬PredecessorHalfFin13Atom0891 chi) ∨
      (PredecessorHalfFin13Atom2195 chi ∧
      ¬PredecessorHalfFin13Atom0893 chi))) ∨
      ((PredecessorHalfFin13Atom2195 chi ∧
      ¬PredecessorHalfFin13Atom0895 chi) ∨
      ((PredecessorHalfFin13Atom2195 chi ∧
      ¬PredecessorHalfFin13Atom0929 chi) ∨
      (PredecessorHalfFin13Atom2195 chi ∧
      ¬PredecessorHalfFin13Atom0964 chi)))) ∨
      (((¬PredecessorHalfFin13Atom2195 chi ∧
      PredecessorHalfFin13Atom0891 chi ∧
      PredecessorHalfFin13Atom0893 chi ∧
      PredecessorHalfFin13Atom0895 chi ∧
      PredecessorHalfFin13Atom0929 chi ∧
      PredecessorHalfFin13Atom0964 chi) ∨
      ((PredecessorHalfFin13Atom2196 chi ∧
      ¬PredecessorHalfFin13Atom0892 chi) ∨
      (PredecessorHalfFin13Atom2196 chi ∧
      ¬PredecessorHalfFin13Atom0893 chi))) ∨
      ((PredecessorHalfFin13Atom2196 chi ∧
      ¬PredecessorHalfFin13Atom0930 chi) ∨
      ((PredecessorHalfFin13Atom2196 chi ∧
      ¬PredecessorHalfFin13Atom0965 chi) ∨
      (¬PredecessorHalfFin13Atom2196 chi ∧
      PredecessorHalfFin13Atom0892 chi ∧
      PredecessorHalfFin13Atom0893 chi ∧
      PredecessorHalfFin13Atom0896 chi ∧
      PredecessorHalfFin13Atom0930 chi ∧
      PredecessorHalfFin13Atom0965 chi))))) ∨
      ((((PredecessorHalfFin13Atom2197 chi ∧
      ¬PredecessorHalfFin13Atom0894 chi) ∨
      ((PredecessorHalfFin13Atom2197 chi ∧
      ¬PredecessorHalfFin13Atom0895 chi) ∨
      (PredecessorHalfFin13Atom2197 chi ∧
      ¬PredecessorHalfFin13Atom0931 chi))) ∨
      ((PredecessorHalfFin13Atom2197 chi ∧
      ¬PredecessorHalfFin13Atom0966 chi) ∨
      ((PredecessorHalfFin13Atom2198 chi ∧
      ¬PredecessorHalfFin13Atom0897 chi) ∨
      (PredecessorHalfFin13Atom2198 chi ∧
      ¬PredecessorHalfFin13Atom0898 chi)))) ∨
      (((PredecessorHalfFin13Atom2198 chi ∧
      ¬PredecessorHalfFin13Atom0902 chi) ∨
      ((PredecessorHalfFin13Atom2198 chi ∧
      ¬PredecessorHalfFin13Atom0912 chi) ∨
      (PredecessorHalfFin13Atom2198 chi ∧
      ¬PredecessorHalfFin13Atom0967 chi))) ∨
      ((¬PredecessorHalfFin13Atom2198 chi ∧
      PredecessorHalfFin13Atom0897 chi ∧
      PredecessorHalfFin13Atom0898 chi ∧
      PredecessorHalfFin13Atom0902 chi ∧
      PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0967 chi) ∨
      ((PredecessorHalfFin13Atom2199 chi ∧
      ¬PredecessorHalfFin13Atom0897 chi) ∨
      (PredecessorHalfFin13Atom2199 chi ∧
      ¬PredecessorHalfFin13Atom0899 chi)))))) ∨
      (((((PredecessorHalfFin13Atom2199 chi ∧
      ¬PredecessorHalfFin13Atom0903 chi) ∨
      ((PredecessorHalfFin13Atom2199 chi ∧
      ¬PredecessorHalfFin13Atom0913 chi) ∨
      (PredecessorHalfFin13Atom2199 chi ∧
      ¬PredecessorHalfFin13Atom0968 chi))) ∨
      ((¬PredecessorHalfFin13Atom2199 chi ∧
      PredecessorHalfFin13Atom0897 chi ∧
      PredecessorHalfFin13Atom0899 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0913 chi ∧
      PredecessorHalfFin13Atom0968 chi) ∨
      ((PredecessorHalfFin13Atom2200 chi ∧
      ¬PredecessorHalfFin13Atom0897 chi) ∨
      (PredecessorHalfFin13Atom2200 chi ∧
      ¬PredecessorHalfFin13Atom0900 chi)))) ∨
      (((PredecessorHalfFin13Atom2200 chi ∧
      ¬PredecessorHalfFin13Atom0904 chi) ∨
      ((PredecessorHalfFin13Atom2200 chi ∧
      ¬PredecessorHalfFin13Atom0914 chi) ∨
      (PredecessorHalfFin13Atom2200 chi ∧
      ¬PredecessorHalfFin13Atom0969 chi))) ∨
      ((¬PredecessorHalfFin13Atom2200 chi ∧
      PredecessorHalfFin13Atom0897 chi ∧
      PredecessorHalfFin13Atom0900 chi ∧
      PredecessorHalfFin13Atom0904 chi ∧
      PredecessorHalfFin13Atom0914 chi ∧
      PredecessorHalfFin13Atom0969 chi) ∨
      ((PredecessorHalfFin13Atom2201 chi ∧
      ¬PredecessorHalfFin13Atom0897 chi) ∨
      (PredecessorHalfFin13Atom2201 chi ∧
      ¬PredecessorHalfFin13Atom0901 chi))))) ∨
      ((((PredecessorHalfFin13Atom2201 chi ∧
      ¬PredecessorHalfFin13Atom0905 chi) ∨
      ((PredecessorHalfFin13Atom2201 chi ∧
      ¬PredecessorHalfFin13Atom0915 chi) ∨
      (PredecessorHalfFin13Atom2201 chi ∧
      ¬PredecessorHalfFin13Atom0970 chi))) ∨
      ((¬PredecessorHalfFin13Atom2201 chi ∧
      PredecessorHalfFin13Atom0897 chi ∧
      PredecessorHalfFin13Atom0901 chi ∧
      PredecessorHalfFin13Atom0905 chi ∧
      PredecessorHalfFin13Atom0915 chi ∧
      PredecessorHalfFin13Atom0970 chi) ∨
      ((PredecessorHalfFin13Atom2202 chi ∧
      ¬PredecessorHalfFin13Atom0898 chi) ∨
      (PredecessorHalfFin13Atom2202 chi ∧
      ¬PredecessorHalfFin13Atom0899 chi)))) ∨
      (((PredecessorHalfFin13Atom2202 chi ∧
      ¬PredecessorHalfFin13Atom0906 chi) ∨
      ((PredecessorHalfFin13Atom2202 chi ∧
      ¬PredecessorHalfFin13Atom0916 chi) ∨
      (PredecessorHalfFin13Atom2202 chi ∧
      ¬PredecessorHalfFin13Atom0971 chi))) ∨
      (((¬PredecessorHalfFin13Atom2202 chi ∧
      PredecessorHalfFin13Atom0898 chi ∧
      PredecessorHalfFin13Atom0899 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0916 chi ∧
      PredecessorHalfFin13Atom0971 chi) ∨
      (PredecessorHalfFin13Atom2203 chi ∧
      ¬PredecessorHalfFin13Atom0898 chi)) ∨
      ((PredecessorHalfFin13Atom2203 chi ∧
      ¬PredecessorHalfFin13Atom0900 chi) ∨
      (PredecessorHalfFin13Atom2203 chi ∧
      ¬PredecessorHalfFin13Atom0907 chi))))))))) := by
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
              exact predecessorHalfFin13_clause24261 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24262 chi hbad
              ·
                exact predecessorHalfFin13_clause24263 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24265 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24266 chi hbad
              ·
                exact predecessorHalfFin13_clause24267 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24268 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24269 chi hbad
              ·
                exact predecessorHalfFin13_clause24270 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24272 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24274 chi hbad
              ·
                exact predecessorHalfFin13_clause24275 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24277 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24278 chi hbad
              ·
                exact predecessorHalfFin13_clause24279 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24280 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24281 chi hbad
              ·
                exact predecessorHalfFin13_clause24282 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24283 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24284 chi hbad
              ·
                exact predecessorHalfFin13_clause24285 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24286 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24287 chi hbad
              ·
                exact predecessorHalfFin13_clause24288 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24289 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24290 chi hbad
              ·
                exact predecessorHalfFin13_clause24291 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24292 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24293 chi hbad
              ·
                exact predecessorHalfFin13_clause24294 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24295 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24296 chi hbad
              ·
                exact predecessorHalfFin13_clause24297 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24298 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24299 chi hbad
              ·
                exact predecessorHalfFin13_clause24300 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24301 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24302 chi hbad
              ·
                exact predecessorHalfFin13_clause24303 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24304 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24305 chi hbad
              ·
                exact predecessorHalfFin13_clause24306 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24308 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24310 chi hbad
              ·
                exact predecessorHalfFin13_clause24311 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24313 chi hbad
              ·
                exact predecessorHalfFin13_clause24314 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24315 chi hbad
              ·
                exact predecessorHalfFin13_clause24316 chi hbad
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
              exact predecessorHalfFin13_clause24317 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24319 chi hbad
              ·
                exact predecessorHalfFin13_clause24320 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24321 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24322 chi hbad
              ·
                exact predecessorHalfFin13_clause24323 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24324 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24325 chi hbad
              ·
                exact predecessorHalfFin13_clause24326 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24328 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24329 chi hbad
              ·
                exact predecessorHalfFin13_clause24330 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24331 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24332 chi hbad
              ·
                exact predecessorHalfFin13_clause24334 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24335 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24337 chi hbad
              ·
                exact predecessorHalfFin13_clause24338 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24339 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24340 chi hbad
              ·
                exact predecessorHalfFin13_clause24341 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24342 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24343 chi hbad
              ·
                exact predecessorHalfFin13_clause24344 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24345 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24346 chi hbad
              ·
                exact predecessorHalfFin13_clause24347 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24348 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24349 chi hbad
              ·
                exact predecessorHalfFin13_clause24350 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24351 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24352 chi hbad
              ·
                exact predecessorHalfFin13_clause24353 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24354 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24355 chi hbad
              ·
                exact predecessorHalfFin13_clause24356 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24357 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24358 chi hbad
              ·
                exact predecessorHalfFin13_clause24359 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24360 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24361 chi hbad
              ·
                exact predecessorHalfFin13_clause24362 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24363 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24364 chi hbad
              ·
                exact predecessorHalfFin13_clause24365 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24366 chi hbad
              ·
                exact predecessorHalfFin13_clause24367 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24368 chi hbad
              ·
                exact predecessorHalfFin13_clause24369 chi hbad

end ErdosSzekeres

end
