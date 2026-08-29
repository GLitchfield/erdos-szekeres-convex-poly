module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk086
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk087

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 113. -/

theorem predecessorHalfFin13_rejectSemanticSegment113
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom2203 chi ∧
      ¬PredecessorHalfFin13Atom0917 chi) ∨
      ((PredecessorHalfFin13Atom2203 chi ∧
      ¬PredecessorHalfFin13Atom0972 chi) ∨
      (¬PredecessorHalfFin13Atom2203 chi ∧
      PredecessorHalfFin13Atom0898 chi ∧
      PredecessorHalfFin13Atom0900 chi ∧
      PredecessorHalfFin13Atom0907 chi ∧
      PredecessorHalfFin13Atom0917 chi ∧
      PredecessorHalfFin13Atom0972 chi))) ∨
      ((PredecessorHalfFin13Atom2204 chi ∧
      ¬PredecessorHalfFin13Atom0898 chi) ∨
      ((PredecessorHalfFin13Atom2204 chi ∧
      ¬PredecessorHalfFin13Atom0901 chi) ∨
      (PredecessorHalfFin13Atom2204 chi ∧
      ¬PredecessorHalfFin13Atom0908 chi)))) ∨
      (((PredecessorHalfFin13Atom2204 chi ∧
      ¬PredecessorHalfFin13Atom0918 chi) ∨
      ((PredecessorHalfFin13Atom2204 chi ∧
      ¬PredecessorHalfFin13Atom0973 chi) ∨
      (¬PredecessorHalfFin13Atom2204 chi ∧
      PredecessorHalfFin13Atom0898 chi ∧
      PredecessorHalfFin13Atom0901 chi ∧
      PredecessorHalfFin13Atom0908 chi ∧
      PredecessorHalfFin13Atom0918 chi ∧
      PredecessorHalfFin13Atom0973 chi))) ∨
      ((PredecessorHalfFin13Atom2205 chi ∧
      ¬PredecessorHalfFin13Atom0899 chi) ∨
      ((PredecessorHalfFin13Atom2205 chi ∧
      ¬PredecessorHalfFin13Atom0900 chi) ∨
      (PredecessorHalfFin13Atom2205 chi ∧
      ¬PredecessorHalfFin13Atom0909 chi))))) ∨
      ((((PredecessorHalfFin13Atom2205 chi ∧
      ¬PredecessorHalfFin13Atom0919 chi) ∨
      ((PredecessorHalfFin13Atom2205 chi ∧
      ¬PredecessorHalfFin13Atom0974 chi) ∨
      (¬PredecessorHalfFin13Atom2205 chi ∧
      PredecessorHalfFin13Atom0899 chi ∧
      PredecessorHalfFin13Atom0900 chi ∧
      PredecessorHalfFin13Atom0909 chi ∧
      PredecessorHalfFin13Atom0919 chi ∧
      PredecessorHalfFin13Atom0974 chi))) ∨
      ((PredecessorHalfFin13Atom2206 chi ∧
      ¬PredecessorHalfFin13Atom0899 chi) ∨
      ((PredecessorHalfFin13Atom2206 chi ∧
      ¬PredecessorHalfFin13Atom0901 chi) ∨
      (PredecessorHalfFin13Atom2206 chi ∧
      ¬PredecessorHalfFin13Atom0910 chi)))) ∨
      (((PredecessorHalfFin13Atom2206 chi ∧
      ¬PredecessorHalfFin13Atom0920 chi) ∨
      ((PredecessorHalfFin13Atom2206 chi ∧
      ¬PredecessorHalfFin13Atom0975 chi) ∨
      (¬PredecessorHalfFin13Atom2206 chi ∧
      PredecessorHalfFin13Atom0899 chi ∧
      PredecessorHalfFin13Atom0901 chi ∧
      PredecessorHalfFin13Atom0910 chi ∧
      PredecessorHalfFin13Atom0920 chi ∧
      PredecessorHalfFin13Atom0975 chi))) ∨
      ((PredecessorHalfFin13Atom2207 chi ∧
      ¬PredecessorHalfFin13Atom0900 chi) ∨
      ((PredecessorHalfFin13Atom2207 chi ∧
      ¬PredecessorHalfFin13Atom0901 chi) ∨
      (PredecessorHalfFin13Atom2207 chi ∧
      ¬PredecessorHalfFin13Atom0921 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom2207 chi ∧
      PredecessorHalfFin13Atom0900 chi ∧
      PredecessorHalfFin13Atom0901 chi ∧
      PredecessorHalfFin13Atom0911 chi ∧
      PredecessorHalfFin13Atom0921 chi ∧
      PredecessorHalfFin13Atom0976 chi) ∨
      ((PredecessorHalfFin13Atom2208 chi ∧
      ¬PredecessorHalfFin13Atom0902 chi) ∨
      (PredecessorHalfFin13Atom2208 chi ∧
      ¬PredecessorHalfFin13Atom0903 chi))) ∨
      ((PredecessorHalfFin13Atom2208 chi ∧
      ¬PredecessorHalfFin13Atom0906 chi) ∨
      ((PredecessorHalfFin13Atom2208 chi ∧
      ¬PredecessorHalfFin13Atom0922 chi) ∨
      (PredecessorHalfFin13Atom2208 chi ∧
      ¬PredecessorHalfFin13Atom0977 chi)))) ∨
      (((¬PredecessorHalfFin13Atom2208 chi ∧
      PredecessorHalfFin13Atom0902 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0922 chi ∧
      PredecessorHalfFin13Atom0977 chi) ∨
      ((PredecessorHalfFin13Atom2209 chi ∧
      ¬PredecessorHalfFin13Atom0902 chi) ∨
      (PredecessorHalfFin13Atom2209 chi ∧
      ¬PredecessorHalfFin13Atom0904 chi))) ∨
      ((PredecessorHalfFin13Atom2209 chi ∧
      ¬PredecessorHalfFin13Atom0907 chi) ∨
      ((PredecessorHalfFin13Atom2209 chi ∧
      ¬PredecessorHalfFin13Atom0923 chi) ∨
      (PredecessorHalfFin13Atom2209 chi ∧
      ¬PredecessorHalfFin13Atom0978 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom2209 chi ∧
      PredecessorHalfFin13Atom0902 chi ∧
      PredecessorHalfFin13Atom0904 chi ∧
      PredecessorHalfFin13Atom0907 chi ∧
      PredecessorHalfFin13Atom0923 chi ∧
      PredecessorHalfFin13Atom0978 chi) ∨
      ((PredecessorHalfFin13Atom2210 chi ∧
      ¬PredecessorHalfFin13Atom0902 chi) ∨
      (PredecessorHalfFin13Atom2210 chi ∧
      ¬PredecessorHalfFin13Atom0905 chi))) ∨
      ((PredecessorHalfFin13Atom2210 chi ∧
      ¬PredecessorHalfFin13Atom0908 chi) ∨
      ((PredecessorHalfFin13Atom2210 chi ∧
      ¬PredecessorHalfFin13Atom0924 chi) ∨
      (PredecessorHalfFin13Atom2210 chi ∧
      ¬PredecessorHalfFin13Atom0979 chi)))) ∨
      (((¬PredecessorHalfFin13Atom2210 chi ∧
      PredecessorHalfFin13Atom0902 chi ∧
      PredecessorHalfFin13Atom0905 chi ∧
      PredecessorHalfFin13Atom0908 chi ∧
      PredecessorHalfFin13Atom0924 chi ∧
      PredecessorHalfFin13Atom0979 chi) ∨
      ((PredecessorHalfFin13Atom2211 chi ∧
      ¬PredecessorHalfFin13Atom0903 chi) ∨
      (PredecessorHalfFin13Atom2211 chi ∧
      ¬PredecessorHalfFin13Atom0904 chi))) ∨
      (((PredecessorHalfFin13Atom2211 chi ∧
      ¬PredecessorHalfFin13Atom0909 chi) ∨
      (PredecessorHalfFin13Atom2211 chi ∧
      ¬PredecessorHalfFin13Atom0925 chi)) ∨
      ((PredecessorHalfFin13Atom2211 chi ∧
      ¬PredecessorHalfFin13Atom0980 chi) ∨
      (¬PredecessorHalfFin13Atom2211 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0904 chi ∧
      PredecessorHalfFin13Atom0909 chi ∧
      PredecessorHalfFin13Atom0925 chi ∧
      PredecessorHalfFin13Atom0980 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom2212 chi ∧
      ¬PredecessorHalfFin13Atom0903 chi) ∨
      ((PredecessorHalfFin13Atom2212 chi ∧
      ¬PredecessorHalfFin13Atom0905 chi) ∨
      (PredecessorHalfFin13Atom2212 chi ∧
      ¬PredecessorHalfFin13Atom0910 chi))) ∨
      ((PredecessorHalfFin13Atom2212 chi ∧
      ¬PredecessorHalfFin13Atom0926 chi) ∨
      ((PredecessorHalfFin13Atom2212 chi ∧
      ¬PredecessorHalfFin13Atom0981 chi) ∨
      (¬PredecessorHalfFin13Atom2212 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0905 chi ∧
      PredecessorHalfFin13Atom0910 chi ∧
      PredecessorHalfFin13Atom0926 chi ∧
      PredecessorHalfFin13Atom0981 chi)))) ∨
      (((PredecessorHalfFin13Atom2213 chi ∧
      ¬PredecessorHalfFin13Atom0904 chi) ∨
      ((PredecessorHalfFin13Atom2213 chi ∧
      ¬PredecessorHalfFin13Atom0905 chi) ∨
      (PredecessorHalfFin13Atom2213 chi ∧
      ¬PredecessorHalfFin13Atom0982 chi))) ∨
      ((PredecessorHalfFin13Atom2214 chi ∧
      ¬PredecessorHalfFin13Atom0906 chi) ∨
      ((PredecessorHalfFin13Atom2214 chi ∧
      ¬PredecessorHalfFin13Atom0907 chi) ∨
      (PredecessorHalfFin13Atom2214 chi ∧
      ¬PredecessorHalfFin13Atom0909 chi))))) ∨
      ((((PredecessorHalfFin13Atom2214 chi ∧
      ¬PredecessorHalfFin13Atom0928 chi) ∨
      ((PredecessorHalfFin13Atom2214 chi ∧
      ¬PredecessorHalfFin13Atom0983 chi) ∨
      (¬PredecessorHalfFin13Atom2214 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0907 chi ∧
      PredecessorHalfFin13Atom0909 chi ∧
      PredecessorHalfFin13Atom0928 chi ∧
      PredecessorHalfFin13Atom0983 chi))) ∨
      ((PredecessorHalfFin13Atom2215 chi ∧
      ¬PredecessorHalfFin13Atom0906 chi) ∨
      ((PredecessorHalfFin13Atom2215 chi ∧
      ¬PredecessorHalfFin13Atom0908 chi) ∨
      (PredecessorHalfFin13Atom2215 chi ∧
      ¬PredecessorHalfFin13Atom0910 chi)))) ∨
      (((PredecessorHalfFin13Atom2215 chi ∧
      ¬PredecessorHalfFin13Atom0929 chi) ∨
      ((PredecessorHalfFin13Atom2215 chi ∧
      ¬PredecessorHalfFin13Atom0984 chi) ∨
      (¬PredecessorHalfFin13Atom2215 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0908 chi ∧
      PredecessorHalfFin13Atom0910 chi ∧
      PredecessorHalfFin13Atom0929 chi ∧
      PredecessorHalfFin13Atom0984 chi))) ∨
      ((PredecessorHalfFin13Atom2216 chi ∧
      ¬PredecessorHalfFin13Atom0908 chi) ∨
      ((PredecessorHalfFin13Atom2216 chi ∧
      ¬PredecessorHalfFin13Atom0930 chi) ∨
      (PredecessorHalfFin13Atom2216 chi ∧
      ¬PredecessorHalfFin13Atom0985 chi)))))) ∨
      (((((PredecessorHalfFin13Atom2217 chi ∧
      ¬PredecessorHalfFin13Atom0909 chi) ∨
      ((PredecessorHalfFin13Atom2217 chi ∧
      ¬PredecessorHalfFin13Atom0910 chi) ∨
      (PredecessorHalfFin13Atom2217 chi ∧
      ¬PredecessorHalfFin13Atom0931 chi))) ∨
      ((PredecessorHalfFin13Atom2217 chi ∧
      ¬PredecessorHalfFin13Atom0986 chi) ∨
      ((PredecessorHalfFin13Atom2218 chi ∧
      ¬PredecessorHalfFin13Atom0912 chi) ∨
      (PredecessorHalfFin13Atom2218 chi ∧
      ¬PredecessorHalfFin13Atom0913 chi)))) ∨
      (((PredecessorHalfFin13Atom2218 chi ∧
      ¬PredecessorHalfFin13Atom0916 chi) ∨
      ((PredecessorHalfFin13Atom2218 chi ∧
      ¬PredecessorHalfFin13Atom0922 chi) ∨
      (PredecessorHalfFin13Atom2218 chi ∧
      ¬PredecessorHalfFin13Atom0987 chi))) ∨
      ((¬PredecessorHalfFin13Atom2218 chi ∧
      PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0913 chi ∧
      PredecessorHalfFin13Atom0916 chi ∧
      PredecessorHalfFin13Atom0922 chi ∧
      PredecessorHalfFin13Atom0987 chi) ∨
      ((PredecessorHalfFin13Atom2219 chi ∧
      ¬PredecessorHalfFin13Atom0912 chi) ∨
      (PredecessorHalfFin13Atom2219 chi ∧
      ¬PredecessorHalfFin13Atom0914 chi))))) ∨
      ((((PredecessorHalfFin13Atom2219 chi ∧
      ¬PredecessorHalfFin13Atom0917 chi) ∨
      ((PredecessorHalfFin13Atom2219 chi ∧
      ¬PredecessorHalfFin13Atom0923 chi) ∨
      (PredecessorHalfFin13Atom2219 chi ∧
      ¬PredecessorHalfFin13Atom0988 chi))) ∨
      ((¬PredecessorHalfFin13Atom2219 chi ∧
      PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0914 chi ∧
      PredecessorHalfFin13Atom0917 chi ∧
      PredecessorHalfFin13Atom0923 chi ∧
      PredecessorHalfFin13Atom0988 chi) ∨
      ((PredecessorHalfFin13Atom2220 chi ∧
      ¬PredecessorHalfFin13Atom0912 chi) ∨
      (PredecessorHalfFin13Atom2220 chi ∧
      ¬PredecessorHalfFin13Atom0915 chi)))) ∨
      (((PredecessorHalfFin13Atom2220 chi ∧
      ¬PredecessorHalfFin13Atom0918 chi) ∨
      ((PredecessorHalfFin13Atom2220 chi ∧
      ¬PredecessorHalfFin13Atom0924 chi) ∨
      (PredecessorHalfFin13Atom2220 chi ∧
      ¬PredecessorHalfFin13Atom0989 chi))) ∨
      (((¬PredecessorHalfFin13Atom2220 chi ∧
      PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0915 chi ∧
      PredecessorHalfFin13Atom0918 chi ∧
      PredecessorHalfFin13Atom0924 chi ∧
      PredecessorHalfFin13Atom0989 chi) ∨
      (PredecessorHalfFin13Atom2221 chi ∧
      ¬PredecessorHalfFin13Atom0913 chi)) ∨
      ((PredecessorHalfFin13Atom2221 chi ∧
      ¬PredecessorHalfFin13Atom0914 chi) ∨
      (PredecessorHalfFin13Atom2221 chi ∧
      ¬PredecessorHalfFin13Atom0919 chi))))))))) := by
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
              exact predecessorHalfFin13_clause24370 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24371 chi hbad
              ·
                exact predecessorHalfFin13_clause24372 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24373 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24374 chi hbad
              ·
                exact predecessorHalfFin13_clause24375 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24376 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24377 chi hbad
              ·
                exact predecessorHalfFin13_clause24378 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24379 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24380 chi hbad
              ·
                exact predecessorHalfFin13_clause24381 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24382 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24383 chi hbad
              ·
                exact predecessorHalfFin13_clause24384 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24385 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24386 chi hbad
              ·
                exact predecessorHalfFin13_clause24387 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24388 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24389 chi hbad
              ·
                exact predecessorHalfFin13_clause24390 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24391 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24392 chi hbad
              ·
                exact predecessorHalfFin13_clause24394 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24396 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24397 chi hbad
              ·
                exact predecessorHalfFin13_clause24398 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24399 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24400 chi hbad
              ·
                exact predecessorHalfFin13_clause24401 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24402 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24403 chi hbad
              ·
                exact predecessorHalfFin13_clause24404 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24405 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24406 chi hbad
              ·
                exact predecessorHalfFin13_clause24407 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24408 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24409 chi hbad
              ·
                exact predecessorHalfFin13_clause24410 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24411 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24412 chi hbad
              ·
                exact predecessorHalfFin13_clause24413 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24414 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24415 chi hbad
              ·
                exact predecessorHalfFin13_clause24416 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24417 chi hbad
              ·
                exact predecessorHalfFin13_clause24418 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24419 chi hbad
              ·
                exact predecessorHalfFin13_clause24420 chi hbad
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
              exact predecessorHalfFin13_clause24421 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24422 chi hbad
              ·
                exact predecessorHalfFin13_clause24423 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24424 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24425 chi hbad
              ·
                exact predecessorHalfFin13_clause24426 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24427 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24428 chi hbad
              ·
                exact predecessorHalfFin13_clause24431 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24433 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24434 chi hbad
              ·
                exact predecessorHalfFin13_clause24435 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24436 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24437 chi hbad
              ·
                exact predecessorHalfFin13_clause24438 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24439 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24440 chi hbad
              ·
                exact predecessorHalfFin13_clause24441 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24442 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24443 chi hbad
              ·
                exact predecessorHalfFin13_clause24444 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24446 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24448 chi hbad
              ·
                exact predecessorHalfFin13_clause24449 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24451 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24452 chi hbad
              ·
                exact predecessorHalfFin13_clause24454 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24455 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24457 chi hbad
              ·
                exact predecessorHalfFin13_clause24458 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24459 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24460 chi hbad
              ·
                exact predecessorHalfFin13_clause24461 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24462 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24463 chi hbad
              ·
                exact predecessorHalfFin13_clause24464 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24465 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24466 chi hbad
              ·
                exact predecessorHalfFin13_clause24467 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24468 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24469 chi hbad
              ·
                exact predecessorHalfFin13_clause24470 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24471 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24472 chi hbad
              ·
                exact predecessorHalfFin13_clause24473 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24474 chi hbad
              ·
                exact predecessorHalfFin13_clause24475 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24476 chi hbad
              ·
                exact predecessorHalfFin13_clause24477 chi hbad

end ErdosSzekeres

end
