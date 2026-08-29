module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk087
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk088

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 114. -/

theorem predecessorHalfFin13_rejectSemanticSegment114
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom2221 chi ∧
      ¬PredecessorHalfFin13Atom0925 chi) ∨
      ((PredecessorHalfFin13Atom2221 chi ∧
      ¬PredecessorHalfFin13Atom0990 chi) ∨
      (PredecessorHalfFin13Atom2222 chi ∧
      ¬PredecessorHalfFin13Atom0913 chi))) ∨
      ((PredecessorHalfFin13Atom2222 chi ∧
      ¬PredecessorHalfFin13Atom0915 chi) ∨
      ((PredecessorHalfFin13Atom2222 chi ∧
      ¬PredecessorHalfFin13Atom0920 chi) ∨
      (PredecessorHalfFin13Atom2222 chi ∧
      ¬PredecessorHalfFin13Atom0926 chi)))) ∨
      (((PredecessorHalfFin13Atom2222 chi ∧
      ¬PredecessorHalfFin13Atom0991 chi) ∨
      ((¬PredecessorHalfFin13Atom2222 chi ∧
      PredecessorHalfFin13Atom0913 chi ∧
      PredecessorHalfFin13Atom0915 chi ∧
      PredecessorHalfFin13Atom0920 chi ∧
      PredecessorHalfFin13Atom0926 chi ∧
      PredecessorHalfFin13Atom0991 chi) ∨
      (PredecessorHalfFin13Atom2223 chi ∧
      ¬PredecessorHalfFin13Atom0914 chi))) ∨
      ((PredecessorHalfFin13Atom2223 chi ∧
      ¬PredecessorHalfFin13Atom0915 chi) ∨
      ((PredecessorHalfFin13Atom2223 chi ∧
      ¬PredecessorHalfFin13Atom0927 chi) ∨
      (PredecessorHalfFin13Atom2223 chi ∧
      ¬PredecessorHalfFin13Atom0992 chi))))) ∨
      ((((PredecessorHalfFin13Atom2224 chi ∧
      ¬PredecessorHalfFin13Atom0916 chi) ∨
      ((PredecessorHalfFin13Atom2224 chi ∧
      ¬PredecessorHalfFin13Atom0917 chi) ∨
      (PredecessorHalfFin13Atom2224 chi ∧
      ¬PredecessorHalfFin13Atom0919 chi))) ∨
      ((PredecessorHalfFin13Atom2224 chi ∧
      ¬PredecessorHalfFin13Atom0928 chi) ∨
      ((PredecessorHalfFin13Atom2224 chi ∧
      ¬PredecessorHalfFin13Atom0993 chi) ∨
      (¬PredecessorHalfFin13Atom2224 chi ∧
      PredecessorHalfFin13Atom0916 chi ∧
      PredecessorHalfFin13Atom0917 chi ∧
      PredecessorHalfFin13Atom0919 chi ∧
      PredecessorHalfFin13Atom0928 chi ∧
      PredecessorHalfFin13Atom0993 chi)))) ∨
      (((PredecessorHalfFin13Atom2225 chi ∧
      ¬PredecessorHalfFin13Atom0916 chi) ∨
      ((PredecessorHalfFin13Atom2225 chi ∧
      ¬PredecessorHalfFin13Atom0918 chi) ∨
      (PredecessorHalfFin13Atom2225 chi ∧
      ¬PredecessorHalfFin13Atom0920 chi))) ∨
      ((PredecessorHalfFin13Atom2225 chi ∧
      ¬PredecessorHalfFin13Atom0929 chi) ∨
      ((PredecessorHalfFin13Atom2225 chi ∧
      ¬PredecessorHalfFin13Atom0994 chi) ∨
      (¬PredecessorHalfFin13Atom2225 chi ∧
      PredecessorHalfFin13Atom0916 chi ∧
      PredecessorHalfFin13Atom0918 chi ∧
      PredecessorHalfFin13Atom0920 chi ∧
      PredecessorHalfFin13Atom0929 chi ∧
      PredecessorHalfFin13Atom0994 chi)))))) ∨
      (((((PredecessorHalfFin13Atom2226 chi ∧
      ¬PredecessorHalfFin13Atom0917 chi) ∨
      ((PredecessorHalfFin13Atom2226 chi ∧
      ¬PredecessorHalfFin13Atom0918 chi) ∨
      (PredecessorHalfFin13Atom2226 chi ∧
      ¬PredecessorHalfFin13Atom0921 chi))) ∨
      ((PredecessorHalfFin13Atom2226 chi ∧
      ¬PredecessorHalfFin13Atom0930 chi) ∨
      ((PredecessorHalfFin13Atom2226 chi ∧
      ¬PredecessorHalfFin13Atom0995 chi) ∨
      (¬PredecessorHalfFin13Atom2226 chi ∧
      PredecessorHalfFin13Atom0917 chi ∧
      PredecessorHalfFin13Atom0918 chi ∧
      PredecessorHalfFin13Atom0921 chi ∧
      PredecessorHalfFin13Atom0930 chi ∧
      PredecessorHalfFin13Atom0995 chi)))) ∨
      (((PredecessorHalfFin13Atom2227 chi ∧
      ¬PredecessorHalfFin13Atom0920 chi) ∨
      ((PredecessorHalfFin13Atom2227 chi ∧
      ¬PredecessorHalfFin13Atom0921 chi) ∨
      (PredecessorHalfFin13Atom2227 chi ∧
      ¬PredecessorHalfFin13Atom0931 chi))) ∨
      ((PredecessorHalfFin13Atom2227 chi ∧
      ¬PredecessorHalfFin13Atom0996 chi) ∨
      ((PredecessorHalfFin13Atom2228 chi ∧
      ¬PredecessorHalfFin13Atom0922 chi) ∨
      (PredecessorHalfFin13Atom2228 chi ∧
      ¬PredecessorHalfFin13Atom0923 chi))))) ∨
      ((((PredecessorHalfFin13Atom2228 chi ∧
      ¬PredecessorHalfFin13Atom0925 chi) ∨
      ((PredecessorHalfFin13Atom2228 chi ∧
      ¬PredecessorHalfFin13Atom0928 chi) ∨
      (PredecessorHalfFin13Atom2228 chi ∧
      ¬PredecessorHalfFin13Atom0997 chi))) ∨
      ((PredecessorHalfFin13Atom2229 chi ∧
      ¬PredecessorHalfFin13Atom0922 chi) ∨
      ((PredecessorHalfFin13Atom2229 chi ∧
      ¬PredecessorHalfFin13Atom0924 chi) ∨
      (PredecessorHalfFin13Atom2229 chi ∧
      ¬PredecessorHalfFin13Atom0926 chi)))) ∨
      (((PredecessorHalfFin13Atom2229 chi ∧
      ¬PredecessorHalfFin13Atom0929 chi) ∨
      ((PredecessorHalfFin13Atom2229 chi ∧
      ¬PredecessorHalfFin13Atom0998 chi) ∨
      (¬PredecessorHalfFin13Atom2229 chi ∧
      PredecessorHalfFin13Atom0922 chi ∧
      PredecessorHalfFin13Atom0924 chi ∧
      PredecessorHalfFin13Atom0926 chi ∧
      PredecessorHalfFin13Atom0929 chi ∧
      PredecessorHalfFin13Atom0998 chi))) ∨
      (((PredecessorHalfFin13Atom2230 chi ∧
      ¬PredecessorHalfFin13Atom0923 chi) ∨
      (PredecessorHalfFin13Atom2230 chi ∧
      ¬PredecessorHalfFin13Atom0924 chi)) ∨
      ((PredecessorHalfFin13Atom2230 chi ∧
      ¬PredecessorHalfFin13Atom0930 chi) ∨
      (PredecessorHalfFin13Atom2230 chi ∧
      ¬PredecessorHalfFin13Atom0999 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom2231 chi ∧
      ¬PredecessorHalfFin13Atom0925 chi) ∨
      ((PredecessorHalfFin13Atom2231 chi ∧
      ¬PredecessorHalfFin13Atom0926 chi) ∨
      (PredecessorHalfFin13Atom2231 chi ∧
      ¬PredecessorHalfFin13Atom0931 chi))) ∨
      ((PredecessorHalfFin13Atom2231 chi ∧
      ¬PredecessorHalfFin13Atom1000 chi) ∨
      ((PredecessorHalfFin13Atom2232 chi ∧
      ¬PredecessorHalfFin13Atom0928 chi) ∨
      (PredecessorHalfFin13Atom2232 chi ∧
      ¬PredecessorHalfFin13Atom0929 chi)))) ∨
      (((PredecessorHalfFin13Atom2232 chi ∧
      ¬PredecessorHalfFin13Atom0930 chi) ∨
      ((PredecessorHalfFin13Atom2232 chi ∧
      ¬PredecessorHalfFin13Atom0931 chi) ∨
      (PredecessorHalfFin13Atom2233 chi ∧
      ¬PredecessorHalfFin13Atom0932 chi))) ∨
      ((PredecessorHalfFin13Atom2233 chi ∧
      ¬PredecessorHalfFin13Atom0933 chi) ∨
      ((PredecessorHalfFin13Atom2233 chi ∧
      ¬PredecessorHalfFin13Atom0937 chi) ∨
      (PredecessorHalfFin13Atom2233 chi ∧
      ¬PredecessorHalfFin13Atom0947 chi))))) ∨
      ((((PredecessorHalfFin13Atom2233 chi ∧
      ¬PredecessorHalfFin13Atom0967 chi) ∨
      ((¬PredecessorHalfFin13Atom2233 chi ∧
      PredecessorHalfFin13Atom0932 chi ∧
      PredecessorHalfFin13Atom0933 chi ∧
      PredecessorHalfFin13Atom0937 chi ∧
      PredecessorHalfFin13Atom0947 chi ∧
      PredecessorHalfFin13Atom0967 chi) ∨
      (PredecessorHalfFin13Atom2234 chi ∧
      ¬PredecessorHalfFin13Atom0932 chi))) ∨
      ((PredecessorHalfFin13Atom2234 chi ∧
      ¬PredecessorHalfFin13Atom0934 chi) ∨
      ((PredecessorHalfFin13Atom2234 chi ∧
      ¬PredecessorHalfFin13Atom0938 chi) ∨
      (PredecessorHalfFin13Atom2234 chi ∧
      ¬PredecessorHalfFin13Atom0948 chi)))) ∨
      (((PredecessorHalfFin13Atom2234 chi ∧
      ¬PredecessorHalfFin13Atom0968 chi) ∨
      ((¬PredecessorHalfFin13Atom2234 chi ∧
      PredecessorHalfFin13Atom0932 chi ∧
      PredecessorHalfFin13Atom0934 chi ∧
      PredecessorHalfFin13Atom0938 chi ∧
      PredecessorHalfFin13Atom0948 chi ∧
      PredecessorHalfFin13Atom0968 chi) ∨
      (PredecessorHalfFin13Atom2235 chi ∧
      ¬PredecessorHalfFin13Atom0932 chi))) ∨
      ((PredecessorHalfFin13Atom2235 chi ∧
      ¬PredecessorHalfFin13Atom0935 chi) ∨
      ((PredecessorHalfFin13Atom2235 chi ∧
      ¬PredecessorHalfFin13Atom0939 chi) ∨
      (PredecessorHalfFin13Atom2235 chi ∧
      ¬PredecessorHalfFin13Atom0949 chi)))))) ∨
      (((((PredecessorHalfFin13Atom2235 chi ∧
      ¬PredecessorHalfFin13Atom0969 chi) ∨
      ((¬PredecessorHalfFin13Atom2235 chi ∧
      PredecessorHalfFin13Atom0932 chi ∧
      PredecessorHalfFin13Atom0935 chi ∧
      PredecessorHalfFin13Atom0939 chi ∧
      PredecessorHalfFin13Atom0949 chi ∧
      PredecessorHalfFin13Atom0969 chi) ∨
      (PredecessorHalfFin13Atom2236 chi ∧
      ¬PredecessorHalfFin13Atom0932 chi))) ∨
      ((PredecessorHalfFin13Atom2236 chi ∧
      ¬PredecessorHalfFin13Atom0936 chi) ∨
      ((PredecessorHalfFin13Atom2236 chi ∧
      ¬PredecessorHalfFin13Atom0940 chi) ∨
      (PredecessorHalfFin13Atom2236 chi ∧
      ¬PredecessorHalfFin13Atom0950 chi)))) ∨
      (((PredecessorHalfFin13Atom2236 chi ∧
      ¬PredecessorHalfFin13Atom0970 chi) ∨
      ((¬PredecessorHalfFin13Atom2236 chi ∧
      PredecessorHalfFin13Atom0932 chi ∧
      PredecessorHalfFin13Atom0936 chi ∧
      PredecessorHalfFin13Atom0940 chi ∧
      PredecessorHalfFin13Atom0950 chi ∧
      PredecessorHalfFin13Atom0970 chi) ∨
      (PredecessorHalfFin13Atom2237 chi ∧
      ¬PredecessorHalfFin13Atom0933 chi))) ∨
      ((PredecessorHalfFin13Atom2237 chi ∧
      ¬PredecessorHalfFin13Atom0934 chi) ∨
      ((PredecessorHalfFin13Atom2237 chi ∧
      ¬PredecessorHalfFin13Atom0941 chi) ∨
      (PredecessorHalfFin13Atom2237 chi ∧
      ¬PredecessorHalfFin13Atom0951 chi))))) ∨
      ((((PredecessorHalfFin13Atom2237 chi ∧
      ¬PredecessorHalfFin13Atom0971 chi) ∨
      ((¬PredecessorHalfFin13Atom2237 chi ∧
      PredecessorHalfFin13Atom0933 chi ∧
      PredecessorHalfFin13Atom0934 chi ∧
      PredecessorHalfFin13Atom0941 chi ∧
      PredecessorHalfFin13Atom0951 chi ∧
      PredecessorHalfFin13Atom0971 chi) ∨
      (PredecessorHalfFin13Atom2238 chi ∧
      ¬PredecessorHalfFin13Atom0933 chi))) ∨
      ((PredecessorHalfFin13Atom2238 chi ∧
      ¬PredecessorHalfFin13Atom0935 chi) ∨
      ((PredecessorHalfFin13Atom2238 chi ∧
      ¬PredecessorHalfFin13Atom0942 chi) ∨
      (PredecessorHalfFin13Atom2238 chi ∧
      ¬PredecessorHalfFin13Atom0952 chi)))) ∨
      (((PredecessorHalfFin13Atom2238 chi ∧
      ¬PredecessorHalfFin13Atom0972 chi) ∨
      ((PredecessorHalfFin13Atom2239 chi ∧
      ¬PredecessorHalfFin13Atom0933 chi) ∨
      (PredecessorHalfFin13Atom2239 chi ∧
      ¬PredecessorHalfFin13Atom0936 chi))) ∨
      (((PredecessorHalfFin13Atom2239 chi ∧
      ¬PredecessorHalfFin13Atom0943 chi) ∨
      (PredecessorHalfFin13Atom2239 chi ∧
      ¬PredecessorHalfFin13Atom0953 chi)) ∨
      ((PredecessorHalfFin13Atom2239 chi ∧
      ¬PredecessorHalfFin13Atom0973 chi) ∨
      (¬PredecessorHalfFin13Atom2239 chi ∧
      PredecessorHalfFin13Atom0933 chi ∧
      PredecessorHalfFin13Atom0936 chi ∧
      PredecessorHalfFin13Atom0943 chi ∧
      PredecessorHalfFin13Atom0953 chi ∧
      PredecessorHalfFin13Atom0973 chi))))))))) := by
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
              exact predecessorHalfFin13_clause24478 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24479 chi hbad
              ·
                exact predecessorHalfFin13_clause24481 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24482 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24483 chi hbad
              ·
                exact predecessorHalfFin13_clause24484 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24485 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24486 chi hbad
              ·
                exact predecessorHalfFin13_clause24487 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24488 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24490 chi hbad
              ·
                exact predecessorHalfFin13_clause24491 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24493 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24494 chi hbad
              ·
                exact predecessorHalfFin13_clause24495 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24496 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24497 chi hbad
              ·
                exact predecessorHalfFin13_clause24498 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24499 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24500 chi hbad
              ·
                exact predecessorHalfFin13_clause24501 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24502 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24503 chi hbad
              ·
                exact predecessorHalfFin13_clause24504 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24505 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24506 chi hbad
              ·
                exact predecessorHalfFin13_clause24507 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24508 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24509 chi hbad
              ·
                exact predecessorHalfFin13_clause24510 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24512 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24513 chi hbad
              ·
                exact predecessorHalfFin13_clause24514 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24515 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24517 chi hbad
              ·
                exact predecessorHalfFin13_clause24518 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24519 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24520 chi hbad
              ·
                exact predecessorHalfFin13_clause24521 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24523 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24524 chi hbad
              ·
                exact predecessorHalfFin13_clause24525 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24526 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24527 chi hbad
              ·
                exact predecessorHalfFin13_clause24528 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24529 chi hbad
              ·
                exact predecessorHalfFin13_clause24530 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24532 chi hbad
              ·
                exact predecessorHalfFin13_clause24533 chi hbad
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
              exact predecessorHalfFin13_clause24535 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24536 chi hbad
              ·
                exact predecessorHalfFin13_clause24538 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24539 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24541 chi hbad
              ·
                exact predecessorHalfFin13_clause24542 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24543 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24544 chi hbad
              ·
                exact predecessorHalfFin13_clause24547 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24548 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24549 chi hbad
              ·
                exact predecessorHalfFin13_clause24550 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24551 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24552 chi hbad
              ·
                exact predecessorHalfFin13_clause24553 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24554 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24555 chi hbad
              ·
                exact predecessorHalfFin13_clause24556 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24557 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24558 chi hbad
              ·
                exact predecessorHalfFin13_clause24559 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24560 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24561 chi hbad
              ·
                exact predecessorHalfFin13_clause24562 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24563 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24564 chi hbad
              ·
                exact predecessorHalfFin13_clause24565 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24566 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24567 chi hbad
              ·
                exact predecessorHalfFin13_clause24568 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24569 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24570 chi hbad
              ·
                exact predecessorHalfFin13_clause24571 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24572 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24573 chi hbad
              ·
                exact predecessorHalfFin13_clause24574 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24575 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24576 chi hbad
              ·
                exact predecessorHalfFin13_clause24577 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24578 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24579 chi hbad
              ·
                exact predecessorHalfFin13_clause24580 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24581 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24583 chi hbad
              ·
                exact predecessorHalfFin13_clause24584 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24585 chi hbad
              ·
                exact predecessorHalfFin13_clause24586 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24587 chi hbad
              ·
                exact predecessorHalfFin13_clause24588 chi hbad

end ErdosSzekeres

end
