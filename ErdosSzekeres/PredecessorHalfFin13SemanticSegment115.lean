module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk088
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk089

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 115. -/

theorem predecessorHalfFin13_rejectSemanticSegment115
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom2240 chi ∧
      ¬PredecessorHalfFin13Atom0934 chi) ∨
      ((PredecessorHalfFin13Atom2240 chi ∧
      ¬PredecessorHalfFin13Atom0935 chi) ∨
      (PredecessorHalfFin13Atom2240 chi ∧
      ¬PredecessorHalfFin13Atom0944 chi))) ∨
      ((PredecessorHalfFin13Atom2240 chi ∧
      ¬PredecessorHalfFin13Atom0954 chi) ∨
      ((PredecessorHalfFin13Atom2240 chi ∧
      ¬PredecessorHalfFin13Atom0974 chi) ∨
      (¬PredecessorHalfFin13Atom2240 chi ∧
      PredecessorHalfFin13Atom0934 chi ∧
      PredecessorHalfFin13Atom0935 chi ∧
      PredecessorHalfFin13Atom0944 chi ∧
      PredecessorHalfFin13Atom0954 chi ∧
      PredecessorHalfFin13Atom0974 chi)))) ∨
      (((PredecessorHalfFin13Atom2241 chi ∧
      ¬PredecessorHalfFin13Atom0934 chi) ∨
      ((PredecessorHalfFin13Atom2241 chi ∧
      ¬PredecessorHalfFin13Atom0936 chi) ∨
      (PredecessorHalfFin13Atom2241 chi ∧
      ¬PredecessorHalfFin13Atom0945 chi))) ∨
      ((PredecessorHalfFin13Atom2241 chi ∧
      ¬PredecessorHalfFin13Atom0955 chi) ∨
      ((PredecessorHalfFin13Atom2241 chi ∧
      ¬PredecessorHalfFin13Atom0975 chi) ∨
      (¬PredecessorHalfFin13Atom2241 chi ∧
      PredecessorHalfFin13Atom0934 chi ∧
      PredecessorHalfFin13Atom0936 chi ∧
      PredecessorHalfFin13Atom0945 chi ∧
      PredecessorHalfFin13Atom0955 chi ∧
      PredecessorHalfFin13Atom0975 chi))))) ∨
      ((((PredecessorHalfFin13Atom2242 chi ∧
      ¬PredecessorHalfFin13Atom0935 chi) ∨
      ((PredecessorHalfFin13Atom2242 chi ∧
      ¬PredecessorHalfFin13Atom0936 chi) ∨
      (PredecessorHalfFin13Atom2242 chi ∧
      ¬PredecessorHalfFin13Atom0956 chi))) ∨
      ((PredecessorHalfFin13Atom2243 chi ∧
      ¬PredecessorHalfFin13Atom0937 chi) ∨
      ((PredecessorHalfFin13Atom2243 chi ∧
      ¬PredecessorHalfFin13Atom0938 chi) ∨
      (PredecessorHalfFin13Atom2243 chi ∧
      ¬PredecessorHalfFin13Atom0941 chi)))) ∨
      (((PredecessorHalfFin13Atom2243 chi ∧
      ¬PredecessorHalfFin13Atom0957 chi) ∨
      ((PredecessorHalfFin13Atom2243 chi ∧
      ¬PredecessorHalfFin13Atom0977 chi) ∨
      (¬PredecessorHalfFin13Atom2243 chi ∧
      PredecessorHalfFin13Atom0937 chi ∧
      PredecessorHalfFin13Atom0938 chi ∧
      PredecessorHalfFin13Atom0941 chi ∧
      PredecessorHalfFin13Atom0957 chi ∧
      PredecessorHalfFin13Atom0977 chi))) ∨
      ((PredecessorHalfFin13Atom2244 chi ∧
      ¬PredecessorHalfFin13Atom0937 chi) ∨
      ((PredecessorHalfFin13Atom2244 chi ∧
      ¬PredecessorHalfFin13Atom0939 chi) ∨
      (PredecessorHalfFin13Atom2244 chi ∧
      ¬PredecessorHalfFin13Atom0942 chi)))))) ∨
      (((((PredecessorHalfFin13Atom2244 chi ∧
      ¬PredecessorHalfFin13Atom0958 chi) ∨
      ((PredecessorHalfFin13Atom2244 chi ∧
      ¬PredecessorHalfFin13Atom0978 chi) ∨
      (¬PredecessorHalfFin13Atom2244 chi ∧
      PredecessorHalfFin13Atom0937 chi ∧
      PredecessorHalfFin13Atom0939 chi ∧
      PredecessorHalfFin13Atom0942 chi ∧
      PredecessorHalfFin13Atom0958 chi ∧
      PredecessorHalfFin13Atom0978 chi))) ∨
      ((PredecessorHalfFin13Atom2245 chi ∧
      ¬PredecessorHalfFin13Atom0937 chi) ∨
      ((PredecessorHalfFin13Atom2245 chi ∧
      ¬PredecessorHalfFin13Atom0940 chi) ∨
      (PredecessorHalfFin13Atom2245 chi ∧
      ¬PredecessorHalfFin13Atom0943 chi)))) ∨
      (((PredecessorHalfFin13Atom2245 chi ∧
      ¬PredecessorHalfFin13Atom0959 chi) ∨
      ((PredecessorHalfFin13Atom2245 chi ∧
      ¬PredecessorHalfFin13Atom0979 chi) ∨
      (¬PredecessorHalfFin13Atom2245 chi ∧
      PredecessorHalfFin13Atom0937 chi ∧
      PredecessorHalfFin13Atom0940 chi ∧
      PredecessorHalfFin13Atom0943 chi ∧
      PredecessorHalfFin13Atom0959 chi ∧
      PredecessorHalfFin13Atom0979 chi))) ∨
      ((PredecessorHalfFin13Atom2246 chi ∧
      ¬PredecessorHalfFin13Atom0938 chi) ∨
      ((PredecessorHalfFin13Atom2246 chi ∧
      ¬PredecessorHalfFin13Atom0939 chi) ∨
      (PredecessorHalfFin13Atom2246 chi ∧
      ¬PredecessorHalfFin13Atom0944 chi))))) ∨
      ((((PredecessorHalfFin13Atom2246 chi ∧
      ¬PredecessorHalfFin13Atom0960 chi) ∨
      ((PredecessorHalfFin13Atom2246 chi ∧
      ¬PredecessorHalfFin13Atom0980 chi) ∨
      (¬PredecessorHalfFin13Atom2246 chi ∧
      PredecessorHalfFin13Atom0938 chi ∧
      PredecessorHalfFin13Atom0939 chi ∧
      PredecessorHalfFin13Atom0944 chi ∧
      PredecessorHalfFin13Atom0960 chi ∧
      PredecessorHalfFin13Atom0980 chi))) ∨
      ((PredecessorHalfFin13Atom2247 chi ∧
      ¬PredecessorHalfFin13Atom0938 chi) ∨
      ((PredecessorHalfFin13Atom2247 chi ∧
      ¬PredecessorHalfFin13Atom0940 chi) ∨
      (PredecessorHalfFin13Atom2247 chi ∧
      ¬PredecessorHalfFin13Atom0945 chi)))) ∨
      (((PredecessorHalfFin13Atom2247 chi ∧
      ¬PredecessorHalfFin13Atom0961 chi) ∨
      ((PredecessorHalfFin13Atom2247 chi ∧
      ¬PredecessorHalfFin13Atom0981 chi) ∨
      (¬PredecessorHalfFin13Atom2247 chi ∧
      PredecessorHalfFin13Atom0938 chi ∧
      PredecessorHalfFin13Atom0940 chi ∧
      PredecessorHalfFin13Atom0945 chi ∧
      PredecessorHalfFin13Atom0961 chi ∧
      PredecessorHalfFin13Atom0981 chi))) ∨
      (((PredecessorHalfFin13Atom2248 chi ∧
      ¬PredecessorHalfFin13Atom0940 chi) ∨
      (PredecessorHalfFin13Atom2248 chi ∧
      ¬PredecessorHalfFin13Atom0962 chi)) ∨
      ((PredecessorHalfFin13Atom2248 chi ∧
      ¬PredecessorHalfFin13Atom0982 chi) ∨
      (PredecessorHalfFin13Atom2249 chi ∧
      ¬PredecessorHalfFin13Atom0941 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom2249 chi ∧
      ¬PredecessorHalfFin13Atom0942 chi) ∨
      ((PredecessorHalfFin13Atom2249 chi ∧
      ¬PredecessorHalfFin13Atom0944 chi) ∨
      (PredecessorHalfFin13Atom2249 chi ∧
      ¬PredecessorHalfFin13Atom0963 chi))) ∨
      ((PredecessorHalfFin13Atom2249 chi ∧
      ¬PredecessorHalfFin13Atom0983 chi) ∨
      ((¬PredecessorHalfFin13Atom2249 chi ∧
      PredecessorHalfFin13Atom0941 chi ∧
      PredecessorHalfFin13Atom0942 chi ∧
      PredecessorHalfFin13Atom0944 chi ∧
      PredecessorHalfFin13Atom0963 chi ∧
      PredecessorHalfFin13Atom0983 chi) ∨
      (PredecessorHalfFin13Atom2250 chi ∧
      ¬PredecessorHalfFin13Atom0941 chi)))) ∨
      (((PredecessorHalfFin13Atom2250 chi ∧
      ¬PredecessorHalfFin13Atom0943 chi) ∨
      ((PredecessorHalfFin13Atom2250 chi ∧
      ¬PredecessorHalfFin13Atom0945 chi) ∨
      (PredecessorHalfFin13Atom2250 chi ∧
      ¬PredecessorHalfFin13Atom0964 chi))) ∨
      ((PredecessorHalfFin13Atom2250 chi ∧
      ¬PredecessorHalfFin13Atom0984 chi) ∨
      ((¬PredecessorHalfFin13Atom2250 chi ∧
      PredecessorHalfFin13Atom0941 chi ∧
      PredecessorHalfFin13Atom0943 chi ∧
      PredecessorHalfFin13Atom0945 chi ∧
      PredecessorHalfFin13Atom0964 chi ∧
      PredecessorHalfFin13Atom0984 chi) ∨
      (PredecessorHalfFin13Atom2251 chi ∧
      ¬PredecessorHalfFin13Atom0942 chi))))) ∨
      ((((PredecessorHalfFin13Atom2251 chi ∧
      ¬PredecessorHalfFin13Atom0943 chi) ∨
      ((PredecessorHalfFin13Atom2251 chi ∧
      ¬PredecessorHalfFin13Atom0965 chi) ∨
      (PredecessorHalfFin13Atom2251 chi ∧
      ¬PredecessorHalfFin13Atom0985 chi))) ∨
      ((PredecessorHalfFin13Atom2252 chi ∧
      ¬PredecessorHalfFin13Atom0944 chi) ∨
      ((PredecessorHalfFin13Atom2252 chi ∧
      ¬PredecessorHalfFin13Atom0945 chi) ∨
      (PredecessorHalfFin13Atom2252 chi ∧
      ¬PredecessorHalfFin13Atom0966 chi)))) ∨
      (((PredecessorHalfFin13Atom2252 chi ∧
      ¬PredecessorHalfFin13Atom0986 chi) ∨
      ((PredecessorHalfFin13Atom2253 chi ∧
      ¬PredecessorHalfFin13Atom0947 chi) ∨
      (PredecessorHalfFin13Atom2253 chi ∧
      ¬PredecessorHalfFin13Atom0948 chi))) ∨
      (((PredecessorHalfFin13Atom2253 chi ∧
      ¬PredecessorHalfFin13Atom0951 chi) ∨
      (PredecessorHalfFin13Atom2253 chi ∧
      ¬PredecessorHalfFin13Atom0957 chi)) ∨
      ((PredecessorHalfFin13Atom2253 chi ∧
      ¬PredecessorHalfFin13Atom0987 chi) ∨
      (¬PredecessorHalfFin13Atom2253 chi ∧
      PredecessorHalfFin13Atom0947 chi ∧
      PredecessorHalfFin13Atom0948 chi ∧
      PredecessorHalfFin13Atom0951 chi ∧
      PredecessorHalfFin13Atom0957 chi ∧
      PredecessorHalfFin13Atom0987 chi)))))) ∨
      (((((PredecessorHalfFin13Atom2254 chi ∧
      ¬PredecessorHalfFin13Atom0947 chi) ∨
      ((PredecessorHalfFin13Atom2254 chi ∧
      ¬PredecessorHalfFin13Atom0949 chi) ∨
      (PredecessorHalfFin13Atom2254 chi ∧
      ¬PredecessorHalfFin13Atom0952 chi))) ∨
      ((PredecessorHalfFin13Atom2254 chi ∧
      ¬PredecessorHalfFin13Atom0958 chi) ∨
      ((PredecessorHalfFin13Atom2254 chi ∧
      ¬PredecessorHalfFin13Atom0988 chi) ∨
      (PredecessorHalfFin13Atom2255 chi ∧
      ¬PredecessorHalfFin13Atom0947 chi)))) ∨
      (((PredecessorHalfFin13Atom2255 chi ∧
      ¬PredecessorHalfFin13Atom0950 chi) ∨
      ((PredecessorHalfFin13Atom2255 chi ∧
      ¬PredecessorHalfFin13Atom0953 chi) ∨
      (PredecessorHalfFin13Atom2255 chi ∧
      ¬PredecessorHalfFin13Atom0959 chi))) ∨
      ((PredecessorHalfFin13Atom2255 chi ∧
      ¬PredecessorHalfFin13Atom0989 chi) ∨
      ((¬PredecessorHalfFin13Atom2255 chi ∧
      PredecessorHalfFin13Atom0947 chi ∧
      PredecessorHalfFin13Atom0950 chi ∧
      PredecessorHalfFin13Atom0953 chi ∧
      PredecessorHalfFin13Atom0959 chi ∧
      PredecessorHalfFin13Atom0989 chi) ∨
      (PredecessorHalfFin13Atom2256 chi ∧
      ¬PredecessorHalfFin13Atom0948 chi))))) ∨
      ((((PredecessorHalfFin13Atom2256 chi ∧
      ¬PredecessorHalfFin13Atom0949 chi) ∨
      ((PredecessorHalfFin13Atom2256 chi ∧
      ¬PredecessorHalfFin13Atom0954 chi) ∨
      (PredecessorHalfFin13Atom2256 chi ∧
      ¬PredecessorHalfFin13Atom0960 chi))) ∨
      ((PredecessorHalfFin13Atom2256 chi ∧
      ¬PredecessorHalfFin13Atom0990 chi) ∨
      ((¬PredecessorHalfFin13Atom2256 chi ∧
      PredecessorHalfFin13Atom0948 chi ∧
      PredecessorHalfFin13Atom0949 chi ∧
      PredecessorHalfFin13Atom0954 chi ∧
      PredecessorHalfFin13Atom0960 chi ∧
      PredecessorHalfFin13Atom0990 chi) ∨
      (PredecessorHalfFin13Atom2257 chi ∧
      ¬PredecessorHalfFin13Atom0948 chi)))) ∨
      (((PredecessorHalfFin13Atom2257 chi ∧
      ¬PredecessorHalfFin13Atom0950 chi) ∨
      ((PredecessorHalfFin13Atom2257 chi ∧
      ¬PredecessorHalfFin13Atom0955 chi) ∨
      (PredecessorHalfFin13Atom2257 chi ∧
      ¬PredecessorHalfFin13Atom0961 chi))) ∨
      (((PredecessorHalfFin13Atom2257 chi ∧
      ¬PredecessorHalfFin13Atom0991 chi) ∨
      (¬PredecessorHalfFin13Atom2257 chi ∧
      PredecessorHalfFin13Atom0948 chi ∧
      PredecessorHalfFin13Atom0950 chi ∧
      PredecessorHalfFin13Atom0955 chi ∧
      PredecessorHalfFin13Atom0961 chi ∧
      PredecessorHalfFin13Atom0991 chi)) ∨
      ((PredecessorHalfFin13Atom2258 chi ∧
      ¬PredecessorHalfFin13Atom0950 chi) ∨
      (PredecessorHalfFin13Atom2258 chi ∧
      ¬PredecessorHalfFin13Atom0956 chi))))))))) := by
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
              exact predecessorHalfFin13_clause24589 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24590 chi hbad
              ·
                exact predecessorHalfFin13_clause24591 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24592 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24593 chi hbad
              ·
                exact predecessorHalfFin13_clause24594 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24595 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24596 chi hbad
              ·
                exact predecessorHalfFin13_clause24597 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24598 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24599 chi hbad
              ·
                exact predecessorHalfFin13_clause24600 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24601 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24602 chi hbad
              ·
                exact predecessorHalfFin13_clause24604 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24607 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24608 chi hbad
              ·
                exact predecessorHalfFin13_clause24609 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24610 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24611 chi hbad
              ·
                exact predecessorHalfFin13_clause24612 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24613 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24614 chi hbad
              ·
                exact predecessorHalfFin13_clause24615 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24616 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24617 chi hbad
              ·
                exact predecessorHalfFin13_clause24618 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24619 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24620 chi hbad
              ·
                exact predecessorHalfFin13_clause24621 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24622 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24623 chi hbad
              ·
                exact predecessorHalfFin13_clause24624 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24625 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24626 chi hbad
              ·
                exact predecessorHalfFin13_clause24627 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24628 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24629 chi hbad
              ·
                exact predecessorHalfFin13_clause24630 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24631 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24632 chi hbad
              ·
                exact predecessorHalfFin13_clause24633 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24634 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24635 chi hbad
              ·
                exact predecessorHalfFin13_clause24636 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24638 chi hbad
              ·
                exact predecessorHalfFin13_clause24640 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24641 chi hbad
              ·
                exact predecessorHalfFin13_clause24643 chi hbad
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
              exact predecessorHalfFin13_clause24644 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24645 chi hbad
              ·
                exact predecessorHalfFin13_clause24646 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24647 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24648 chi hbad
              ·
                exact predecessorHalfFin13_clause24649 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24650 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24651 chi hbad
              ·
                exact predecessorHalfFin13_clause24652 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24653 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24654 chi hbad
              ·
                exact predecessorHalfFin13_clause24655 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24656 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24658 chi hbad
              ·
                exact predecessorHalfFin13_clause24659 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24661 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24662 chi hbad
              ·
                exact predecessorHalfFin13_clause24664 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24665 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24667 chi hbad
              ·
                exact predecessorHalfFin13_clause24668 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24669 chi hbad
              ·
                exact predecessorHalfFin13_clause24670 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24671 chi hbad
              ·
                exact predecessorHalfFin13_clause24672 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24673 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24674 chi hbad
              ·
                exact predecessorHalfFin13_clause24675 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24676 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24677 chi hbad
              ·
                exact predecessorHalfFin13_clause24679 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24680 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24681 chi hbad
              ·
                exact predecessorHalfFin13_clause24682 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24683 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24684 chi hbad
              ·
                exact predecessorHalfFin13_clause24685 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24686 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24687 chi hbad
              ·
                exact predecessorHalfFin13_clause24688 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24689 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24690 chi hbad
              ·
                exact predecessorHalfFin13_clause24691 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24692 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24693 chi hbad
              ·
                exact predecessorHalfFin13_clause24694 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24695 chi hbad
              ·
                exact predecessorHalfFin13_clause24696 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24698 chi hbad
              ·
                exact predecessorHalfFin13_clause24699 chi hbad

end ErdosSzekeres

end
