module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk089

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 116. -/

theorem predecessorHalfFin13_rejectSemanticSegment116
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom2258 chi ∧
      ¬PredecessorHalfFin13Atom0962 chi) ∨
      ((PredecessorHalfFin13Atom2258 chi ∧
      ¬PredecessorHalfFin13Atom0992 chi) ∨
      (PredecessorHalfFin13Atom2259 chi ∧
      ¬PredecessorHalfFin13Atom0951 chi))) ∨
      ((PredecessorHalfFin13Atom2259 chi ∧
      ¬PredecessorHalfFin13Atom0952 chi) ∨
      ((PredecessorHalfFin13Atom2259 chi ∧
      ¬PredecessorHalfFin13Atom0954 chi) ∨
      (PredecessorHalfFin13Atom2259 chi ∧
      ¬PredecessorHalfFin13Atom0963 chi)))) ∨
      (((PredecessorHalfFin13Atom2259 chi ∧
      ¬PredecessorHalfFin13Atom0993 chi) ∨
      ((¬PredecessorHalfFin13Atom2259 chi ∧
      PredecessorHalfFin13Atom0951 chi ∧
      PredecessorHalfFin13Atom0952 chi ∧
      PredecessorHalfFin13Atom0954 chi ∧
      PredecessorHalfFin13Atom0963 chi ∧
      PredecessorHalfFin13Atom0993 chi) ∨
      (PredecessorHalfFin13Atom2260 chi ∧
      ¬PredecessorHalfFin13Atom0951 chi))) ∨
      ((PredecessorHalfFin13Atom2260 chi ∧
      ¬PredecessorHalfFin13Atom0953 chi) ∨
      ((PredecessorHalfFin13Atom2260 chi ∧
      ¬PredecessorHalfFin13Atom0955 chi) ∨
      (PredecessorHalfFin13Atom2260 chi ∧
      ¬PredecessorHalfFin13Atom0964 chi))))) ∨
      ((((PredecessorHalfFin13Atom2260 chi ∧
      ¬PredecessorHalfFin13Atom0994 chi) ∨
      ((¬PredecessorHalfFin13Atom2260 chi ∧
      PredecessorHalfFin13Atom0951 chi ∧
      PredecessorHalfFin13Atom0953 chi ∧
      PredecessorHalfFin13Atom0955 chi ∧
      PredecessorHalfFin13Atom0964 chi ∧
      PredecessorHalfFin13Atom0994 chi) ∨
      (PredecessorHalfFin13Atom2261 chi ∧
      ¬PredecessorHalfFin13Atom0953 chi))) ∨
      ((PredecessorHalfFin13Atom2261 chi ∧
      ¬PredecessorHalfFin13Atom0965 chi) ∨
      ((PredecessorHalfFin13Atom2261 chi ∧
      ¬PredecessorHalfFin13Atom0995 chi) ∨
      (PredecessorHalfFin13Atom2262 chi ∧
      ¬PredecessorHalfFin13Atom0955 chi)))) ∨
      (((PredecessorHalfFin13Atom2262 chi ∧
      ¬PredecessorHalfFin13Atom0966 chi) ∨
      ((PredecessorHalfFin13Atom2262 chi ∧
      ¬PredecessorHalfFin13Atom0996 chi) ∨
      (¬PredecessorHalfFin13Atom2262 chi ∧
      PredecessorHalfFin13Atom0954 chi ∧
      PredecessorHalfFin13Atom0955 chi ∧
      PredecessorHalfFin13Atom0956 chi ∧
      PredecessorHalfFin13Atom0966 chi ∧
      PredecessorHalfFin13Atom0996 chi))) ∨
      ((PredecessorHalfFin13Atom2263 chi ∧
      ¬PredecessorHalfFin13Atom0957 chi) ∨
      ((PredecessorHalfFin13Atom2263 chi ∧
      ¬PredecessorHalfFin13Atom0958 chi) ∨
      (PredecessorHalfFin13Atom2263 chi ∧
      ¬PredecessorHalfFin13Atom0960 chi)))))) ∨
      (((((PredecessorHalfFin13Atom2263 chi ∧
      ¬PredecessorHalfFin13Atom0963 chi) ∨
      ((PredecessorHalfFin13Atom2263 chi ∧
      ¬PredecessorHalfFin13Atom0997 chi) ∨
      (¬PredecessorHalfFin13Atom2263 chi ∧
      PredecessorHalfFin13Atom0957 chi ∧
      PredecessorHalfFin13Atom0958 chi ∧
      PredecessorHalfFin13Atom0960 chi ∧
      PredecessorHalfFin13Atom0963 chi ∧
      PredecessorHalfFin13Atom0997 chi))) ∨
      ((PredecessorHalfFin13Atom2264 chi ∧
      ¬PredecessorHalfFin13Atom0957 chi) ∨
      ((PredecessorHalfFin13Atom2264 chi ∧
      ¬PredecessorHalfFin13Atom0959 chi) ∨
      (PredecessorHalfFin13Atom2264 chi ∧
      ¬PredecessorHalfFin13Atom0961 chi)))) ∨
      (((PredecessorHalfFin13Atom2264 chi ∧
      ¬PredecessorHalfFin13Atom0964 chi) ∨
      ((PredecessorHalfFin13Atom2264 chi ∧
      ¬PredecessorHalfFin13Atom0998 chi) ∨
      (¬PredecessorHalfFin13Atom2264 chi ∧
      PredecessorHalfFin13Atom0957 chi ∧
      PredecessorHalfFin13Atom0959 chi ∧
      PredecessorHalfFin13Atom0961 chi ∧
      PredecessorHalfFin13Atom0964 chi ∧
      PredecessorHalfFin13Atom0998 chi))) ∨
      ((PredecessorHalfFin13Atom2265 chi ∧
      ¬PredecessorHalfFin13Atom0958 chi) ∨
      ((PredecessorHalfFin13Atom2265 chi ∧
      ¬PredecessorHalfFin13Atom0959 chi) ∨
      (PredecessorHalfFin13Atom2265 chi ∧
      ¬PredecessorHalfFin13Atom0965 chi))))) ∨
      ((((PredecessorHalfFin13Atom2266 chi ∧
      ¬PredecessorHalfFin13Atom0960 chi) ∨
      ((PredecessorHalfFin13Atom2266 chi ∧
      ¬PredecessorHalfFin13Atom0961 chi) ∨
      (PredecessorHalfFin13Atom2266 chi ∧
      ¬PredecessorHalfFin13Atom0966 chi))) ∨
      ((PredecessorHalfFin13Atom2266 chi ∧
      ¬PredecessorHalfFin13Atom1000 chi) ∨
      ((¬PredecessorHalfFin13Atom2266 chi ∧
      PredecessorHalfFin13Atom0960 chi ∧
      PredecessorHalfFin13Atom0961 chi ∧
      PredecessorHalfFin13Atom0962 chi ∧
      PredecessorHalfFin13Atom0966 chi ∧
      PredecessorHalfFin13Atom1000 chi) ∨
      (PredecessorHalfFin13Atom2267 chi ∧
      ¬PredecessorHalfFin13Atom0964 chi)))) ∨
      (((PredecessorHalfFin13Atom2267 chi ∧
      ¬PredecessorHalfFin13Atom0966 chi) ∨
      ((PredecessorHalfFin13Atom2268 chi ∧
      ¬PredecessorHalfFin13Atom0967 chi) ∨
      (PredecessorHalfFin13Atom2268 chi ∧
      ¬PredecessorHalfFin13Atom0968 chi))) ∨
      (((PredecessorHalfFin13Atom2268 chi ∧
      ¬PredecessorHalfFin13Atom0971 chi) ∨
      (PredecessorHalfFin13Atom2268 chi ∧
      ¬PredecessorHalfFin13Atom0977 chi)) ∨
      ((PredecessorHalfFin13Atom2268 chi ∧
      ¬PredecessorHalfFin13Atom0987 chi) ∨
      (¬PredecessorHalfFin13Atom2268 chi ∧
      PredecessorHalfFin13Atom0967 chi ∧
      PredecessorHalfFin13Atom0968 chi ∧
      PredecessorHalfFin13Atom0971 chi ∧
      PredecessorHalfFin13Atom0977 chi ∧
      PredecessorHalfFin13Atom0987 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom2269 chi ∧
      ¬PredecessorHalfFin13Atom0967 chi) ∨
      ((PredecessorHalfFin13Atom2269 chi ∧
      ¬PredecessorHalfFin13Atom0969 chi) ∨
      (PredecessorHalfFin13Atom2269 chi ∧
      ¬PredecessorHalfFin13Atom0972 chi))) ∨
      ((PredecessorHalfFin13Atom2269 chi ∧
      ¬PredecessorHalfFin13Atom0978 chi) ∨
      ((PredecessorHalfFin13Atom2269 chi ∧
      ¬PredecessorHalfFin13Atom0988 chi) ∨
      (¬PredecessorHalfFin13Atom2269 chi ∧
      PredecessorHalfFin13Atom0967 chi ∧
      PredecessorHalfFin13Atom0969 chi ∧
      PredecessorHalfFin13Atom0972 chi ∧
      PredecessorHalfFin13Atom0978 chi ∧
      PredecessorHalfFin13Atom0988 chi)))) ∨
      (((PredecessorHalfFin13Atom2270 chi ∧
      ¬PredecessorHalfFin13Atom0967 chi) ∨
      ((PredecessorHalfFin13Atom2270 chi ∧
      ¬PredecessorHalfFin13Atom0970 chi) ∨
      (PredecessorHalfFin13Atom2270 chi ∧
      ¬PredecessorHalfFin13Atom0973 chi))) ∨
      ((PredecessorHalfFin13Atom2270 chi ∧
      ¬PredecessorHalfFin13Atom0979 chi) ∨
      ((PredecessorHalfFin13Atom2270 chi ∧
      ¬PredecessorHalfFin13Atom0989 chi) ∨
      (¬PredecessorHalfFin13Atom2270 chi ∧
      PredecessorHalfFin13Atom0967 chi ∧
      PredecessorHalfFin13Atom0970 chi ∧
      PredecessorHalfFin13Atom0973 chi ∧
      PredecessorHalfFin13Atom0979 chi ∧
      PredecessorHalfFin13Atom0989 chi))))) ∨
      ((((PredecessorHalfFin13Atom2271 chi ∧
      ¬PredecessorHalfFin13Atom0968 chi) ∨
      ((PredecessorHalfFin13Atom2271 chi ∧
      ¬PredecessorHalfFin13Atom0969 chi) ∨
      (PredecessorHalfFin13Atom2271 chi ∧
      ¬PredecessorHalfFin13Atom0974 chi))) ∨
      ((PredecessorHalfFin13Atom2271 chi ∧
      ¬PredecessorHalfFin13Atom0980 chi) ∨
      ((PredecessorHalfFin13Atom2271 chi ∧
      ¬PredecessorHalfFin13Atom0990 chi) ∨
      (PredecessorHalfFin13Atom2272 chi ∧
      ¬PredecessorHalfFin13Atom0968 chi)))) ∨
      (((PredecessorHalfFin13Atom2272 chi ∧
      ¬PredecessorHalfFin13Atom0970 chi) ∨
      ((PredecessorHalfFin13Atom2272 chi ∧
      ¬PredecessorHalfFin13Atom0975 chi) ∨
      (PredecessorHalfFin13Atom2272 chi ∧
      ¬PredecessorHalfFin13Atom0981 chi))) ∨
      ((PredecessorHalfFin13Atom2272 chi ∧
      ¬PredecessorHalfFin13Atom0991 chi) ∨
      ((¬PredecessorHalfFin13Atom2272 chi ∧
      PredecessorHalfFin13Atom0968 chi ∧
      PredecessorHalfFin13Atom0970 chi ∧
      PredecessorHalfFin13Atom0975 chi ∧
      PredecessorHalfFin13Atom0981 chi ∧
      PredecessorHalfFin13Atom0991 chi) ∨
      (PredecessorHalfFin13Atom2273 chi ∧
      ¬PredecessorHalfFin13Atom0969 chi)))))) ∨
      (((((PredecessorHalfFin13Atom2273 chi ∧
      ¬PredecessorHalfFin13Atom0970 chi) ∨
      ((PredecessorHalfFin13Atom2273 chi ∧
      ¬PredecessorHalfFin13Atom0976 chi) ∨
      (PredecessorHalfFin13Atom2273 chi ∧
      ¬PredecessorHalfFin13Atom0982 chi))) ∨
      ((PredecessorHalfFin13Atom2273 chi ∧
      ¬PredecessorHalfFin13Atom0992 chi) ∨
      ((¬PredecessorHalfFin13Atom2273 chi ∧
      PredecessorHalfFin13Atom0969 chi ∧
      PredecessorHalfFin13Atom0970 chi ∧
      PredecessorHalfFin13Atom0976 chi ∧
      PredecessorHalfFin13Atom0982 chi ∧
      PredecessorHalfFin13Atom0992 chi) ∨
      (PredecessorHalfFin13Atom2274 chi ∧
      ¬PredecessorHalfFin13Atom0971 chi)))) ∨
      (((PredecessorHalfFin13Atom2274 chi ∧
      ¬PredecessorHalfFin13Atom0972 chi) ∨
      ((PredecessorHalfFin13Atom2274 chi ∧
      ¬PredecessorHalfFin13Atom0974 chi) ∨
      (PredecessorHalfFin13Atom2274 chi ∧
      ¬PredecessorHalfFin13Atom0983 chi))) ∨
      ((PredecessorHalfFin13Atom2274 chi ∧
      ¬PredecessorHalfFin13Atom0993 chi) ∨
      ((¬PredecessorHalfFin13Atom2274 chi ∧
      PredecessorHalfFin13Atom0971 chi ∧
      PredecessorHalfFin13Atom0972 chi ∧
      PredecessorHalfFin13Atom0974 chi ∧
      PredecessorHalfFin13Atom0983 chi ∧
      PredecessorHalfFin13Atom0993 chi) ∨
      (PredecessorHalfFin13Atom2275 chi ∧
      ¬PredecessorHalfFin13Atom0971 chi))))) ∨
      ((((PredecessorHalfFin13Atom2275 chi ∧
      ¬PredecessorHalfFin13Atom0973 chi) ∨
      ((PredecessorHalfFin13Atom2275 chi ∧
      ¬PredecessorHalfFin13Atom0975 chi) ∨
      (PredecessorHalfFin13Atom2275 chi ∧
      ¬PredecessorHalfFin13Atom0984 chi))) ∨
      ((PredecessorHalfFin13Atom2275 chi ∧
      ¬PredecessorHalfFin13Atom0994 chi) ∨
      ((¬PredecessorHalfFin13Atom2275 chi ∧
      PredecessorHalfFin13Atom0971 chi ∧
      PredecessorHalfFin13Atom0973 chi ∧
      PredecessorHalfFin13Atom0975 chi ∧
      PredecessorHalfFin13Atom0984 chi ∧
      PredecessorHalfFin13Atom0994 chi) ∨
      (PredecessorHalfFin13Atom2276 chi ∧
      ¬PredecessorHalfFin13Atom0972 chi)))) ∨
      (((PredecessorHalfFin13Atom2276 chi ∧
      ¬PredecessorHalfFin13Atom0976 chi) ∨
      ((PredecessorHalfFin13Atom2276 chi ∧
      ¬PredecessorHalfFin13Atom0985 chi) ∨
      (PredecessorHalfFin13Atom2276 chi ∧
      ¬PredecessorHalfFin13Atom0995 chi))) ∨
      (((¬PredecessorHalfFin13Atom2276 chi ∧
      PredecessorHalfFin13Atom0972 chi ∧
      PredecessorHalfFin13Atom0973 chi ∧
      PredecessorHalfFin13Atom0976 chi ∧
      PredecessorHalfFin13Atom0985 chi ∧
      PredecessorHalfFin13Atom0995 chi) ∨
      (PredecessorHalfFin13Atom2277 chi ∧
      ¬PredecessorHalfFin13Atom0974 chi)) ∨
      ((PredecessorHalfFin13Atom2277 chi ∧
      ¬PredecessorHalfFin13Atom0975 chi) ∨
      (PredecessorHalfFin13Atom2277 chi ∧
      ¬PredecessorHalfFin13Atom0976 chi))))))))) := by
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
              exact predecessorHalfFin13_clause24700 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24701 chi hbad
              ·
                exact predecessorHalfFin13_clause24703 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24704 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24705 chi hbad
              ·
                exact predecessorHalfFin13_clause24706 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24707 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24708 chi hbad
              ·
                exact predecessorHalfFin13_clause24709 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24710 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24711 chi hbad
              ·
                exact predecessorHalfFin13_clause24712 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24713 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24714 chi hbad
              ·
                exact predecessorHalfFin13_clause24716 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24718 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24719 chi hbad
              ·
                exact predecessorHalfFin13_clause24722 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24724 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24725 chi hbad
              ·
                exact predecessorHalfFin13_clause24726 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24727 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24728 chi hbad
              ·
                exact predecessorHalfFin13_clause24729 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24730 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24731 chi hbad
              ·
                exact predecessorHalfFin13_clause24732 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24733 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24734 chi hbad
              ·
                exact predecessorHalfFin13_clause24735 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24736 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24737 chi hbad
              ·
                exact predecessorHalfFin13_clause24738 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24739 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24740 chi hbad
              ·
                exact predecessorHalfFin13_clause24742 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24745 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24746 chi hbad
              ·
                exact predecessorHalfFin13_clause24748 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24749 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24750 chi hbad
              ·
                exact predecessorHalfFin13_clause24752 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24754 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24757 chi hbad
              ·
                exact predecessorHalfFin13_clause24758 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24759 chi hbad
              ·
                exact predecessorHalfFin13_clause24760 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24761 chi hbad
              ·
                exact predecessorHalfFin13_clause24762 chi hbad
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
              exact predecessorHalfFin13_clause24763 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24764 chi hbad
              ·
                exact predecessorHalfFin13_clause24765 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24766 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24767 chi hbad
              ·
                exact predecessorHalfFin13_clause24768 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24769 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24770 chi hbad
              ·
                exact predecessorHalfFin13_clause24771 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24772 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24773 chi hbad
              ·
                exact predecessorHalfFin13_clause24774 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24775 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24776 chi hbad
              ·
                exact predecessorHalfFin13_clause24777 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24778 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24779 chi hbad
              ·
                exact predecessorHalfFin13_clause24781 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24782 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24783 chi hbad
              ·
                exact predecessorHalfFin13_clause24784 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24785 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24786 chi hbad
              ·
                exact predecessorHalfFin13_clause24787 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24788 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24789 chi hbad
              ·
                exact predecessorHalfFin13_clause24790 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24791 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24792 chi hbad
              ·
                exact predecessorHalfFin13_clause24793 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24794 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24795 chi hbad
              ·
                exact predecessorHalfFin13_clause24796 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24797 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24798 chi hbad
              ·
                exact predecessorHalfFin13_clause24799 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24800 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24801 chi hbad
              ·
                exact predecessorHalfFin13_clause24802 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24803 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24804 chi hbad
              ·
                exact predecessorHalfFin13_clause24805 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause24807 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24808 chi hbad
              ·
                exact predecessorHalfFin13_clause24809 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24810 chi hbad
              ·
                exact predecessorHalfFin13_clause24811 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause24812 chi hbad
              ·
                exact predecessorHalfFin13_clause24813 chi hbad

end ErdosSzekeres

end
