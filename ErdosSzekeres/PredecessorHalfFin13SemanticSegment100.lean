module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk076
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk077

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 100. -/

theorem predecessorHalfFin13_rejectSemanticSegment100
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom1969 chi ∧
      ¬PredecessorHalfFin13Atom0934 chi) ∨
      ((¬PredecessorHalfFin13Atom1969 chi ∧
      PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0934 chi) ∨
      (PredecessorHalfFin13Atom1970 chi ∧
      ¬PredecessorHalfFin13Atom0736 chi))) ∨
      ((PredecessorHalfFin13Atom1970 chi ∧
      ¬PredecessorHalfFin13Atom0740 chi) ∨
      ((PredecessorHalfFin13Atom1970 chi ∧
      ¬PredecessorHalfFin13Atom0745 chi) ∨
      (PredecessorHalfFin13Atom1970 chi ∧
      ¬PredecessorHalfFin13Atom0760 chi)))) ∨
      (((PredecessorHalfFin13Atom1970 chi ∧
      ¬PredecessorHalfFin13Atom0935 chi) ∨
      ((PredecessorHalfFin13Atom1971 chi ∧
      ¬PredecessorHalfFin13Atom0736 chi) ∨
      (PredecessorHalfFin13Atom1971 chi ∧
      ¬PredecessorHalfFin13Atom0741 chi))) ∨
      ((PredecessorHalfFin13Atom1971 chi ∧
      ¬PredecessorHalfFin13Atom0746 chi) ∨
      ((PredecessorHalfFin13Atom1971 chi ∧
      ¬PredecessorHalfFin13Atom0761 chi) ∨
      (PredecessorHalfFin13Atom1971 chi ∧
      ¬PredecessorHalfFin13Atom0936 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom1971 chi ∧
      PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0936 chi) ∨
      ((PredecessorHalfFin13Atom1972 chi ∧
      ¬PredecessorHalfFin13Atom0737 chi) ∨
      (PredecessorHalfFin13Atom1972 chi ∧
      ¬PredecessorHalfFin13Atom0738 chi))) ∨
      ((PredecessorHalfFin13Atom1972 chi ∧
      ¬PredecessorHalfFin13Atom0747 chi) ∨
      ((PredecessorHalfFin13Atom1972 chi ∧
      ¬PredecessorHalfFin13Atom0762 chi) ∨
      (PredecessorHalfFin13Atom1972 chi ∧
      ¬PredecessorHalfFin13Atom0937 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1972 chi ∧
      PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0937 chi) ∨
      ((PredecessorHalfFin13Atom1973 chi ∧
      ¬PredecessorHalfFin13Atom0737 chi) ∨
      (PredecessorHalfFin13Atom1973 chi ∧
      ¬PredecessorHalfFin13Atom0739 chi))) ∨
      ((PredecessorHalfFin13Atom1973 chi ∧
      ¬PredecessorHalfFin13Atom0748 chi) ∨
      ((PredecessorHalfFin13Atom1973 chi ∧
      ¬PredecessorHalfFin13Atom0763 chi) ∨
      (PredecessorHalfFin13Atom1973 chi ∧
      ¬PredecessorHalfFin13Atom0938 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom1973 chi ∧
      PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0938 chi) ∨
      ((PredecessorHalfFin13Atom1974 chi ∧
      ¬PredecessorHalfFin13Atom0737 chi) ∨
      (PredecessorHalfFin13Atom1974 chi ∧
      ¬PredecessorHalfFin13Atom0740 chi))) ∨
      ((PredecessorHalfFin13Atom1974 chi ∧
      ¬PredecessorHalfFin13Atom0749 chi) ∨
      ((PredecessorHalfFin13Atom1974 chi ∧
      ¬PredecessorHalfFin13Atom0764 chi) ∨
      (PredecessorHalfFin13Atom1974 chi ∧
      ¬PredecessorHalfFin13Atom0939 chi)))) ∨
      (((PredecessorHalfFin13Atom1975 chi ∧
      ¬PredecessorHalfFin13Atom0737 chi) ∨
      ((PredecessorHalfFin13Atom1975 chi ∧
      ¬PredecessorHalfFin13Atom0741 chi) ∨
      (PredecessorHalfFin13Atom1975 chi ∧
      ¬PredecessorHalfFin13Atom0750 chi))) ∨
      ((PredecessorHalfFin13Atom1975 chi ∧
      ¬PredecessorHalfFin13Atom0765 chi) ∨
      ((PredecessorHalfFin13Atom1975 chi ∧
      ¬PredecessorHalfFin13Atom0940 chi) ∨
      (¬PredecessorHalfFin13Atom1975 chi ∧
      PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0940 chi))))) ∨
      ((((PredecessorHalfFin13Atom1976 chi ∧
      ¬PredecessorHalfFin13Atom0738 chi) ∨
      ((PredecessorHalfFin13Atom1976 chi ∧
      ¬PredecessorHalfFin13Atom0739 chi) ∨
      (PredecessorHalfFin13Atom1976 chi ∧
      ¬PredecessorHalfFin13Atom0751 chi))) ∨
      ((PredecessorHalfFin13Atom1976 chi ∧
      ¬PredecessorHalfFin13Atom0766 chi) ∨
      ((PredecessorHalfFin13Atom1976 chi ∧
      ¬PredecessorHalfFin13Atom0941 chi) ∨
      (¬PredecessorHalfFin13Atom1976 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0941 chi)))) ∨
      (((PredecessorHalfFin13Atom1977 chi ∧
      ¬PredecessorHalfFin13Atom0738 chi) ∨
      ((PredecessorHalfFin13Atom1977 chi ∧
      ¬PredecessorHalfFin13Atom0740 chi) ∨
      (PredecessorHalfFin13Atom1977 chi ∧
      ¬PredecessorHalfFin13Atom0752 chi))) ∨
      (((PredecessorHalfFin13Atom1977 chi ∧
      ¬PredecessorHalfFin13Atom0767 chi) ∨
      (PredecessorHalfFin13Atom1977 chi ∧
      ¬PredecessorHalfFin13Atom0942 chi)) ∨
      ((PredecessorHalfFin13Atom1978 chi ∧
      ¬PredecessorHalfFin13Atom0738 chi) ∨
      (PredecessorHalfFin13Atom1978 chi ∧
      ¬PredecessorHalfFin13Atom0741 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom1978 chi ∧
      ¬PredecessorHalfFin13Atom0753 chi) ∨
      ((PredecessorHalfFin13Atom1978 chi ∧
      ¬PredecessorHalfFin13Atom0768 chi) ∨
      (PredecessorHalfFin13Atom1978 chi ∧
      ¬PredecessorHalfFin13Atom0943 chi))) ∨
      ((¬PredecessorHalfFin13Atom1978 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0943 chi) ∨
      ((PredecessorHalfFin13Atom1979 chi ∧
      ¬PredecessorHalfFin13Atom0739 chi) ∨
      (PredecessorHalfFin13Atom1979 chi ∧
      ¬PredecessorHalfFin13Atom0740 chi)))) ∨
      (((PredecessorHalfFin13Atom1979 chi ∧
      ¬PredecessorHalfFin13Atom0754 chi) ∨
      ((PredecessorHalfFin13Atom1979 chi ∧
      ¬PredecessorHalfFin13Atom0769 chi) ∨
      (PredecessorHalfFin13Atom1979 chi ∧
      ¬PredecessorHalfFin13Atom0944 chi))) ∨
      ((PredecessorHalfFin13Atom1980 chi ∧
      ¬PredecessorHalfFin13Atom0739 chi) ∨
      ((PredecessorHalfFin13Atom1980 chi ∧
      ¬PredecessorHalfFin13Atom0741 chi) ∨
      (PredecessorHalfFin13Atom1980 chi ∧
      ¬PredecessorHalfFin13Atom0755 chi))))) ∨
      ((((PredecessorHalfFin13Atom1980 chi ∧
      ¬PredecessorHalfFin13Atom0770 chi) ∨
      ((PredecessorHalfFin13Atom1980 chi ∧
      ¬PredecessorHalfFin13Atom0945 chi) ∨
      (¬PredecessorHalfFin13Atom1980 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0945 chi))) ∨
      ((PredecessorHalfFin13Atom1981 chi ∧
      ¬PredecessorHalfFin13Atom0740 chi) ∨
      ((PredecessorHalfFin13Atom1981 chi ∧
      ¬PredecessorHalfFin13Atom0741 chi) ∨
      (PredecessorHalfFin13Atom1981 chi ∧
      ¬PredecessorHalfFin13Atom0756 chi)))) ∨
      (((PredecessorHalfFin13Atom1981 chi ∧
      ¬PredecessorHalfFin13Atom0771 chi) ∨
      ((PredecessorHalfFin13Atom1981 chi ∧
      ¬PredecessorHalfFin13Atom0946 chi) ∨
      (PredecessorHalfFin13Atom1982 chi ∧
      ¬PredecessorHalfFin13Atom0742 chi))) ∨
      ((PredecessorHalfFin13Atom1982 chi ∧
      ¬PredecessorHalfFin13Atom0743 chi) ∨
      ((PredecessorHalfFin13Atom1982 chi ∧
      ¬PredecessorHalfFin13Atom0747 chi) ∨
      (PredecessorHalfFin13Atom1982 chi ∧
      ¬PredecessorHalfFin13Atom0772 chi)))))) ∨
      (((((PredecessorHalfFin13Atom1982 chi ∧
      ¬PredecessorHalfFin13Atom0947 chi) ∨
      ((¬PredecessorHalfFin13Atom1982 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0947 chi) ∨
      (PredecessorHalfFin13Atom1983 chi ∧
      ¬PredecessorHalfFin13Atom0742 chi))) ∨
      ((PredecessorHalfFin13Atom1983 chi ∧
      ¬PredecessorHalfFin13Atom0744 chi) ∨
      ((PredecessorHalfFin13Atom1983 chi ∧
      ¬PredecessorHalfFin13Atom0748 chi) ∨
      (PredecessorHalfFin13Atom1983 chi ∧
      ¬PredecessorHalfFin13Atom0773 chi)))) ∨
      (((PredecessorHalfFin13Atom1983 chi ∧
      ¬PredecessorHalfFin13Atom0948 chi) ∨
      ((¬PredecessorHalfFin13Atom1983 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0948 chi) ∨
      (PredecessorHalfFin13Atom1984 chi ∧
      ¬PredecessorHalfFin13Atom0742 chi))) ∨
      ((PredecessorHalfFin13Atom1984 chi ∧
      ¬PredecessorHalfFin13Atom0745 chi) ∨
      ((PredecessorHalfFin13Atom1984 chi ∧
      ¬PredecessorHalfFin13Atom0749 chi) ∨
      (PredecessorHalfFin13Atom1984 chi ∧
      ¬PredecessorHalfFin13Atom0774 chi))))) ∨
      ((((PredecessorHalfFin13Atom1984 chi ∧
      ¬PredecessorHalfFin13Atom0949 chi) ∨
      ((¬PredecessorHalfFin13Atom1984 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0745 chi ∧
      PredecessorHalfFin13Atom0749 chi ∧
      PredecessorHalfFin13Atom0774 chi ∧
      PredecessorHalfFin13Atom0949 chi) ∨
      (PredecessorHalfFin13Atom1985 chi ∧
      ¬PredecessorHalfFin13Atom0742 chi))) ∨
      ((PredecessorHalfFin13Atom1985 chi ∧
      ¬PredecessorHalfFin13Atom0746 chi) ∨
      ((PredecessorHalfFin13Atom1985 chi ∧
      ¬PredecessorHalfFin13Atom0750 chi) ∨
      (PredecessorHalfFin13Atom1985 chi ∧
      ¬PredecessorHalfFin13Atom0775 chi)))) ∨
      (((PredecessorHalfFin13Atom1985 chi ∧
      ¬PredecessorHalfFin13Atom0950 chi) ∨
      ((¬PredecessorHalfFin13Atom1985 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0950 chi) ∨
      (PredecessorHalfFin13Atom1986 chi ∧
      ¬PredecessorHalfFin13Atom0743 chi))) ∨
      (((PredecessorHalfFin13Atom1986 chi ∧
      ¬PredecessorHalfFin13Atom0744 chi) ∨
      (PredecessorHalfFin13Atom1986 chi ∧
      ¬PredecessorHalfFin13Atom0751 chi)) ∨
      ((PredecessorHalfFin13Atom1986 chi ∧
      ¬PredecessorHalfFin13Atom0776 chi) ∨
      (PredecessorHalfFin13Atom1986 chi ∧
      ¬PredecessorHalfFin13Atom0951 chi))))))))) := by
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
              exact predecessorHalfFin13_clause22967 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22968 chi hbad
              ·
                exact predecessorHalfFin13_clause22969 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22970 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22971 chi hbad
              ·
                exact predecessorHalfFin13_clause22972 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22973 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22975 chi hbad
              ·
                exact predecessorHalfFin13_clause22976 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22977 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22978 chi hbad
              ·
                exact predecessorHalfFin13_clause22979 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22980 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22981 chi hbad
              ·
                exact predecessorHalfFin13_clause22982 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22983 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22984 chi hbad
              ·
                exact predecessorHalfFin13_clause22985 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22986 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22987 chi hbad
              ·
                exact predecessorHalfFin13_clause22988 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22989 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22990 chi hbad
              ·
                exact predecessorHalfFin13_clause22991 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22992 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22993 chi hbad
              ·
                exact predecessorHalfFin13_clause22994 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22995 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22996 chi hbad
              ·
                exact predecessorHalfFin13_clause22997 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22999 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23000 chi hbad
              ·
                exact predecessorHalfFin13_clause23001 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23002 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23003 chi hbad
              ·
                exact predecessorHalfFin13_clause23004 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23005 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23006 chi hbad
              ·
                exact predecessorHalfFin13_clause23007 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23008 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23009 chi hbad
              ·
                exact predecessorHalfFin13_clause23010 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23011 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23012 chi hbad
              ·
                exact predecessorHalfFin13_clause23013 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23014 chi hbad
              ·
                exact predecessorHalfFin13_clause23015 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23017 chi hbad
              ·
                exact predecessorHalfFin13_clause23018 chi hbad
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
              exact predecessorHalfFin13_clause23019 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23020 chi hbad
              ·
                exact predecessorHalfFin13_clause23021 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23022 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23023 chi hbad
              ·
                exact predecessorHalfFin13_clause23024 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23025 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23026 chi hbad
              ·
                exact predecessorHalfFin13_clause23027 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23029 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23030 chi hbad
              ·
                exact predecessorHalfFin13_clause23031 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23032 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23033 chi hbad
              ·
                exact predecessorHalfFin13_clause23034 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23035 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23036 chi hbad
              ·
                exact predecessorHalfFin13_clause23037 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23038 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23039 chi hbad
              ·
                exact predecessorHalfFin13_clause23041 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23042 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23043 chi hbad
              ·
                exact predecessorHalfFin13_clause23044 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23045 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23046 chi hbad
              ·
                exact predecessorHalfFin13_clause23047 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23048 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23049 chi hbad
              ·
                exact predecessorHalfFin13_clause23050 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23051 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23052 chi hbad
              ·
                exact predecessorHalfFin13_clause23053 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23054 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23055 chi hbad
              ·
                exact predecessorHalfFin13_clause23056 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23057 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23058 chi hbad
              ·
                exact predecessorHalfFin13_clause23059 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23060 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23061 chi hbad
              ·
                exact predecessorHalfFin13_clause23062 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23063 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23064 chi hbad
              ·
                exact predecessorHalfFin13_clause23065 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23066 chi hbad
              ·
                exact predecessorHalfFin13_clause23067 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23068 chi hbad
              ·
                exact predecessorHalfFin13_clause23069 chi hbad

end ErdosSzekeres

end
