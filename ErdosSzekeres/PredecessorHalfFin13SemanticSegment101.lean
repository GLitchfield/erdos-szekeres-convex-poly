module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk077
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk078

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 101. -/

theorem predecessorHalfFin13_rejectSemanticSegment101
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((¬PredecessorHalfFin13Atom1986 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0951 chi) ∨
      ((PredecessorHalfFin13Atom1987 chi ∧
      ¬PredecessorHalfFin13Atom0743 chi) ∨
      (PredecessorHalfFin13Atom1987 chi ∧
      ¬PredecessorHalfFin13Atom0745 chi))) ∨
      ((PredecessorHalfFin13Atom1987 chi ∧
      ¬PredecessorHalfFin13Atom0752 chi) ∨
      ((PredecessorHalfFin13Atom1987 chi ∧
      ¬PredecessorHalfFin13Atom0777 chi) ∨
      (PredecessorHalfFin13Atom1987 chi ∧
      ¬PredecessorHalfFin13Atom0952 chi)))) ∨
      (((PredecessorHalfFin13Atom1988 chi ∧
      ¬PredecessorHalfFin13Atom0743 chi) ∨
      ((PredecessorHalfFin13Atom1988 chi ∧
      ¬PredecessorHalfFin13Atom0746 chi) ∨
      (PredecessorHalfFin13Atom1988 chi ∧
      ¬PredecessorHalfFin13Atom0753 chi))) ∨
      ((PredecessorHalfFin13Atom1988 chi ∧
      ¬PredecessorHalfFin13Atom0778 chi) ∨
      ((PredecessorHalfFin13Atom1988 chi ∧
      ¬PredecessorHalfFin13Atom0953 chi) ∨
      (¬PredecessorHalfFin13Atom1988 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0953 chi))))) ∨
      ((((PredecessorHalfFin13Atom1989 chi ∧
      ¬PredecessorHalfFin13Atom0744 chi) ∨
      ((PredecessorHalfFin13Atom1989 chi ∧
      ¬PredecessorHalfFin13Atom0754 chi) ∨
      (PredecessorHalfFin13Atom1989 chi ∧
      ¬PredecessorHalfFin13Atom0779 chi))) ∨
      ((PredecessorHalfFin13Atom1989 chi ∧
      ¬PredecessorHalfFin13Atom0954 chi) ∨
      ((PredecessorHalfFin13Atom1990 chi ∧
      ¬PredecessorHalfFin13Atom0744 chi) ∨
      (PredecessorHalfFin13Atom1990 chi ∧
      ¬PredecessorHalfFin13Atom0746 chi)))) ∨
      (((PredecessorHalfFin13Atom1990 chi ∧
      ¬PredecessorHalfFin13Atom0755 chi) ∨
      ((PredecessorHalfFin13Atom1990 chi ∧
      ¬PredecessorHalfFin13Atom0780 chi) ∨
      (PredecessorHalfFin13Atom1990 chi ∧
      ¬PredecessorHalfFin13Atom0955 chi))) ∨
      ((¬PredecessorHalfFin13Atom1990 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0955 chi) ∨
      ((PredecessorHalfFin13Atom1991 chi ∧
      ¬PredecessorHalfFin13Atom0745 chi) ∨
      (PredecessorHalfFin13Atom1991 chi ∧
      ¬PredecessorHalfFin13Atom0746 chi)))))) ∨
      (((((PredecessorHalfFin13Atom1991 chi ∧
      ¬PredecessorHalfFin13Atom0781 chi) ∨
      ((PredecessorHalfFin13Atom1991 chi ∧
      ¬PredecessorHalfFin13Atom0956 chi) ∨
      (PredecessorHalfFin13Atom1992 chi ∧
      ¬PredecessorHalfFin13Atom0747 chi))) ∨
      ((PredecessorHalfFin13Atom1992 chi ∧
      ¬PredecessorHalfFin13Atom0748 chi) ∨
      ((PredecessorHalfFin13Atom1992 chi ∧
      ¬PredecessorHalfFin13Atom0751 chi) ∨
      (PredecessorHalfFin13Atom1992 chi ∧
      ¬PredecessorHalfFin13Atom0782 chi)))) ∨
      (((PredecessorHalfFin13Atom1992 chi ∧
      ¬PredecessorHalfFin13Atom0957 chi) ∨
      ((¬PredecessorHalfFin13Atom1992 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0957 chi) ∨
      (PredecessorHalfFin13Atom1993 chi ∧
      ¬PredecessorHalfFin13Atom0747 chi))) ∨
      ((PredecessorHalfFin13Atom1993 chi ∧
      ¬PredecessorHalfFin13Atom0749 chi) ∨
      ((PredecessorHalfFin13Atom1993 chi ∧
      ¬PredecessorHalfFin13Atom0752 chi) ∨
      (PredecessorHalfFin13Atom1993 chi ∧
      ¬PredecessorHalfFin13Atom0783 chi))))) ∨
      ((((PredecessorHalfFin13Atom1993 chi ∧
      ¬PredecessorHalfFin13Atom0958 chi) ∨
      ((PredecessorHalfFin13Atom1994 chi ∧
      ¬PredecessorHalfFin13Atom0747 chi) ∨
      (PredecessorHalfFin13Atom1994 chi ∧
      ¬PredecessorHalfFin13Atom0750 chi))) ∨
      ((PredecessorHalfFin13Atom1994 chi ∧
      ¬PredecessorHalfFin13Atom0753 chi) ∨
      ((PredecessorHalfFin13Atom1994 chi ∧
      ¬PredecessorHalfFin13Atom0784 chi) ∨
      (PredecessorHalfFin13Atom1994 chi ∧
      ¬PredecessorHalfFin13Atom0959 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1994 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0959 chi) ∨
      ((PredecessorHalfFin13Atom1995 chi ∧
      ¬PredecessorHalfFin13Atom0748 chi) ∨
      (PredecessorHalfFin13Atom1995 chi ∧
      ¬PredecessorHalfFin13Atom0749 chi))) ∨
      (((PredecessorHalfFin13Atom1995 chi ∧
      ¬PredecessorHalfFin13Atom0754 chi) ∨
      (PredecessorHalfFin13Atom1995 chi ∧
      ¬PredecessorHalfFin13Atom0785 chi)) ∨
      ((PredecessorHalfFin13Atom1995 chi ∧
      ¬PredecessorHalfFin13Atom0960 chi) ∨
      (¬PredecessorHalfFin13Atom1995 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0749 chi ∧
      PredecessorHalfFin13Atom0754 chi ∧
      PredecessorHalfFin13Atom0785 chi ∧
      PredecessorHalfFin13Atom0960 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom1996 chi ∧
      ¬PredecessorHalfFin13Atom0748 chi) ∨
      ((PredecessorHalfFin13Atom1996 chi ∧
      ¬PredecessorHalfFin13Atom0750 chi) ∨
      (PredecessorHalfFin13Atom1996 chi ∧
      ¬PredecessorHalfFin13Atom0755 chi))) ∨
      ((PredecessorHalfFin13Atom1996 chi ∧
      ¬PredecessorHalfFin13Atom0786 chi) ∨
      ((PredecessorHalfFin13Atom1996 chi ∧
      ¬PredecessorHalfFin13Atom0961 chi) ∨
      (¬PredecessorHalfFin13Atom1996 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0961 chi)))) ∨
      (((PredecessorHalfFin13Atom1997 chi ∧
      ¬PredecessorHalfFin13Atom0750 chi) ∨
      ((PredecessorHalfFin13Atom1997 chi ∧
      ¬PredecessorHalfFin13Atom0756 chi) ∨
      (PredecessorHalfFin13Atom1997 chi ∧
      ¬PredecessorHalfFin13Atom0787 chi))) ∨
      ((PredecessorHalfFin13Atom1997 chi ∧
      ¬PredecessorHalfFin13Atom0962 chi) ∨
      ((PredecessorHalfFin13Atom1998 chi ∧
      ¬PredecessorHalfFin13Atom0751 chi) ∨
      (PredecessorHalfFin13Atom1998 chi ∧
      ¬PredecessorHalfFin13Atom0752 chi))))) ∨
      ((((PredecessorHalfFin13Atom1998 chi ∧
      ¬PredecessorHalfFin13Atom0754 chi) ∨
      ((PredecessorHalfFin13Atom1998 chi ∧
      ¬PredecessorHalfFin13Atom0788 chi) ∨
      (PredecessorHalfFin13Atom1998 chi ∧
      ¬PredecessorHalfFin13Atom0963 chi))) ∨
      ((PredecessorHalfFin13Atom1999 chi ∧
      ¬PredecessorHalfFin13Atom0751 chi) ∨
      ((PredecessorHalfFin13Atom1999 chi ∧
      ¬PredecessorHalfFin13Atom0753 chi) ∨
      (PredecessorHalfFin13Atom1999 chi ∧
      ¬PredecessorHalfFin13Atom0755 chi)))) ∨
      (((PredecessorHalfFin13Atom1999 chi ∧
      ¬PredecessorHalfFin13Atom0789 chi) ∨
      ((PredecessorHalfFin13Atom1999 chi ∧
      ¬PredecessorHalfFin13Atom0964 chi) ∨
      (¬PredecessorHalfFin13Atom1999 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0964 chi))) ∨
      ((PredecessorHalfFin13Atom2000 chi ∧
      ¬PredecessorHalfFin13Atom0752 chi) ∨
      ((PredecessorHalfFin13Atom2000 chi ∧
      ¬PredecessorHalfFin13Atom0753 chi) ∨
      (PredecessorHalfFin13Atom2000 chi ∧
      ¬PredecessorHalfFin13Atom0756 chi)))))) ∨
      (((((PredecessorHalfFin13Atom2000 chi ∧
      ¬PredecessorHalfFin13Atom0790 chi) ∨
      ((PredecessorHalfFin13Atom2000 chi ∧
      ¬PredecessorHalfFin13Atom0965 chi) ∨
      (PredecessorHalfFin13Atom2001 chi ∧
      ¬PredecessorHalfFin13Atom0754 chi))) ∨
      ((PredecessorHalfFin13Atom2001 chi ∧
      ¬PredecessorHalfFin13Atom0755 chi) ∨
      ((PredecessorHalfFin13Atom2001 chi ∧
      ¬PredecessorHalfFin13Atom0756 chi) ∨
      (PredecessorHalfFin13Atom2001 chi ∧
      ¬PredecessorHalfFin13Atom0791 chi)))) ∨
      (((PredecessorHalfFin13Atom2001 chi ∧
      ¬PredecessorHalfFin13Atom0966 chi) ∨
      ((PredecessorHalfFin13Atom2002 chi ∧
      ¬PredecessorHalfFin13Atom0757 chi) ∨
      (PredecessorHalfFin13Atom2002 chi ∧
      ¬PredecessorHalfFin13Atom0758 chi))) ∨
      ((PredecessorHalfFin13Atom2002 chi ∧
      ¬PredecessorHalfFin13Atom0762 chi) ∨
      ((PredecessorHalfFin13Atom2002 chi ∧
      ¬PredecessorHalfFin13Atom0772 chi) ∨
      (PredecessorHalfFin13Atom2002 chi ∧
      ¬PredecessorHalfFin13Atom0967 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom2002 chi ∧
      PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0967 chi) ∨
      ((PredecessorHalfFin13Atom2003 chi ∧
      ¬PredecessorHalfFin13Atom0757 chi) ∨
      (PredecessorHalfFin13Atom2003 chi ∧
      ¬PredecessorHalfFin13Atom0759 chi))) ∨
      ((PredecessorHalfFin13Atom2003 chi ∧
      ¬PredecessorHalfFin13Atom0763 chi) ∨
      ((PredecessorHalfFin13Atom2003 chi ∧
      ¬PredecessorHalfFin13Atom0773 chi) ∨
      (PredecessorHalfFin13Atom2003 chi ∧
      ¬PredecessorHalfFin13Atom0968 chi)))) ∨
      (((¬PredecessorHalfFin13Atom2003 chi ∧
      PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0968 chi) ∨
      ((PredecessorHalfFin13Atom2004 chi ∧
      ¬PredecessorHalfFin13Atom0757 chi) ∨
      (PredecessorHalfFin13Atom2004 chi ∧
      ¬PredecessorHalfFin13Atom0760 chi))) ∨
      (((PredecessorHalfFin13Atom2004 chi ∧
      ¬PredecessorHalfFin13Atom0764 chi) ∨
      (PredecessorHalfFin13Atom2004 chi ∧
      ¬PredecessorHalfFin13Atom0774 chi)) ∨
      ((PredecessorHalfFin13Atom2004 chi ∧
      ¬PredecessorHalfFin13Atom0969 chi) ∨
      (PredecessorHalfFin13Atom2005 chi ∧
      ¬PredecessorHalfFin13Atom0757 chi))))))))) := by
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
              exact predecessorHalfFin13_clause23070 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23071 chi hbad
              ·
                exact predecessorHalfFin13_clause23072 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23073 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23074 chi hbad
              ·
                exact predecessorHalfFin13_clause23075 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23077 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23078 chi hbad
              ·
                exact predecessorHalfFin13_clause23079 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23080 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23081 chi hbad
              ·
                exact predecessorHalfFin13_clause23082 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23083 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23085 chi hbad
              ·
                exact predecessorHalfFin13_clause23086 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23087 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23089 chi hbad
              ·
                exact predecessorHalfFin13_clause23090 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23091 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23092 chi hbad
              ·
                exact predecessorHalfFin13_clause23093 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23094 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23095 chi hbad
              ·
                exact predecessorHalfFin13_clause23096 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23098 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23099 chi hbad
              ·
                exact predecessorHalfFin13_clause23101 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23102 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23103 chi hbad
              ·
                exact predecessorHalfFin13_clause23104 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23105 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23106 chi hbad
              ·
                exact predecessorHalfFin13_clause23107 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23108 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23109 chi hbad
              ·
                exact predecessorHalfFin13_clause23110 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23111 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23113 chi hbad
              ·
                exact predecessorHalfFin13_clause23114 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23115 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23116 chi hbad
              ·
                exact predecessorHalfFin13_clause23117 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23118 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23119 chi hbad
              ·
                exact predecessorHalfFin13_clause23120 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23121 chi hbad
              ·
                exact predecessorHalfFin13_clause23122 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23123 chi hbad
              ·
                exact predecessorHalfFin13_clause23124 chi hbad
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
              exact predecessorHalfFin13_clause23125 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23126 chi hbad
              ·
                exact predecessorHalfFin13_clause23127 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23128 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23129 chi hbad
              ·
                exact predecessorHalfFin13_clause23130 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23132 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23133 chi hbad
              ·
                exact predecessorHalfFin13_clause23134 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23135 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23137 chi hbad
              ·
                exact predecessorHalfFin13_clause23138 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23139 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23140 chi hbad
              ·
                exact predecessorHalfFin13_clause23141 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23143 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23144 chi hbad
              ·
                exact predecessorHalfFin13_clause23145 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23146 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23147 chi hbad
              ·
                exact predecessorHalfFin13_clause23148 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23149 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23150 chi hbad
              ·
                exact predecessorHalfFin13_clause23151 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23152 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23153 chi hbad
              ·
                exact predecessorHalfFin13_clause23155 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23156 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23157 chi hbad
              ·
                exact predecessorHalfFin13_clause23158 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23159 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23161 chi hbad
              ·
                exact predecessorHalfFin13_clause23162 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23163 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23164 chi hbad
              ·
                exact predecessorHalfFin13_clause23165 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23166 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23167 chi hbad
              ·
                exact predecessorHalfFin13_clause23168 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23169 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23170 chi hbad
              ·
                exact predecessorHalfFin13_clause23171 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23172 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23173 chi hbad
              ·
                exact predecessorHalfFin13_clause23174 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23175 chi hbad
              ·
                exact predecessorHalfFin13_clause23176 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23177 chi hbad
              ·
                exact predecessorHalfFin13_clause23179 chi hbad

end ErdosSzekeres

end
