module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk076

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 099. -/

theorem predecessorHalfFin13_rejectSemanticSegment099
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((¬PredecessorHalfFin13Atom1951 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0916 chi) ∨
      ((PredecessorHalfFin13Atom1952 chi ∧
      ¬PredecessorHalfFin13Atom0722 chi) ∨
      (PredecessorHalfFin13Atom1952 chi ∧
      ¬PredecessorHalfFin13Atom0724 chi))) ∨
      ((PredecessorHalfFin13Atom1952 chi ∧
      ¬PredecessorHalfFin13Atom0731 chi) ∨
      ((PredecessorHalfFin13Atom1952 chi ∧
      ¬PredecessorHalfFin13Atom0777 chi) ∨
      (PredecessorHalfFin13Atom1952 chi ∧
      ¬PredecessorHalfFin13Atom0917 chi)))) ∨
      (((PredecessorHalfFin13Atom1953 chi ∧
      ¬PredecessorHalfFin13Atom0722 chi) ∨
      ((PredecessorHalfFin13Atom1953 chi ∧
      ¬PredecessorHalfFin13Atom0725 chi) ∨
      (PredecessorHalfFin13Atom1953 chi ∧
      ¬PredecessorHalfFin13Atom0732 chi))) ∨
      ((PredecessorHalfFin13Atom1953 chi ∧
      ¬PredecessorHalfFin13Atom0778 chi) ∨
      ((PredecessorHalfFin13Atom1953 chi ∧
      ¬PredecessorHalfFin13Atom0918 chi) ∨
      (¬PredecessorHalfFin13Atom1953 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0918 chi))))) ∨
      ((((PredecessorHalfFin13Atom1954 chi ∧
      ¬PredecessorHalfFin13Atom0723 chi) ∨
      ((PredecessorHalfFin13Atom1954 chi ∧
      ¬PredecessorHalfFin13Atom0724 chi) ∨
      (PredecessorHalfFin13Atom1954 chi ∧
      ¬PredecessorHalfFin13Atom0733 chi))) ∨
      ((PredecessorHalfFin13Atom1954 chi ∧
      ¬PredecessorHalfFin13Atom0779 chi) ∨
      ((PredecessorHalfFin13Atom1954 chi ∧
      ¬PredecessorHalfFin13Atom0919 chi) ∨
      (¬PredecessorHalfFin13Atom1954 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0724 chi ∧
      PredecessorHalfFin13Atom0733 chi ∧
      PredecessorHalfFin13Atom0779 chi ∧
      PredecessorHalfFin13Atom0919 chi)))) ∨
      (((PredecessorHalfFin13Atom1955 chi ∧
      ¬PredecessorHalfFin13Atom0723 chi) ∨
      ((PredecessorHalfFin13Atom1955 chi ∧
      ¬PredecessorHalfFin13Atom0725 chi) ∨
      (PredecessorHalfFin13Atom1955 chi ∧
      ¬PredecessorHalfFin13Atom0734 chi))) ∨
      ((PredecessorHalfFin13Atom1955 chi ∧
      ¬PredecessorHalfFin13Atom0780 chi) ∨
      ((PredecessorHalfFin13Atom1955 chi ∧
      ¬PredecessorHalfFin13Atom0920 chi) ∨
      (¬PredecessorHalfFin13Atom1955 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0920 chi)))))) ∨
      (((((PredecessorHalfFin13Atom1956 chi ∧
      ¬PredecessorHalfFin13Atom0724 chi) ∨
      ((PredecessorHalfFin13Atom1956 chi ∧
      ¬PredecessorHalfFin13Atom0725 chi) ∨
      (PredecessorHalfFin13Atom1956 chi ∧
      ¬PredecessorHalfFin13Atom0735 chi))) ∨
      ((PredecessorHalfFin13Atom1956 chi ∧
      ¬PredecessorHalfFin13Atom0781 chi) ∨
      ((PredecessorHalfFin13Atom1956 chi ∧
      ¬PredecessorHalfFin13Atom0921 chi) ∨
      (PredecessorHalfFin13Atom1957 chi ∧
      ¬PredecessorHalfFin13Atom0726 chi)))) ∨
      (((PredecessorHalfFin13Atom1957 chi ∧
      ¬PredecessorHalfFin13Atom0727 chi) ∨
      ((PredecessorHalfFin13Atom1957 chi ∧
      ¬PredecessorHalfFin13Atom0730 chi) ∨
      (PredecessorHalfFin13Atom1957 chi ∧
      ¬PredecessorHalfFin13Atom0782 chi))) ∨
      ((PredecessorHalfFin13Atom1957 chi ∧
      ¬PredecessorHalfFin13Atom0922 chi) ∨
      ((¬PredecessorHalfFin13Atom1957 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0922 chi) ∨
      (PredecessorHalfFin13Atom1958 chi ∧
      ¬PredecessorHalfFin13Atom0726 chi))))) ∨
      ((((PredecessorHalfFin13Atom1958 chi ∧
      ¬PredecessorHalfFin13Atom0728 chi) ∨
      ((PredecessorHalfFin13Atom1958 chi ∧
      ¬PredecessorHalfFin13Atom0731 chi) ∨
      (PredecessorHalfFin13Atom1958 chi ∧
      ¬PredecessorHalfFin13Atom0783 chi))) ∨
      ((PredecessorHalfFin13Atom1958 chi ∧
      ¬PredecessorHalfFin13Atom0923 chi) ∨
      ((¬PredecessorHalfFin13Atom1958 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0728 chi ∧
      PredecessorHalfFin13Atom0731 chi ∧
      PredecessorHalfFin13Atom0783 chi ∧
      PredecessorHalfFin13Atom0923 chi) ∨
      (PredecessorHalfFin13Atom1959 chi ∧
      ¬PredecessorHalfFin13Atom0726 chi)))) ∨
      (((PredecessorHalfFin13Atom1959 chi ∧
      ¬PredecessorHalfFin13Atom0729 chi) ∨
      ((PredecessorHalfFin13Atom1959 chi ∧
      ¬PredecessorHalfFin13Atom0732 chi) ∨
      (PredecessorHalfFin13Atom1959 chi ∧
      ¬PredecessorHalfFin13Atom0784 chi))) ∨
      (((PredecessorHalfFin13Atom1959 chi ∧
      ¬PredecessorHalfFin13Atom0924 chi) ∨
      (¬PredecessorHalfFin13Atom1959 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0924 chi)) ∨
      ((PredecessorHalfFin13Atom1960 chi ∧
      ¬PredecessorHalfFin13Atom0727 chi) ∨
      (PredecessorHalfFin13Atom1960 chi ∧
      ¬PredecessorHalfFin13Atom0728 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom1960 chi ∧
      ¬PredecessorHalfFin13Atom0733 chi) ∨
      ((PredecessorHalfFin13Atom1960 chi ∧
      ¬PredecessorHalfFin13Atom0785 chi) ∨
      (PredecessorHalfFin13Atom1960 chi ∧
      ¬PredecessorHalfFin13Atom0925 chi))) ∨
      ((¬PredecessorHalfFin13Atom1960 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0728 chi ∧
      PredecessorHalfFin13Atom0733 chi ∧
      PredecessorHalfFin13Atom0785 chi ∧
      PredecessorHalfFin13Atom0925 chi) ∨
      ((PredecessorHalfFin13Atom1961 chi ∧
      ¬PredecessorHalfFin13Atom0727 chi) ∨
      (PredecessorHalfFin13Atom1961 chi ∧
      ¬PredecessorHalfFin13Atom0729 chi)))) ∨
      (((PredecessorHalfFin13Atom1961 chi ∧
      ¬PredecessorHalfFin13Atom0734 chi) ∨
      ((PredecessorHalfFin13Atom1961 chi ∧
      ¬PredecessorHalfFin13Atom0786 chi) ∨
      (PredecessorHalfFin13Atom1961 chi ∧
      ¬PredecessorHalfFin13Atom0926 chi))) ∨
      ((¬PredecessorHalfFin13Atom1961 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0926 chi) ∨
      ((PredecessorHalfFin13Atom1962 chi ∧
      ¬PredecessorHalfFin13Atom0728 chi) ∨
      (PredecessorHalfFin13Atom1962 chi ∧
      ¬PredecessorHalfFin13Atom0729 chi))))) ∨
      ((((PredecessorHalfFin13Atom1962 chi ∧
      ¬PredecessorHalfFin13Atom0787 chi) ∨
      ((PredecessorHalfFin13Atom1962 chi ∧
      ¬PredecessorHalfFin13Atom0927 chi) ∨
      (PredecessorHalfFin13Atom1963 chi ∧
      ¬PredecessorHalfFin13Atom0730 chi))) ∨
      ((PredecessorHalfFin13Atom1963 chi ∧
      ¬PredecessorHalfFin13Atom0731 chi) ∨
      ((PredecessorHalfFin13Atom1963 chi ∧
      ¬PredecessorHalfFin13Atom0733 chi) ∨
      (PredecessorHalfFin13Atom1963 chi ∧
      ¬PredecessorHalfFin13Atom0788 chi)))) ∨
      (((PredecessorHalfFin13Atom1963 chi ∧
      ¬PredecessorHalfFin13Atom0928 chi) ∨
      ((¬PredecessorHalfFin13Atom1963 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0731 chi ∧
      PredecessorHalfFin13Atom0733 chi ∧
      PredecessorHalfFin13Atom0788 chi ∧
      PredecessorHalfFin13Atom0928 chi) ∨
      (PredecessorHalfFin13Atom1964 chi ∧
      ¬PredecessorHalfFin13Atom0730 chi))) ∨
      (((PredecessorHalfFin13Atom1964 chi ∧
      ¬PredecessorHalfFin13Atom0732 chi) ∨
      (PredecessorHalfFin13Atom1964 chi ∧
      ¬PredecessorHalfFin13Atom0734 chi)) ∨
      ((PredecessorHalfFin13Atom1964 chi ∧
      ¬PredecessorHalfFin13Atom0789 chi) ∨
      (PredecessorHalfFin13Atom1964 chi ∧
      ¬PredecessorHalfFin13Atom0929 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom1964 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0929 chi) ∨
      ((PredecessorHalfFin13Atom1965 chi ∧
      ¬PredecessorHalfFin13Atom0731 chi) ∨
      (PredecessorHalfFin13Atom1965 chi ∧
      ¬PredecessorHalfFin13Atom0732 chi))) ∨
      ((PredecessorHalfFin13Atom1965 chi ∧
      ¬PredecessorHalfFin13Atom0790 chi) ∨
      ((PredecessorHalfFin13Atom1965 chi ∧
      ¬PredecessorHalfFin13Atom0930 chi) ∨
      (PredecessorHalfFin13Atom1966 chi ∧
      ¬PredecessorHalfFin13Atom0733 chi)))) ∨
      (((PredecessorHalfFin13Atom1966 chi ∧
      ¬PredecessorHalfFin13Atom0734 chi) ∨
      ((PredecessorHalfFin13Atom1966 chi ∧
      ¬PredecessorHalfFin13Atom0791 chi) ∨
      (PredecessorHalfFin13Atom1966 chi ∧
      ¬PredecessorHalfFin13Atom0931 chi))) ∨
      ((PredecessorHalfFin13Atom1967 chi ∧
      ¬PredecessorHalfFin13Atom0736 chi) ∨
      ((PredecessorHalfFin13Atom1967 chi ∧
      ¬PredecessorHalfFin13Atom0737 chi) ∨
      (PredecessorHalfFin13Atom1967 chi ∧
      ¬PredecessorHalfFin13Atom0742 chi))))) ∨
      ((((PredecessorHalfFin13Atom1967 chi ∧
      ¬PredecessorHalfFin13Atom0757 chi) ∨
      ((PredecessorHalfFin13Atom1967 chi ∧
      ¬PredecessorHalfFin13Atom0932 chi) ∨
      (¬PredecessorHalfFin13Atom1967 chi ∧
      PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0932 chi))) ∨
      ((PredecessorHalfFin13Atom1968 chi ∧
      ¬PredecessorHalfFin13Atom0736 chi) ∨
      ((PredecessorHalfFin13Atom1968 chi ∧
      ¬PredecessorHalfFin13Atom0738 chi) ∨
      (PredecessorHalfFin13Atom1968 chi ∧
      ¬PredecessorHalfFin13Atom0743 chi)))) ∨
      (((PredecessorHalfFin13Atom1968 chi ∧
      ¬PredecessorHalfFin13Atom0758 chi) ∨
      ((PredecessorHalfFin13Atom1968 chi ∧
      ¬PredecessorHalfFin13Atom0933 chi) ∨
      (¬PredecessorHalfFin13Atom1968 chi ∧
      PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0933 chi))) ∨
      (((PredecessorHalfFin13Atom1969 chi ∧
      ¬PredecessorHalfFin13Atom0736 chi) ∨
      (PredecessorHalfFin13Atom1969 chi ∧
      ¬PredecessorHalfFin13Atom0739 chi)) ∨
      ((PredecessorHalfFin13Atom1969 chi ∧
      ¬PredecessorHalfFin13Atom0744 chi) ∨
      (PredecessorHalfFin13Atom1969 chi ∧
      ¬PredecessorHalfFin13Atom0759 chi))))))))) := by
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
              exact predecessorHalfFin13_clause22860 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22861 chi hbad
              ·
                exact predecessorHalfFin13_clause22862 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22863 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22864 chi hbad
              ·
                exact predecessorHalfFin13_clause22865 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22867 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22868 chi hbad
              ·
                exact predecessorHalfFin13_clause22869 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22870 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22871 chi hbad
              ·
                exact predecessorHalfFin13_clause22872 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22873 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22874 chi hbad
              ·
                exact predecessorHalfFin13_clause22875 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22876 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22877 chi hbad
              ·
                exact predecessorHalfFin13_clause22878 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22879 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22880 chi hbad
              ·
                exact predecessorHalfFin13_clause22881 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22882 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22883 chi hbad
              ·
                exact predecessorHalfFin13_clause22884 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22885 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22886 chi hbad
              ·
                exact predecessorHalfFin13_clause22887 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22888 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22889 chi hbad
              ·
                exact predecessorHalfFin13_clause22891 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22892 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22893 chi hbad
              ·
                exact predecessorHalfFin13_clause22894 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22895 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22896 chi hbad
              ·
                exact predecessorHalfFin13_clause22897 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22898 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22899 chi hbad
              ·
                exact predecessorHalfFin13_clause22900 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22901 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22902 chi hbad
              ·
                exact predecessorHalfFin13_clause22903 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22904 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22905 chi hbad
              ·
                exact predecessorHalfFin13_clause22906 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22907 chi hbad
              ·
                exact predecessorHalfFin13_clause22908 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22909 chi hbad
              ·
                exact predecessorHalfFin13_clause22910 chi hbad
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
              exact predecessorHalfFin13_clause22911 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22912 chi hbad
              ·
                exact predecessorHalfFin13_clause22913 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22914 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22915 chi hbad
              ·
                exact predecessorHalfFin13_clause22916 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22917 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22918 chi hbad
              ·
                exact predecessorHalfFin13_clause22919 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22920 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22921 chi hbad
              ·
                exact predecessorHalfFin13_clause22922 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22924 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22925 chi hbad
              ·
                exact predecessorHalfFin13_clause22927 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22928 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22929 chi hbad
              ·
                exact predecessorHalfFin13_clause22930 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22931 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22932 chi hbad
              ·
                exact predecessorHalfFin13_clause22933 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22934 chi hbad
              ·
                exact predecessorHalfFin13_clause22935 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22936 chi hbad
              ·
                exact predecessorHalfFin13_clause22937 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22938 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22939 chi hbad
              ·
                exact predecessorHalfFin13_clause22940 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22942 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22943 chi hbad
              ·
                exact predecessorHalfFin13_clause22945 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22946 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22948 chi hbad
              ·
                exact predecessorHalfFin13_clause22949 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22951 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22952 chi hbad
              ·
                exact predecessorHalfFin13_clause22953 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22954 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22955 chi hbad
              ·
                exact predecessorHalfFin13_clause22956 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22957 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22958 chi hbad
              ·
                exact predecessorHalfFin13_clause22959 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22960 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22961 chi hbad
              ·
                exact predecessorHalfFin13_clause22962 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22963 chi hbad
              ·
                exact predecessorHalfFin13_clause22964 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22965 chi hbad
              ·
                exact predecessorHalfFin13_clause22966 chi hbad

end ErdosSzekeres

end
