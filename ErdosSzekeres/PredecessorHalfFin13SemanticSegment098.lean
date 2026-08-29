module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk075
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk076

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 098. -/

theorem predecessorHalfFin13_rejectSemanticSegment098
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((¬PredecessorHalfFin13Atom1934 chi ∧
      PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0899 chi) ∨
      ((PredecessorHalfFin13Atom1935 chi ∧
      ¬PredecessorHalfFin13Atom0715 chi) ∨
      (PredecessorHalfFin13Atom1935 chi ∧
      ¬PredecessorHalfFin13Atom0719 chi))) ∨
      ((PredecessorHalfFin13Atom1935 chi ∧
      ¬PredecessorHalfFin13Atom0724 chi) ∨
      ((PredecessorHalfFin13Atom1935 chi ∧
      ¬PredecessorHalfFin13Atom0760 chi) ∨
      (PredecessorHalfFin13Atom1935 chi ∧
      ¬PredecessorHalfFin13Atom0900 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1935 chi ∧
      PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0719 chi ∧
      PredecessorHalfFin13Atom0724 chi ∧
      PredecessorHalfFin13Atom0760 chi ∧
      PredecessorHalfFin13Atom0900 chi) ∨
      ((PredecessorHalfFin13Atom1936 chi ∧
      ¬PredecessorHalfFin13Atom0715 chi) ∨
      (PredecessorHalfFin13Atom1936 chi ∧
      ¬PredecessorHalfFin13Atom0720 chi))) ∨
      ((PredecessorHalfFin13Atom1936 chi ∧
      ¬PredecessorHalfFin13Atom0725 chi) ∨
      ((PredecessorHalfFin13Atom1936 chi ∧
      ¬PredecessorHalfFin13Atom0761 chi) ∨
      (PredecessorHalfFin13Atom1936 chi ∧
      ¬PredecessorHalfFin13Atom0901 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom1936 chi ∧
      PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0901 chi) ∨
      ((PredecessorHalfFin13Atom1937 chi ∧
      ¬PredecessorHalfFin13Atom0716 chi) ∨
      (PredecessorHalfFin13Atom1937 chi ∧
      ¬PredecessorHalfFin13Atom0717 chi))) ∨
      ((PredecessorHalfFin13Atom1937 chi ∧
      ¬PredecessorHalfFin13Atom0726 chi) ∨
      ((PredecessorHalfFin13Atom1937 chi ∧
      ¬PredecessorHalfFin13Atom0762 chi) ∨
      (PredecessorHalfFin13Atom1937 chi ∧
      ¬PredecessorHalfFin13Atom0902 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1937 chi ∧
      PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0902 chi) ∨
      ((PredecessorHalfFin13Atom1938 chi ∧
      ¬PredecessorHalfFin13Atom0716 chi) ∨
      (PredecessorHalfFin13Atom1938 chi ∧
      ¬PredecessorHalfFin13Atom0718 chi))) ∨
      ((PredecessorHalfFin13Atom1938 chi ∧
      ¬PredecessorHalfFin13Atom0727 chi) ∨
      ((PredecessorHalfFin13Atom1938 chi ∧
      ¬PredecessorHalfFin13Atom0763 chi) ∨
      (PredecessorHalfFin13Atom1938 chi ∧
      ¬PredecessorHalfFin13Atom0903 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom1938 chi ∧
      PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0903 chi) ∨
      ((PredecessorHalfFin13Atom1939 chi ∧
      ¬PredecessorHalfFin13Atom0716 chi) ∨
      (PredecessorHalfFin13Atom1939 chi ∧
      ¬PredecessorHalfFin13Atom0719 chi))) ∨
      ((PredecessorHalfFin13Atom1939 chi ∧
      ¬PredecessorHalfFin13Atom0728 chi) ∨
      ((PredecessorHalfFin13Atom1939 chi ∧
      ¬PredecessorHalfFin13Atom0764 chi) ∨
      (PredecessorHalfFin13Atom1939 chi ∧
      ¬PredecessorHalfFin13Atom0904 chi)))) ∨
      (((PredecessorHalfFin13Atom1940 chi ∧
      ¬PredecessorHalfFin13Atom0716 chi) ∨
      ((PredecessorHalfFin13Atom1940 chi ∧
      ¬PredecessorHalfFin13Atom0720 chi) ∨
      (PredecessorHalfFin13Atom1940 chi ∧
      ¬PredecessorHalfFin13Atom0729 chi))) ∨
      ((PredecessorHalfFin13Atom1940 chi ∧
      ¬PredecessorHalfFin13Atom0765 chi) ∨
      ((PredecessorHalfFin13Atom1940 chi ∧
      ¬PredecessorHalfFin13Atom0905 chi) ∨
      (¬PredecessorHalfFin13Atom1940 chi ∧
      PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0905 chi))))) ∨
      ((((PredecessorHalfFin13Atom1941 chi ∧
      ¬PredecessorHalfFin13Atom0717 chi) ∨
      ((PredecessorHalfFin13Atom1941 chi ∧
      ¬PredecessorHalfFin13Atom0718 chi) ∨
      (PredecessorHalfFin13Atom1941 chi ∧
      ¬PredecessorHalfFin13Atom0730 chi))) ∨
      ((PredecessorHalfFin13Atom1941 chi ∧
      ¬PredecessorHalfFin13Atom0766 chi) ∨
      ((PredecessorHalfFin13Atom1941 chi ∧
      ¬PredecessorHalfFin13Atom0906 chi) ∨
      (¬PredecessorHalfFin13Atom1941 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0906 chi)))) ∨
      (((PredecessorHalfFin13Atom1942 chi ∧
      ¬PredecessorHalfFin13Atom0717 chi) ∨
      ((PredecessorHalfFin13Atom1942 chi ∧
      ¬PredecessorHalfFin13Atom0719 chi) ∨
      (PredecessorHalfFin13Atom1942 chi ∧
      ¬PredecessorHalfFin13Atom0731 chi))) ∨
      (((PredecessorHalfFin13Atom1942 chi ∧
      ¬PredecessorHalfFin13Atom0767 chi) ∨
      (PredecessorHalfFin13Atom1942 chi ∧
      ¬PredecessorHalfFin13Atom0907 chi)) ∨
      ((PredecessorHalfFin13Atom1943 chi ∧
      ¬PredecessorHalfFin13Atom0717 chi) ∨
      (PredecessorHalfFin13Atom1943 chi ∧
      ¬PredecessorHalfFin13Atom0720 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom1943 chi ∧
      ¬PredecessorHalfFin13Atom0732 chi) ∨
      ((PredecessorHalfFin13Atom1943 chi ∧
      ¬PredecessorHalfFin13Atom0768 chi) ∨
      (PredecessorHalfFin13Atom1943 chi ∧
      ¬PredecessorHalfFin13Atom0908 chi))) ∨
      ((¬PredecessorHalfFin13Atom1943 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0908 chi) ∨
      ((PredecessorHalfFin13Atom1944 chi ∧
      ¬PredecessorHalfFin13Atom0718 chi) ∨
      (PredecessorHalfFin13Atom1944 chi ∧
      ¬PredecessorHalfFin13Atom0719 chi)))) ∨
      (((PredecessorHalfFin13Atom1944 chi ∧
      ¬PredecessorHalfFin13Atom0733 chi) ∨
      ((PredecessorHalfFin13Atom1944 chi ∧
      ¬PredecessorHalfFin13Atom0769 chi) ∨
      (PredecessorHalfFin13Atom1944 chi ∧
      ¬PredecessorHalfFin13Atom0909 chi))) ∨
      ((PredecessorHalfFin13Atom1945 chi ∧
      ¬PredecessorHalfFin13Atom0718 chi) ∨
      ((PredecessorHalfFin13Atom1945 chi ∧
      ¬PredecessorHalfFin13Atom0720 chi) ∨
      (PredecessorHalfFin13Atom1945 chi ∧
      ¬PredecessorHalfFin13Atom0734 chi))))) ∨
      ((((PredecessorHalfFin13Atom1945 chi ∧
      ¬PredecessorHalfFin13Atom0770 chi) ∨
      ((PredecessorHalfFin13Atom1945 chi ∧
      ¬PredecessorHalfFin13Atom0910 chi) ∨
      (¬PredecessorHalfFin13Atom1945 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0910 chi))) ∨
      ((PredecessorHalfFin13Atom1946 chi ∧
      ¬PredecessorHalfFin13Atom0719 chi) ∨
      ((PredecessorHalfFin13Atom1946 chi ∧
      ¬PredecessorHalfFin13Atom0720 chi) ∨
      (PredecessorHalfFin13Atom1946 chi ∧
      ¬PredecessorHalfFin13Atom0735 chi)))) ∨
      (((PredecessorHalfFin13Atom1946 chi ∧
      ¬PredecessorHalfFin13Atom0771 chi) ∨
      ((PredecessorHalfFin13Atom1946 chi ∧
      ¬PredecessorHalfFin13Atom0911 chi) ∨
      (PredecessorHalfFin13Atom1947 chi ∧
      ¬PredecessorHalfFin13Atom0721 chi))) ∨
      ((PredecessorHalfFin13Atom1947 chi ∧
      ¬PredecessorHalfFin13Atom0722 chi) ∨
      ((PredecessorHalfFin13Atom1947 chi ∧
      ¬PredecessorHalfFin13Atom0726 chi) ∨
      (PredecessorHalfFin13Atom1947 chi ∧
      ¬PredecessorHalfFin13Atom0772 chi)))))) ∨
      (((((PredecessorHalfFin13Atom1947 chi ∧
      ¬PredecessorHalfFin13Atom0912 chi) ∨
      ((¬PredecessorHalfFin13Atom1947 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0912 chi) ∨
      (PredecessorHalfFin13Atom1948 chi ∧
      ¬PredecessorHalfFin13Atom0721 chi))) ∨
      ((PredecessorHalfFin13Atom1948 chi ∧
      ¬PredecessorHalfFin13Atom0723 chi) ∨
      ((PredecessorHalfFin13Atom1948 chi ∧
      ¬PredecessorHalfFin13Atom0727 chi) ∨
      (PredecessorHalfFin13Atom1948 chi ∧
      ¬PredecessorHalfFin13Atom0773 chi)))) ∨
      (((PredecessorHalfFin13Atom1948 chi ∧
      ¬PredecessorHalfFin13Atom0913 chi) ∨
      ((¬PredecessorHalfFin13Atom1948 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0913 chi) ∨
      (PredecessorHalfFin13Atom1949 chi ∧
      ¬PredecessorHalfFin13Atom0721 chi))) ∨
      ((PredecessorHalfFin13Atom1949 chi ∧
      ¬PredecessorHalfFin13Atom0724 chi) ∨
      ((PredecessorHalfFin13Atom1949 chi ∧
      ¬PredecessorHalfFin13Atom0728 chi) ∨
      (PredecessorHalfFin13Atom1949 chi ∧
      ¬PredecessorHalfFin13Atom0774 chi))))) ∨
      ((((PredecessorHalfFin13Atom1949 chi ∧
      ¬PredecessorHalfFin13Atom0914 chi) ∨
      ((¬PredecessorHalfFin13Atom1949 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0724 chi ∧
      PredecessorHalfFin13Atom0728 chi ∧
      PredecessorHalfFin13Atom0774 chi ∧
      PredecessorHalfFin13Atom0914 chi) ∨
      (PredecessorHalfFin13Atom1950 chi ∧
      ¬PredecessorHalfFin13Atom0721 chi))) ∨
      ((PredecessorHalfFin13Atom1950 chi ∧
      ¬PredecessorHalfFin13Atom0725 chi) ∨
      ((PredecessorHalfFin13Atom1950 chi ∧
      ¬PredecessorHalfFin13Atom0729 chi) ∨
      (PredecessorHalfFin13Atom1950 chi ∧
      ¬PredecessorHalfFin13Atom0775 chi)))) ∨
      (((PredecessorHalfFin13Atom1950 chi ∧
      ¬PredecessorHalfFin13Atom0915 chi) ∨
      ((¬PredecessorHalfFin13Atom1950 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0915 chi) ∨
      (PredecessorHalfFin13Atom1951 chi ∧
      ¬PredecessorHalfFin13Atom0722 chi))) ∨
      (((PredecessorHalfFin13Atom1951 chi ∧
      ¬PredecessorHalfFin13Atom0723 chi) ∨
      (PredecessorHalfFin13Atom1951 chi ∧
      ¬PredecessorHalfFin13Atom0730 chi)) ∨
      ((PredecessorHalfFin13Atom1951 chi ∧
      ¬PredecessorHalfFin13Atom0776 chi) ∨
      (PredecessorHalfFin13Atom1951 chi ∧
      ¬PredecessorHalfFin13Atom0916 chi))))))))) := by
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
              exact predecessorHalfFin13_clause22758 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22759 chi hbad
              ·
                exact predecessorHalfFin13_clause22760 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22761 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22762 chi hbad
              ·
                exact predecessorHalfFin13_clause22763 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22764 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22765 chi hbad
              ·
                exact predecessorHalfFin13_clause22766 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22767 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22768 chi hbad
              ·
                exact predecessorHalfFin13_clause22769 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22770 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22771 chi hbad
              ·
                exact predecessorHalfFin13_clause22772 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22773 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22774 chi hbad
              ·
                exact predecessorHalfFin13_clause22775 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22776 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22777 chi hbad
              ·
                exact predecessorHalfFin13_clause22778 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22779 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22780 chi hbad
              ·
                exact predecessorHalfFin13_clause22781 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22782 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22783 chi hbad
              ·
                exact predecessorHalfFin13_clause22784 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22785 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22786 chi hbad
              ·
                exact predecessorHalfFin13_clause22787 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22789 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22790 chi hbad
              ·
                exact predecessorHalfFin13_clause22791 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22792 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22793 chi hbad
              ·
                exact predecessorHalfFin13_clause22794 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22795 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22796 chi hbad
              ·
                exact predecessorHalfFin13_clause22797 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22798 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22799 chi hbad
              ·
                exact predecessorHalfFin13_clause22800 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22801 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22802 chi hbad
              ·
                exact predecessorHalfFin13_clause22803 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22804 chi hbad
              ·
                exact predecessorHalfFin13_clause22805 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22807 chi hbad
              ·
                exact predecessorHalfFin13_clause22808 chi hbad
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
              exact predecessorHalfFin13_clause22809 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22810 chi hbad
              ·
                exact predecessorHalfFin13_clause22811 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22812 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22813 chi hbad
              ·
                exact predecessorHalfFin13_clause22814 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22815 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22816 chi hbad
              ·
                exact predecessorHalfFin13_clause22817 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22819 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22820 chi hbad
              ·
                exact predecessorHalfFin13_clause22821 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22822 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22823 chi hbad
              ·
                exact predecessorHalfFin13_clause22824 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22825 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22826 chi hbad
              ·
                exact predecessorHalfFin13_clause22827 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22828 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22829 chi hbad
              ·
                exact predecessorHalfFin13_clause22831 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22832 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22833 chi hbad
              ·
                exact predecessorHalfFin13_clause22834 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22835 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22836 chi hbad
              ·
                exact predecessorHalfFin13_clause22837 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22838 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22839 chi hbad
              ·
                exact predecessorHalfFin13_clause22840 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22841 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22842 chi hbad
              ·
                exact predecessorHalfFin13_clause22843 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22844 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22845 chi hbad
              ·
                exact predecessorHalfFin13_clause22846 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22847 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22848 chi hbad
              ·
                exact predecessorHalfFin13_clause22849 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22850 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22851 chi hbad
              ·
                exact predecessorHalfFin13_clause22852 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22853 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22854 chi hbad
              ·
                exact predecessorHalfFin13_clause22855 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22856 chi hbad
              ·
                exact predecessorHalfFin13_clause22857 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22858 chi hbad
              ·
                exact predecessorHalfFin13_clause22859 chi hbad

end ErdosSzekeres

end
