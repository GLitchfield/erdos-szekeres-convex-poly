module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk074
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk075

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 097. -/

theorem predecessorHalfFin13_rejectSemanticSegment097
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom1918 chi ∧
      ¬PredecessorHalfFin13Atom0711 chi) ∨
      ((PredecessorHalfFin13Atom1918 chi ∧
      ¬PredecessorHalfFin13Atom0722 chi) ∨
      (PredecessorHalfFin13Atom1918 chi ∧
      ¬PredecessorHalfFin13Atom0743 chi))) ∨
      ((PredecessorHalfFin13Atom1918 chi ∧
      ¬PredecessorHalfFin13Atom0883 chi) ∨
      ((¬PredecessorHalfFin13Atom1918 chi ∧
      PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0883 chi) ∨
      (PredecessorHalfFin13Atom1919 chi ∧
      ¬PredecessorHalfFin13Atom0709 chi)))) ∨
      (((PredecessorHalfFin13Atom1919 chi ∧
      ¬PredecessorHalfFin13Atom0712 chi) ∨
      ((PredecessorHalfFin13Atom1919 chi ∧
      ¬PredecessorHalfFin13Atom0723 chi) ∨
      (PredecessorHalfFin13Atom1919 chi ∧
      ¬PredecessorHalfFin13Atom0744 chi))) ∨
      ((PredecessorHalfFin13Atom1919 chi ∧
      ¬PredecessorHalfFin13Atom0884 chi) ∨
      ((¬PredecessorHalfFin13Atom1919 chi ∧
      PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0884 chi) ∨
      (PredecessorHalfFin13Atom1920 chi ∧
      ¬PredecessorHalfFin13Atom0709 chi))))) ∨
      ((((PredecessorHalfFin13Atom1920 chi ∧
      ¬PredecessorHalfFin13Atom0713 chi) ∨
      ((PredecessorHalfFin13Atom1920 chi ∧
      ¬PredecessorHalfFin13Atom0724 chi) ∨
      (PredecessorHalfFin13Atom1920 chi ∧
      ¬PredecessorHalfFin13Atom0745 chi))) ∨
      ((PredecessorHalfFin13Atom1920 chi ∧
      ¬PredecessorHalfFin13Atom0885 chi) ∨
      ((¬PredecessorHalfFin13Atom1920 chi ∧
      PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0713 chi ∧
      PredecessorHalfFin13Atom0724 chi ∧
      PredecessorHalfFin13Atom0745 chi ∧
      PredecessorHalfFin13Atom0885 chi) ∨
      (PredecessorHalfFin13Atom1921 chi ∧
      ¬PredecessorHalfFin13Atom0709 chi)))) ∨
      (((PredecessorHalfFin13Atom1921 chi ∧
      ¬PredecessorHalfFin13Atom0714 chi) ∨
      ((PredecessorHalfFin13Atom1921 chi ∧
      ¬PredecessorHalfFin13Atom0725 chi) ∨
      (PredecessorHalfFin13Atom1921 chi ∧
      ¬PredecessorHalfFin13Atom0746 chi))) ∨
      ((PredecessorHalfFin13Atom1921 chi ∧
      ¬PredecessorHalfFin13Atom0886 chi) ∨
      ((¬PredecessorHalfFin13Atom1921 chi ∧
      PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0886 chi) ∨
      (PredecessorHalfFin13Atom1922 chi ∧
      ¬PredecessorHalfFin13Atom0710 chi)))))) ∨
      (((((PredecessorHalfFin13Atom1922 chi ∧
      ¬PredecessorHalfFin13Atom0711 chi) ∨
      ((PredecessorHalfFin13Atom1922 chi ∧
      ¬PredecessorHalfFin13Atom0726 chi) ∨
      (PredecessorHalfFin13Atom1922 chi ∧
      ¬PredecessorHalfFin13Atom0747 chi))) ∨
      ((PredecessorHalfFin13Atom1922 chi ∧
      ¬PredecessorHalfFin13Atom0887 chi) ∨
      ((¬PredecessorHalfFin13Atom1922 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0887 chi) ∨
      (PredecessorHalfFin13Atom1923 chi ∧
      ¬PredecessorHalfFin13Atom0710 chi)))) ∨
      (((PredecessorHalfFin13Atom1923 chi ∧
      ¬PredecessorHalfFin13Atom0712 chi) ∨
      ((PredecessorHalfFin13Atom1923 chi ∧
      ¬PredecessorHalfFin13Atom0727 chi) ∨
      (PredecessorHalfFin13Atom1923 chi ∧
      ¬PredecessorHalfFin13Atom0748 chi))) ∨
      ((PredecessorHalfFin13Atom1923 chi ∧
      ¬PredecessorHalfFin13Atom0888 chi) ∨
      ((¬PredecessorHalfFin13Atom1923 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0888 chi) ∨
      (PredecessorHalfFin13Atom1924 chi ∧
      ¬PredecessorHalfFin13Atom0710 chi))))) ∨
      ((((PredecessorHalfFin13Atom1924 chi ∧
      ¬PredecessorHalfFin13Atom0713 chi) ∨
      ((PredecessorHalfFin13Atom1924 chi ∧
      ¬PredecessorHalfFin13Atom0728 chi) ∨
      (PredecessorHalfFin13Atom1924 chi ∧
      ¬PredecessorHalfFin13Atom0749 chi))) ∨
      ((PredecessorHalfFin13Atom1924 chi ∧
      ¬PredecessorHalfFin13Atom0889 chi) ∨
      ((PredecessorHalfFin13Atom1925 chi ∧
      ¬PredecessorHalfFin13Atom0710 chi) ∨
      (PredecessorHalfFin13Atom1925 chi ∧
      ¬PredecessorHalfFin13Atom0714 chi)))) ∨
      (((PredecessorHalfFin13Atom1925 chi ∧
      ¬PredecessorHalfFin13Atom0729 chi) ∨
      ((PredecessorHalfFin13Atom1925 chi ∧
      ¬PredecessorHalfFin13Atom0750 chi) ∨
      (PredecessorHalfFin13Atom1925 chi ∧
      ¬PredecessorHalfFin13Atom0890 chi))) ∨
      (((¬PredecessorHalfFin13Atom1925 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0890 chi) ∨
      (PredecessorHalfFin13Atom1926 chi ∧
      ¬PredecessorHalfFin13Atom0711 chi)) ∨
      ((PredecessorHalfFin13Atom1926 chi ∧
      ¬PredecessorHalfFin13Atom0712 chi) ∨
      (PredecessorHalfFin13Atom1926 chi ∧
      ¬PredecessorHalfFin13Atom0730 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom1926 chi ∧
      ¬PredecessorHalfFin13Atom0751 chi) ∨
      ((PredecessorHalfFin13Atom1926 chi ∧
      ¬PredecessorHalfFin13Atom0891 chi) ∨
      (¬PredecessorHalfFin13Atom1926 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0891 chi))) ∨
      ((PredecessorHalfFin13Atom1927 chi ∧
      ¬PredecessorHalfFin13Atom0711 chi) ∨
      ((PredecessorHalfFin13Atom1927 chi ∧
      ¬PredecessorHalfFin13Atom0713 chi) ∨
      (PredecessorHalfFin13Atom1927 chi ∧
      ¬PredecessorHalfFin13Atom0731 chi)))) ∨
      (((PredecessorHalfFin13Atom1927 chi ∧
      ¬PredecessorHalfFin13Atom0752 chi) ∨
      ((PredecessorHalfFin13Atom1927 chi ∧
      ¬PredecessorHalfFin13Atom0892 chi) ∨
      (¬PredecessorHalfFin13Atom1927 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0713 chi ∧
      PredecessorHalfFin13Atom0731 chi ∧
      PredecessorHalfFin13Atom0752 chi ∧
      PredecessorHalfFin13Atom0892 chi))) ∨
      ((PredecessorHalfFin13Atom1928 chi ∧
      ¬PredecessorHalfFin13Atom0711 chi) ∨
      ((PredecessorHalfFin13Atom1928 chi ∧
      ¬PredecessorHalfFin13Atom0714 chi) ∨
      (PredecessorHalfFin13Atom1928 chi ∧
      ¬PredecessorHalfFin13Atom0732 chi))))) ∨
      ((((PredecessorHalfFin13Atom1928 chi ∧
      ¬PredecessorHalfFin13Atom0753 chi) ∨
      ((PredecessorHalfFin13Atom1928 chi ∧
      ¬PredecessorHalfFin13Atom0893 chi) ∨
      (¬PredecessorHalfFin13Atom1928 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0893 chi))) ∨
      ((PredecessorHalfFin13Atom1929 chi ∧
      ¬PredecessorHalfFin13Atom0712 chi) ∨
      ((PredecessorHalfFin13Atom1929 chi ∧
      ¬PredecessorHalfFin13Atom0713 chi) ∨
      (PredecessorHalfFin13Atom1929 chi ∧
      ¬PredecessorHalfFin13Atom0733 chi)))) ∨
      (((PredecessorHalfFin13Atom1929 chi ∧
      ¬PredecessorHalfFin13Atom0754 chi) ∨
      ((PredecessorHalfFin13Atom1929 chi ∧
      ¬PredecessorHalfFin13Atom0894 chi) ∨
      (¬PredecessorHalfFin13Atom1929 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0713 chi ∧
      PredecessorHalfFin13Atom0733 chi ∧
      PredecessorHalfFin13Atom0754 chi ∧
      PredecessorHalfFin13Atom0894 chi))) ∨
      ((PredecessorHalfFin13Atom1930 chi ∧
      ¬PredecessorHalfFin13Atom0712 chi) ∨
      ((PredecessorHalfFin13Atom1930 chi ∧
      ¬PredecessorHalfFin13Atom0714 chi) ∨
      (PredecessorHalfFin13Atom1930 chi ∧
      ¬PredecessorHalfFin13Atom0734 chi)))))) ∨
      (((((PredecessorHalfFin13Atom1930 chi ∧
      ¬PredecessorHalfFin13Atom0755 chi) ∨
      ((PredecessorHalfFin13Atom1930 chi ∧
      ¬PredecessorHalfFin13Atom0895 chi) ∨
      (¬PredecessorHalfFin13Atom1930 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0895 chi))) ∨
      ((PredecessorHalfFin13Atom1931 chi ∧
      ¬PredecessorHalfFin13Atom0713 chi) ∨
      ((PredecessorHalfFin13Atom1931 chi ∧
      ¬PredecessorHalfFin13Atom0714 chi) ∨
      (PredecessorHalfFin13Atom1931 chi ∧
      ¬PredecessorHalfFin13Atom0735 chi)))) ∨
      (((PredecessorHalfFin13Atom1931 chi ∧
      ¬PredecessorHalfFin13Atom0756 chi) ∨
      ((PredecessorHalfFin13Atom1931 chi ∧
      ¬PredecessorHalfFin13Atom0896 chi) ∨
      (PredecessorHalfFin13Atom1932 chi ∧
      ¬PredecessorHalfFin13Atom0715 chi))) ∨
      ((PredecessorHalfFin13Atom1932 chi ∧
      ¬PredecessorHalfFin13Atom0716 chi) ∨
      ((PredecessorHalfFin13Atom1932 chi ∧
      ¬PredecessorHalfFin13Atom0721 chi) ∨
      (PredecessorHalfFin13Atom1932 chi ∧
      ¬PredecessorHalfFin13Atom0757 chi))))) ∨
      ((((PredecessorHalfFin13Atom1932 chi ∧
      ¬PredecessorHalfFin13Atom0897 chi) ∨
      ((¬PredecessorHalfFin13Atom1932 chi ∧
      PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0897 chi) ∨
      (PredecessorHalfFin13Atom1933 chi ∧
      ¬PredecessorHalfFin13Atom0715 chi))) ∨
      ((PredecessorHalfFin13Atom1933 chi ∧
      ¬PredecessorHalfFin13Atom0717 chi) ∨
      ((PredecessorHalfFin13Atom1933 chi ∧
      ¬PredecessorHalfFin13Atom0722 chi) ∨
      (PredecessorHalfFin13Atom1933 chi ∧
      ¬PredecessorHalfFin13Atom0758 chi)))) ∨
      (((PredecessorHalfFin13Atom1933 chi ∧
      ¬PredecessorHalfFin13Atom0898 chi) ∨
      ((¬PredecessorHalfFin13Atom1933 chi ∧
      PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0898 chi) ∨
      (PredecessorHalfFin13Atom1934 chi ∧
      ¬PredecessorHalfFin13Atom0715 chi))) ∨
      (((PredecessorHalfFin13Atom1934 chi ∧
      ¬PredecessorHalfFin13Atom0718 chi) ∨
      (PredecessorHalfFin13Atom1934 chi ∧
      ¬PredecessorHalfFin13Atom0723 chi)) ∨
      ((PredecessorHalfFin13Atom1934 chi ∧
      ¬PredecessorHalfFin13Atom0759 chi) ∨
      (PredecessorHalfFin13Atom1934 chi ∧
      ¬PredecessorHalfFin13Atom0899 chi))))))))) := by
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
              exact predecessorHalfFin13_clause22658 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22659 chi hbad
              ·
                exact predecessorHalfFin13_clause22660 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22661 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22662 chi hbad
              ·
                exact predecessorHalfFin13_clause22663 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22664 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22665 chi hbad
              ·
                exact predecessorHalfFin13_clause22666 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22667 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22668 chi hbad
              ·
                exact predecessorHalfFin13_clause22669 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22670 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22671 chi hbad
              ·
                exact predecessorHalfFin13_clause22672 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22673 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22674 chi hbad
              ·
                exact predecessorHalfFin13_clause22675 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22676 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22677 chi hbad
              ·
                exact predecessorHalfFin13_clause22678 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22679 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22680 chi hbad
              ·
                exact predecessorHalfFin13_clause22681 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22682 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22683 chi hbad
              ·
                exact predecessorHalfFin13_clause22684 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22685 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22686 chi hbad
              ·
                exact predecessorHalfFin13_clause22687 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22688 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22689 chi hbad
              ·
                exact predecessorHalfFin13_clause22690 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22691 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22692 chi hbad
              ·
                exact predecessorHalfFin13_clause22693 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22694 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22695 chi hbad
              ·
                exact predecessorHalfFin13_clause22696 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22697 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22699 chi hbad
              ·
                exact predecessorHalfFin13_clause22700 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22701 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22702 chi hbad
              ·
                exact predecessorHalfFin13_clause22703 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22704 chi hbad
              ·
                exact predecessorHalfFin13_clause22705 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22706 chi hbad
              ·
                exact predecessorHalfFin13_clause22707 chi hbad
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
              exact predecessorHalfFin13_clause22708 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22709 chi hbad
              ·
                exact predecessorHalfFin13_clause22710 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22711 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22712 chi hbad
              ·
                exact predecessorHalfFin13_clause22713 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22714 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22715 chi hbad
              ·
                exact predecessorHalfFin13_clause22716 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22717 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22718 chi hbad
              ·
                exact predecessorHalfFin13_clause22719 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22720 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22721 chi hbad
              ·
                exact predecessorHalfFin13_clause22722 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22723 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22724 chi hbad
              ·
                exact predecessorHalfFin13_clause22725 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22726 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22727 chi hbad
              ·
                exact predecessorHalfFin13_clause22728 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22729 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22730 chi hbad
              ·
                exact predecessorHalfFin13_clause22731 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22732 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22733 chi hbad
              ·
                exact predecessorHalfFin13_clause22734 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22735 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22736 chi hbad
              ·
                exact predecessorHalfFin13_clause22737 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22738 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22739 chi hbad
              ·
                exact predecessorHalfFin13_clause22741 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22742 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22743 chi hbad
              ·
                exact predecessorHalfFin13_clause22744 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22745 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22746 chi hbad
              ·
                exact predecessorHalfFin13_clause22747 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22748 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22749 chi hbad
              ·
                exact predecessorHalfFin13_clause22750 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22751 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22752 chi hbad
              ·
                exact predecessorHalfFin13_clause22753 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22754 chi hbad
              ·
                exact predecessorHalfFin13_clause22755 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22756 chi hbad
              ·
                exact predecessorHalfFin13_clause22757 chi hbad

end ErdosSzekeres

end
