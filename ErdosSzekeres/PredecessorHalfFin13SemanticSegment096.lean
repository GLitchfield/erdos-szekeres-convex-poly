module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk073
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk074

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 096. -/

theorem predecessorHalfFin13_rejectSemanticSegment096
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom1899 chi ∧
      ¬PredecessorHalfFin13Atom0706 chi) ∨
      ((PredecessorHalfFin13Atom1899 chi ∧
      ¬PredecessorHalfFin13Atom0780 chi) ∨
      (PredecessorHalfFin13Atom1899 chi ∧
      ¬PredecessorHalfFin13Atom0864 chi))) ∨
      ((¬PredecessorHalfFin13Atom1899 chi ∧
      PredecessorHalfFin13Atom0695 chi ∧
      PredecessorHalfFin13Atom0697 chi ∧
      PredecessorHalfFin13Atom0706 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0864 chi) ∨
      ((PredecessorHalfFin13Atom1900 chi ∧
      ¬PredecessorHalfFin13Atom0697 chi) ∨
      (PredecessorHalfFin13Atom1900 chi ∧
      ¬PredecessorHalfFin13Atom0707 chi)))) ∨
      (((PredecessorHalfFin13Atom1900 chi ∧
      ¬PredecessorHalfFin13Atom0781 chi) ∨
      ((PredecessorHalfFin13Atom1900 chi ∧
      ¬PredecessorHalfFin13Atom0865 chi) ∨
      (PredecessorHalfFin13Atom1901 chi ∧
      ¬PredecessorHalfFin13Atom0698 chi))) ∨
      ((PredecessorHalfFin13Atom1901 chi ∧
      ¬PredecessorHalfFin13Atom0699 chi) ∨
      ((PredecessorHalfFin13Atom1901 chi ∧
      ¬PredecessorHalfFin13Atom0702 chi) ∨
      (PredecessorHalfFin13Atom1901 chi ∧
      ¬PredecessorHalfFin13Atom0782 chi))))) ∨
      ((((PredecessorHalfFin13Atom1901 chi ∧
      ¬PredecessorHalfFin13Atom0866 chi) ∨
      ((¬PredecessorHalfFin13Atom1901 chi ∧
      PredecessorHalfFin13Atom0698 chi ∧
      PredecessorHalfFin13Atom0699 chi ∧
      PredecessorHalfFin13Atom0702 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0866 chi) ∨
      (PredecessorHalfFin13Atom1902 chi ∧
      ¬PredecessorHalfFin13Atom0698 chi))) ∨
      ((PredecessorHalfFin13Atom1902 chi ∧
      ¬PredecessorHalfFin13Atom0700 chi) ∨
      ((PredecessorHalfFin13Atom1902 chi ∧
      ¬PredecessorHalfFin13Atom0703 chi) ∨
      (PredecessorHalfFin13Atom1902 chi ∧
      ¬PredecessorHalfFin13Atom0783 chi)))) ∨
      (((PredecessorHalfFin13Atom1902 chi ∧
      ¬PredecessorHalfFin13Atom0867 chi) ∨
      ((PredecessorHalfFin13Atom1903 chi ∧
      ¬PredecessorHalfFin13Atom0698 chi) ∨
      (PredecessorHalfFin13Atom1903 chi ∧
      ¬PredecessorHalfFin13Atom0701 chi))) ∨
      ((PredecessorHalfFin13Atom1903 chi ∧
      ¬PredecessorHalfFin13Atom0704 chi) ∨
      ((PredecessorHalfFin13Atom1903 chi ∧
      ¬PredecessorHalfFin13Atom0784 chi) ∨
      (PredecessorHalfFin13Atom1903 chi ∧
      ¬PredecessorHalfFin13Atom0868 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom1903 chi ∧
      PredecessorHalfFin13Atom0698 chi ∧
      PredecessorHalfFin13Atom0701 chi ∧
      PredecessorHalfFin13Atom0704 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0868 chi) ∨
      ((PredecessorHalfFin13Atom1904 chi ∧
      ¬PredecessorHalfFin13Atom0699 chi) ∨
      (PredecessorHalfFin13Atom1904 chi ∧
      ¬PredecessorHalfFin13Atom0700 chi))) ∨
      ((PredecessorHalfFin13Atom1904 chi ∧
      ¬PredecessorHalfFin13Atom0705 chi) ∨
      ((PredecessorHalfFin13Atom1904 chi ∧
      ¬PredecessorHalfFin13Atom0785 chi) ∨
      (PredecessorHalfFin13Atom1904 chi ∧
      ¬PredecessorHalfFin13Atom0869 chi)))) ∨
      (((PredecessorHalfFin13Atom1905 chi ∧
      ¬PredecessorHalfFin13Atom0699 chi) ∨
      ((PredecessorHalfFin13Atom1905 chi ∧
      ¬PredecessorHalfFin13Atom0701 chi) ∨
      (PredecessorHalfFin13Atom1905 chi ∧
      ¬PredecessorHalfFin13Atom0706 chi))) ∨
      ((PredecessorHalfFin13Atom1905 chi ∧
      ¬PredecessorHalfFin13Atom0786 chi) ∨
      ((PredecessorHalfFin13Atom1905 chi ∧
      ¬PredecessorHalfFin13Atom0870 chi) ∨
      (¬PredecessorHalfFin13Atom1905 chi ∧
      PredecessorHalfFin13Atom0699 chi ∧
      PredecessorHalfFin13Atom0701 chi ∧
      PredecessorHalfFin13Atom0706 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0870 chi))))) ∨
      ((((PredecessorHalfFin13Atom1906 chi ∧
      ¬PredecessorHalfFin13Atom0701 chi) ∨
      ((PredecessorHalfFin13Atom1906 chi ∧
      ¬PredecessorHalfFin13Atom0871 chi) ∨
      (PredecessorHalfFin13Atom1907 chi ∧
      ¬PredecessorHalfFin13Atom0702 chi))) ∨
      ((PredecessorHalfFin13Atom1907 chi ∧
      ¬PredecessorHalfFin13Atom0703 chi) ∨
      ((PredecessorHalfFin13Atom1907 chi ∧
      ¬PredecessorHalfFin13Atom0788 chi) ∨
      (PredecessorHalfFin13Atom1907 chi ∧
      ¬PredecessorHalfFin13Atom0872 chi)))) ∨
      (((PredecessorHalfFin13Atom1908 chi ∧
      ¬PredecessorHalfFin13Atom0702 chi) ∨
      ((PredecessorHalfFin13Atom1908 chi ∧
      ¬PredecessorHalfFin13Atom0704 chi) ∨
      (PredecessorHalfFin13Atom1908 chi ∧
      ¬PredecessorHalfFin13Atom0706 chi))) ∨
      (((PredecessorHalfFin13Atom1908 chi ∧
      ¬PredecessorHalfFin13Atom0789 chi) ∨
      (PredecessorHalfFin13Atom1908 chi ∧
      ¬PredecessorHalfFin13Atom0873 chi)) ∨
      ((¬PredecessorHalfFin13Atom1908 chi ∧
      PredecessorHalfFin13Atom0702 chi ∧
      PredecessorHalfFin13Atom0704 chi ∧
      PredecessorHalfFin13Atom0706 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0873 chi) ∨
      (PredecessorHalfFin13Atom1909 chi ∧
      ¬PredecessorHalfFin13Atom0704 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom1909 chi ∧
      ¬PredecessorHalfFin13Atom0790 chi) ∨
      ((PredecessorHalfFin13Atom1909 chi ∧
      ¬PredecessorHalfFin13Atom0874 chi) ∨
      (PredecessorHalfFin13Atom1910 chi ∧
      ¬PredecessorHalfFin13Atom0706 chi))) ∨
      ((PredecessorHalfFin13Atom1910 chi ∧
      ¬PredecessorHalfFin13Atom0707 chi) ∨
      ((PredecessorHalfFin13Atom1910 chi ∧
      ¬PredecessorHalfFin13Atom0791 chi) ∨
      (PredecessorHalfFin13Atom1910 chi ∧
      ¬PredecessorHalfFin13Atom0875 chi)))) ∨
      (((PredecessorHalfFin13Atom1911 chi ∧
      ¬PredecessorHalfFin13Atom0708 chi) ∨
      ((PredecessorHalfFin13Atom1911 chi ∧
      ¬PredecessorHalfFin13Atom0709 chi) ∨
      (PredecessorHalfFin13Atom1911 chi ∧
      ¬PredecessorHalfFin13Atom0715 chi))) ∨
      ((PredecessorHalfFin13Atom1911 chi ∧
      ¬PredecessorHalfFin13Atom0736 chi) ∨
      ((PredecessorHalfFin13Atom1911 chi ∧
      ¬PredecessorHalfFin13Atom0876 chi) ∨
      (¬PredecessorHalfFin13Atom1911 chi ∧
      PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0876 chi))))) ∨
      ((((PredecessorHalfFin13Atom1912 chi ∧
      ¬PredecessorHalfFin13Atom0708 chi) ∨
      ((PredecessorHalfFin13Atom1912 chi ∧
      ¬PredecessorHalfFin13Atom0710 chi) ∨
      (PredecessorHalfFin13Atom1912 chi ∧
      ¬PredecessorHalfFin13Atom0716 chi))) ∨
      ((PredecessorHalfFin13Atom1912 chi ∧
      ¬PredecessorHalfFin13Atom0737 chi) ∨
      ((PredecessorHalfFin13Atom1912 chi ∧
      ¬PredecessorHalfFin13Atom0877 chi) ∨
      (¬PredecessorHalfFin13Atom1912 chi ∧
      PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0877 chi)))) ∨
      (((PredecessorHalfFin13Atom1913 chi ∧
      ¬PredecessorHalfFin13Atom0708 chi) ∨
      ((PredecessorHalfFin13Atom1913 chi ∧
      ¬PredecessorHalfFin13Atom0711 chi) ∨
      (PredecessorHalfFin13Atom1913 chi ∧
      ¬PredecessorHalfFin13Atom0717 chi))) ∨
      ((PredecessorHalfFin13Atom1913 chi ∧
      ¬PredecessorHalfFin13Atom0738 chi) ∨
      ((PredecessorHalfFin13Atom1913 chi ∧
      ¬PredecessorHalfFin13Atom0878 chi) ∨
      (¬PredecessorHalfFin13Atom1913 chi ∧
      PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0878 chi)))))) ∨
      (((((PredecessorHalfFin13Atom1914 chi ∧
      ¬PredecessorHalfFin13Atom0708 chi) ∨
      ((PredecessorHalfFin13Atom1914 chi ∧
      ¬PredecessorHalfFin13Atom0712 chi) ∨
      (PredecessorHalfFin13Atom1914 chi ∧
      ¬PredecessorHalfFin13Atom0718 chi))) ∨
      ((PredecessorHalfFin13Atom1914 chi ∧
      ¬PredecessorHalfFin13Atom0739 chi) ∨
      ((PredecessorHalfFin13Atom1914 chi ∧
      ¬PredecessorHalfFin13Atom0879 chi) ∨
      (¬PredecessorHalfFin13Atom1914 chi ∧
      PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0879 chi)))) ∨
      (((PredecessorHalfFin13Atom1915 chi ∧
      ¬PredecessorHalfFin13Atom0708 chi) ∨
      ((PredecessorHalfFin13Atom1915 chi ∧
      ¬PredecessorHalfFin13Atom0713 chi) ∨
      (PredecessorHalfFin13Atom1915 chi ∧
      ¬PredecessorHalfFin13Atom0719 chi))) ∨
      ((PredecessorHalfFin13Atom1915 chi ∧
      ¬PredecessorHalfFin13Atom0740 chi) ∨
      ((PredecessorHalfFin13Atom1915 chi ∧
      ¬PredecessorHalfFin13Atom0880 chi) ∨
      (¬PredecessorHalfFin13Atom1915 chi ∧
      PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0713 chi ∧
      PredecessorHalfFin13Atom0719 chi ∧
      PredecessorHalfFin13Atom0740 chi ∧
      PredecessorHalfFin13Atom0880 chi))))) ∨
      ((((PredecessorHalfFin13Atom1916 chi ∧
      ¬PredecessorHalfFin13Atom0708 chi) ∨
      ((PredecessorHalfFin13Atom1916 chi ∧
      ¬PredecessorHalfFin13Atom0714 chi) ∨
      (PredecessorHalfFin13Atom1916 chi ∧
      ¬PredecessorHalfFin13Atom0720 chi))) ∨
      ((PredecessorHalfFin13Atom1916 chi ∧
      ¬PredecessorHalfFin13Atom0741 chi) ∨
      ((PredecessorHalfFin13Atom1916 chi ∧
      ¬PredecessorHalfFin13Atom0881 chi) ∨
      (¬PredecessorHalfFin13Atom1916 chi ∧
      PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0881 chi)))) ∨
      (((PredecessorHalfFin13Atom1917 chi ∧
      ¬PredecessorHalfFin13Atom0709 chi) ∨
      ((PredecessorHalfFin13Atom1917 chi ∧
      ¬PredecessorHalfFin13Atom0710 chi) ∨
      (PredecessorHalfFin13Atom1917 chi ∧
      ¬PredecessorHalfFin13Atom0721 chi))) ∨
      (((PredecessorHalfFin13Atom1917 chi ∧
      ¬PredecessorHalfFin13Atom0742 chi) ∨
      (PredecessorHalfFin13Atom1917 chi ∧
      ¬PredecessorHalfFin13Atom0882 chi)) ∨
      ((¬PredecessorHalfFin13Atom1917 chi ∧
      PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0882 chi) ∨
      (PredecessorHalfFin13Atom1918 chi ∧
      ¬PredecessorHalfFin13Atom0709 chi))))))))) := by
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
              exact predecessorHalfFin13_clause22545 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22546 chi hbad
              ·
                exact predecessorHalfFin13_clause22547 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22548 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22550 chi hbad
              ·
                exact predecessorHalfFin13_clause22551 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22552 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22553 chi hbad
              ·
                exact predecessorHalfFin13_clause22555 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22556 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22557 chi hbad
              ·
                exact predecessorHalfFin13_clause22558 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22559 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22560 chi hbad
              ·
                exact predecessorHalfFin13_clause22561 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22562 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22563 chi hbad
              ·
                exact predecessorHalfFin13_clause22564 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22565 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22567 chi hbad
              ·
                exact predecessorHalfFin13_clause22568 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22569 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22570 chi hbad
              ·
                exact predecessorHalfFin13_clause22571 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22572 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22573 chi hbad
              ·
                exact predecessorHalfFin13_clause22574 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22575 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22576 chi hbad
              ·
                exact predecessorHalfFin13_clause22577 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22579 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22580 chi hbad
              ·
                exact predecessorHalfFin13_clause22581 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22582 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22583 chi hbad
              ·
                exact predecessorHalfFin13_clause22584 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22586 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22589 chi hbad
              ·
                exact predecessorHalfFin13_clause22591 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22592 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22594 chi hbad
              ·
                exact predecessorHalfFin13_clause22595 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22597 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22598 chi hbad
              ·
                exact predecessorHalfFin13_clause22599 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22600 chi hbad
              ·
                exact predecessorHalfFin13_clause22601 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22602 chi hbad
              ·
                exact predecessorHalfFin13_clause22604 chi hbad
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
              exact predecessorHalfFin13_clause22606 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22607 chi hbad
              ·
                exact predecessorHalfFin13_clause22610 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22611 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22612 chi hbad
              ·
                exact predecessorHalfFin13_clause22613 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22615 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22616 chi hbad
              ·
                exact predecessorHalfFin13_clause22617 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22618 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22619 chi hbad
              ·
                exact predecessorHalfFin13_clause22620 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22621 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22622 chi hbad
              ·
                exact predecessorHalfFin13_clause22623 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22624 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22625 chi hbad
              ·
                exact predecessorHalfFin13_clause22626 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22627 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22628 chi hbad
              ·
                exact predecessorHalfFin13_clause22629 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22630 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22631 chi hbad
              ·
                exact predecessorHalfFin13_clause22632 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22633 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22634 chi hbad
              ·
                exact predecessorHalfFin13_clause22635 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22636 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22637 chi hbad
              ·
                exact predecessorHalfFin13_clause22638 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22639 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22640 chi hbad
              ·
                exact predecessorHalfFin13_clause22641 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22642 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22643 chi hbad
              ·
                exact predecessorHalfFin13_clause22644 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22645 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22646 chi hbad
              ·
                exact predecessorHalfFin13_clause22647 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22648 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22649 chi hbad
              ·
                exact predecessorHalfFin13_clause22650 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22651 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22652 chi hbad
              ·
                exact predecessorHalfFin13_clause22653 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22654 chi hbad
              ·
                exact predecessorHalfFin13_clause22655 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22656 chi hbad
              ·
                exact predecessorHalfFin13_clause22657 chi hbad

end ErdosSzekeres

end
