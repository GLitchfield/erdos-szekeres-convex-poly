module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk072
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk073

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 095. -/

theorem predecessorHalfFin13_rejectSemanticSegment095
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom1881 chi ∧
      ¬PredecessorHalfFin13Atom0689 chi) ∨
      ((PredecessorHalfFin13Atom1881 chi ∧
      ¬PredecessorHalfFin13Atom0698 chi) ∨
      (PredecessorHalfFin13Atom1881 chi ∧
      ¬PredecessorHalfFin13Atom0762 chi))) ∨
      ((PredecessorHalfFin13Atom1881 chi ∧
      ¬PredecessorHalfFin13Atom0846 chi) ∨
      ((¬PredecessorHalfFin13Atom1881 chi ∧
      PredecessorHalfFin13Atom0688 chi ∧
      PredecessorHalfFin13Atom0689 chi ∧
      PredecessorHalfFin13Atom0698 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0846 chi) ∨
      (PredecessorHalfFin13Atom1882 chi ∧
      ¬PredecessorHalfFin13Atom0688 chi)))) ∨
      (((PredecessorHalfFin13Atom1882 chi ∧
      ¬PredecessorHalfFin13Atom0690 chi) ∨
      ((PredecessorHalfFin13Atom1882 chi ∧
      ¬PredecessorHalfFin13Atom0699 chi) ∨
      (PredecessorHalfFin13Atom1882 chi ∧
      ¬PredecessorHalfFin13Atom0763 chi))) ∨
      ((PredecessorHalfFin13Atom1882 chi ∧
      ¬PredecessorHalfFin13Atom0847 chi) ∨
      ((¬PredecessorHalfFin13Atom1882 chi ∧
      PredecessorHalfFin13Atom0688 chi ∧
      PredecessorHalfFin13Atom0690 chi ∧
      PredecessorHalfFin13Atom0699 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0847 chi) ∨
      (PredecessorHalfFin13Atom1883 chi ∧
      ¬PredecessorHalfFin13Atom0688 chi))))) ∨
      ((((PredecessorHalfFin13Atom1883 chi ∧
      ¬PredecessorHalfFin13Atom0691 chi) ∨
      ((PredecessorHalfFin13Atom1883 chi ∧
      ¬PredecessorHalfFin13Atom0700 chi) ∨
      (PredecessorHalfFin13Atom1883 chi ∧
      ¬PredecessorHalfFin13Atom0764 chi))) ∨
      ((PredecessorHalfFin13Atom1883 chi ∧
      ¬PredecessorHalfFin13Atom0848 chi) ∨
      ((PredecessorHalfFin13Atom1884 chi ∧
      ¬PredecessorHalfFin13Atom0688 chi) ∨
      (PredecessorHalfFin13Atom1884 chi ∧
      ¬PredecessorHalfFin13Atom0692 chi)))) ∨
      (((PredecessorHalfFin13Atom1884 chi ∧
      ¬PredecessorHalfFin13Atom0701 chi) ∨
      ((PredecessorHalfFin13Atom1884 chi ∧
      ¬PredecessorHalfFin13Atom0765 chi) ∨
      (PredecessorHalfFin13Atom1884 chi ∧
      ¬PredecessorHalfFin13Atom0849 chi))) ∨
      ((¬PredecessorHalfFin13Atom1884 chi ∧
      PredecessorHalfFin13Atom0688 chi ∧
      PredecessorHalfFin13Atom0692 chi ∧
      PredecessorHalfFin13Atom0701 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0849 chi) ∨
      ((PredecessorHalfFin13Atom1885 chi ∧
      ¬PredecessorHalfFin13Atom0689 chi) ∨
      (PredecessorHalfFin13Atom1885 chi ∧
      ¬PredecessorHalfFin13Atom0690 chi)))))) ∨
      (((((PredecessorHalfFin13Atom1885 chi ∧
      ¬PredecessorHalfFin13Atom0702 chi) ∨
      ((PredecessorHalfFin13Atom1885 chi ∧
      ¬PredecessorHalfFin13Atom0766 chi) ∨
      (PredecessorHalfFin13Atom1885 chi ∧
      ¬PredecessorHalfFin13Atom0850 chi))) ∨
      ((¬PredecessorHalfFin13Atom1885 chi ∧
      PredecessorHalfFin13Atom0689 chi ∧
      PredecessorHalfFin13Atom0690 chi ∧
      PredecessorHalfFin13Atom0702 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0850 chi) ∨
      ((PredecessorHalfFin13Atom1886 chi ∧
      ¬PredecessorHalfFin13Atom0689 chi) ∨
      (PredecessorHalfFin13Atom1886 chi ∧
      ¬PredecessorHalfFin13Atom0691 chi)))) ∨
      (((PredecessorHalfFin13Atom1886 chi ∧
      ¬PredecessorHalfFin13Atom0703 chi) ∨
      ((PredecessorHalfFin13Atom1886 chi ∧
      ¬PredecessorHalfFin13Atom0767 chi) ∨
      (PredecessorHalfFin13Atom1886 chi ∧
      ¬PredecessorHalfFin13Atom0851 chi))) ∨
      ((¬PredecessorHalfFin13Atom1886 chi ∧
      PredecessorHalfFin13Atom0689 chi ∧
      PredecessorHalfFin13Atom0691 chi ∧
      PredecessorHalfFin13Atom0703 chi ∧
      PredecessorHalfFin13Atom0767 chi ∧
      PredecessorHalfFin13Atom0851 chi) ∨
      ((PredecessorHalfFin13Atom1887 chi ∧
      ¬PredecessorHalfFin13Atom0689 chi) ∨
      (PredecessorHalfFin13Atom1887 chi ∧
      ¬PredecessorHalfFin13Atom0692 chi))))) ∨
      ((((PredecessorHalfFin13Atom1887 chi ∧
      ¬PredecessorHalfFin13Atom0704 chi) ∨
      ((PredecessorHalfFin13Atom1887 chi ∧
      ¬PredecessorHalfFin13Atom0768 chi) ∨
      (PredecessorHalfFin13Atom1887 chi ∧
      ¬PredecessorHalfFin13Atom0852 chi))) ∨
      ((¬PredecessorHalfFin13Atom1887 chi ∧
      PredecessorHalfFin13Atom0689 chi ∧
      PredecessorHalfFin13Atom0692 chi ∧
      PredecessorHalfFin13Atom0704 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0852 chi) ∨
      ((PredecessorHalfFin13Atom1888 chi ∧
      ¬PredecessorHalfFin13Atom0690 chi) ∨
      (PredecessorHalfFin13Atom1888 chi ∧
      ¬PredecessorHalfFin13Atom0691 chi)))) ∨
      (((PredecessorHalfFin13Atom1888 chi ∧
      ¬PredecessorHalfFin13Atom0705 chi) ∨
      ((PredecessorHalfFin13Atom1888 chi ∧
      ¬PredecessorHalfFin13Atom0769 chi) ∨
      (PredecessorHalfFin13Atom1888 chi ∧
      ¬PredecessorHalfFin13Atom0853 chi))) ∨
      (((PredecessorHalfFin13Atom1889 chi ∧
      ¬PredecessorHalfFin13Atom0690 chi) ∨
      (PredecessorHalfFin13Atom1889 chi ∧
      ¬PredecessorHalfFin13Atom0692 chi)) ∨
      ((PredecessorHalfFin13Atom1889 chi ∧
      ¬PredecessorHalfFin13Atom0706 chi) ∨
      (PredecessorHalfFin13Atom1889 chi ∧
      ¬PredecessorHalfFin13Atom0770 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom1889 chi ∧
      ¬PredecessorHalfFin13Atom0854 chi) ∨
      ((¬PredecessorHalfFin13Atom1889 chi ∧
      PredecessorHalfFin13Atom0690 chi ∧
      PredecessorHalfFin13Atom0692 chi ∧
      PredecessorHalfFin13Atom0706 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0854 chi) ∨
      (PredecessorHalfFin13Atom1890 chi ∧
      ¬PredecessorHalfFin13Atom0692 chi))) ∨
      ((PredecessorHalfFin13Atom1890 chi ∧
      ¬PredecessorHalfFin13Atom0707 chi) ∨
      ((PredecessorHalfFin13Atom1890 chi ∧
      ¬PredecessorHalfFin13Atom0771 chi) ∨
      (PredecessorHalfFin13Atom1890 chi ∧
      ¬PredecessorHalfFin13Atom0855 chi)))) ∨
      (((PredecessorHalfFin13Atom1891 chi ∧
      ¬PredecessorHalfFin13Atom0693 chi) ∨
      ((PredecessorHalfFin13Atom1891 chi ∧
      ¬PredecessorHalfFin13Atom0694 chi) ∨
      (PredecessorHalfFin13Atom1891 chi ∧
      ¬PredecessorHalfFin13Atom0698 chi))) ∨
      ((PredecessorHalfFin13Atom1891 chi ∧
      ¬PredecessorHalfFin13Atom0772 chi) ∨
      ((PredecessorHalfFin13Atom1891 chi ∧
      ¬PredecessorHalfFin13Atom0856 chi) ∨
      (¬PredecessorHalfFin13Atom1891 chi ∧
      PredecessorHalfFin13Atom0693 chi ∧
      PredecessorHalfFin13Atom0694 chi ∧
      PredecessorHalfFin13Atom0698 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0856 chi))))) ∨
      ((((PredecessorHalfFin13Atom1892 chi ∧
      ¬PredecessorHalfFin13Atom0693 chi) ∨
      ((PredecessorHalfFin13Atom1892 chi ∧
      ¬PredecessorHalfFin13Atom0695 chi) ∨
      (PredecessorHalfFin13Atom1892 chi ∧
      ¬PredecessorHalfFin13Atom0699 chi))) ∨
      ((PredecessorHalfFin13Atom1892 chi ∧
      ¬PredecessorHalfFin13Atom0773 chi) ∨
      ((PredecessorHalfFin13Atom1892 chi ∧
      ¬PredecessorHalfFin13Atom0857 chi) ∨
      (¬PredecessorHalfFin13Atom1892 chi ∧
      PredecessorHalfFin13Atom0693 chi ∧
      PredecessorHalfFin13Atom0695 chi ∧
      PredecessorHalfFin13Atom0699 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0857 chi)))) ∨
      (((PredecessorHalfFin13Atom1893 chi ∧
      ¬PredecessorHalfFin13Atom0693 chi) ∨
      ((PredecessorHalfFin13Atom1893 chi ∧
      ¬PredecessorHalfFin13Atom0696 chi) ∨
      (PredecessorHalfFin13Atom1893 chi ∧
      ¬PredecessorHalfFin13Atom0774 chi))) ∨
      (((PredecessorHalfFin13Atom1893 chi ∧
      ¬PredecessorHalfFin13Atom0858 chi) ∨
      (PredecessorHalfFin13Atom1894 chi ∧
      ¬PredecessorHalfFin13Atom0693 chi)) ∨
      ((PredecessorHalfFin13Atom1894 chi ∧
      ¬PredecessorHalfFin13Atom0697 chi) ∨
      (PredecessorHalfFin13Atom1894 chi ∧
      ¬PredecessorHalfFin13Atom0701 chi)))))) ∨
      (((((PredecessorHalfFin13Atom1894 chi ∧
      ¬PredecessorHalfFin13Atom0775 chi) ∨
      ((PredecessorHalfFin13Atom1894 chi ∧
      ¬PredecessorHalfFin13Atom0859 chi) ∨
      (¬PredecessorHalfFin13Atom1894 chi ∧
      PredecessorHalfFin13Atom0693 chi ∧
      PredecessorHalfFin13Atom0697 chi ∧
      PredecessorHalfFin13Atom0701 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0859 chi))) ∨
      ((PredecessorHalfFin13Atom1895 chi ∧
      ¬PredecessorHalfFin13Atom0694 chi) ∨
      ((PredecessorHalfFin13Atom1895 chi ∧
      ¬PredecessorHalfFin13Atom0695 chi) ∨
      (PredecessorHalfFin13Atom1895 chi ∧
      ¬PredecessorHalfFin13Atom0702 chi)))) ∨
      (((PredecessorHalfFin13Atom1895 chi ∧
      ¬PredecessorHalfFin13Atom0776 chi) ∨
      ((PredecessorHalfFin13Atom1895 chi ∧
      ¬PredecessorHalfFin13Atom0860 chi) ∨
      (¬PredecessorHalfFin13Atom1895 chi ∧
      PredecessorHalfFin13Atom0694 chi ∧
      PredecessorHalfFin13Atom0695 chi ∧
      PredecessorHalfFin13Atom0702 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0860 chi))) ∨
      ((PredecessorHalfFin13Atom1896 chi ∧
      ¬PredecessorHalfFin13Atom0694 chi) ∨
      ((PredecessorHalfFin13Atom1896 chi ∧
      ¬PredecessorHalfFin13Atom0703 chi) ∨
      (PredecessorHalfFin13Atom1896 chi ∧
      ¬PredecessorHalfFin13Atom0777 chi))))) ∨
      ((((PredecessorHalfFin13Atom1896 chi ∧
      ¬PredecessorHalfFin13Atom0861 chi) ∨
      ((PredecessorHalfFin13Atom1897 chi ∧
      ¬PredecessorHalfFin13Atom0694 chi) ∨
      (PredecessorHalfFin13Atom1897 chi ∧
      ¬PredecessorHalfFin13Atom0697 chi))) ∨
      ((PredecessorHalfFin13Atom1897 chi ∧
      ¬PredecessorHalfFin13Atom0704 chi) ∨
      ((PredecessorHalfFin13Atom1897 chi ∧
      ¬PredecessorHalfFin13Atom0778 chi) ∨
      (PredecessorHalfFin13Atom1897 chi ∧
      ¬PredecessorHalfFin13Atom0862 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1897 chi ∧
      PredecessorHalfFin13Atom0694 chi ∧
      PredecessorHalfFin13Atom0697 chi ∧
      PredecessorHalfFin13Atom0704 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0862 chi) ∨
      ((PredecessorHalfFin13Atom1898 chi ∧
      ¬PredecessorHalfFin13Atom0695 chi) ∨
      (PredecessorHalfFin13Atom1898 chi ∧
      ¬PredecessorHalfFin13Atom0696 chi))) ∨
      (((PredecessorHalfFin13Atom1898 chi ∧
      ¬PredecessorHalfFin13Atom0779 chi) ∨
      (PredecessorHalfFin13Atom1898 chi ∧
      ¬PredecessorHalfFin13Atom0863 chi)) ∨
      ((PredecessorHalfFin13Atom1899 chi ∧
      ¬PredecessorHalfFin13Atom0695 chi) ∨
      (PredecessorHalfFin13Atom1899 chi ∧
      ¬PredecessorHalfFin13Atom0697 chi))))))))) := by
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
              exact predecessorHalfFin13_clause22436 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22437 chi hbad
              ·
                exact predecessorHalfFin13_clause22438 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22439 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22440 chi hbad
              ·
                exact predecessorHalfFin13_clause22441 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22442 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22443 chi hbad
              ·
                exact predecessorHalfFin13_clause22444 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22445 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22446 chi hbad
              ·
                exact predecessorHalfFin13_clause22447 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22448 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22449 chi hbad
              ·
                exact predecessorHalfFin13_clause22450 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22451 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22453 chi hbad
              ·
                exact predecessorHalfFin13_clause22454 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22455 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22456 chi hbad
              ·
                exact predecessorHalfFin13_clause22457 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22458 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22459 chi hbad
              ·
                exact predecessorHalfFin13_clause22460 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22461 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22462 chi hbad
              ·
                exact predecessorHalfFin13_clause22463 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22464 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22465 chi hbad
              ·
                exact predecessorHalfFin13_clause22466 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22467 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22468 chi hbad
              ·
                exact predecessorHalfFin13_clause22469 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22470 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22471 chi hbad
              ·
                exact predecessorHalfFin13_clause22472 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22473 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22474 chi hbad
              ·
                exact predecessorHalfFin13_clause22475 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22476 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22477 chi hbad
              ·
                exact predecessorHalfFin13_clause22478 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22479 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22480 chi hbad
              ·
                exact predecessorHalfFin13_clause22481 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22483 chi hbad
              ·
                exact predecessorHalfFin13_clause22484 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22485 chi hbad
              ·
                exact predecessorHalfFin13_clause22486 chi hbad
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
              exact predecessorHalfFin13_clause22487 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22488 chi hbad
              ·
                exact predecessorHalfFin13_clause22490 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22491 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22492 chi hbad
              ·
                exact predecessorHalfFin13_clause22493 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22495 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22496 chi hbad
              ·
                exact predecessorHalfFin13_clause22497 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22498 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22499 chi hbad
              ·
                exact predecessorHalfFin13_clause22500 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22501 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22502 chi hbad
              ·
                exact predecessorHalfFin13_clause22503 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22504 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22505 chi hbad
              ·
                exact predecessorHalfFin13_clause22506 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22507 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22508 chi hbad
              ·
                exact predecessorHalfFin13_clause22510 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22511 chi hbad
              ·
                exact predecessorHalfFin13_clause22513 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22514 chi hbad
              ·
                exact predecessorHalfFin13_clause22515 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22516 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22517 chi hbad
              ·
                exact predecessorHalfFin13_clause22518 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22519 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22520 chi hbad
              ·
                exact predecessorHalfFin13_clause22521 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22522 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22523 chi hbad
              ·
                exact predecessorHalfFin13_clause22524 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22525 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22527 chi hbad
              ·
                exact predecessorHalfFin13_clause22528 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22529 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22531 chi hbad
              ·
                exact predecessorHalfFin13_clause22532 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22533 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22534 chi hbad
              ·
                exact predecessorHalfFin13_clause22535 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22536 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22537 chi hbad
              ·
                exact predecessorHalfFin13_clause22538 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22540 chi hbad
              ·
                exact predecessorHalfFin13_clause22541 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22543 chi hbad
              ·
                exact predecessorHalfFin13_clause22544 chi hbad

end ErdosSzekeres

end
