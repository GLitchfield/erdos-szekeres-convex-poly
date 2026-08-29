module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk072

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 094. -/

theorem predecessorHalfFin13_rejectSemanticSegment094
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((¬PredecessorHalfFin13Atom1863 chi ∧
      PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0684 chi ∧
      PredecessorHalfFin13Atom0695 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0828 chi) ∨
      ((PredecessorHalfFin13Atom1864 chi ∧
      ¬PredecessorHalfFin13Atom0681 chi) ∨
      (PredecessorHalfFin13Atom1864 chi ∧
      ¬PredecessorHalfFin13Atom0685 chi))) ∨
      ((PredecessorHalfFin13Atom1864 chi ∧
      ¬PredecessorHalfFin13Atom0696 chi) ∨
      ((PredecessorHalfFin13Atom1864 chi ∧
      ¬PredecessorHalfFin13Atom0745 chi) ∨
      (PredecessorHalfFin13Atom1864 chi ∧
      ¬PredecessorHalfFin13Atom0829 chi)))) ∨
      (((PredecessorHalfFin13Atom1865 chi ∧
      ¬PredecessorHalfFin13Atom0681 chi) ∨
      ((PredecessorHalfFin13Atom1865 chi ∧
      ¬PredecessorHalfFin13Atom0686 chi) ∨
      (PredecessorHalfFin13Atom1865 chi ∧
      ¬PredecessorHalfFin13Atom0697 chi))) ∨
      ((PredecessorHalfFin13Atom1865 chi ∧
      ¬PredecessorHalfFin13Atom0746 chi) ∨
      ((PredecessorHalfFin13Atom1865 chi ∧
      ¬PredecessorHalfFin13Atom0830 chi) ∨
      (¬PredecessorHalfFin13Atom1865 chi ∧
      PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0686 chi ∧
      PredecessorHalfFin13Atom0697 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0830 chi))))) ∨
      ((((PredecessorHalfFin13Atom1866 chi ∧
      ¬PredecessorHalfFin13Atom0682 chi) ∨
      ((PredecessorHalfFin13Atom1866 chi ∧
      ¬PredecessorHalfFin13Atom0683 chi) ∨
      (PredecessorHalfFin13Atom1866 chi ∧
      ¬PredecessorHalfFin13Atom0698 chi))) ∨
      ((PredecessorHalfFin13Atom1866 chi ∧
      ¬PredecessorHalfFin13Atom0747 chi) ∨
      ((PredecessorHalfFin13Atom1866 chi ∧
      ¬PredecessorHalfFin13Atom0831 chi) ∨
      (¬PredecessorHalfFin13Atom1866 chi ∧
      PredecessorHalfFin13Atom0682 chi ∧
      PredecessorHalfFin13Atom0683 chi ∧
      PredecessorHalfFin13Atom0698 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0831 chi)))) ∨
      (((PredecessorHalfFin13Atom1867 chi ∧
      ¬PredecessorHalfFin13Atom0682 chi) ∨
      ((PredecessorHalfFin13Atom1867 chi ∧
      ¬PredecessorHalfFin13Atom0684 chi) ∨
      (PredecessorHalfFin13Atom1867 chi ∧
      ¬PredecessorHalfFin13Atom0699 chi))) ∨
      ((PredecessorHalfFin13Atom1867 chi ∧
      ¬PredecessorHalfFin13Atom0748 chi) ∨
      ((PredecessorHalfFin13Atom1867 chi ∧
      ¬PredecessorHalfFin13Atom0832 chi) ∨
      (¬PredecessorHalfFin13Atom1867 chi ∧
      PredecessorHalfFin13Atom0682 chi ∧
      PredecessorHalfFin13Atom0684 chi ∧
      PredecessorHalfFin13Atom0699 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0832 chi)))))) ∨
      (((((PredecessorHalfFin13Atom1868 chi ∧
      ¬PredecessorHalfFin13Atom0682 chi) ∨
      ((PredecessorHalfFin13Atom1868 chi ∧
      ¬PredecessorHalfFin13Atom0685 chi) ∨
      (PredecessorHalfFin13Atom1868 chi ∧
      ¬PredecessorHalfFin13Atom0700 chi))) ∨
      ((PredecessorHalfFin13Atom1868 chi ∧
      ¬PredecessorHalfFin13Atom0749 chi) ∨
      ((PredecessorHalfFin13Atom1868 chi ∧
      ¬PredecessorHalfFin13Atom0833 chi) ∨
      (PredecessorHalfFin13Atom1869 chi ∧
      ¬PredecessorHalfFin13Atom0682 chi)))) ∨
      (((PredecessorHalfFin13Atom1869 chi ∧
      ¬PredecessorHalfFin13Atom0686 chi) ∨
      ((PredecessorHalfFin13Atom1869 chi ∧
      ¬PredecessorHalfFin13Atom0701 chi) ∨
      (PredecessorHalfFin13Atom1869 chi ∧
      ¬PredecessorHalfFin13Atom0750 chi))) ∨
      ((PredecessorHalfFin13Atom1869 chi ∧
      ¬PredecessorHalfFin13Atom0834 chi) ∨
      ((¬PredecessorHalfFin13Atom1869 chi ∧
      PredecessorHalfFin13Atom0682 chi ∧
      PredecessorHalfFin13Atom0686 chi ∧
      PredecessorHalfFin13Atom0701 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0834 chi) ∨
      (PredecessorHalfFin13Atom1870 chi ∧
      ¬PredecessorHalfFin13Atom0683 chi))))) ∨
      ((((PredecessorHalfFin13Atom1870 chi ∧
      ¬PredecessorHalfFin13Atom0684 chi) ∨
      ((PredecessorHalfFin13Atom1870 chi ∧
      ¬PredecessorHalfFin13Atom0702 chi) ∨
      (PredecessorHalfFin13Atom1870 chi ∧
      ¬PredecessorHalfFin13Atom0751 chi))) ∨
      ((PredecessorHalfFin13Atom1870 chi ∧
      ¬PredecessorHalfFin13Atom0835 chi) ∨
      ((¬PredecessorHalfFin13Atom1870 chi ∧
      PredecessorHalfFin13Atom0683 chi ∧
      PredecessorHalfFin13Atom0684 chi ∧
      PredecessorHalfFin13Atom0702 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0835 chi) ∨
      (PredecessorHalfFin13Atom1871 chi ∧
      ¬PredecessorHalfFin13Atom0683 chi)))) ∨
      (((PredecessorHalfFin13Atom1871 chi ∧
      ¬PredecessorHalfFin13Atom0685 chi) ∨
      ((PredecessorHalfFin13Atom1871 chi ∧
      ¬PredecessorHalfFin13Atom0703 chi) ∨
      (PredecessorHalfFin13Atom1871 chi ∧
      ¬PredecessorHalfFin13Atom0752 chi))) ∨
      (((PredecessorHalfFin13Atom1871 chi ∧
      ¬PredecessorHalfFin13Atom0836 chi) ∨
      (PredecessorHalfFin13Atom1872 chi ∧
      ¬PredecessorHalfFin13Atom0683 chi)) ∨
      ((PredecessorHalfFin13Atom1872 chi ∧
      ¬PredecessorHalfFin13Atom0686 chi) ∨
      (PredecessorHalfFin13Atom1872 chi ∧
      ¬PredecessorHalfFin13Atom0704 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom1872 chi ∧
      ¬PredecessorHalfFin13Atom0753 chi) ∨
      ((PredecessorHalfFin13Atom1872 chi ∧
      ¬PredecessorHalfFin13Atom0837 chi) ∨
      (¬PredecessorHalfFin13Atom1872 chi ∧
      PredecessorHalfFin13Atom0683 chi ∧
      PredecessorHalfFin13Atom0686 chi ∧
      PredecessorHalfFin13Atom0704 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0837 chi))) ∨
      ((PredecessorHalfFin13Atom1873 chi ∧
      ¬PredecessorHalfFin13Atom0684 chi) ∨
      ((PredecessorHalfFin13Atom1873 chi ∧
      ¬PredecessorHalfFin13Atom0685 chi) ∨
      (PredecessorHalfFin13Atom1873 chi ∧
      ¬PredecessorHalfFin13Atom0705 chi)))) ∨
      (((PredecessorHalfFin13Atom1873 chi ∧
      ¬PredecessorHalfFin13Atom0754 chi) ∨
      ((PredecessorHalfFin13Atom1873 chi ∧
      ¬PredecessorHalfFin13Atom0838 chi) ∨
      (¬PredecessorHalfFin13Atom1873 chi ∧
      PredecessorHalfFin13Atom0684 chi ∧
      PredecessorHalfFin13Atom0685 chi ∧
      PredecessorHalfFin13Atom0705 chi ∧
      PredecessorHalfFin13Atom0754 chi ∧
      PredecessorHalfFin13Atom0838 chi))) ∨
      ((PredecessorHalfFin13Atom1874 chi ∧
      ¬PredecessorHalfFin13Atom0684 chi) ∨
      ((PredecessorHalfFin13Atom1874 chi ∧
      ¬PredecessorHalfFin13Atom0686 chi) ∨
      (PredecessorHalfFin13Atom1874 chi ∧
      ¬PredecessorHalfFin13Atom0706 chi))))) ∨
      ((((PredecessorHalfFin13Atom1874 chi ∧
      ¬PredecessorHalfFin13Atom0755 chi) ∨
      ((PredecessorHalfFin13Atom1874 chi ∧
      ¬PredecessorHalfFin13Atom0839 chi) ∨
      (¬PredecessorHalfFin13Atom1874 chi ∧
      PredecessorHalfFin13Atom0684 chi ∧
      PredecessorHalfFin13Atom0686 chi ∧
      PredecessorHalfFin13Atom0706 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0839 chi))) ∨
      ((PredecessorHalfFin13Atom1875 chi ∧
      ¬PredecessorHalfFin13Atom0685 chi) ∨
      ((PredecessorHalfFin13Atom1875 chi ∧
      ¬PredecessorHalfFin13Atom0686 chi) ∨
      (PredecessorHalfFin13Atom1875 chi ∧
      ¬PredecessorHalfFin13Atom0707 chi)))) ∨
      (((PredecessorHalfFin13Atom1875 chi ∧
      ¬PredecessorHalfFin13Atom0756 chi) ∨
      ((PredecessorHalfFin13Atom1875 chi ∧
      ¬PredecessorHalfFin13Atom0840 chi) ∨
      (PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom0687 chi))) ∨
      ((PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom0688 chi) ∨
      ((PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom0693 chi) ∨
      (PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom0757 chi)))))) ∨
      (((((PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom0841 chi) ∨
      ((¬PredecessorHalfFin13Atom1876 chi ∧
      PredecessorHalfFin13Atom0687 chi ∧
      PredecessorHalfFin13Atom0688 chi ∧
      PredecessorHalfFin13Atom0693 chi ∧
      PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0841 chi) ∨
      (PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom0687 chi))) ∨
      ((PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom0689 chi) ∨
      ((PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom0694 chi) ∨
      (PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom0758 chi)))) ∨
      (((PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom0842 chi) ∨
      ((¬PredecessorHalfFin13Atom1877 chi ∧
      PredecessorHalfFin13Atom0687 chi ∧
      PredecessorHalfFin13Atom0689 chi ∧
      PredecessorHalfFin13Atom0694 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0842 chi) ∨
      (PredecessorHalfFin13Atom1878 chi ∧
      ¬PredecessorHalfFin13Atom0687 chi))) ∨
      ((PredecessorHalfFin13Atom1878 chi ∧
      ¬PredecessorHalfFin13Atom0690 chi) ∨
      ((PredecessorHalfFin13Atom1878 chi ∧
      ¬PredecessorHalfFin13Atom0695 chi) ∨
      (PredecessorHalfFin13Atom1878 chi ∧
      ¬PredecessorHalfFin13Atom0759 chi))))) ∨
      ((((PredecessorHalfFin13Atom1878 chi ∧
      ¬PredecessorHalfFin13Atom0843 chi) ∨
      ((¬PredecessorHalfFin13Atom1878 chi ∧
      PredecessorHalfFin13Atom0687 chi ∧
      PredecessorHalfFin13Atom0690 chi ∧
      PredecessorHalfFin13Atom0695 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0843 chi) ∨
      (PredecessorHalfFin13Atom1879 chi ∧
      ¬PredecessorHalfFin13Atom0687 chi))) ∨
      ((PredecessorHalfFin13Atom1879 chi ∧
      ¬PredecessorHalfFin13Atom0696 chi) ∨
      ((PredecessorHalfFin13Atom1879 chi ∧
      ¬PredecessorHalfFin13Atom0760 chi) ∨
      (PredecessorHalfFin13Atom1879 chi ∧
      ¬PredecessorHalfFin13Atom0844 chi)))) ∨
      (((PredecessorHalfFin13Atom1880 chi ∧
      ¬PredecessorHalfFin13Atom0687 chi) ∨
      ((PredecessorHalfFin13Atom1880 chi ∧
      ¬PredecessorHalfFin13Atom0692 chi) ∨
      (PredecessorHalfFin13Atom1880 chi ∧
      ¬PredecessorHalfFin13Atom0697 chi))) ∨
      (((PredecessorHalfFin13Atom1880 chi ∧
      ¬PredecessorHalfFin13Atom0761 chi) ∨
      (PredecessorHalfFin13Atom1880 chi ∧
      ¬PredecessorHalfFin13Atom0845 chi)) ∨
      ((¬PredecessorHalfFin13Atom1880 chi ∧
      PredecessorHalfFin13Atom0687 chi ∧
      PredecessorHalfFin13Atom0692 chi ∧
      PredecessorHalfFin13Atom0697 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0845 chi) ∨
      (PredecessorHalfFin13Atom1881 chi ∧
      ¬PredecessorHalfFin13Atom0688 chi))))))))) := by
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
              exact predecessorHalfFin13_clause22332 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22333 chi hbad
              ·
                exact predecessorHalfFin13_clause22334 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22335 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22336 chi hbad
              ·
                exact predecessorHalfFin13_clause22337 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22339 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22340 chi hbad
              ·
                exact predecessorHalfFin13_clause22341 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22342 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22343 chi hbad
              ·
                exact predecessorHalfFin13_clause22344 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22345 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22346 chi hbad
              ·
                exact predecessorHalfFin13_clause22347 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22348 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22349 chi hbad
              ·
                exact predecessorHalfFin13_clause22350 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22351 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22352 chi hbad
              ·
                exact predecessorHalfFin13_clause22353 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22354 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22355 chi hbad
              ·
                exact predecessorHalfFin13_clause22356 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22357 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22358 chi hbad
              ·
                exact predecessorHalfFin13_clause22359 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22360 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22361 chi hbad
              ·
                exact predecessorHalfFin13_clause22363 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22364 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22365 chi hbad
              ·
                exact predecessorHalfFin13_clause22366 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22367 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22368 chi hbad
              ·
                exact predecessorHalfFin13_clause22369 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22370 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22371 chi hbad
              ·
                exact predecessorHalfFin13_clause22372 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22373 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22374 chi hbad
              ·
                exact predecessorHalfFin13_clause22375 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22376 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22377 chi hbad
              ·
                exact predecessorHalfFin13_clause22378 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22379 chi hbad
              ·
                exact predecessorHalfFin13_clause22381 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22382 chi hbad
              ·
                exact predecessorHalfFin13_clause22383 chi hbad
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
              exact predecessorHalfFin13_clause22384 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22385 chi hbad
              ·
                exact predecessorHalfFin13_clause22386 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22387 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22388 chi hbad
              ·
                exact predecessorHalfFin13_clause22389 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22390 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22391 chi hbad
              ·
                exact predecessorHalfFin13_clause22392 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22393 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22394 chi hbad
              ·
                exact predecessorHalfFin13_clause22395 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22396 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22397 chi hbad
              ·
                exact predecessorHalfFin13_clause22398 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22399 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22400 chi hbad
              ·
                exact predecessorHalfFin13_clause22401 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22402 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22403 chi hbad
              ·
                exact predecessorHalfFin13_clause22405 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22406 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22407 chi hbad
              ·
                exact predecessorHalfFin13_clause22408 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22409 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22410 chi hbad
              ·
                exact predecessorHalfFin13_clause22411 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22412 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22413 chi hbad
              ·
                exact predecessorHalfFin13_clause22414 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22415 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22416 chi hbad
              ·
                exact predecessorHalfFin13_clause22417 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22418 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22419 chi hbad
              ·
                exact predecessorHalfFin13_clause22420 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22421 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22422 chi hbad
              ·
                exact predecessorHalfFin13_clause22423 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22425 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22426 chi hbad
              ·
                exact predecessorHalfFin13_clause22427 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22429 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22430 chi hbad
              ·
                exact predecessorHalfFin13_clause22431 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22432 chi hbad
              ·
                exact predecessorHalfFin13_clause22433 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22434 chi hbad
              ·
                exact predecessorHalfFin13_clause22435 chi hbad

end ErdosSzekeres

end
