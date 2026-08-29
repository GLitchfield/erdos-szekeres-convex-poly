module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk071
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk072

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 093. -/

theorem predecessorHalfFin13_rejectSemanticSegment093
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom0699 chi) ∨
      ((PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom0727 chi) ∨
      (PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom0811 chi))) ∨
      ((¬PredecessorHalfFin13Atom1846 chi ∧
      PredecessorHalfFin13Atom0675 chi ∧
      PredecessorHalfFin13Atom0677 chi ∧
      PredecessorHalfFin13Atom0699 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0811 chi) ∨
      ((PredecessorHalfFin13Atom1847 chi ∧
      ¬PredecessorHalfFin13Atom0675 chi) ∨
      (PredecessorHalfFin13Atom1847 chi ∧
      ¬PredecessorHalfFin13Atom0678 chi)))) ∨
      (((PredecessorHalfFin13Atom1847 chi ∧
      ¬PredecessorHalfFin13Atom0700 chi) ∨
      ((PredecessorHalfFin13Atom1847 chi ∧
      ¬PredecessorHalfFin13Atom0728 chi) ∨
      (PredecessorHalfFin13Atom1847 chi ∧
      ¬PredecessorHalfFin13Atom0812 chi))) ∨
      ((PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom0675 chi) ∨
      ((PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom0679 chi) ∨
      (PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom0701 chi))))) ∨
      ((((PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom0729 chi) ∨
      ((PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom0813 chi) ∨
      (¬PredecessorHalfFin13Atom1848 chi ∧
      PredecessorHalfFin13Atom0675 chi ∧
      PredecessorHalfFin13Atom0679 chi ∧
      PredecessorHalfFin13Atom0701 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0813 chi))) ∨
      ((PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom0676 chi) ∨
      ((PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom0677 chi) ∨
      (PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom0702 chi)))) ∨
      (((PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom0730 chi) ∨
      ((PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom0814 chi) ∨
      (¬PredecessorHalfFin13Atom1849 chi ∧
      PredecessorHalfFin13Atom0676 chi ∧
      PredecessorHalfFin13Atom0677 chi ∧
      PredecessorHalfFin13Atom0702 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0814 chi))) ∨
      ((PredecessorHalfFin13Atom1850 chi ∧
      ¬PredecessorHalfFin13Atom0676 chi) ∨
      ((PredecessorHalfFin13Atom1850 chi ∧
      ¬PredecessorHalfFin13Atom0678 chi) ∨
      (PredecessorHalfFin13Atom1850 chi ∧
      ¬PredecessorHalfFin13Atom0703 chi)))))) ∨
      (((((PredecessorHalfFin13Atom1850 chi ∧
      ¬PredecessorHalfFin13Atom0731 chi) ∨
      ((PredecessorHalfFin13Atom1850 chi ∧
      ¬PredecessorHalfFin13Atom0815 chi) ∨
      (PredecessorHalfFin13Atom1851 chi ∧
      ¬PredecessorHalfFin13Atom0676 chi))) ∨
      ((PredecessorHalfFin13Atom1851 chi ∧
      ¬PredecessorHalfFin13Atom0679 chi) ∨
      ((PredecessorHalfFin13Atom1851 chi ∧
      ¬PredecessorHalfFin13Atom0704 chi) ∨
      (PredecessorHalfFin13Atom1851 chi ∧
      ¬PredecessorHalfFin13Atom0732 chi)))) ∨
      (((PredecessorHalfFin13Atom1851 chi ∧
      ¬PredecessorHalfFin13Atom0816 chi) ∨
      ((¬PredecessorHalfFin13Atom1851 chi ∧
      PredecessorHalfFin13Atom0676 chi ∧
      PredecessorHalfFin13Atom0679 chi ∧
      PredecessorHalfFin13Atom0704 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0816 chi) ∨
      (PredecessorHalfFin13Atom1852 chi ∧
      ¬PredecessorHalfFin13Atom0677 chi))) ∨
      ((PredecessorHalfFin13Atom1852 chi ∧
      ¬PredecessorHalfFin13Atom0678 chi) ∨
      ((PredecessorHalfFin13Atom1852 chi ∧
      ¬PredecessorHalfFin13Atom0705 chi) ∨
      (PredecessorHalfFin13Atom1852 chi ∧
      ¬PredecessorHalfFin13Atom0733 chi))))) ∨
      ((((PredecessorHalfFin13Atom1852 chi ∧
      ¬PredecessorHalfFin13Atom0817 chi) ∨
      ((PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom0677 chi) ∨
      (PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom0679 chi))) ∨
      ((PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom0706 chi) ∨
      ((PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom0734 chi) ∨
      (PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom0818 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1853 chi ∧
      PredecessorHalfFin13Atom0677 chi ∧
      PredecessorHalfFin13Atom0679 chi ∧
      PredecessorHalfFin13Atom0706 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0818 chi) ∨
      ((PredecessorHalfFin13Atom1854 chi ∧
      ¬PredecessorHalfFin13Atom0678 chi) ∨
      (PredecessorHalfFin13Atom1854 chi ∧
      ¬PredecessorHalfFin13Atom0679 chi))) ∨
      (((PredecessorHalfFin13Atom1854 chi ∧
      ¬PredecessorHalfFin13Atom0735 chi) ∨
      (PredecessorHalfFin13Atom1854 chi ∧
      ¬PredecessorHalfFin13Atom0819 chi)) ∨
      ((PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom0680 chi) ∨
      (PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom0681 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom0687 chi) ∨
      ((PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom0736 chi) ∨
      (PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom0820 chi))) ∨
      ((¬PredecessorHalfFin13Atom1855 chi ∧
      PredecessorHalfFin13Atom0680 chi ∧
      PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0687 chi ∧
      PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0820 chi) ∨
      ((PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom0680 chi) ∨
      (PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom0682 chi)))) ∨
      (((PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom0688 chi) ∨
      ((PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom0737 chi) ∨
      (PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom0821 chi))) ∨
      ((¬PredecessorHalfFin13Atom1856 chi ∧
      PredecessorHalfFin13Atom0680 chi ∧
      PredecessorHalfFin13Atom0682 chi ∧
      PredecessorHalfFin13Atom0688 chi ∧
      PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0821 chi) ∨
      ((PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom0680 chi) ∨
      (PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom0683 chi))))) ∨
      ((((PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom0689 chi) ∨
      ((PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom0738 chi) ∨
      (PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom0822 chi))) ∨
      ((¬PredecessorHalfFin13Atom1857 chi ∧
      PredecessorHalfFin13Atom0680 chi ∧
      PredecessorHalfFin13Atom0683 chi ∧
      PredecessorHalfFin13Atom0689 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0822 chi) ∨
      ((PredecessorHalfFin13Atom1858 chi ∧
      ¬PredecessorHalfFin13Atom0680 chi) ∨
      (PredecessorHalfFin13Atom1858 chi ∧
      ¬PredecessorHalfFin13Atom0684 chi)))) ∨
      (((PredecessorHalfFin13Atom1858 chi ∧
      ¬PredecessorHalfFin13Atom0690 chi) ∨
      ((PredecessorHalfFin13Atom1858 chi ∧
      ¬PredecessorHalfFin13Atom0739 chi) ∨
      (PredecessorHalfFin13Atom1858 chi ∧
      ¬PredecessorHalfFin13Atom0823 chi))) ∨
      (((¬PredecessorHalfFin13Atom1858 chi ∧
      PredecessorHalfFin13Atom0680 chi ∧
      PredecessorHalfFin13Atom0684 chi ∧
      PredecessorHalfFin13Atom0690 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0823 chi) ∨
      (PredecessorHalfFin13Atom1859 chi ∧
      ¬PredecessorHalfFin13Atom0680 chi)) ∨
      ((PredecessorHalfFin13Atom1859 chi ∧
      ¬PredecessorHalfFin13Atom0685 chi) ∨
      (PredecessorHalfFin13Atom1859 chi ∧
      ¬PredecessorHalfFin13Atom0691 chi)))))) ∨
      (((((PredecessorHalfFin13Atom1859 chi ∧
      ¬PredecessorHalfFin13Atom0740 chi) ∨
      ((PredecessorHalfFin13Atom1859 chi ∧
      ¬PredecessorHalfFin13Atom0824 chi) ∨
      (PredecessorHalfFin13Atom1860 chi ∧
      ¬PredecessorHalfFin13Atom0680 chi))) ∨
      ((PredecessorHalfFin13Atom1860 chi ∧
      ¬PredecessorHalfFin13Atom0686 chi) ∨
      ((PredecessorHalfFin13Atom1860 chi ∧
      ¬PredecessorHalfFin13Atom0692 chi) ∨
      (PredecessorHalfFin13Atom1860 chi ∧
      ¬PredecessorHalfFin13Atom0741 chi)))) ∨
      (((PredecessorHalfFin13Atom1860 chi ∧
      ¬PredecessorHalfFin13Atom0825 chi) ∨
      ((¬PredecessorHalfFin13Atom1860 chi ∧
      PredecessorHalfFin13Atom0680 chi ∧
      PredecessorHalfFin13Atom0686 chi ∧
      PredecessorHalfFin13Atom0692 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0825 chi) ∨
      (PredecessorHalfFin13Atom1861 chi ∧
      ¬PredecessorHalfFin13Atom0681 chi))) ∨
      ((PredecessorHalfFin13Atom1861 chi ∧
      ¬PredecessorHalfFin13Atom0682 chi) ∨
      ((PredecessorHalfFin13Atom1861 chi ∧
      ¬PredecessorHalfFin13Atom0693 chi) ∨
      (PredecessorHalfFin13Atom1861 chi ∧
      ¬PredecessorHalfFin13Atom0742 chi))))) ∨
      ((((PredecessorHalfFin13Atom1861 chi ∧
      ¬PredecessorHalfFin13Atom0826 chi) ∨
      ((¬PredecessorHalfFin13Atom1861 chi ∧
      PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0682 chi ∧
      PredecessorHalfFin13Atom0693 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0826 chi) ∨
      (PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom0681 chi))) ∨
      ((PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom0683 chi) ∨
      ((PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom0694 chi) ∨
      (PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom0743 chi)))) ∨
      (((PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom0827 chi) ∨
      ((¬PredecessorHalfFin13Atom1862 chi ∧
      PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0683 chi ∧
      PredecessorHalfFin13Atom0694 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0827 chi) ∨
      (PredecessorHalfFin13Atom1863 chi ∧
      ¬PredecessorHalfFin13Atom0681 chi))) ∨
      (((PredecessorHalfFin13Atom1863 chi ∧
      ¬PredecessorHalfFin13Atom0684 chi) ∨
      (PredecessorHalfFin13Atom1863 chi ∧
      ¬PredecessorHalfFin13Atom0695 chi)) ∨
      ((PredecessorHalfFin13Atom1863 chi ∧
      ¬PredecessorHalfFin13Atom0744 chi) ∨
      (PredecessorHalfFin13Atom1863 chi ∧
      ¬PredecessorHalfFin13Atom0828 chi))))))))) := by
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
              exact predecessorHalfFin13_clause22227 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22228 chi hbad
              ·
                exact predecessorHalfFin13_clause22229 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22230 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22231 chi hbad
              ·
                exact predecessorHalfFin13_clause22232 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22233 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22234 chi hbad
              ·
                exact predecessorHalfFin13_clause22235 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22237 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22238 chi hbad
              ·
                exact predecessorHalfFin13_clause22239 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22240 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22241 chi hbad
              ·
                exact predecessorHalfFin13_clause22242 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22243 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22244 chi hbad
              ·
                exact predecessorHalfFin13_clause22245 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22246 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22247 chi hbad
              ·
                exact predecessorHalfFin13_clause22248 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22249 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22250 chi hbad
              ·
                exact predecessorHalfFin13_clause22251 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22252 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22253 chi hbad
              ·
                exact predecessorHalfFin13_clause22255 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22256 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22257 chi hbad
              ·
                exact predecessorHalfFin13_clause22258 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22259 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22260 chi hbad
              ·
                exact predecessorHalfFin13_clause22261 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22262 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22263 chi hbad
              ·
                exact predecessorHalfFin13_clause22264 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22265 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22267 chi hbad
              ·
                exact predecessorHalfFin13_clause22268 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22269 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22270 chi hbad
              ·
                exact predecessorHalfFin13_clause22271 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22272 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22273 chi hbad
              ·
                exact predecessorHalfFin13_clause22274 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22276 chi hbad
              ·
                exact predecessorHalfFin13_clause22277 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22279 chi hbad
              ·
                exact predecessorHalfFin13_clause22280 chi hbad
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
              exact predecessorHalfFin13_clause22281 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22282 chi hbad
              ·
                exact predecessorHalfFin13_clause22283 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22284 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22285 chi hbad
              ·
                exact predecessorHalfFin13_clause22286 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22287 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22288 chi hbad
              ·
                exact predecessorHalfFin13_clause22289 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22290 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22291 chi hbad
              ·
                exact predecessorHalfFin13_clause22292 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22293 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22294 chi hbad
              ·
                exact predecessorHalfFin13_clause22295 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22296 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22297 chi hbad
              ·
                exact predecessorHalfFin13_clause22298 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22299 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22300 chi hbad
              ·
                exact predecessorHalfFin13_clause22301 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22302 chi hbad
              ·
                exact predecessorHalfFin13_clause22303 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22304 chi hbad
              ·
                exact predecessorHalfFin13_clause22305 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22306 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22307 chi hbad
              ·
                exact predecessorHalfFin13_clause22309 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22310 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22311 chi hbad
              ·
                exact predecessorHalfFin13_clause22312 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22313 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22314 chi hbad
              ·
                exact predecessorHalfFin13_clause22315 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22316 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22317 chi hbad
              ·
                exact predecessorHalfFin13_clause22318 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22319 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22320 chi hbad
              ·
                exact predecessorHalfFin13_clause22321 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22322 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22323 chi hbad
              ·
                exact predecessorHalfFin13_clause22324 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22325 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22326 chi hbad
              ·
                exact predecessorHalfFin13_clause22327 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22328 chi hbad
              ·
                exact predecessorHalfFin13_clause22329 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22330 chi hbad
              ·
                exact predecessorHalfFin13_clause22331 chi hbad

end ErdosSzekeres

end
