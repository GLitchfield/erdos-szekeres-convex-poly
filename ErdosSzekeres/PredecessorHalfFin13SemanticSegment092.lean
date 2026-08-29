module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk070
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk071

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 092. -/

theorem predecessorHalfFin13_rejectSemanticSegment092
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom0794 chi) ∨
      ((¬PredecessorHalfFin13Atom1829 chi ∧
      PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0675 chi ∧
      PredecessorHalfFin13Atom0682 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0794 chi) ∨
      (PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom0672 chi))) ∨
      ((PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom0676 chi) ∨
      ((PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom0683 chi) ∨
      (PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom0711 chi)))) ∨
      (((PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom0795 chi) ∨
      ((¬PredecessorHalfFin13Atom1830 chi ∧
      PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0676 chi ∧
      PredecessorHalfFin13Atom0683 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0795 chi) ∨
      (PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom0672 chi))) ∨
      ((PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom0677 chi) ∨
      ((PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom0684 chi) ∨
      (PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom0712 chi))))) ∨
      ((((PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom0796 chi) ∨
      ((¬PredecessorHalfFin13Atom1831 chi ∧
      PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0677 chi ∧
      PredecessorHalfFin13Atom0684 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0796 chi) ∨
      (PredecessorHalfFin13Atom1832 chi ∧
      ¬PredecessorHalfFin13Atom0672 chi))) ∨
      ((PredecessorHalfFin13Atom1832 chi ∧
      ¬PredecessorHalfFin13Atom0678 chi) ∨
      ((PredecessorHalfFin13Atom1832 chi ∧
      ¬PredecessorHalfFin13Atom0685 chi) ∨
      (PredecessorHalfFin13Atom1832 chi ∧
      ¬PredecessorHalfFin13Atom0713 chi)))) ∨
      (((PredecessorHalfFin13Atom1832 chi ∧
      ¬PredecessorHalfFin13Atom0797 chi) ∨
      ((PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom0672 chi) ∨
      (PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom0679 chi))) ∨
      ((PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom0686 chi) ∨
      ((PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom0714 chi) ∨
      (PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom0798 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom1833 chi ∧
      PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0679 chi ∧
      PredecessorHalfFin13Atom0686 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0798 chi) ∨
      ((PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom0673 chi) ∨
      (PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom0674 chi))) ∨
      ((PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom0687 chi) ∨
      ((PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom0715 chi) ∨
      (PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom0799 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1834 chi ∧
      PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0687 chi ∧
      PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0799 chi) ∨
      ((PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom0673 chi) ∨
      (PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom0675 chi))) ∨
      ((PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom0688 chi) ∨
      ((PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom0716 chi) ∨
      (PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom0800 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom1835 chi ∧
      PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0675 chi ∧
      PredecessorHalfFin13Atom0688 chi ∧
      PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0800 chi) ∨
      ((PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom0673 chi) ∨
      (PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom0676 chi))) ∨
      ((PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom0689 chi) ∨
      ((PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom0717 chi) ∨
      (PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom0801 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1836 chi ∧
      PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0676 chi ∧
      PredecessorHalfFin13Atom0689 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0801 chi) ∨
      ((PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom0673 chi) ∨
      (PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom0677 chi))) ∨
      (((PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom0690 chi) ∨
      (PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom0718 chi)) ∨
      ((PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom0802 chi) ∨
      (¬PredecessorHalfFin13Atom1837 chi ∧
      PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0677 chi ∧
      PredecessorHalfFin13Atom0690 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0802 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom1838 chi ∧
      ¬PredecessorHalfFin13Atom0673 chi) ∨
      ((PredecessorHalfFin13Atom1838 chi ∧
      ¬PredecessorHalfFin13Atom0678 chi) ∨
      (PredecessorHalfFin13Atom1838 chi ∧
      ¬PredecessorHalfFin13Atom0691 chi))) ∨
      ((PredecessorHalfFin13Atom1838 chi ∧
      ¬PredecessorHalfFin13Atom0719 chi) ∨
      ((PredecessorHalfFin13Atom1838 chi ∧
      ¬PredecessorHalfFin13Atom0803 chi) ∨
      (PredecessorHalfFin13Atom1839 chi ∧
      ¬PredecessorHalfFin13Atom0673 chi)))) ∨
      (((PredecessorHalfFin13Atom1839 chi ∧
      ¬PredecessorHalfFin13Atom0679 chi) ∨
      ((PredecessorHalfFin13Atom1839 chi ∧
      ¬PredecessorHalfFin13Atom0692 chi) ∨
      (PredecessorHalfFin13Atom1839 chi ∧
      ¬PredecessorHalfFin13Atom0720 chi))) ∨
      ((PredecessorHalfFin13Atom1839 chi ∧
      ¬PredecessorHalfFin13Atom0804 chi) ∨
      ((¬PredecessorHalfFin13Atom1839 chi ∧
      PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0679 chi ∧
      PredecessorHalfFin13Atom0692 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0804 chi) ∨
      (PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom0674 chi))))) ∨
      ((((PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom0675 chi) ∨
      ((PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom0693 chi) ∨
      (PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom0721 chi))) ∨
      ((PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom0805 chi) ∨
      ((¬PredecessorHalfFin13Atom1840 chi ∧
      PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0675 chi ∧
      PredecessorHalfFin13Atom0693 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0805 chi) ∨
      (PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom0674 chi)))) ∨
      (((PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom0676 chi) ∨
      ((PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom0694 chi) ∨
      (PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom0722 chi))) ∨
      ((PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom0806 chi) ∨
      ((¬PredecessorHalfFin13Atom1841 chi ∧
      PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0676 chi ∧
      PredecessorHalfFin13Atom0694 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0806 chi) ∨
      (PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom0674 chi)))))) ∨
      (((((PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom0677 chi) ∨
      ((PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom0695 chi) ∨
      (PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom0723 chi))) ∨
      ((PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom0807 chi) ∨
      ((¬PredecessorHalfFin13Atom1842 chi ∧
      PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0677 chi ∧
      PredecessorHalfFin13Atom0695 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0807 chi) ∨
      (PredecessorHalfFin13Atom1843 chi ∧
      ¬PredecessorHalfFin13Atom0674 chi)))) ∨
      (((PredecessorHalfFin13Atom1843 chi ∧
      ¬PredecessorHalfFin13Atom0678 chi) ∨
      ((PredecessorHalfFin13Atom1843 chi ∧
      ¬PredecessorHalfFin13Atom0696 chi) ∨
      (PredecessorHalfFin13Atom1843 chi ∧
      ¬PredecessorHalfFin13Atom0724 chi))) ∨
      ((PredecessorHalfFin13Atom1843 chi ∧
      ¬PredecessorHalfFin13Atom0808 chi) ∨
      ((¬PredecessorHalfFin13Atom1843 chi ∧
      PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0678 chi ∧
      PredecessorHalfFin13Atom0696 chi ∧
      PredecessorHalfFin13Atom0724 chi ∧
      PredecessorHalfFin13Atom0808 chi) ∨
      (PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom0674 chi))))) ∨
      ((((PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom0679 chi) ∨
      ((PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom0697 chi) ∨
      (PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom0725 chi))) ∨
      ((PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom0809 chi) ∨
      ((¬PredecessorHalfFin13Atom1844 chi ∧
      PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0679 chi ∧
      PredecessorHalfFin13Atom0697 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0809 chi) ∨
      (PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom0675 chi)))) ∨
      (((PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom0676 chi) ∨
      ((PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom0698 chi) ∨
      (PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom0726 chi))) ∨
      (((PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom0810 chi) ∨
      (¬PredecessorHalfFin13Atom1845 chi ∧
      PredecessorHalfFin13Atom0675 chi ∧
      PredecessorHalfFin13Atom0676 chi ∧
      PredecessorHalfFin13Atom0698 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0810 chi)) ∨
      ((PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom0675 chi) ∨
      (PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom0677 chi))))))))) := by
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
              exact predecessorHalfFin13_clause22127 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22128 chi hbad
              ·
                exact predecessorHalfFin13_clause22129 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22130 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22131 chi hbad
              ·
                exact predecessorHalfFin13_clause22132 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22133 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22134 chi hbad
              ·
                exact predecessorHalfFin13_clause22135 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22136 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22137 chi hbad
              ·
                exact predecessorHalfFin13_clause22138 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22139 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22140 chi hbad
              ·
                exact predecessorHalfFin13_clause22141 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22142 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22143 chi hbad
              ·
                exact predecessorHalfFin13_clause22144 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22145 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22147 chi hbad
              ·
                exact predecessorHalfFin13_clause22148 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22149 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22150 chi hbad
              ·
                exact predecessorHalfFin13_clause22151 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22152 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22153 chi hbad
              ·
                exact predecessorHalfFin13_clause22154 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22155 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22156 chi hbad
              ·
                exact predecessorHalfFin13_clause22157 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22158 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22159 chi hbad
              ·
                exact predecessorHalfFin13_clause22160 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22161 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22162 chi hbad
              ·
                exact predecessorHalfFin13_clause22163 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22164 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22165 chi hbad
              ·
                exact predecessorHalfFin13_clause22166 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22167 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22168 chi hbad
              ·
                exact predecessorHalfFin13_clause22169 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22170 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22171 chi hbad
              ·
                exact predecessorHalfFin13_clause22172 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22173 chi hbad
              ·
                exact predecessorHalfFin13_clause22174 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22175 chi hbad
              ·
                exact predecessorHalfFin13_clause22176 chi hbad
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
              exact predecessorHalfFin13_clause22177 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22178 chi hbad
              ·
                exact predecessorHalfFin13_clause22179 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22180 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22181 chi hbad
              ·
                exact predecessorHalfFin13_clause22183 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22184 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22185 chi hbad
              ·
                exact predecessorHalfFin13_clause22186 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22187 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22188 chi hbad
              ·
                exact predecessorHalfFin13_clause22189 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22190 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22191 chi hbad
              ·
                exact predecessorHalfFin13_clause22192 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22193 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22194 chi hbad
              ·
                exact predecessorHalfFin13_clause22195 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22196 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22197 chi hbad
              ·
                exact predecessorHalfFin13_clause22198 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22199 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22200 chi hbad
              ·
                exact predecessorHalfFin13_clause22201 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22202 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22203 chi hbad
              ·
                exact predecessorHalfFin13_clause22204 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22205 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22206 chi hbad
              ·
                exact predecessorHalfFin13_clause22207 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22208 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22209 chi hbad
              ·
                exact predecessorHalfFin13_clause22210 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22211 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22212 chi hbad
              ·
                exact predecessorHalfFin13_clause22213 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22214 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22215 chi hbad
              ·
                exact predecessorHalfFin13_clause22216 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22217 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22218 chi hbad
              ·
                exact predecessorHalfFin13_clause22219 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22220 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22221 chi hbad
              ·
                exact predecessorHalfFin13_clause22222 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22223 chi hbad
              ·
                exact predecessorHalfFin13_clause22224 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22225 chi hbad
              ·
                exact predecessorHalfFin13_clause22226 chi hbad

end ErdosSzekeres

end
