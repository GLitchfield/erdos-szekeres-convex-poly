module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk080
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk081

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 105. -/

theorem predecessorHalfFin13_rejectSemanticSegment105
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom2061 chi ∧
      ¬PredecessorHalfFin13Atom0900 chi) ∨
      ((PredecessorHalfFin13Atom2062 chi ∧
      ¬PredecessorHalfFin13Atom0799 chi) ∨
      (PredecessorHalfFin13Atom2062 chi ∧
      ¬PredecessorHalfFin13Atom0804 chi))) ∨
      ((PredecessorHalfFin13Atom2062 chi ∧
      ¬PredecessorHalfFin13Atom0809 chi) ∨
      ((PredecessorHalfFin13Atom2062 chi ∧
      ¬PredecessorHalfFin13Atom0845 chi) ∨
      (PredecessorHalfFin13Atom2062 chi ∧
      ¬PredecessorHalfFin13Atom0901 chi)))) ∨
      (((¬PredecessorHalfFin13Atom2062 chi ∧
      PredecessorHalfFin13Atom0799 chi ∧
      PredecessorHalfFin13Atom0804 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0845 chi ∧
      PredecessorHalfFin13Atom0901 chi) ∨
      ((PredecessorHalfFin13Atom2063 chi ∧
      ¬PredecessorHalfFin13Atom0800 chi) ∨
      (PredecessorHalfFin13Atom2063 chi ∧
      ¬PredecessorHalfFin13Atom0801 chi))) ∨
      ((PredecessorHalfFin13Atom2063 chi ∧
      ¬PredecessorHalfFin13Atom0810 chi) ∨
      ((PredecessorHalfFin13Atom2063 chi ∧
      ¬PredecessorHalfFin13Atom0846 chi) ∨
      (PredecessorHalfFin13Atom2063 chi ∧
      ¬PredecessorHalfFin13Atom0902 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom2063 chi ∧
      PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0846 chi ∧
      PredecessorHalfFin13Atom0902 chi) ∨
      ((PredecessorHalfFin13Atom2064 chi ∧
      ¬PredecessorHalfFin13Atom0800 chi) ∨
      (PredecessorHalfFin13Atom2064 chi ∧
      ¬PredecessorHalfFin13Atom0802 chi))) ∨
      ((PredecessorHalfFin13Atom2064 chi ∧
      ¬PredecessorHalfFin13Atom0811 chi) ∨
      ((PredecessorHalfFin13Atom2064 chi ∧
      ¬PredecessorHalfFin13Atom0847 chi) ∨
      (PredecessorHalfFin13Atom2064 chi ∧
      ¬PredecessorHalfFin13Atom0903 chi)))) ∨
      (((¬PredecessorHalfFin13Atom2064 chi ∧
      PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0847 chi ∧
      PredecessorHalfFin13Atom0903 chi) ∨
      ((PredecessorHalfFin13Atom2065 chi ∧
      ¬PredecessorHalfFin13Atom0800 chi) ∨
      (PredecessorHalfFin13Atom2065 chi ∧
      ¬PredecessorHalfFin13Atom0803 chi))) ∨
      ((PredecessorHalfFin13Atom2065 chi ∧
      ¬PredecessorHalfFin13Atom0812 chi) ∨
      ((PredecessorHalfFin13Atom2065 chi ∧
      ¬PredecessorHalfFin13Atom0848 chi) ∨
      (PredecessorHalfFin13Atom2065 chi ∧
      ¬PredecessorHalfFin13Atom0904 chi)))))) ∨
      (((((PredecessorHalfFin13Atom2066 chi ∧
      ¬PredecessorHalfFin13Atom0800 chi) ∨
      ((PredecessorHalfFin13Atom2066 chi ∧
      ¬PredecessorHalfFin13Atom0804 chi) ∨
      (PredecessorHalfFin13Atom2066 chi ∧
      ¬PredecessorHalfFin13Atom0813 chi))) ∨
      ((PredecessorHalfFin13Atom2066 chi ∧
      ¬PredecessorHalfFin13Atom0849 chi) ∨
      ((PredecessorHalfFin13Atom2066 chi ∧
      ¬PredecessorHalfFin13Atom0905 chi) ∨
      (¬PredecessorHalfFin13Atom2066 chi ∧
      PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0804 chi ∧
      PredecessorHalfFin13Atom0813 chi ∧
      PredecessorHalfFin13Atom0849 chi ∧
      PredecessorHalfFin13Atom0905 chi)))) ∨
      (((PredecessorHalfFin13Atom2067 chi ∧
      ¬PredecessorHalfFin13Atom0801 chi) ∨
      ((PredecessorHalfFin13Atom2067 chi ∧
      ¬PredecessorHalfFin13Atom0802 chi) ∨
      (PredecessorHalfFin13Atom2067 chi ∧
      ¬PredecessorHalfFin13Atom0814 chi))) ∨
      ((PredecessorHalfFin13Atom2067 chi ∧
      ¬PredecessorHalfFin13Atom0850 chi) ∨
      ((PredecessorHalfFin13Atom2067 chi ∧
      ¬PredecessorHalfFin13Atom0906 chi) ∨
      (¬PredecessorHalfFin13Atom2067 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0850 chi ∧
      PredecessorHalfFin13Atom0906 chi))))) ∨
      ((((PredecessorHalfFin13Atom2068 chi ∧
      ¬PredecessorHalfFin13Atom0801 chi) ∨
      ((PredecessorHalfFin13Atom2068 chi ∧
      ¬PredecessorHalfFin13Atom0803 chi) ∨
      (PredecessorHalfFin13Atom2068 chi ∧
      ¬PredecessorHalfFin13Atom0815 chi))) ∨
      ((PredecessorHalfFin13Atom2068 chi ∧
      ¬PredecessorHalfFin13Atom0851 chi) ∨
      ((PredecessorHalfFin13Atom2068 chi ∧
      ¬PredecessorHalfFin13Atom0907 chi) ∨
      (¬PredecessorHalfFin13Atom2068 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0803 chi ∧
      PredecessorHalfFin13Atom0815 chi ∧
      PredecessorHalfFin13Atom0851 chi ∧
      PredecessorHalfFin13Atom0907 chi)))) ∨
      (((PredecessorHalfFin13Atom2069 chi ∧
      ¬PredecessorHalfFin13Atom0801 chi) ∨
      ((PredecessorHalfFin13Atom2069 chi ∧
      ¬PredecessorHalfFin13Atom0804 chi) ∨
      (PredecessorHalfFin13Atom2069 chi ∧
      ¬PredecessorHalfFin13Atom0816 chi))) ∨
      (((PredecessorHalfFin13Atom2069 chi ∧
      ¬PredecessorHalfFin13Atom0852 chi) ∨
      (PredecessorHalfFin13Atom2069 chi ∧
      ¬PredecessorHalfFin13Atom0908 chi)) ∨
      ((¬PredecessorHalfFin13Atom2069 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0804 chi ∧
      PredecessorHalfFin13Atom0816 chi ∧
      PredecessorHalfFin13Atom0852 chi ∧
      PredecessorHalfFin13Atom0908 chi) ∨
      (PredecessorHalfFin13Atom2070 chi ∧
      ¬PredecessorHalfFin13Atom0802 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom2070 chi ∧
      ¬PredecessorHalfFin13Atom0803 chi) ∨
      ((PredecessorHalfFin13Atom2070 chi ∧
      ¬PredecessorHalfFin13Atom0817 chi) ∨
      (PredecessorHalfFin13Atom2070 chi ∧
      ¬PredecessorHalfFin13Atom0853 chi))) ∨
      ((PredecessorHalfFin13Atom2070 chi ∧
      ¬PredecessorHalfFin13Atom0909 chi) ∨
      ((PredecessorHalfFin13Atom2071 chi ∧
      ¬PredecessorHalfFin13Atom0802 chi) ∨
      (PredecessorHalfFin13Atom2071 chi ∧
      ¬PredecessorHalfFin13Atom0804 chi)))) ∨
      (((PredecessorHalfFin13Atom2071 chi ∧
      ¬PredecessorHalfFin13Atom0818 chi) ∨
      ((PredecessorHalfFin13Atom2071 chi ∧
      ¬PredecessorHalfFin13Atom0854 chi) ∨
      (PredecessorHalfFin13Atom2071 chi ∧
      ¬PredecessorHalfFin13Atom0910 chi))) ∨
      ((¬PredecessorHalfFin13Atom2071 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0804 chi ∧
      PredecessorHalfFin13Atom0818 chi ∧
      PredecessorHalfFin13Atom0854 chi ∧
      PredecessorHalfFin13Atom0910 chi) ∨
      ((PredecessorHalfFin13Atom2072 chi ∧
      ¬PredecessorHalfFin13Atom0803 chi) ∨
      (PredecessorHalfFin13Atom2072 chi ∧
      ¬PredecessorHalfFin13Atom0804 chi))))) ∨
      ((((PredecessorHalfFin13Atom2072 chi ∧
      ¬PredecessorHalfFin13Atom0819 chi) ∨
      ((PredecessorHalfFin13Atom2072 chi ∧
      ¬PredecessorHalfFin13Atom0855 chi) ∨
      (PredecessorHalfFin13Atom2072 chi ∧
      ¬PredecessorHalfFin13Atom0911 chi))) ∨
      ((PredecessorHalfFin13Atom2073 chi ∧
      ¬PredecessorHalfFin13Atom0805 chi) ∨
      ((PredecessorHalfFin13Atom2073 chi ∧
      ¬PredecessorHalfFin13Atom0806 chi) ∨
      (PredecessorHalfFin13Atom2073 chi ∧
      ¬PredecessorHalfFin13Atom0810 chi)))) ∨
      (((PredecessorHalfFin13Atom2073 chi ∧
      ¬PredecessorHalfFin13Atom0856 chi) ∨
      ((PredecessorHalfFin13Atom2073 chi ∧
      ¬PredecessorHalfFin13Atom0912 chi) ∨
      (¬PredecessorHalfFin13Atom2073 chi ∧
      PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0856 chi ∧
      PredecessorHalfFin13Atom0912 chi))) ∨
      ((PredecessorHalfFin13Atom2074 chi ∧
      ¬PredecessorHalfFin13Atom0805 chi) ∨
      ((PredecessorHalfFin13Atom2074 chi ∧
      ¬PredecessorHalfFin13Atom0807 chi) ∨
      (PredecessorHalfFin13Atom2074 chi ∧
      ¬PredecessorHalfFin13Atom0811 chi)))))) ∨
      (((((PredecessorHalfFin13Atom2074 chi ∧
      ¬PredecessorHalfFin13Atom0857 chi) ∨
      ((PredecessorHalfFin13Atom2074 chi ∧
      ¬PredecessorHalfFin13Atom0913 chi) ∨
      (¬PredecessorHalfFin13Atom2074 chi ∧
      PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0857 chi ∧
      PredecessorHalfFin13Atom0913 chi))) ∨
      ((PredecessorHalfFin13Atom2075 chi ∧
      ¬PredecessorHalfFin13Atom0805 chi) ∨
      ((PredecessorHalfFin13Atom2075 chi ∧
      ¬PredecessorHalfFin13Atom0808 chi) ∨
      (PredecessorHalfFin13Atom2075 chi ∧
      ¬PredecessorHalfFin13Atom0812 chi)))) ∨
      (((PredecessorHalfFin13Atom2075 chi ∧
      ¬PredecessorHalfFin13Atom0858 chi) ∨
      ((PredecessorHalfFin13Atom2075 chi ∧
      ¬PredecessorHalfFin13Atom0914 chi) ∨
      (PredecessorHalfFin13Atom2076 chi ∧
      ¬PredecessorHalfFin13Atom0805 chi))) ∨
      ((PredecessorHalfFin13Atom2076 chi ∧
      ¬PredecessorHalfFin13Atom0809 chi) ∨
      ((PredecessorHalfFin13Atom2076 chi ∧
      ¬PredecessorHalfFin13Atom0813 chi) ∨
      (PredecessorHalfFin13Atom2076 chi ∧
      ¬PredecessorHalfFin13Atom0859 chi))))) ∨
      ((((PredecessorHalfFin13Atom2076 chi ∧
      ¬PredecessorHalfFin13Atom0915 chi) ∨
      ((¬PredecessorHalfFin13Atom2076 chi ∧
      PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0813 chi ∧
      PredecessorHalfFin13Atom0859 chi ∧
      PredecessorHalfFin13Atom0915 chi) ∨
      (PredecessorHalfFin13Atom2077 chi ∧
      ¬PredecessorHalfFin13Atom0806 chi))) ∨
      ((PredecessorHalfFin13Atom2077 chi ∧
      ¬PredecessorHalfFin13Atom0807 chi) ∨
      ((PredecessorHalfFin13Atom2077 chi ∧
      ¬PredecessorHalfFin13Atom0814 chi) ∨
      (PredecessorHalfFin13Atom2077 chi ∧
      ¬PredecessorHalfFin13Atom0860 chi)))) ∨
      (((PredecessorHalfFin13Atom2077 chi ∧
      ¬PredecessorHalfFin13Atom0916 chi) ∨
      ((¬PredecessorHalfFin13Atom2077 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0860 chi ∧
      PredecessorHalfFin13Atom0916 chi) ∨
      (PredecessorHalfFin13Atom2078 chi ∧
      ¬PredecessorHalfFin13Atom0806 chi))) ∨
      (((PredecessorHalfFin13Atom2078 chi ∧
      ¬PredecessorHalfFin13Atom0808 chi) ∨
      (PredecessorHalfFin13Atom2078 chi ∧
      ¬PredecessorHalfFin13Atom0815 chi)) ∨
      ((PredecessorHalfFin13Atom2078 chi ∧
      ¬PredecessorHalfFin13Atom0861 chi) ∨
      (PredecessorHalfFin13Atom2078 chi ∧
      ¬PredecessorHalfFin13Atom0917 chi))))))))) := by
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
              exact predecessorHalfFin13_clause23519 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23521 chi hbad
              ·
                exact predecessorHalfFin13_clause23522 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23523 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23524 chi hbad
              ·
                exact predecessorHalfFin13_clause23525 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23526 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23527 chi hbad
              ·
                exact predecessorHalfFin13_clause23528 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23529 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23530 chi hbad
              ·
                exact predecessorHalfFin13_clause23531 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23532 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23533 chi hbad
              ·
                exact predecessorHalfFin13_clause23534 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23535 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23536 chi hbad
              ·
                exact predecessorHalfFin13_clause23537 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23538 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23539 chi hbad
              ·
                exact predecessorHalfFin13_clause23540 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23541 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23542 chi hbad
              ·
                exact predecessorHalfFin13_clause23543 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23545 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23546 chi hbad
              ·
                exact predecessorHalfFin13_clause23547 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23548 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23549 chi hbad
              ·
                exact predecessorHalfFin13_clause23550 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23551 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23552 chi hbad
              ·
                exact predecessorHalfFin13_clause23553 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23554 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23555 chi hbad
              ·
                exact predecessorHalfFin13_clause23556 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23557 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23558 chi hbad
              ·
                exact predecessorHalfFin13_clause23559 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23560 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23561 chi hbad
              ·
                exact predecessorHalfFin13_clause23562 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23563 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23564 chi hbad
              ·
                exact predecessorHalfFin13_clause23565 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23566 chi hbad
              ·
                exact predecessorHalfFin13_clause23567 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23568 chi hbad
              ·
                exact predecessorHalfFin13_clause23569 chi hbad
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
              exact predecessorHalfFin13_clause23570 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23571 chi hbad
              ·
                exact predecessorHalfFin13_clause23572 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23573 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23575 chi hbad
              ·
                exact predecessorHalfFin13_clause23576 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23577 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23578 chi hbad
              ·
                exact predecessorHalfFin13_clause23579 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23580 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23581 chi hbad
              ·
                exact predecessorHalfFin13_clause23582 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23583 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23584 chi hbad
              ·
                exact predecessorHalfFin13_clause23585 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23587 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23588 chi hbad
              ·
                exact predecessorHalfFin13_clause23589 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23590 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23591 chi hbad
              ·
                exact predecessorHalfFin13_clause23592 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23593 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23594 chi hbad
              ·
                exact predecessorHalfFin13_clause23595 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23596 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23597 chi hbad
              ·
                exact predecessorHalfFin13_clause23598 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23599 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23600 chi hbad
              ·
                exact predecessorHalfFin13_clause23601 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23602 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23603 chi hbad
              ·
                exact predecessorHalfFin13_clause23605 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23606 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23607 chi hbad
              ·
                exact predecessorHalfFin13_clause23608 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23609 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23610 chi hbad
              ·
                exact predecessorHalfFin13_clause23611 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23612 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23613 chi hbad
              ·
                exact predecessorHalfFin13_clause23614 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23615 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23616 chi hbad
              ·
                exact predecessorHalfFin13_clause23617 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23618 chi hbad
              ·
                exact predecessorHalfFin13_clause23619 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23620 chi hbad
              ·
                exact predecessorHalfFin13_clause23621 chi hbad

end ErdosSzekeres

end
