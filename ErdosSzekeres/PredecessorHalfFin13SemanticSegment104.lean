module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk079
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk080

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 104. -/

theorem predecessorHalfFin13_rejectSemanticSegment104
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom2044 chi ∧
      ¬PredecessorHalfFin13Atom0883 chi) ∨
      ((¬PredecessorHalfFin13Atom2044 chi ∧
      PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0883 chi) ∨
      (PredecessorHalfFin13Atom2045 chi ∧
      ¬PredecessorHalfFin13Atom0793 chi))) ∨
      ((PredecessorHalfFin13Atom2045 chi ∧
      ¬PredecessorHalfFin13Atom0796 chi) ∨
      ((PredecessorHalfFin13Atom2045 chi ∧
      ¬PredecessorHalfFin13Atom0807 chi) ∨
      (PredecessorHalfFin13Atom2045 chi ∧
      ¬PredecessorHalfFin13Atom0828 chi)))) ∨
      (((PredecessorHalfFin13Atom2045 chi ∧
      ¬PredecessorHalfFin13Atom0884 chi) ∨
      ((¬PredecessorHalfFin13Atom2045 chi ∧
      PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0884 chi) ∨
      (PredecessorHalfFin13Atom2046 chi ∧
      ¬PredecessorHalfFin13Atom0793 chi))) ∨
      ((PredecessorHalfFin13Atom2046 chi ∧
      ¬PredecessorHalfFin13Atom0797 chi) ∨
      ((PredecessorHalfFin13Atom2046 chi ∧
      ¬PredecessorHalfFin13Atom0808 chi) ∨
      (PredecessorHalfFin13Atom2046 chi ∧
      ¬PredecessorHalfFin13Atom0829 chi))))) ∨
      ((((PredecessorHalfFin13Atom2046 chi ∧
      ¬PredecessorHalfFin13Atom0885 chi) ∨
      ((PredecessorHalfFin13Atom2047 chi ∧
      ¬PredecessorHalfFin13Atom0793 chi) ∨
      (PredecessorHalfFin13Atom2047 chi ∧
      ¬PredecessorHalfFin13Atom0798 chi))) ∨
      ((PredecessorHalfFin13Atom2047 chi ∧
      ¬PredecessorHalfFin13Atom0809 chi) ∨
      ((PredecessorHalfFin13Atom2047 chi ∧
      ¬PredecessorHalfFin13Atom0830 chi) ∨
      (PredecessorHalfFin13Atom2047 chi ∧
      ¬PredecessorHalfFin13Atom0886 chi)))) ∨
      (((¬PredecessorHalfFin13Atom2047 chi ∧
      PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0886 chi) ∨
      ((PredecessorHalfFin13Atom2048 chi ∧
      ¬PredecessorHalfFin13Atom0794 chi) ∨
      (PredecessorHalfFin13Atom2048 chi ∧
      ¬PredecessorHalfFin13Atom0795 chi))) ∨
      ((PredecessorHalfFin13Atom2048 chi ∧
      ¬PredecessorHalfFin13Atom0810 chi) ∨
      ((PredecessorHalfFin13Atom2048 chi ∧
      ¬PredecessorHalfFin13Atom0831 chi) ∨
      (PredecessorHalfFin13Atom2048 chi ∧
      ¬PredecessorHalfFin13Atom0887 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom2048 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0887 chi) ∨
      ((PredecessorHalfFin13Atom2049 chi ∧
      ¬PredecessorHalfFin13Atom0794 chi) ∨
      (PredecessorHalfFin13Atom2049 chi ∧
      ¬PredecessorHalfFin13Atom0796 chi))) ∨
      ((PredecessorHalfFin13Atom2049 chi ∧
      ¬PredecessorHalfFin13Atom0811 chi) ∨
      ((PredecessorHalfFin13Atom2049 chi ∧
      ¬PredecessorHalfFin13Atom0832 chi) ∨
      (PredecessorHalfFin13Atom2049 chi ∧
      ¬PredecessorHalfFin13Atom0888 chi)))) ∨
      (((¬PredecessorHalfFin13Atom2049 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0888 chi) ∨
      ((PredecessorHalfFin13Atom2050 chi ∧
      ¬PredecessorHalfFin13Atom0794 chi) ∨
      (PredecessorHalfFin13Atom2050 chi ∧
      ¬PredecessorHalfFin13Atom0797 chi))) ∨
      ((PredecessorHalfFin13Atom2050 chi ∧
      ¬PredecessorHalfFin13Atom0812 chi) ∨
      ((PredecessorHalfFin13Atom2050 chi ∧
      ¬PredecessorHalfFin13Atom0833 chi) ∨
      (PredecessorHalfFin13Atom2050 chi ∧
      ¬PredecessorHalfFin13Atom0889 chi))))) ∨
      ((((PredecessorHalfFin13Atom2051 chi ∧
      ¬PredecessorHalfFin13Atom0794 chi) ∨
      ((PredecessorHalfFin13Atom2051 chi ∧
      ¬PredecessorHalfFin13Atom0798 chi) ∨
      (PredecessorHalfFin13Atom2051 chi ∧
      ¬PredecessorHalfFin13Atom0813 chi))) ∨
      ((PredecessorHalfFin13Atom2051 chi ∧
      ¬PredecessorHalfFin13Atom0834 chi) ∨
      ((PredecessorHalfFin13Atom2051 chi ∧
      ¬PredecessorHalfFin13Atom0890 chi) ∨
      (¬PredecessorHalfFin13Atom2051 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0813 chi ∧
      PredecessorHalfFin13Atom0834 chi ∧
      PredecessorHalfFin13Atom0890 chi)))) ∨
      (((PredecessorHalfFin13Atom2052 chi ∧
      ¬PredecessorHalfFin13Atom0795 chi) ∨
      ((PredecessorHalfFin13Atom2052 chi ∧
      ¬PredecessorHalfFin13Atom0796 chi) ∨
      (PredecessorHalfFin13Atom2052 chi ∧
      ¬PredecessorHalfFin13Atom0814 chi))) ∨
      (((PredecessorHalfFin13Atom2052 chi ∧
      ¬PredecessorHalfFin13Atom0835 chi) ∨
      (PredecessorHalfFin13Atom2052 chi ∧
      ¬PredecessorHalfFin13Atom0891 chi)) ∨
      ((¬PredecessorHalfFin13Atom2052 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0891 chi) ∨
      (PredecessorHalfFin13Atom2053 chi ∧
      ¬PredecessorHalfFin13Atom0795 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom2053 chi ∧
      ¬PredecessorHalfFin13Atom0797 chi) ∨
      ((PredecessorHalfFin13Atom2053 chi ∧
      ¬PredecessorHalfFin13Atom0815 chi) ∨
      (PredecessorHalfFin13Atom2053 chi ∧
      ¬PredecessorHalfFin13Atom0836 chi))) ∨
      ((PredecessorHalfFin13Atom2053 chi ∧
      ¬PredecessorHalfFin13Atom0892 chi) ∨
      ((¬PredecessorHalfFin13Atom2053 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0797 chi ∧
      PredecessorHalfFin13Atom0815 chi ∧
      PredecessorHalfFin13Atom0836 chi ∧
      PredecessorHalfFin13Atom0892 chi) ∨
      (PredecessorHalfFin13Atom2054 chi ∧
      ¬PredecessorHalfFin13Atom0795 chi)))) ∨
      (((PredecessorHalfFin13Atom2054 chi ∧
      ¬PredecessorHalfFin13Atom0798 chi) ∨
      ((PredecessorHalfFin13Atom2054 chi ∧
      ¬PredecessorHalfFin13Atom0816 chi) ∨
      (PredecessorHalfFin13Atom2054 chi ∧
      ¬PredecessorHalfFin13Atom0837 chi))) ∨
      ((PredecessorHalfFin13Atom2054 chi ∧
      ¬PredecessorHalfFin13Atom0893 chi) ∨
      ((¬PredecessorHalfFin13Atom2054 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0816 chi ∧
      PredecessorHalfFin13Atom0837 chi ∧
      PredecessorHalfFin13Atom0893 chi) ∨
      (PredecessorHalfFin13Atom2055 chi ∧
      ¬PredecessorHalfFin13Atom0796 chi))))) ∨
      ((((PredecessorHalfFin13Atom2055 chi ∧
      ¬PredecessorHalfFin13Atom0797 chi) ∨
      ((PredecessorHalfFin13Atom2055 chi ∧
      ¬PredecessorHalfFin13Atom0817 chi) ∨
      (PredecessorHalfFin13Atom2055 chi ∧
      ¬PredecessorHalfFin13Atom0838 chi))) ∨
      ((PredecessorHalfFin13Atom2055 chi ∧
      ¬PredecessorHalfFin13Atom0894 chi) ∨
      ((PredecessorHalfFin13Atom2056 chi ∧
      ¬PredecessorHalfFin13Atom0796 chi) ∨
      (PredecessorHalfFin13Atom2056 chi ∧
      ¬PredecessorHalfFin13Atom0798 chi)))) ∨
      (((PredecessorHalfFin13Atom2056 chi ∧
      ¬PredecessorHalfFin13Atom0818 chi) ∨
      ((PredecessorHalfFin13Atom2056 chi ∧
      ¬PredecessorHalfFin13Atom0839 chi) ∨
      (PredecessorHalfFin13Atom2056 chi ∧
      ¬PredecessorHalfFin13Atom0895 chi))) ∨
      ((¬PredecessorHalfFin13Atom2056 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0818 chi ∧
      PredecessorHalfFin13Atom0839 chi ∧
      PredecessorHalfFin13Atom0895 chi) ∨
      ((PredecessorHalfFin13Atom2057 chi ∧
      ¬PredecessorHalfFin13Atom0797 chi) ∨
      (PredecessorHalfFin13Atom2057 chi ∧
      ¬PredecessorHalfFin13Atom0798 chi)))))) ∨
      (((((PredecessorHalfFin13Atom2057 chi ∧
      ¬PredecessorHalfFin13Atom0819 chi) ∨
      ((PredecessorHalfFin13Atom2057 chi ∧
      ¬PredecessorHalfFin13Atom0840 chi) ∨
      (PredecessorHalfFin13Atom2057 chi ∧
      ¬PredecessorHalfFin13Atom0896 chi))) ∨
      ((PredecessorHalfFin13Atom2058 chi ∧
      ¬PredecessorHalfFin13Atom0799 chi) ∨
      ((PredecessorHalfFin13Atom2058 chi ∧
      ¬PredecessorHalfFin13Atom0800 chi) ∨
      (PredecessorHalfFin13Atom2058 chi ∧
      ¬PredecessorHalfFin13Atom0805 chi)))) ∨
      (((PredecessorHalfFin13Atom2058 chi ∧
      ¬PredecessorHalfFin13Atom0841 chi) ∨
      ((PredecessorHalfFin13Atom2058 chi ∧
      ¬PredecessorHalfFin13Atom0897 chi) ∨
      (¬PredecessorHalfFin13Atom2058 chi ∧
      PredecessorHalfFin13Atom0799 chi ∧
      PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0841 chi ∧
      PredecessorHalfFin13Atom0897 chi))) ∨
      ((PredecessorHalfFin13Atom2059 chi ∧
      ¬PredecessorHalfFin13Atom0799 chi) ∨
      ((PredecessorHalfFin13Atom2059 chi ∧
      ¬PredecessorHalfFin13Atom0801 chi) ∨
      (PredecessorHalfFin13Atom2059 chi ∧
      ¬PredecessorHalfFin13Atom0806 chi))))) ∨
      ((((PredecessorHalfFin13Atom2059 chi ∧
      ¬PredecessorHalfFin13Atom0842 chi) ∨
      ((PredecessorHalfFin13Atom2059 chi ∧
      ¬PredecessorHalfFin13Atom0898 chi) ∨
      (¬PredecessorHalfFin13Atom2059 chi ∧
      PredecessorHalfFin13Atom0799 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0842 chi ∧
      PredecessorHalfFin13Atom0898 chi))) ∨
      ((PredecessorHalfFin13Atom2060 chi ∧
      ¬PredecessorHalfFin13Atom0799 chi) ∨
      ((PredecessorHalfFin13Atom2060 chi ∧
      ¬PredecessorHalfFin13Atom0802 chi) ∨
      (PredecessorHalfFin13Atom2060 chi ∧
      ¬PredecessorHalfFin13Atom0807 chi)))) ∨
      (((PredecessorHalfFin13Atom2060 chi ∧
      ¬PredecessorHalfFin13Atom0843 chi) ∨
      ((PredecessorHalfFin13Atom2060 chi ∧
      ¬PredecessorHalfFin13Atom0899 chi) ∨
      (¬PredecessorHalfFin13Atom2060 chi ∧
      PredecessorHalfFin13Atom0799 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0843 chi ∧
      PredecessorHalfFin13Atom0899 chi))) ∨
      (((PredecessorHalfFin13Atom2061 chi ∧
      ¬PredecessorHalfFin13Atom0799 chi) ∨
      (PredecessorHalfFin13Atom2061 chi ∧
      ¬PredecessorHalfFin13Atom0803 chi)) ∨
      ((PredecessorHalfFin13Atom2061 chi ∧
      ¬PredecessorHalfFin13Atom0808 chi) ∨
      (PredecessorHalfFin13Atom2061 chi ∧
      ¬PredecessorHalfFin13Atom0844 chi))))))))) := by
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
              exact predecessorHalfFin13_clause23417 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23418 chi hbad
              ·
                exact predecessorHalfFin13_clause23419 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23420 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23421 chi hbad
              ·
                exact predecessorHalfFin13_clause23422 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23423 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23424 chi hbad
              ·
                exact predecessorHalfFin13_clause23425 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23426 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23427 chi hbad
              ·
                exact predecessorHalfFin13_clause23428 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23429 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23431 chi hbad
              ·
                exact predecessorHalfFin13_clause23432 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23433 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23434 chi hbad
              ·
                exact predecessorHalfFin13_clause23435 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23436 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23437 chi hbad
              ·
                exact predecessorHalfFin13_clause23438 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23439 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23440 chi hbad
              ·
                exact predecessorHalfFin13_clause23441 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23442 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23443 chi hbad
              ·
                exact predecessorHalfFin13_clause23444 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23445 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23446 chi hbad
              ·
                exact predecessorHalfFin13_clause23447 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23448 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23449 chi hbad
              ·
                exact predecessorHalfFin13_clause23450 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23451 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23452 chi hbad
              ·
                exact predecessorHalfFin13_clause23453 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23455 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23456 chi hbad
              ·
                exact predecessorHalfFin13_clause23457 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23458 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23459 chi hbad
              ·
                exact predecessorHalfFin13_clause23460 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23461 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23462 chi hbad
              ·
                exact predecessorHalfFin13_clause23463 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23464 chi hbad
              ·
                exact predecessorHalfFin13_clause23465 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23466 chi hbad
              ·
                exact predecessorHalfFin13_clause23467 chi hbad
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
              exact predecessorHalfFin13_clause23468 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23469 chi hbad
              ·
                exact predecessorHalfFin13_clause23470 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23471 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23472 chi hbad
              ·
                exact predecessorHalfFin13_clause23473 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23474 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23475 chi hbad
              ·
                exact predecessorHalfFin13_clause23476 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23477 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23478 chi hbad
              ·
                exact predecessorHalfFin13_clause23479 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23480 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23481 chi hbad
              ·
                exact predecessorHalfFin13_clause23482 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23483 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23485 chi hbad
              ·
                exact predecessorHalfFin13_clause23486 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23487 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23488 chi hbad
              ·
                exact predecessorHalfFin13_clause23489 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23490 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23491 chi hbad
              ·
                exact predecessorHalfFin13_clause23492 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23493 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23494 chi hbad
              ·
                exact predecessorHalfFin13_clause23495 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23497 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23498 chi hbad
              ·
                exact predecessorHalfFin13_clause23499 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23500 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23501 chi hbad
              ·
                exact predecessorHalfFin13_clause23502 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23503 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23504 chi hbad
              ·
                exact predecessorHalfFin13_clause23505 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23506 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23507 chi hbad
              ·
                exact predecessorHalfFin13_clause23508 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23509 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23510 chi hbad
              ·
                exact predecessorHalfFin13_clause23511 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23512 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23513 chi hbad
              ·
                exact predecessorHalfFin13_clause23514 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23515 chi hbad
              ·
                exact predecessorHalfFin13_clause23516 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23517 chi hbad
              ·
                exact predecessorHalfFin13_clause23518 chi hbad

end ErdosSzekeres

end
