module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk081
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk082

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 106. -/

theorem predecessorHalfFin13_rejectSemanticSegment106
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((¬PredecessorHalfFin13Atom2078 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0808 chi ∧
      PredecessorHalfFin13Atom0815 chi ∧
      PredecessorHalfFin13Atom0861 chi ∧
      PredecessorHalfFin13Atom0917 chi) ∨
      ((PredecessorHalfFin13Atom2079 chi ∧
      ¬PredecessorHalfFin13Atom0806 chi) ∨
      (PredecessorHalfFin13Atom2079 chi ∧
      ¬PredecessorHalfFin13Atom0809 chi))) ∨
      ((PredecessorHalfFin13Atom2079 chi ∧
      ¬PredecessorHalfFin13Atom0816 chi) ∨
      ((PredecessorHalfFin13Atom2079 chi ∧
      ¬PredecessorHalfFin13Atom0862 chi) ∨
      (PredecessorHalfFin13Atom2079 chi ∧
      ¬PredecessorHalfFin13Atom0918 chi)))) ∨
      (((¬PredecessorHalfFin13Atom2079 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0816 chi ∧
      PredecessorHalfFin13Atom0862 chi ∧
      PredecessorHalfFin13Atom0918 chi) ∨
      ((PredecessorHalfFin13Atom2080 chi ∧
      ¬PredecessorHalfFin13Atom0807 chi) ∨
      (PredecessorHalfFin13Atom2080 chi ∧
      ¬PredecessorHalfFin13Atom0808 chi))) ∨
      ((PredecessorHalfFin13Atom2080 chi ∧
      ¬PredecessorHalfFin13Atom0817 chi) ∨
      ((PredecessorHalfFin13Atom2080 chi ∧
      ¬PredecessorHalfFin13Atom0863 chi) ∨
      (PredecessorHalfFin13Atom2080 chi ∧
      ¬PredecessorHalfFin13Atom0919 chi))))) ∨
      ((((PredecessorHalfFin13Atom2081 chi ∧
      ¬PredecessorHalfFin13Atom0807 chi) ∨
      ((PredecessorHalfFin13Atom2081 chi ∧
      ¬PredecessorHalfFin13Atom0809 chi) ∨
      (PredecessorHalfFin13Atom2081 chi ∧
      ¬PredecessorHalfFin13Atom0818 chi))) ∨
      ((PredecessorHalfFin13Atom2081 chi ∧
      ¬PredecessorHalfFin13Atom0864 chi) ∨
      ((PredecessorHalfFin13Atom2081 chi ∧
      ¬PredecessorHalfFin13Atom0920 chi) ∨
      (¬PredecessorHalfFin13Atom2081 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0818 chi ∧
      PredecessorHalfFin13Atom0864 chi ∧
      PredecessorHalfFin13Atom0920 chi)))) ∨
      (((PredecessorHalfFin13Atom2082 chi ∧
      ¬PredecessorHalfFin13Atom0808 chi) ∨
      ((PredecessorHalfFin13Atom2082 chi ∧
      ¬PredecessorHalfFin13Atom0809 chi) ∨
      (PredecessorHalfFin13Atom2082 chi ∧
      ¬PredecessorHalfFin13Atom0819 chi))) ∨
      ((PredecessorHalfFin13Atom2082 chi ∧
      ¬PredecessorHalfFin13Atom0865 chi) ∨
      ((PredecessorHalfFin13Atom2082 chi ∧
      ¬PredecessorHalfFin13Atom0921 chi) ∨
      (¬PredecessorHalfFin13Atom2082 chi ∧
      PredecessorHalfFin13Atom0808 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0819 chi ∧
      PredecessorHalfFin13Atom0865 chi ∧
      PredecessorHalfFin13Atom0921 chi)))))) ∨
      (((((PredecessorHalfFin13Atom2083 chi ∧
      ¬PredecessorHalfFin13Atom0810 chi) ∨
      ((PredecessorHalfFin13Atom2083 chi ∧
      ¬PredecessorHalfFin13Atom0811 chi) ∨
      (PredecessorHalfFin13Atom2083 chi ∧
      ¬PredecessorHalfFin13Atom0814 chi))) ∨
      ((PredecessorHalfFin13Atom2083 chi ∧
      ¬PredecessorHalfFin13Atom0866 chi) ∨
      ((PredecessorHalfFin13Atom2083 chi ∧
      ¬PredecessorHalfFin13Atom0922 chi) ∨
      (¬PredecessorHalfFin13Atom2083 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0866 chi ∧
      PredecessorHalfFin13Atom0922 chi)))) ∨
      (((PredecessorHalfFin13Atom2084 chi ∧
      ¬PredecessorHalfFin13Atom0810 chi) ∨
      ((PredecessorHalfFin13Atom2084 chi ∧
      ¬PredecessorHalfFin13Atom0812 chi) ∨
      (PredecessorHalfFin13Atom2084 chi ∧
      ¬PredecessorHalfFin13Atom0815 chi))) ∨
      ((PredecessorHalfFin13Atom2084 chi ∧
      ¬PredecessorHalfFin13Atom0867 chi) ∨
      ((PredecessorHalfFin13Atom2084 chi ∧
      ¬PredecessorHalfFin13Atom0923 chi) ∨
      (¬PredecessorHalfFin13Atom2084 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0812 chi ∧
      PredecessorHalfFin13Atom0815 chi ∧
      PredecessorHalfFin13Atom0867 chi ∧
      PredecessorHalfFin13Atom0923 chi))))) ∨
      ((((PredecessorHalfFin13Atom2085 chi ∧
      ¬PredecessorHalfFin13Atom0810 chi) ∨
      ((PredecessorHalfFin13Atom2085 chi ∧
      ¬PredecessorHalfFin13Atom0813 chi) ∨
      (PredecessorHalfFin13Atom2085 chi ∧
      ¬PredecessorHalfFin13Atom0816 chi))) ∨
      ((PredecessorHalfFin13Atom2085 chi ∧
      ¬PredecessorHalfFin13Atom0868 chi) ∨
      ((PredecessorHalfFin13Atom2085 chi ∧
      ¬PredecessorHalfFin13Atom0924 chi) ∨
      (¬PredecessorHalfFin13Atom2085 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0813 chi ∧
      PredecessorHalfFin13Atom0816 chi ∧
      PredecessorHalfFin13Atom0868 chi ∧
      PredecessorHalfFin13Atom0924 chi)))) ∨
      (((PredecessorHalfFin13Atom2086 chi ∧
      ¬PredecessorHalfFin13Atom0811 chi) ∨
      ((PredecessorHalfFin13Atom2086 chi ∧
      ¬PredecessorHalfFin13Atom0812 chi) ∨
      (PredecessorHalfFin13Atom2086 chi ∧
      ¬PredecessorHalfFin13Atom0817 chi))) ∨
      (((PredecessorHalfFin13Atom2086 chi ∧
      ¬PredecessorHalfFin13Atom0869 chi) ∨
      (PredecessorHalfFin13Atom2086 chi ∧
      ¬PredecessorHalfFin13Atom0925 chi)) ∨
      ((¬PredecessorHalfFin13Atom2086 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0812 chi ∧
      PredecessorHalfFin13Atom0817 chi ∧
      PredecessorHalfFin13Atom0869 chi ∧
      PredecessorHalfFin13Atom0925 chi) ∨
      (PredecessorHalfFin13Atom2087 chi ∧
      ¬PredecessorHalfFin13Atom0811 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom2087 chi ∧
      ¬PredecessorHalfFin13Atom0813 chi) ∨
      ((PredecessorHalfFin13Atom2087 chi ∧
      ¬PredecessorHalfFin13Atom0818 chi) ∨
      (PredecessorHalfFin13Atom2087 chi ∧
      ¬PredecessorHalfFin13Atom0870 chi))) ∨
      ((PredecessorHalfFin13Atom2087 chi ∧
      ¬PredecessorHalfFin13Atom0926 chi) ∨
      ((¬PredecessorHalfFin13Atom2087 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0813 chi ∧
      PredecessorHalfFin13Atom0818 chi ∧
      PredecessorHalfFin13Atom0870 chi ∧
      PredecessorHalfFin13Atom0926 chi) ∨
      (PredecessorHalfFin13Atom2088 chi ∧
      ¬PredecessorHalfFin13Atom0812 chi)))) ∨
      (((PredecessorHalfFin13Atom2088 chi ∧
      ¬PredecessorHalfFin13Atom0813 chi) ∨
      ((PredecessorHalfFin13Atom2088 chi ∧
      ¬PredecessorHalfFin13Atom0871 chi) ∨
      (PredecessorHalfFin13Atom2088 chi ∧
      ¬PredecessorHalfFin13Atom0927 chi))) ∨
      ((PredecessorHalfFin13Atom2089 chi ∧
      ¬PredecessorHalfFin13Atom0814 chi) ∨
      ((PredecessorHalfFin13Atom2089 chi ∧
      ¬PredecessorHalfFin13Atom0815 chi) ∨
      (PredecessorHalfFin13Atom2089 chi ∧
      ¬PredecessorHalfFin13Atom0817 chi))))) ∨
      ((((PredecessorHalfFin13Atom2089 chi ∧
      ¬PredecessorHalfFin13Atom0872 chi) ∨
      ((PredecessorHalfFin13Atom2089 chi ∧
      ¬PredecessorHalfFin13Atom0928 chi) ∨
      (¬PredecessorHalfFin13Atom2089 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0815 chi ∧
      PredecessorHalfFin13Atom0817 chi ∧
      PredecessorHalfFin13Atom0872 chi ∧
      PredecessorHalfFin13Atom0928 chi))) ∨
      ((PredecessorHalfFin13Atom2090 chi ∧
      ¬PredecessorHalfFin13Atom0814 chi) ∨
      ((PredecessorHalfFin13Atom2090 chi ∧
      ¬PredecessorHalfFin13Atom0816 chi) ∨
      (PredecessorHalfFin13Atom2090 chi ∧
      ¬PredecessorHalfFin13Atom0818 chi)))) ∨
      (((PredecessorHalfFin13Atom2090 chi ∧
      ¬PredecessorHalfFin13Atom0873 chi) ∨
      ((PredecessorHalfFin13Atom2090 chi ∧
      ¬PredecessorHalfFin13Atom0929 chi) ∨
      (¬PredecessorHalfFin13Atom2090 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0816 chi ∧
      PredecessorHalfFin13Atom0818 chi ∧
      PredecessorHalfFin13Atom0873 chi ∧
      PredecessorHalfFin13Atom0929 chi))) ∨
      ((PredecessorHalfFin13Atom2091 chi ∧
      ¬PredecessorHalfFin13Atom0815 chi) ∨
      ((PredecessorHalfFin13Atom2091 chi ∧
      ¬PredecessorHalfFin13Atom0816 chi) ∨
      (PredecessorHalfFin13Atom2091 chi ∧
      ¬PredecessorHalfFin13Atom0819 chi)))))) ∨
      (((((PredecessorHalfFin13Atom2091 chi ∧
      ¬PredecessorHalfFin13Atom0874 chi) ∨
      ((PredecessorHalfFin13Atom2091 chi ∧
      ¬PredecessorHalfFin13Atom0930 chi) ∨
      (PredecessorHalfFin13Atom2092 chi ∧
      ¬PredecessorHalfFin13Atom0817 chi))) ∨
      ((PredecessorHalfFin13Atom2092 chi ∧
      ¬PredecessorHalfFin13Atom0818 chi) ∨
      ((PredecessorHalfFin13Atom2092 chi ∧
      ¬PredecessorHalfFin13Atom0819 chi) ∨
      (PredecessorHalfFin13Atom2092 chi ∧
      ¬PredecessorHalfFin13Atom0875 chi)))) ∨
      (((PredecessorHalfFin13Atom2092 chi ∧
      ¬PredecessorHalfFin13Atom0931 chi) ∨
      ((PredecessorHalfFin13Atom2093 chi ∧
      ¬PredecessorHalfFin13Atom0820 chi) ∨
      (PredecessorHalfFin13Atom2093 chi ∧
      ¬PredecessorHalfFin13Atom0821 chi))) ∨
      ((PredecessorHalfFin13Atom2093 chi ∧
      ¬PredecessorHalfFin13Atom0826 chi) ∨
      ((PredecessorHalfFin13Atom2093 chi ∧
      ¬PredecessorHalfFin13Atom0841 chi) ∨
      (PredecessorHalfFin13Atom2093 chi ∧
      ¬PredecessorHalfFin13Atom0932 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom2093 chi ∧
      PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0821 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0841 chi ∧
      PredecessorHalfFin13Atom0932 chi) ∨
      ((PredecessorHalfFin13Atom2094 chi ∧
      ¬PredecessorHalfFin13Atom0820 chi) ∨
      (PredecessorHalfFin13Atom2094 chi ∧
      ¬PredecessorHalfFin13Atom0822 chi))) ∨
      ((PredecessorHalfFin13Atom2094 chi ∧
      ¬PredecessorHalfFin13Atom0827 chi) ∨
      ((PredecessorHalfFin13Atom2094 chi ∧
      ¬PredecessorHalfFin13Atom0842 chi) ∨
      (PredecessorHalfFin13Atom2094 chi ∧
      ¬PredecessorHalfFin13Atom0933 chi)))) ∨
      (((¬PredecessorHalfFin13Atom2094 chi ∧
      PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0842 chi ∧
      PredecessorHalfFin13Atom0933 chi) ∨
      ((PredecessorHalfFin13Atom2095 chi ∧
      ¬PredecessorHalfFin13Atom0820 chi) ∨
      (PredecessorHalfFin13Atom2095 chi ∧
      ¬PredecessorHalfFin13Atom0823 chi))) ∨
      (((PredecessorHalfFin13Atom2095 chi ∧
      ¬PredecessorHalfFin13Atom0828 chi) ∨
      (PredecessorHalfFin13Atom2095 chi ∧
      ¬PredecessorHalfFin13Atom0843 chi)) ∨
      ((PredecessorHalfFin13Atom2095 chi ∧
      ¬PredecessorHalfFin13Atom0934 chi) ∨
      (¬PredecessorHalfFin13Atom2095 chi ∧
      PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0843 chi ∧
      PredecessorHalfFin13Atom0934 chi))))))))) := by
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
              exact predecessorHalfFin13_clause23622 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23623 chi hbad
              ·
                exact predecessorHalfFin13_clause23624 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23625 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23626 chi hbad
              ·
                exact predecessorHalfFin13_clause23627 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23628 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23629 chi hbad
              ·
                exact predecessorHalfFin13_clause23630 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23631 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23632 chi hbad
              ·
                exact predecessorHalfFin13_clause23633 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23635 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23636 chi hbad
              ·
                exact predecessorHalfFin13_clause23637 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23638 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23639 chi hbad
              ·
                exact predecessorHalfFin13_clause23640 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23641 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23642 chi hbad
              ·
                exact predecessorHalfFin13_clause23643 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23644 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23645 chi hbad
              ·
                exact predecessorHalfFin13_clause23646 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23647 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23648 chi hbad
              ·
                exact predecessorHalfFin13_clause23649 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23650 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23651 chi hbad
              ·
                exact predecessorHalfFin13_clause23652 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23653 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23654 chi hbad
              ·
                exact predecessorHalfFin13_clause23655 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23656 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23657 chi hbad
              ·
                exact predecessorHalfFin13_clause23658 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23659 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23660 chi hbad
              ·
                exact predecessorHalfFin13_clause23661 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23662 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23663 chi hbad
              ·
                exact predecessorHalfFin13_clause23664 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23665 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23666 chi hbad
              ·
                exact predecessorHalfFin13_clause23667 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23668 chi hbad
              ·
                exact predecessorHalfFin13_clause23669 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23670 chi hbad
              ·
                exact predecessorHalfFin13_clause23671 chi hbad
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
              exact predecessorHalfFin13_clause23672 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23673 chi hbad
              ·
                exact predecessorHalfFin13_clause23674 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23675 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23676 chi hbad
              ·
                exact predecessorHalfFin13_clause23677 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23678 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23680 chi hbad
              ·
                exact predecessorHalfFin13_clause23681 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23683 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23684 chi hbad
              ·
                exact predecessorHalfFin13_clause23685 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23686 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23687 chi hbad
              ·
                exact predecessorHalfFin13_clause23688 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23689 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23690 chi hbad
              ·
                exact predecessorHalfFin13_clause23691 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23692 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23693 chi hbad
              ·
                exact predecessorHalfFin13_clause23694 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23695 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23696 chi hbad
              ·
                exact predecessorHalfFin13_clause23697 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23698 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23699 chi hbad
              ·
                exact predecessorHalfFin13_clause23701 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23702 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23703 chi hbad
              ·
                exact predecessorHalfFin13_clause23704 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23705 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23707 chi hbad
              ·
                exact predecessorHalfFin13_clause23708 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23709 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23710 chi hbad
              ·
                exact predecessorHalfFin13_clause23711 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23712 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23713 chi hbad
              ·
                exact predecessorHalfFin13_clause23714 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23715 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23716 chi hbad
              ·
                exact predecessorHalfFin13_clause23717 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23718 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23719 chi hbad
              ·
                exact predecessorHalfFin13_clause23720 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23721 chi hbad
              ·
                exact predecessorHalfFin13_clause23722 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23723 chi hbad
              ·
                exact predecessorHalfFin13_clause23724 chi hbad

end ErdosSzekeres

end
