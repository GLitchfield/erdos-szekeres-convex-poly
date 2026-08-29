module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk079

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 103. -/

theorem predecessorHalfFin13_rejectSemanticSegment103
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom2024 chi ∧
      ¬PredecessorHalfFin13Atom0784 chi) ∨
      ((PredecessorHalfFin13Atom2024 chi ∧
      ¬PredecessorHalfFin13Atom0989 chi) ∨
      (¬PredecessorHalfFin13Atom2024 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0989 chi))) ∨
      ((PredecessorHalfFin13Atom2025 chi ∧
      ¬PredecessorHalfFin13Atom0773 chi) ∨
      ((PredecessorHalfFin13Atom2025 chi ∧
      ¬PredecessorHalfFin13Atom0774 chi) ∨
      (PredecessorHalfFin13Atom2025 chi ∧
      ¬PredecessorHalfFin13Atom0779 chi)))) ∨
      (((PredecessorHalfFin13Atom2025 chi ∧
      ¬PredecessorHalfFin13Atom0785 chi) ∨
      ((PredecessorHalfFin13Atom2025 chi ∧
      ¬PredecessorHalfFin13Atom0990 chi) ∨
      (PredecessorHalfFin13Atom2026 chi ∧
      ¬PredecessorHalfFin13Atom0773 chi))) ∨
      ((PredecessorHalfFin13Atom2026 chi ∧
      ¬PredecessorHalfFin13Atom0775 chi) ∨
      ((PredecessorHalfFin13Atom2026 chi ∧
      ¬PredecessorHalfFin13Atom0780 chi) ∨
      (PredecessorHalfFin13Atom2026 chi ∧
      ¬PredecessorHalfFin13Atom0786 chi))))) ∨
      ((((PredecessorHalfFin13Atom2026 chi ∧
      ¬PredecessorHalfFin13Atom0991 chi) ∨
      ((¬PredecessorHalfFin13Atom2026 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0991 chi) ∨
      (PredecessorHalfFin13Atom2027 chi ∧
      ¬PredecessorHalfFin13Atom0775 chi))) ∨
      ((PredecessorHalfFin13Atom2027 chi ∧
      ¬PredecessorHalfFin13Atom0787 chi) ∨
      ((PredecessorHalfFin13Atom2027 chi ∧
      ¬PredecessorHalfFin13Atom0992 chi) ∨
      (PredecessorHalfFin13Atom2028 chi ∧
      ¬PredecessorHalfFin13Atom0776 chi)))) ∨
      (((PredecessorHalfFin13Atom2028 chi ∧
      ¬PredecessorHalfFin13Atom0788 chi) ∨
      ((PredecessorHalfFin13Atom2028 chi ∧
      ¬PredecessorHalfFin13Atom0993 chi) ∨
      (PredecessorHalfFin13Atom2029 chi ∧
      ¬PredecessorHalfFin13Atom0776 chi))) ∨
      ((PredecessorHalfFin13Atom2029 chi ∧
      ¬PredecessorHalfFin13Atom0778 chi) ∨
      ((PredecessorHalfFin13Atom2029 chi ∧
      ¬PredecessorHalfFin13Atom0780 chi) ∨
      (PredecessorHalfFin13Atom2029 chi ∧
      ¬PredecessorHalfFin13Atom0789 chi)))))) ∨
      (((((PredecessorHalfFin13Atom2029 chi ∧
      ¬PredecessorHalfFin13Atom0994 chi) ∨
      ((¬PredecessorHalfFin13Atom2029 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0994 chi) ∨
      (PredecessorHalfFin13Atom2030 chi ∧
      ¬PredecessorHalfFin13Atom0778 chi))) ∨
      ((PredecessorHalfFin13Atom2030 chi ∧
      ¬PredecessorHalfFin13Atom0790 chi) ∨
      ((PredecessorHalfFin13Atom2030 chi ∧
      ¬PredecessorHalfFin13Atom0995 chi) ∨
      (PredecessorHalfFin13Atom2031 chi ∧
      ¬PredecessorHalfFin13Atom0780 chi)))) ∨
      (((PredecessorHalfFin13Atom2031 chi ∧
      ¬PredecessorHalfFin13Atom0781 chi) ∨
      ((PredecessorHalfFin13Atom2031 chi ∧
      ¬PredecessorHalfFin13Atom0791 chi) ∨
      (PredecessorHalfFin13Atom2031 chi ∧
      ¬PredecessorHalfFin13Atom0996 chi))) ∨
      ((PredecessorHalfFin13Atom2032 chi ∧
      ¬PredecessorHalfFin13Atom0782 chi) ∨
      ((PredecessorHalfFin13Atom2032 chi ∧
      ¬PredecessorHalfFin13Atom0783 chi) ∨
      (PredecessorHalfFin13Atom2032 chi ∧
      ¬PredecessorHalfFin13Atom0785 chi))))) ∨
      ((((PredecessorHalfFin13Atom2032 chi ∧
      ¬PredecessorHalfFin13Atom0788 chi) ∨
      ((PredecessorHalfFin13Atom2032 chi ∧
      ¬PredecessorHalfFin13Atom0997 chi) ∨
      (PredecessorHalfFin13Atom2033 chi ∧
      ¬PredecessorHalfFin13Atom0782 chi))) ∨
      ((PredecessorHalfFin13Atom2033 chi ∧
      ¬PredecessorHalfFin13Atom0784 chi) ∨
      ((PredecessorHalfFin13Atom2033 chi ∧
      ¬PredecessorHalfFin13Atom0786 chi) ∨
      (PredecessorHalfFin13Atom2033 chi ∧
      ¬PredecessorHalfFin13Atom0789 chi)))) ∨
      (((PredecessorHalfFin13Atom2033 chi ∧
      ¬PredecessorHalfFin13Atom0998 chi) ∨
      ((¬PredecessorHalfFin13Atom2033 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0998 chi) ∨
      (PredecessorHalfFin13Atom2034 chi ∧
      ¬PredecessorHalfFin13Atom0790 chi))) ∨
      (((PredecessorHalfFin13Atom2034 chi ∧
      ¬PredecessorHalfFin13Atom0999 chi) ∨
      (PredecessorHalfFin13Atom2035 chi ∧
      ¬PredecessorHalfFin13Atom0785 chi)) ∨
      ((PredecessorHalfFin13Atom2035 chi ∧
      ¬PredecessorHalfFin13Atom0786 chi) ∨
      (PredecessorHalfFin13Atom2035 chi ∧
      ¬PredecessorHalfFin13Atom0791 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom2035 chi ∧
      ¬PredecessorHalfFin13Atom1000 chi) ∨
      ((PredecessorHalfFin13Atom2036 chi ∧
      ¬PredecessorHalfFin13Atom0789 chi) ∨
      (PredecessorHalfFin13Atom2036 chi ∧
      ¬PredecessorHalfFin13Atom0790 chi))) ∨
      ((PredecessorHalfFin13Atom2036 chi ∧
      ¬PredecessorHalfFin13Atom0791 chi) ∨
      ((PredecessorHalfFin13Atom2036 chi ∧
      ¬PredecessorHalfFin13Atom1001 chi) ∨
      (PredecessorHalfFin13Atom2037 chi ∧
      ¬PredecessorHalfFin13Atom0792 chi)))) ∨
      (((PredecessorHalfFin13Atom2037 chi ∧
      ¬PredecessorHalfFin13Atom0793 chi) ∨
      ((PredecessorHalfFin13Atom2037 chi ∧
      ¬PredecessorHalfFin13Atom0799 chi) ∨
      (PredecessorHalfFin13Atom2037 chi ∧
      ¬PredecessorHalfFin13Atom0820 chi))) ∨
      ((PredecessorHalfFin13Atom2037 chi ∧
      ¬PredecessorHalfFin13Atom0876 chi) ∨
      ((¬PredecessorHalfFin13Atom2037 chi ∧
      PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0799 chi ∧
      PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0876 chi) ∨
      (PredecessorHalfFin13Atom2038 chi ∧
      ¬PredecessorHalfFin13Atom0792 chi))))) ∨
      ((((PredecessorHalfFin13Atom2038 chi ∧
      ¬PredecessorHalfFin13Atom0794 chi) ∨
      ((PredecessorHalfFin13Atom2038 chi ∧
      ¬PredecessorHalfFin13Atom0800 chi) ∨
      (PredecessorHalfFin13Atom2038 chi ∧
      ¬PredecessorHalfFin13Atom0821 chi))) ∨
      ((PredecessorHalfFin13Atom2038 chi ∧
      ¬PredecessorHalfFin13Atom0877 chi) ∨
      ((¬PredecessorHalfFin13Atom2038 chi ∧
      PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0821 chi ∧
      PredecessorHalfFin13Atom0877 chi) ∨
      (PredecessorHalfFin13Atom2039 chi ∧
      ¬PredecessorHalfFin13Atom0792 chi)))) ∨
      (((PredecessorHalfFin13Atom2039 chi ∧
      ¬PredecessorHalfFin13Atom0795 chi) ∨
      ((PredecessorHalfFin13Atom2039 chi ∧
      ¬PredecessorHalfFin13Atom0801 chi) ∨
      (PredecessorHalfFin13Atom2039 chi ∧
      ¬PredecessorHalfFin13Atom0822 chi))) ∨
      (((PredecessorHalfFin13Atom2039 chi ∧
      ¬PredecessorHalfFin13Atom0878 chi) ∨
      (¬PredecessorHalfFin13Atom2039 chi ∧
      PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0878 chi)) ∨
      ((PredecessorHalfFin13Atom2040 chi ∧
      ¬PredecessorHalfFin13Atom0792 chi) ∨
      (PredecessorHalfFin13Atom2040 chi ∧
      ¬PredecessorHalfFin13Atom0796 chi)))))) ∨
      (((((PredecessorHalfFin13Atom2040 chi ∧
      ¬PredecessorHalfFin13Atom0802 chi) ∨
      ((PredecessorHalfFin13Atom2040 chi ∧
      ¬PredecessorHalfFin13Atom0823 chi) ∨
      (PredecessorHalfFin13Atom2040 chi ∧
      ¬PredecessorHalfFin13Atom0879 chi))) ∨
      ((¬PredecessorHalfFin13Atom2040 chi ∧
      PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0879 chi) ∨
      ((PredecessorHalfFin13Atom2041 chi ∧
      ¬PredecessorHalfFin13Atom0792 chi) ∨
      (PredecessorHalfFin13Atom2041 chi ∧
      ¬PredecessorHalfFin13Atom0803 chi)))) ∨
      (((PredecessorHalfFin13Atom2041 chi ∧
      ¬PredecessorHalfFin13Atom0824 chi) ∨
      ((PredecessorHalfFin13Atom2041 chi ∧
      ¬PredecessorHalfFin13Atom0880 chi) ∨
      (¬PredecessorHalfFin13Atom2041 chi ∧
      PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0797 chi ∧
      PredecessorHalfFin13Atom0803 chi ∧
      PredecessorHalfFin13Atom0824 chi ∧
      PredecessorHalfFin13Atom0880 chi))) ∨
      ((PredecessorHalfFin13Atom2042 chi ∧
      ¬PredecessorHalfFin13Atom0792 chi) ∨
      ((PredecessorHalfFin13Atom2042 chi ∧
      ¬PredecessorHalfFin13Atom0798 chi) ∨
      (PredecessorHalfFin13Atom2042 chi ∧
      ¬PredecessorHalfFin13Atom0804 chi))))) ∨
      ((((PredecessorHalfFin13Atom2042 chi ∧
      ¬PredecessorHalfFin13Atom0825 chi) ∨
      ((PredecessorHalfFin13Atom2042 chi ∧
      ¬PredecessorHalfFin13Atom0881 chi) ∨
      (¬PredecessorHalfFin13Atom2042 chi ∧
      PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0804 chi ∧
      PredecessorHalfFin13Atom0825 chi ∧
      PredecessorHalfFin13Atom0881 chi))) ∨
      ((PredecessorHalfFin13Atom2043 chi ∧
      ¬PredecessorHalfFin13Atom0793 chi) ∨
      ((PredecessorHalfFin13Atom2043 chi ∧
      ¬PredecessorHalfFin13Atom0794 chi) ∨
      (PredecessorHalfFin13Atom2043 chi ∧
      ¬PredecessorHalfFin13Atom0805 chi)))) ∨
      (((PredecessorHalfFin13Atom2043 chi ∧
      ¬PredecessorHalfFin13Atom0826 chi) ∨
      ((PredecessorHalfFin13Atom2043 chi ∧
      ¬PredecessorHalfFin13Atom0882 chi) ∨
      (¬PredecessorHalfFin13Atom2043 chi ∧
      PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0882 chi))) ∨
      (((PredecessorHalfFin13Atom2044 chi ∧
      ¬PredecessorHalfFin13Atom0793 chi) ∨
      (PredecessorHalfFin13Atom2044 chi ∧
      ¬PredecessorHalfFin13Atom0795 chi)) ∨
      ((PredecessorHalfFin13Atom2044 chi ∧
      ¬PredecessorHalfFin13Atom0806 chi) ∨
      (PredecessorHalfFin13Atom2044 chi ∧
      ¬PredecessorHalfFin13Atom0827 chi))))))))) := by
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
              exact predecessorHalfFin13_clause23296 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23297 chi hbad
              ·
                exact predecessorHalfFin13_clause23298 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23299 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23300 chi hbad
              ·
                exact predecessorHalfFin13_clause23301 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23302 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23303 chi hbad
              ·
                exact predecessorHalfFin13_clause23305 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23306 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23307 chi hbad
              ·
                exact predecessorHalfFin13_clause23308 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23309 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23310 chi hbad
              ·
                exact predecessorHalfFin13_clause23312 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23314 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23315 chi hbad
              ·
                exact predecessorHalfFin13_clause23317 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23320 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23321 chi hbad
              ·
                exact predecessorHalfFin13_clause23323 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23324 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23325 chi hbad
              ·
                exact predecessorHalfFin13_clause23326 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23327 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23328 chi hbad
              ·
                exact predecessorHalfFin13_clause23330 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23332 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23333 chi hbad
              ·
                exact predecessorHalfFin13_clause23336 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23337 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23338 chi hbad
              ·
                exact predecessorHalfFin13_clause23339 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23341 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23342 chi hbad
              ·
                exact predecessorHalfFin13_clause23343 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23344 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23345 chi hbad
              ·
                exact predecessorHalfFin13_clause23347 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23348 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23349 chi hbad
              ·
                exact predecessorHalfFin13_clause23350 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23351 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23352 chi hbad
              ·
                exact predecessorHalfFin13_clause23356 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23357 chi hbad
              ·
                exact predecessorHalfFin13_clause23359 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23360 chi hbad
              ·
                exact predecessorHalfFin13_clause23362 chi hbad
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
              exact predecessorHalfFin13_clause23363 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23366 chi hbad
              ·
                exact predecessorHalfFin13_clause23367 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23368 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23369 chi hbad
              ·
                exact predecessorHalfFin13_clause23371 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23372 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23373 chi hbad
              ·
                exact predecessorHalfFin13_clause23374 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23375 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23376 chi hbad
              ·
                exact predecessorHalfFin13_clause23377 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23378 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23379 chi hbad
              ·
                exact predecessorHalfFin13_clause23380 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23381 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23382 chi hbad
              ·
                exact predecessorHalfFin13_clause23383 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23384 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23385 chi hbad
              ·
                exact predecessorHalfFin13_clause23386 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23387 chi hbad
              ·
                exact predecessorHalfFin13_clause23388 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23389 chi hbad
              ·
                exact predecessorHalfFin13_clause23390 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23391 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23392 chi hbad
              ·
                exact predecessorHalfFin13_clause23393 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23394 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23395 chi hbad
              ·
                exact predecessorHalfFin13_clause23397 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23398 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23399 chi hbad
              ·
                exact predecessorHalfFin13_clause23400 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23401 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23402 chi hbad
              ·
                exact predecessorHalfFin13_clause23403 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23404 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23405 chi hbad
              ·
                exact predecessorHalfFin13_clause23406 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23407 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23408 chi hbad
              ·
                exact predecessorHalfFin13_clause23409 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause23410 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23411 chi hbad
              ·
                exact predecessorHalfFin13_clause23412 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23413 chi hbad
              ·
                exact predecessorHalfFin13_clause23414 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause23415 chi hbad
              ·
                exact predecessorHalfFin13_clause23416 chi hbad

end ErdosSzekeres

end
