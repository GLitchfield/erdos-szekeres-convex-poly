module

public import ErdosSzekeres.Fin15AnchoredClauseChunk130
public import ErdosSzekeres.Fin15AnchoredClauseChunk131
public import ErdosSzekeres.Fin15AnchoredClauseChunk132

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 066. -/

theorem fin15Anchored_rejectSemanticSegment066
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom2065 chi ∧
      ¬Fin15AnchoredAtom0778 chi) ∨
      ((Fin15AnchoredAtom2065 chi ∧
      ¬Fin15AnchoredAtom1064 chi) ∨
      (¬Fin15AnchoredAtom2065 chi ∧
      Fin15AnchoredAtom0508 chi ∧
      Fin15AnchoredAtom0512 chi ∧
      Fin15AnchoredAtom0527 chi ∧
      Fin15AnchoredAtom0778 chi ∧
      Fin15AnchoredAtom1064 chi))) ∨
      (((Fin15AnchoredAtom2066 chi ∧
      ¬Fin15AnchoredAtom0510 chi) ∨
      (Fin15AnchoredAtom2066 chi ∧
      ¬Fin15AnchoredAtom0528 chi)) ∨
      ((Fin15AnchoredAtom2066 chi ∧
      ¬Fin15AnchoredAtom0779 chi) ∨
      (¬Fin15AnchoredAtom2066 chi ∧
      Fin15AnchoredAtom0509 chi ∧
      Fin15AnchoredAtom0510 chi ∧
      Fin15AnchoredAtom0528 chi ∧
      Fin15AnchoredAtom0779 chi ∧
      Fin15AnchoredAtom1065 chi)))) ∨
      ((((Fin15AnchoredAtom2067 chi ∧
      ¬Fin15AnchoredAtom0511 chi) ∨
      (Fin15AnchoredAtom2067 chi ∧
      ¬Fin15AnchoredAtom0529 chi)) ∨
      ((Fin15AnchoredAtom2067 chi ∧
      ¬Fin15AnchoredAtom0780 chi) ∨
      (Fin15AnchoredAtom2068 chi ∧
      ¬Fin15AnchoredAtom0509 chi))) ∨
      (((Fin15AnchoredAtom2068 chi ∧
      ¬Fin15AnchoredAtom0512 chi) ∨
      (¬Fin15AnchoredAtom2068 chi ∧
      Fin15AnchoredAtom0509 chi ∧
      Fin15AnchoredAtom0512 chi ∧
      Fin15AnchoredAtom0530 chi ∧
      Fin15AnchoredAtom0781 chi ∧
      Fin15AnchoredAtom1067 chi)) ∨
      ((Fin15AnchoredAtom2069 chi ∧
      ¬Fin15AnchoredAtom0510 chi) ∨
      (Fin15AnchoredAtom2069 chi ∧
      ¬Fin15AnchoredAtom0511 chi))))) ∨
      (((((Fin15AnchoredAtom2069 chi ∧
      ¬Fin15AnchoredAtom0531 chi) ∨
      (Fin15AnchoredAtom2069 chi ∧
      ¬Fin15AnchoredAtom0782 chi)) ∨
      ((Fin15AnchoredAtom2069 chi ∧
      ¬Fin15AnchoredAtom1068 chi) ∨
      (¬Fin15AnchoredAtom2069 chi ∧
      Fin15AnchoredAtom0510 chi ∧
      Fin15AnchoredAtom0511 chi ∧
      Fin15AnchoredAtom0531 chi ∧
      Fin15AnchoredAtom0782 chi ∧
      Fin15AnchoredAtom1068 chi))) ∨
      (((Fin15AnchoredAtom2070 chi ∧
      ¬Fin15AnchoredAtom0510 chi) ∨
      (Fin15AnchoredAtom2070 chi ∧
      ¬Fin15AnchoredAtom0512 chi)) ∨
      ((Fin15AnchoredAtom2070 chi ∧
      ¬Fin15AnchoredAtom0532 chi) ∨
      (Fin15AnchoredAtom2070 chi ∧
      ¬Fin15AnchoredAtom0783 chi)))) ∨
      ((((Fin15AnchoredAtom2070 chi ∧
      ¬Fin15AnchoredAtom1069 chi) ∨
      (¬Fin15AnchoredAtom2070 chi ∧
      Fin15AnchoredAtom0510 chi ∧
      Fin15AnchoredAtom0512 chi ∧
      Fin15AnchoredAtom0532 chi ∧
      Fin15AnchoredAtom0783 chi ∧
      Fin15AnchoredAtom1069 chi)) ∨
      ((Fin15AnchoredAtom2071 chi ∧
      ¬Fin15AnchoredAtom0511 chi) ∨
      (Fin15AnchoredAtom2071 chi ∧
      ¬Fin15AnchoredAtom0512 chi))) ∨
      (((Fin15AnchoredAtom2071 chi ∧
      ¬Fin15AnchoredAtom0533 chi) ∨
      (Fin15AnchoredAtom2071 chi ∧
      ¬Fin15AnchoredAtom0784 chi)) ∨
      ((Fin15AnchoredAtom2071 chi ∧
      ¬Fin15AnchoredAtom1070 chi) ∨
      (¬Fin15AnchoredAtom2071 chi ∧
      Fin15AnchoredAtom0511 chi ∧
      Fin15AnchoredAtom0512 chi ∧
      Fin15AnchoredAtom0533 chi ∧
      Fin15AnchoredAtom0784 chi ∧
      Fin15AnchoredAtom1070 chi)))))) ∨
      ((((((Fin15AnchoredAtom2072 chi ∧
      ¬Fin15AnchoredAtom0513 chi) ∨
      (Fin15AnchoredAtom2072 chi ∧
      ¬Fin15AnchoredAtom0514 chi)) ∨
      ((Fin15AnchoredAtom2072 chi ∧
      ¬Fin15AnchoredAtom0519 chi) ∨
      (Fin15AnchoredAtom2072 chi ∧
      ¬Fin15AnchoredAtom0785 chi))) ∨
      (((Fin15AnchoredAtom2072 chi ∧
      ¬Fin15AnchoredAtom1071 chi) ∨
      (¬Fin15AnchoredAtom2072 chi ∧
      Fin15AnchoredAtom0513 chi ∧
      Fin15AnchoredAtom0514 chi ∧
      Fin15AnchoredAtom0519 chi ∧
      Fin15AnchoredAtom0785 chi ∧
      Fin15AnchoredAtom1071 chi)) ∨
      ((Fin15AnchoredAtom2074 chi ∧
      ¬Fin15AnchoredAtom0513 chi) ∨
      (Fin15AnchoredAtom2074 chi ∧
      ¬Fin15AnchoredAtom0516 chi)))) ∨
      ((((Fin15AnchoredAtom2074 chi ∧
      ¬Fin15AnchoredAtom0521 chi) ∨
      (Fin15AnchoredAtom2074 chi ∧
      ¬Fin15AnchoredAtom0787 chi)) ∨
      ((Fin15AnchoredAtom2074 chi ∧
      ¬Fin15AnchoredAtom1073 chi) ∨
      (¬Fin15AnchoredAtom2074 chi ∧
      Fin15AnchoredAtom0513 chi ∧
      Fin15AnchoredAtom0516 chi ∧
      Fin15AnchoredAtom0521 chi ∧
      Fin15AnchoredAtom0787 chi ∧
      Fin15AnchoredAtom1073 chi))) ∨
      (((Fin15AnchoredAtom2075 chi ∧
      ¬Fin15AnchoredAtom0513 chi) ∨
      (Fin15AnchoredAtom2075 chi ∧
      ¬Fin15AnchoredAtom0522 chi)) ∨
      ((Fin15AnchoredAtom2075 chi ∧
      ¬Fin15AnchoredAtom0788 chi) ∨
      (Fin15AnchoredAtom2075 chi ∧
      ¬Fin15AnchoredAtom1074 chi))))) ∨
      (((((¬Fin15AnchoredAtom2075 chi ∧
      Fin15AnchoredAtom0513 chi ∧
      Fin15AnchoredAtom0517 chi ∧
      Fin15AnchoredAtom0522 chi ∧
      Fin15AnchoredAtom0788 chi ∧
      Fin15AnchoredAtom1074 chi) ∨
      (Fin15AnchoredAtom2076 chi ∧
      ¬Fin15AnchoredAtom0513 chi)) ∨
      ((Fin15AnchoredAtom2076 chi ∧
      ¬Fin15AnchoredAtom0518 chi) ∨
      (Fin15AnchoredAtom2076 chi ∧
      ¬Fin15AnchoredAtom0523 chi))) ∨
      (((Fin15AnchoredAtom2076 chi ∧
      ¬Fin15AnchoredAtom0789 chi) ∨
      (¬Fin15AnchoredAtom2076 chi ∧
      Fin15AnchoredAtom0513 chi ∧
      Fin15AnchoredAtom0518 chi ∧
      Fin15AnchoredAtom0523 chi ∧
      Fin15AnchoredAtom0789 chi ∧
      Fin15AnchoredAtom1075 chi)) ∨
      ((Fin15AnchoredAtom2078 chi ∧
      ¬Fin15AnchoredAtom0514 chi) ∨
      (Fin15AnchoredAtom2078 chi ∧
      ¬Fin15AnchoredAtom0516 chi)))) ∨
      ((((Fin15AnchoredAtom2078 chi ∧
      ¬Fin15AnchoredAtom0525 chi) ∨
      (Fin15AnchoredAtom2078 chi ∧
      ¬Fin15AnchoredAtom0791 chi)) ∨
      ((Fin15AnchoredAtom2078 chi ∧
      ¬Fin15AnchoredAtom1077 chi) ∨
      (¬Fin15AnchoredAtom2078 chi ∧
      Fin15AnchoredAtom0514 chi ∧
      Fin15AnchoredAtom0516 chi ∧
      Fin15AnchoredAtom0525 chi ∧
      Fin15AnchoredAtom0791 chi ∧
      Fin15AnchoredAtom1077 chi))) ∨
      (((Fin15AnchoredAtom2079 chi ∧
      ¬Fin15AnchoredAtom0514 chi) ∨
      (Fin15AnchoredAtom2079 chi ∧
      ¬Fin15AnchoredAtom0517 chi)) ∨
      ((Fin15AnchoredAtom2079 chi ∧
      ¬Fin15AnchoredAtom0526 chi) ∨
      (Fin15AnchoredAtom2079 chi ∧
      ¬Fin15AnchoredAtom0792 chi))))))) ∨
      ((((((Fin15AnchoredAtom2079 chi ∧
      ¬Fin15AnchoredAtom1078 chi) ∨
      ((¬Fin15AnchoredAtom2079 chi ∧
      Fin15AnchoredAtom0514 chi ∧
      Fin15AnchoredAtom0517 chi ∧
      Fin15AnchoredAtom0526 chi ∧
      Fin15AnchoredAtom0792 chi ∧
      Fin15AnchoredAtom1078 chi) ∨
      (Fin15AnchoredAtom2080 chi ∧
      ¬Fin15AnchoredAtom0514 chi))) ∨
      (((Fin15AnchoredAtom2080 chi ∧
      ¬Fin15AnchoredAtom0527 chi) ∨
      (Fin15AnchoredAtom2080 chi ∧
      ¬Fin15AnchoredAtom0793 chi)) ∨
      ((¬Fin15AnchoredAtom2080 chi ∧
      Fin15AnchoredAtom0514 chi ∧
      Fin15AnchoredAtom0518 chi ∧
      Fin15AnchoredAtom0527 chi ∧
      Fin15AnchoredAtom0793 chi ∧
      Fin15AnchoredAtom1079 chi) ∨
      (Fin15AnchoredAtom2084 chi ∧
      ¬Fin15AnchoredAtom0516 chi)))) ∨
      ((((Fin15AnchoredAtom2084 chi ∧
      ¬Fin15AnchoredAtom0517 chi) ∨
      (Fin15AnchoredAtom2084 chi ∧
      ¬Fin15AnchoredAtom0797 chi)) ∨
      ((Fin15AnchoredAtom2084 chi ∧
      ¬Fin15AnchoredAtom1083 chi) ∨
      (¬Fin15AnchoredAtom2084 chi ∧
      Fin15AnchoredAtom0516 chi ∧
      Fin15AnchoredAtom0517 chi ∧
      Fin15AnchoredAtom0531 chi ∧
      Fin15AnchoredAtom0797 chi ∧
      Fin15AnchoredAtom1083 chi))) ∨
      (((Fin15AnchoredAtom2085 chi ∧
      ¬Fin15AnchoredAtom0516 chi) ∨
      (Fin15AnchoredAtom2085 chi ∧
      ¬Fin15AnchoredAtom0518 chi)) ∨
      ((Fin15AnchoredAtom2085 chi ∧
      ¬Fin15AnchoredAtom0532 chi) ∨
      (Fin15AnchoredAtom2085 chi ∧
      ¬Fin15AnchoredAtom0798 chi))))) ∨
      (((((¬Fin15AnchoredAtom2085 chi ∧
      Fin15AnchoredAtom0516 chi ∧
      Fin15AnchoredAtom0518 chi ∧
      Fin15AnchoredAtom0532 chi ∧
      Fin15AnchoredAtom0798 chi ∧
      Fin15AnchoredAtom1084 chi) ∨
      (Fin15AnchoredAtom2086 chi ∧
      ¬Fin15AnchoredAtom0517 chi)) ∨
      ((Fin15AnchoredAtom2086 chi ∧
      ¬Fin15AnchoredAtom0518 chi) ∨
      (Fin15AnchoredAtom2086 chi ∧
      ¬Fin15AnchoredAtom0533 chi))) ∨
      (((Fin15AnchoredAtom2086 chi ∧
      ¬Fin15AnchoredAtom0799 chi) ∨
      (Fin15AnchoredAtom2086 chi ∧
      ¬Fin15AnchoredAtom1085 chi)) ∨
      ((¬Fin15AnchoredAtom2086 chi ∧
      Fin15AnchoredAtom0517 chi ∧
      Fin15AnchoredAtom0518 chi ∧
      Fin15AnchoredAtom0533 chi ∧
      Fin15AnchoredAtom0799 chi ∧
      Fin15AnchoredAtom1085 chi) ∨
      (Fin15AnchoredAtom2087 chi ∧
      ¬Fin15AnchoredAtom0519 chi)))) ∨
      ((((Fin15AnchoredAtom2087 chi ∧
      ¬Fin15AnchoredAtom0800 chi) ∨
      (Fin15AnchoredAtom2088 chi ∧
      ¬Fin15AnchoredAtom0519 chi)) ∨
      ((Fin15AnchoredAtom2088 chi ∧
      ¬Fin15AnchoredAtom0521 chi) ∨
      (Fin15AnchoredAtom2088 chi ∧
      ¬Fin15AnchoredAtom0525 chi))) ∨
      (((Fin15AnchoredAtom2088 chi ∧
      ¬Fin15AnchoredAtom0801 chi) ∨
      (Fin15AnchoredAtom2088 chi ∧
      ¬Fin15AnchoredAtom1087 chi)) ∨
      ((¬Fin15AnchoredAtom2088 chi ∧
      Fin15AnchoredAtom0519 chi ∧
      Fin15AnchoredAtom0521 chi ∧
      Fin15AnchoredAtom0525 chi ∧
      Fin15AnchoredAtom0801 chi ∧
      Fin15AnchoredAtom1087 chi) ∨
      (Fin15AnchoredAtom2089 chi ∧
      ¬Fin15AnchoredAtom0519 chi)))))) ∨
      ((((((Fin15AnchoredAtom2089 chi ∧
      ¬Fin15AnchoredAtom0522 chi) ∨
      (Fin15AnchoredAtom2089 chi ∧
      ¬Fin15AnchoredAtom0526 chi)) ∨
      ((Fin15AnchoredAtom2089 chi ∧
      ¬Fin15AnchoredAtom0802 chi) ∨
      (Fin15AnchoredAtom2089 chi ∧
      ¬Fin15AnchoredAtom1088 chi))) ∨
      (((¬Fin15AnchoredAtom2089 chi ∧
      Fin15AnchoredAtom0519 chi ∧
      Fin15AnchoredAtom0522 chi ∧
      Fin15AnchoredAtom0526 chi ∧
      Fin15AnchoredAtom0802 chi ∧
      Fin15AnchoredAtom1088 chi) ∨
      (Fin15AnchoredAtom2090 chi ∧
      ¬Fin15AnchoredAtom0519 chi)) ∨
      ((Fin15AnchoredAtom2090 chi ∧
      ¬Fin15AnchoredAtom0523 chi) ∨
      (Fin15AnchoredAtom2090 chi ∧
      ¬Fin15AnchoredAtom0527 chi)))) ∨
      ((((Fin15AnchoredAtom2090 chi ∧
      ¬Fin15AnchoredAtom0803 chi) ∨
      (Fin15AnchoredAtom2090 chi ∧
      ¬Fin15AnchoredAtom1089 chi)) ∨
      ((¬Fin15AnchoredAtom2090 chi ∧
      Fin15AnchoredAtom0519 chi ∧
      Fin15AnchoredAtom0523 chi ∧
      Fin15AnchoredAtom0527 chi ∧
      Fin15AnchoredAtom0803 chi ∧
      Fin15AnchoredAtom1089 chi) ∨
      (Fin15AnchoredAtom2091 chi ∧
      ¬Fin15AnchoredAtom0520 chi))) ∨
      (((Fin15AnchoredAtom2091 chi ∧
      ¬Fin15AnchoredAtom0521 chi) ∨
      (Fin15AnchoredAtom2091 chi ∧
      ¬Fin15AnchoredAtom0528 chi)) ∨
      ((Fin15AnchoredAtom2091 chi ∧
      ¬Fin15AnchoredAtom0804 chi) ∨
      (Fin15AnchoredAtom2091 chi ∧
      ¬Fin15AnchoredAtom1090 chi))))) ∨
      (((((¬Fin15AnchoredAtom2091 chi ∧
      Fin15AnchoredAtom0520 chi ∧
      Fin15AnchoredAtom0521 chi ∧
      Fin15AnchoredAtom0528 chi ∧
      Fin15AnchoredAtom0804 chi ∧
      Fin15AnchoredAtom1090 chi) ∨
      (Fin15AnchoredAtom2092 chi ∧
      ¬Fin15AnchoredAtom0520 chi)) ∨
      ((Fin15AnchoredAtom2092 chi ∧
      ¬Fin15AnchoredAtom0529 chi) ∨
      (Fin15AnchoredAtom2092 chi ∧
      ¬Fin15AnchoredAtom0805 chi))) ∨
      (((Fin15AnchoredAtom2092 chi ∧
      ¬Fin15AnchoredAtom1091 chi) ∨
      (¬Fin15AnchoredAtom2092 chi ∧
      Fin15AnchoredAtom0520 chi ∧
      Fin15AnchoredAtom0522 chi ∧
      Fin15AnchoredAtom0529 chi ∧
      Fin15AnchoredAtom0805 chi ∧
      Fin15AnchoredAtom1091 chi)) ∨
      ((Fin15AnchoredAtom2093 chi ∧
      ¬Fin15AnchoredAtom0520 chi) ∨
      (Fin15AnchoredAtom2093 chi ∧
      ¬Fin15AnchoredAtom0523 chi)))) ∨
      ((((Fin15AnchoredAtom2093 chi ∧
      ¬Fin15AnchoredAtom0806 chi) ∨
      (Fin15AnchoredAtom2094 chi ∧
      ¬Fin15AnchoredAtom0521 chi)) ∨
      ((Fin15AnchoredAtom2094 chi ∧
      ¬Fin15AnchoredAtom0522 chi) ∨
      (Fin15AnchoredAtom2094 chi ∧
      ¬Fin15AnchoredAtom0531 chi))) ∨
      (((Fin15AnchoredAtom2094 chi ∧
      ¬Fin15AnchoredAtom0807 chi) ∨
      (Fin15AnchoredAtom2094 chi ∧
      ¬Fin15AnchoredAtom1093 chi)) ∨
      ((¬Fin15AnchoredAtom2094 chi ∧
      Fin15AnchoredAtom0521 chi ∧
      Fin15AnchoredAtom0522 chi ∧
      Fin15AnchoredAtom0531 chi ∧
      Fin15AnchoredAtom0807 chi ∧
      Fin15AnchoredAtom1093 chi) ∨
      (Fin15AnchoredAtom2095 chi ∧
      ¬Fin15AnchoredAtom0521 chi)))))))) ∨
      (((((((Fin15AnchoredAtom2095 chi ∧
      ¬Fin15AnchoredAtom0523 chi) ∨
      ((Fin15AnchoredAtom2095 chi ∧
      ¬Fin15AnchoredAtom0532 chi) ∨
      (Fin15AnchoredAtom2095 chi ∧
      ¬Fin15AnchoredAtom0808 chi))) ∨
      (((Fin15AnchoredAtom2095 chi ∧
      ¬Fin15AnchoredAtom1094 chi) ∨
      (¬Fin15AnchoredAtom2095 chi ∧
      Fin15AnchoredAtom0521 chi ∧
      Fin15AnchoredAtom0523 chi ∧
      Fin15AnchoredAtom0532 chi ∧
      Fin15AnchoredAtom0808 chi ∧
      Fin15AnchoredAtom1094 chi)) ∨
      ((Fin15AnchoredAtom2096 chi ∧
      ¬Fin15AnchoredAtom0522 chi) ∨
      (Fin15AnchoredAtom2096 chi ∧
      ¬Fin15AnchoredAtom0523 chi)))) ∨
      ((((Fin15AnchoredAtom2096 chi ∧
      ¬Fin15AnchoredAtom0533 chi) ∨
      (Fin15AnchoredAtom2096 chi ∧
      ¬Fin15AnchoredAtom0809 chi)) ∨
      ((Fin15AnchoredAtom2096 chi ∧
      ¬Fin15AnchoredAtom1095 chi) ∨
      (¬Fin15AnchoredAtom2096 chi ∧
      Fin15AnchoredAtom0522 chi ∧
      Fin15AnchoredAtom0523 chi ∧
      Fin15AnchoredAtom0533 chi ∧
      Fin15AnchoredAtom0809 chi ∧
      Fin15AnchoredAtom1095 chi))) ∨
      (((Fin15AnchoredAtom2097 chi ∧
      ¬Fin15AnchoredAtom0524 chi) ∨
      (Fin15AnchoredAtom2097 chi ∧
      ¬Fin15AnchoredAtom0525 chi)) ∨
      ((Fin15AnchoredAtom2097 chi ∧
      ¬Fin15AnchoredAtom0528 chi) ∨
      (Fin15AnchoredAtom2097 chi ∧
      ¬Fin15AnchoredAtom0810 chi))))) ∨
      (((((Fin15AnchoredAtom2097 chi ∧
      ¬Fin15AnchoredAtom1096 chi) ∨
      (¬Fin15AnchoredAtom2097 chi ∧
      Fin15AnchoredAtom0524 chi ∧
      Fin15AnchoredAtom0525 chi ∧
      Fin15AnchoredAtom0528 chi ∧
      Fin15AnchoredAtom0810 chi ∧
      Fin15AnchoredAtom1096 chi)) ∨
      ((Fin15AnchoredAtom2098 chi ∧
      ¬Fin15AnchoredAtom0524 chi) ∨
      (Fin15AnchoredAtom2098 chi ∧
      ¬Fin15AnchoredAtom0526 chi))) ∨
      (((Fin15AnchoredAtom2098 chi ∧
      ¬Fin15AnchoredAtom0529 chi) ∨
      (Fin15AnchoredAtom2098 chi ∧
      ¬Fin15AnchoredAtom0811 chi)) ∨
      ((Fin15AnchoredAtom2098 chi ∧
      ¬Fin15AnchoredAtom1097 chi) ∨
      (¬Fin15AnchoredAtom2098 chi ∧
      Fin15AnchoredAtom0524 chi ∧
      Fin15AnchoredAtom0526 chi ∧
      Fin15AnchoredAtom0529 chi ∧
      Fin15AnchoredAtom0811 chi ∧
      Fin15AnchoredAtom1097 chi)))) ∨
      ((((Fin15AnchoredAtom2099 chi ∧
      ¬Fin15AnchoredAtom0524 chi) ∨
      (Fin15AnchoredAtom2099 chi ∧
      ¬Fin15AnchoredAtom0527 chi)) ∨
      ((¬Fin15AnchoredAtom2099 chi ∧
      Fin15AnchoredAtom0524 chi ∧
      Fin15AnchoredAtom0527 chi ∧
      Fin15AnchoredAtom0530 chi ∧
      Fin15AnchoredAtom0812 chi ∧
      Fin15AnchoredAtom1098 chi) ∨
      (Fin15AnchoredAtom2100 chi ∧
      ¬Fin15AnchoredAtom0525 chi))) ∨
      (((Fin15AnchoredAtom2100 chi ∧
      ¬Fin15AnchoredAtom0526 chi) ∨
      (Fin15AnchoredAtom2100 chi ∧
      ¬Fin15AnchoredAtom0531 chi)) ∨
      ((Fin15AnchoredAtom2100 chi ∧
      ¬Fin15AnchoredAtom0813 chi) ∨
      (Fin15AnchoredAtom2100 chi ∧
      ¬Fin15AnchoredAtom1099 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom2100 chi ∧
      Fin15AnchoredAtom0525 chi ∧
      Fin15AnchoredAtom0526 chi ∧
      Fin15AnchoredAtom0531 chi ∧
      Fin15AnchoredAtom0813 chi ∧
      Fin15AnchoredAtom1099 chi) ∨
      (Fin15AnchoredAtom2101 chi ∧
      ¬Fin15AnchoredAtom0525 chi)) ∨
      ((Fin15AnchoredAtom2101 chi ∧
      ¬Fin15AnchoredAtom0527 chi) ∨
      (Fin15AnchoredAtom2101 chi ∧
      ¬Fin15AnchoredAtom0532 chi))) ∨
      (((Fin15AnchoredAtom2101 chi ∧
      ¬Fin15AnchoredAtom0814 chi) ∨
      (Fin15AnchoredAtom2101 chi ∧
      ¬Fin15AnchoredAtom1100 chi)) ∨
      ((¬Fin15AnchoredAtom2101 chi ∧
      Fin15AnchoredAtom0525 chi ∧
      Fin15AnchoredAtom0527 chi ∧
      Fin15AnchoredAtom0532 chi ∧
      Fin15AnchoredAtom0814 chi ∧
      Fin15AnchoredAtom1100 chi) ∨
      (Fin15AnchoredAtom2102 chi ∧
      ¬Fin15AnchoredAtom0526 chi)))) ∨
      ((((Fin15AnchoredAtom2102 chi ∧
      ¬Fin15AnchoredAtom0527 chi) ∨
      (Fin15AnchoredAtom2102 chi ∧
      ¬Fin15AnchoredAtom0533 chi)) ∨
      ((Fin15AnchoredAtom2102 chi ∧
      ¬Fin15AnchoredAtom0815 chi) ∨
      (Fin15AnchoredAtom2102 chi ∧
      ¬Fin15AnchoredAtom1101 chi))) ∨
      (((¬Fin15AnchoredAtom2102 chi ∧
      Fin15AnchoredAtom0526 chi ∧
      Fin15AnchoredAtom0527 chi ∧
      Fin15AnchoredAtom0533 chi ∧
      Fin15AnchoredAtom0815 chi ∧
      Fin15AnchoredAtom1101 chi) ∨
      (Fin15AnchoredAtom2103 chi ∧
      ¬Fin15AnchoredAtom0528 chi)) ∨
      ((Fin15AnchoredAtom2103 chi ∧
      ¬Fin15AnchoredAtom0529 chi) ∨
      (Fin15AnchoredAtom2103 chi ∧
      ¬Fin15AnchoredAtom0531 chi))))) ∨
      (((((Fin15AnchoredAtom2103 chi ∧
      ¬Fin15AnchoredAtom0816 chi) ∨
      (Fin15AnchoredAtom2103 chi ∧
      ¬Fin15AnchoredAtom1102 chi)) ∨
      ((¬Fin15AnchoredAtom2103 chi ∧
      Fin15AnchoredAtom0528 chi ∧
      Fin15AnchoredAtom0529 chi ∧
      Fin15AnchoredAtom0531 chi ∧
      Fin15AnchoredAtom0816 chi ∧
      Fin15AnchoredAtom1102 chi) ∨
      (Fin15AnchoredAtom2104 chi ∧
      ¬Fin15AnchoredAtom0532 chi))) ∨
      (((Fin15AnchoredAtom2104 chi ∧
      ¬Fin15AnchoredAtom0817 chi) ∨
      (¬Fin15AnchoredAtom2104 chi ∧
      Fin15AnchoredAtom0528 chi ∧
      Fin15AnchoredAtom0530 chi ∧
      Fin15AnchoredAtom0532 chi ∧
      Fin15AnchoredAtom0817 chi ∧
      Fin15AnchoredAtom1103 chi)) ∨
      ((Fin15AnchoredAtom2105 chi ∧
      ¬Fin15AnchoredAtom0529 chi) ∨
      (Fin15AnchoredAtom2106 chi ∧
      ¬Fin15AnchoredAtom0531 chi)))) ∨
      ((((Fin15AnchoredAtom2106 chi ∧
      ¬Fin15AnchoredAtom0532 chi) ∨
      (Fin15AnchoredAtom2106 chi ∧
      ¬Fin15AnchoredAtom0533 chi)) ∨
      ((Fin15AnchoredAtom2106 chi ∧
      ¬Fin15AnchoredAtom0819 chi) ∨
      (Fin15AnchoredAtom2106 chi ∧
      ¬Fin15AnchoredAtom1105 chi))) ∨
      (((¬Fin15AnchoredAtom2106 chi ∧
      Fin15AnchoredAtom0531 chi ∧
      Fin15AnchoredAtom0532 chi ∧
      Fin15AnchoredAtom0533 chi ∧
      Fin15AnchoredAtom0819 chi ∧
      Fin15AnchoredAtom1105 chi) ∨
      (Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom0534 chi)) ∨
      ((Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom0535 chi) ∨
      (Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom0545 chi))))))) ∨
      ((((((Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom0600 chi) ∨
      ((Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom1106 chi) ∨
      (¬Fin15AnchoredAtom2107 chi ∧
      Fin15AnchoredAtom0534 chi ∧
      Fin15AnchoredAtom0535 chi ∧
      Fin15AnchoredAtom0545 chi ∧
      Fin15AnchoredAtom0600 chi ∧
      Fin15AnchoredAtom1106 chi))) ∨
      (((Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom0534 chi) ∨
      (Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom0536 chi)) ∨
      ((Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom0546 chi) ∨
      (Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom0601 chi)))) ∨
      ((((Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom1107 chi) ∨
      (¬Fin15AnchoredAtom2108 chi ∧
      Fin15AnchoredAtom0534 chi ∧
      Fin15AnchoredAtom0536 chi ∧
      Fin15AnchoredAtom0546 chi ∧
      Fin15AnchoredAtom0601 chi ∧
      Fin15AnchoredAtom1107 chi)) ∨
      ((Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom0534 chi) ∨
      (Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom0537 chi))) ∨
      (((Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom0547 chi) ∨
      (Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom0602 chi)) ∨
      ((Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom1108 chi) ∨
      (¬Fin15AnchoredAtom2109 chi ∧
      Fin15AnchoredAtom0534 chi ∧
      Fin15AnchoredAtom0537 chi ∧
      Fin15AnchoredAtom0547 chi ∧
      Fin15AnchoredAtom0602 chi ∧
      Fin15AnchoredAtom1108 chi))))) ∨
      (((((Fin15AnchoredAtom2110 chi ∧
      ¬Fin15AnchoredAtom0534 chi) ∨
      (Fin15AnchoredAtom2110 chi ∧
      ¬Fin15AnchoredAtom0538 chi)) ∨
      ((Fin15AnchoredAtom2110 chi ∧
      ¬Fin15AnchoredAtom0548 chi) ∨
      (Fin15AnchoredAtom2110 chi ∧
      ¬Fin15AnchoredAtom1109 chi))) ∨
      (((¬Fin15AnchoredAtom2110 chi ∧
      Fin15AnchoredAtom0534 chi ∧
      Fin15AnchoredAtom0538 chi ∧
      Fin15AnchoredAtom0548 chi ∧
      Fin15AnchoredAtom0603 chi ∧
      Fin15AnchoredAtom1109 chi) ∨
      (Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom0534 chi)) ∨
      ((Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom0539 chi) ∨
      (Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom0549 chi)))) ∨
      ((((Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom0604 chi) ∨
      (Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom1110 chi)) ∨
      ((¬Fin15AnchoredAtom2111 chi ∧
      Fin15AnchoredAtom0534 chi ∧
      Fin15AnchoredAtom0539 chi ∧
      Fin15AnchoredAtom0549 chi ∧
      Fin15AnchoredAtom0604 chi ∧
      Fin15AnchoredAtom1110 chi) ∨
      (Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom0534 chi))) ∨
      (((Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom0540 chi) ∨
      (Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom0550 chi)) ∨
      ((Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom0605 chi) ∨
      (Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom1111 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom2112 chi ∧
      Fin15AnchoredAtom0534 chi ∧
      Fin15AnchoredAtom0540 chi ∧
      Fin15AnchoredAtom0550 chi ∧
      Fin15AnchoredAtom0605 chi ∧
      Fin15AnchoredAtom1111 chi) ∨
      (Fin15AnchoredAtom2113 chi ∧
      ¬Fin15AnchoredAtom0541 chi)) ∨
      ((Fin15AnchoredAtom2113 chi ∧
      ¬Fin15AnchoredAtom0551 chi) ∨
      (Fin15AnchoredAtom2113 chi ∧
      ¬Fin15AnchoredAtom0606 chi))) ∨
      (((Fin15AnchoredAtom2113 chi ∧
      ¬Fin15AnchoredAtom1112 chi) ∨
      (¬Fin15AnchoredAtom2113 chi ∧
      Fin15AnchoredAtom0534 chi ∧
      Fin15AnchoredAtom0541 chi ∧
      Fin15AnchoredAtom0551 chi ∧
      Fin15AnchoredAtom0606 chi ∧
      Fin15AnchoredAtom1112 chi)) ∨
      ((Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom0534 chi) ∨
      (Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom0542 chi)))) ∨
      ((((Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom0552 chi) ∨
      (Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom0607 chi)) ∨
      ((Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom1113 chi) ∨
      (¬Fin15AnchoredAtom2114 chi ∧
      Fin15AnchoredAtom0534 chi ∧
      Fin15AnchoredAtom0542 chi ∧
      Fin15AnchoredAtom0552 chi ∧
      Fin15AnchoredAtom0607 chi ∧
      Fin15AnchoredAtom1113 chi))) ∨
      (((Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom0534 chi) ∨
      (Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom0543 chi)) ∨
      ((Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom0553 chi) ∨
      (Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom0608 chi))))) ∨
      (((((Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom1114 chi) ∨
      (¬Fin15AnchoredAtom2115 chi ∧
      Fin15AnchoredAtom0534 chi ∧
      Fin15AnchoredAtom0543 chi ∧
      Fin15AnchoredAtom0553 chi ∧
      Fin15AnchoredAtom0608 chi ∧
      Fin15AnchoredAtom1114 chi)) ∨
      ((Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom0534 chi) ∨
      (Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom0544 chi))) ∨
      (((Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom0554 chi) ∨
      (Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom0609 chi)) ∨
      ((Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom1115 chi) ∨
      (¬Fin15AnchoredAtom2116 chi ∧
      Fin15AnchoredAtom0534 chi ∧
      Fin15AnchoredAtom0544 chi ∧
      Fin15AnchoredAtom0554 chi ∧
      Fin15AnchoredAtom0609 chi ∧
      Fin15AnchoredAtom1115 chi)))) ∨
      ((((Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom0535 chi) ∨
      (Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom0536 chi)) ∨
      ((Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom0555 chi) ∨
      (Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom0610 chi))) ∨
      (((Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom1116 chi) ∨
      (¬Fin15AnchoredAtom2117 chi ∧
      Fin15AnchoredAtom0535 chi ∧
      Fin15AnchoredAtom0536 chi ∧
      Fin15AnchoredAtom0555 chi ∧
      Fin15AnchoredAtom0610 chi ∧
      Fin15AnchoredAtom1116 chi)) ∨
      ((Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom0535 chi) ∨
      (Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom0537 chi)))))))))) := by
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
              rcases hbad with hbad | hbad
              ·
                exact fin15Anchored_clause16658 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16659 chi hbad
                ·
                  exact fin15Anchored_clause16660 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16661 chi hbad
                ·
                  exact fin15Anchored_clause16662 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16663 chi hbad
                ·
                  exact fin15Anchored_clause16664 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16665 chi hbad
                ·
                  exact fin15Anchored_clause16666 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16667 chi hbad
                ·
                  exact fin15Anchored_clause16668 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16669 chi hbad
                ·
                  exact fin15Anchored_clause16670 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16671 chi hbad
                ·
                  exact fin15Anchored_clause16672 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16673 chi hbad
                ·
                  exact fin15Anchored_clause16674 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16675 chi hbad
                ·
                  exact fin15Anchored_clause16676 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16677 chi hbad
                ·
                  exact fin15Anchored_clause16678 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16679 chi hbad
                ·
                  exact fin15Anchored_clause16680 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16681 chi hbad
                ·
                  exact fin15Anchored_clause16682 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16683 chi hbad
                ·
                  exact fin15Anchored_clause16684 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16685 chi hbad
                ·
                  exact fin15Anchored_clause16686 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16687 chi hbad
                ·
                  exact fin15Anchored_clause16688 chi hbad
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
                  exact fin15Anchored_clause16689 chi hbad
                ·
                  exact fin15Anchored_clause16690 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16691 chi hbad
                ·
                  exact fin15Anchored_clause16692 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16693 chi hbad
                ·
                  exact fin15Anchored_clause16694 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16695 chi hbad
                ·
                  exact fin15Anchored_clause16696 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16697 chi hbad
                ·
                  exact fin15Anchored_clause16698 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16699 chi hbad
                ·
                  exact fin15Anchored_clause16700 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16701 chi hbad
                ·
                  exact fin15Anchored_clause16702 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16703 chi hbad
                ·
                  exact fin15Anchored_clause16704 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16705 chi hbad
                ·
                  exact fin15Anchored_clause16706 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16707 chi hbad
                ·
                  exact fin15Anchored_clause16708 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16709 chi hbad
                ·
                  exact fin15Anchored_clause16710 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16711 chi hbad
                ·
                  exact fin15Anchored_clause16712 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16713 chi hbad
                ·
                  exact fin15Anchored_clause16714 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16715 chi hbad
                ·
                  exact fin15Anchored_clause16716 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16717 chi hbad
                ·
                  exact fin15Anchored_clause16718 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16719 chi hbad
                ·
                  exact fin15Anchored_clause16720 chi hbad
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
                exact fin15Anchored_clause16721 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16722 chi hbad
                ·
                  exact fin15Anchored_clause16723 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16724 chi hbad
                ·
                  exact fin15Anchored_clause16725 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16726 chi hbad
                ·
                  exact fin15Anchored_clause16727 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16728 chi hbad
                ·
                  exact fin15Anchored_clause16729 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16730 chi hbad
                ·
                  exact fin15Anchored_clause16731 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16732 chi hbad
                ·
                  exact fin15Anchored_clause16733 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16734 chi hbad
                ·
                  exact fin15Anchored_clause16735 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16736 chi hbad
                ·
                  exact fin15Anchored_clause16737 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16738 chi hbad
                ·
                  exact fin15Anchored_clause16739 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16740 chi hbad
                ·
                  exact fin15Anchored_clause16741 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16742 chi hbad
                ·
                  exact fin15Anchored_clause16743 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16744 chi hbad
                ·
                  exact fin15Anchored_clause16745 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16746 chi hbad
                ·
                  exact fin15Anchored_clause16747 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16748 chi hbad
                ·
                  exact fin15Anchored_clause16749 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16750 chi hbad
                ·
                  exact fin15Anchored_clause16751 chi hbad
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
                  exact fin15Anchored_clause16752 chi hbad
                ·
                  exact fin15Anchored_clause16753 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16754 chi hbad
                ·
                  exact fin15Anchored_clause16755 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16756 chi hbad
                ·
                  exact fin15Anchored_clause16757 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16758 chi hbad
                ·
                  exact fin15Anchored_clause16759 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16760 chi hbad
                ·
                  exact fin15Anchored_clause16761 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16762 chi hbad
                ·
                  exact fin15Anchored_clause16763 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16764 chi hbad
                ·
                  exact fin15Anchored_clause16765 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16766 chi hbad
                ·
                  exact fin15Anchored_clause16767 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16768 chi hbad
                ·
                  exact fin15Anchored_clause16769 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16770 chi hbad
                ·
                  exact fin15Anchored_clause16771 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16772 chi hbad
                ·
                  exact fin15Anchored_clause16773 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16774 chi hbad
                ·
                  exact fin15Anchored_clause16775 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16776 chi hbad
                ·
                  exact fin15Anchored_clause16777 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16778 chi hbad
                ·
                  exact fin15Anchored_clause16779 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16780 chi hbad
                ·
                  exact fin15Anchored_clause16781 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16782 chi hbad
                ·
                  exact fin15Anchored_clause16783 chi hbad
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
              rcases hbad with hbad | hbad
              ·
                exact fin15Anchored_clause16784 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16785 chi hbad
                ·
                  exact fin15Anchored_clause16786 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16787 chi hbad
                ·
                  exact fin15Anchored_clause16788 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16789 chi hbad
                ·
                  exact fin15Anchored_clause16790 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16791 chi hbad
                ·
                  exact fin15Anchored_clause16792 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16793 chi hbad
                ·
                  exact fin15Anchored_clause16794 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16795 chi hbad
                ·
                  exact fin15Anchored_clause16796 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16797 chi hbad
                ·
                  exact fin15Anchored_clause16798 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16799 chi hbad
                ·
                  exact fin15Anchored_clause16800 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16801 chi hbad
                ·
                  exact fin15Anchored_clause16802 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16803 chi hbad
                ·
                  exact fin15Anchored_clause16804 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16805 chi hbad
                ·
                  exact fin15Anchored_clause16806 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16807 chi hbad
                ·
                  exact fin15Anchored_clause16808 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16809 chi hbad
                ·
                  exact fin15Anchored_clause16810 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16811 chi hbad
                ·
                  exact fin15Anchored_clause16812 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16813 chi hbad
                ·
                  exact fin15Anchored_clause16814 chi hbad
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
                  exact fin15Anchored_clause16815 chi hbad
                ·
                  exact fin15Anchored_clause16816 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16817 chi hbad
                ·
                  exact fin15Anchored_clause16818 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16819 chi hbad
                ·
                  exact fin15Anchored_clause16820 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16821 chi hbad
                ·
                  exact fin15Anchored_clause16822 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16823 chi hbad
                ·
                  exact fin15Anchored_clause16824 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16825 chi hbad
                ·
                  exact fin15Anchored_clause16826 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16827 chi hbad
                ·
                  exact fin15Anchored_clause16828 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16829 chi hbad
                ·
                  exact fin15Anchored_clause16830 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16831 chi hbad
                ·
                  exact fin15Anchored_clause16832 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16833 chi hbad
                ·
                  exact fin15Anchored_clause16834 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16835 chi hbad
                ·
                  exact fin15Anchored_clause16836 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16837 chi hbad
                ·
                  exact fin15Anchored_clause16838 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16839 chi hbad
                ·
                  exact fin15Anchored_clause16840 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16841 chi hbad
                ·
                  exact fin15Anchored_clause16842 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16843 chi hbad
                ·
                  exact fin15Anchored_clause16844 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16845 chi hbad
                ·
                  exact fin15Anchored_clause16846 chi hbad
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
                exact fin15Anchored_clause16847 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16848 chi hbad
                ·
                  exact fin15Anchored_clause16849 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16850 chi hbad
                ·
                  exact fin15Anchored_clause16851 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16852 chi hbad
                ·
                  exact fin15Anchored_clause16853 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16854 chi hbad
                ·
                  exact fin15Anchored_clause16855 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16856 chi hbad
                ·
                  exact fin15Anchored_clause16857 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16858 chi hbad
                ·
                  exact fin15Anchored_clause16859 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16860 chi hbad
                ·
                  exact fin15Anchored_clause16861 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16862 chi hbad
                ·
                  exact fin15Anchored_clause16863 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16864 chi hbad
                ·
                  exact fin15Anchored_clause16865 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16866 chi hbad
                ·
                  exact fin15Anchored_clause16867 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16868 chi hbad
                ·
                  exact fin15Anchored_clause16869 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16870 chi hbad
                ·
                  exact fin15Anchored_clause16871 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16872 chi hbad
                ·
                  exact fin15Anchored_clause16873 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16874 chi hbad
                ·
                  exact fin15Anchored_clause16875 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16876 chi hbad
                ·
                  exact fin15Anchored_clause16877 chi hbad
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
                  exact fin15Anchored_clause16878 chi hbad
                ·
                  exact fin15Anchored_clause16879 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16880 chi hbad
                ·
                  exact fin15Anchored_clause16881 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16882 chi hbad
                ·
                  exact fin15Anchored_clause16883 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16884 chi hbad
                ·
                  exact fin15Anchored_clause16885 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16886 chi hbad
                ·
                  exact fin15Anchored_clause16887 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16888 chi hbad
                ·
                  exact fin15Anchored_clause16889 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16890 chi hbad
                ·
                  exact fin15Anchored_clause16891 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16892 chi hbad
                ·
                  exact fin15Anchored_clause16893 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16894 chi hbad
                ·
                  exact fin15Anchored_clause16895 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16896 chi hbad
                ·
                  exact fin15Anchored_clause16897 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16898 chi hbad
                ·
                  exact fin15Anchored_clause16899 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16900 chi hbad
                ·
                  exact fin15Anchored_clause16901 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16902 chi hbad
                ·
                  exact fin15Anchored_clause16903 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16904 chi hbad
                ·
                  exact fin15Anchored_clause16905 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16906 chi hbad
                ·
                  exact fin15Anchored_clause16907 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16908 chi hbad
                ·
                  exact fin15Anchored_clause16909 chi hbad

end ErdosSzekeres

end
