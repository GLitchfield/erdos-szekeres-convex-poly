module

public import ErdosSzekeres.Fin15AnchoredClauseChunk132
public import ErdosSzekeres.Fin15AnchoredClauseChunk133
public import ErdosSzekeres.Fin15AnchoredClauseChunk134

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 067. -/

theorem fin15Anchored_rejectSemanticSegment067
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom0556 chi) ∨
      ((Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom0611 chi) ∨
      (Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom1117 chi))) ∨
      (((¬Fin15AnchoredAtom2118 chi ∧
      Fin15AnchoredAtom0535 chi ∧
      Fin15AnchoredAtom0537 chi ∧
      Fin15AnchoredAtom0556 chi ∧
      Fin15AnchoredAtom0611 chi ∧
      Fin15AnchoredAtom1117 chi) ∨
      (Fin15AnchoredAtom2119 chi ∧
      ¬Fin15AnchoredAtom0535 chi)) ∨
      ((Fin15AnchoredAtom2119 chi ∧
      ¬Fin15AnchoredAtom0538 chi) ∨
      (Fin15AnchoredAtom2119 chi ∧
      ¬Fin15AnchoredAtom0557 chi)))) ∨
      ((((Fin15AnchoredAtom2119 chi ∧
      ¬Fin15AnchoredAtom0612 chi) ∨
      (Fin15AnchoredAtom2119 chi ∧
      ¬Fin15AnchoredAtom1118 chi)) ∨
      ((¬Fin15AnchoredAtom2119 chi ∧
      Fin15AnchoredAtom0535 chi ∧
      Fin15AnchoredAtom0538 chi ∧
      Fin15AnchoredAtom0557 chi ∧
      Fin15AnchoredAtom0612 chi ∧
      Fin15AnchoredAtom1118 chi) ∨
      (Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom0535 chi))) ∨
      (((Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom0539 chi) ∨
      (Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom0558 chi)) ∨
      ((Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom0613 chi) ∨
      (Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom1119 chi))))) ∨
      (((((¬Fin15AnchoredAtom2120 chi ∧
      Fin15AnchoredAtom0535 chi ∧
      Fin15AnchoredAtom0539 chi ∧
      Fin15AnchoredAtom0558 chi ∧
      Fin15AnchoredAtom0613 chi ∧
      Fin15AnchoredAtom1119 chi) ∨
      (Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom0535 chi)) ∨
      ((Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom0540 chi) ∨
      (Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom0559 chi))) ∨
      (((Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom0614 chi) ∨
      (Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom1120 chi)) ∨
      ((¬Fin15AnchoredAtom2121 chi ∧
      Fin15AnchoredAtom0535 chi ∧
      Fin15AnchoredAtom0540 chi ∧
      Fin15AnchoredAtom0559 chi ∧
      Fin15AnchoredAtom0614 chi ∧
      Fin15AnchoredAtom1120 chi) ∨
      (Fin15AnchoredAtom2122 chi ∧
      ¬Fin15AnchoredAtom0535 chi)))) ∨
      ((((Fin15AnchoredAtom2122 chi ∧
      ¬Fin15AnchoredAtom0541 chi) ∨
      (Fin15AnchoredAtom2122 chi ∧
      ¬Fin15AnchoredAtom0560 chi)) ∨
      ((Fin15AnchoredAtom2122 chi ∧
      ¬Fin15AnchoredAtom1121 chi) ∨
      (¬Fin15AnchoredAtom2122 chi ∧
      Fin15AnchoredAtom0535 chi ∧
      Fin15AnchoredAtom0541 chi ∧
      Fin15AnchoredAtom0560 chi ∧
      Fin15AnchoredAtom0615 chi ∧
      Fin15AnchoredAtom1121 chi))) ∨
      (((Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom0535 chi) ∨
      (Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom0542 chi)) ∨
      ((Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom0561 chi) ∨
      (Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom0616 chi)))))) ∨
      ((((((Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom1122 chi) ∨
      (¬Fin15AnchoredAtom2123 chi ∧
      Fin15AnchoredAtom0535 chi ∧
      Fin15AnchoredAtom0542 chi ∧
      Fin15AnchoredAtom0561 chi ∧
      Fin15AnchoredAtom0616 chi ∧
      Fin15AnchoredAtom1122 chi)) ∨
      ((Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom0535 chi) ∨
      (Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom0543 chi))) ∨
      (((Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom0562 chi) ∨
      (Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom0617 chi)) ∨
      ((Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom1123 chi) ∨
      (¬Fin15AnchoredAtom2124 chi ∧
      Fin15AnchoredAtom0535 chi ∧
      Fin15AnchoredAtom0543 chi ∧
      Fin15AnchoredAtom0562 chi ∧
      Fin15AnchoredAtom0617 chi ∧
      Fin15AnchoredAtom1123 chi)))) ∨
      ((((Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom0535 chi) ∨
      (Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom0544 chi)) ∨
      ((Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom0563 chi) ∨
      (Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom0618 chi))) ∨
      (((Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom1124 chi) ∨
      (¬Fin15AnchoredAtom2125 chi ∧
      Fin15AnchoredAtom0535 chi ∧
      Fin15AnchoredAtom0544 chi ∧
      Fin15AnchoredAtom0563 chi ∧
      Fin15AnchoredAtom0618 chi ∧
      Fin15AnchoredAtom1124 chi)) ∨
      ((Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom0536 chi) ∨
      (Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom0537 chi))))) ∨
      (((((Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom0564 chi) ∨
      (Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom0619 chi)) ∨
      ((Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom1125 chi) ∨
      (¬Fin15AnchoredAtom2126 chi ∧
      Fin15AnchoredAtom0536 chi ∧
      Fin15AnchoredAtom0537 chi ∧
      Fin15AnchoredAtom0564 chi ∧
      Fin15AnchoredAtom0619 chi ∧
      Fin15AnchoredAtom1125 chi))) ∨
      (((Fin15AnchoredAtom2127 chi ∧
      ¬Fin15AnchoredAtom0536 chi) ∨
      (Fin15AnchoredAtom2127 chi ∧
      ¬Fin15AnchoredAtom0538 chi)) ∨
      ((Fin15AnchoredAtom2127 chi ∧
      ¬Fin15AnchoredAtom0565 chi) ∨
      (Fin15AnchoredAtom2127 chi ∧
      ¬Fin15AnchoredAtom0620 chi)))) ∨
      ((((Fin15AnchoredAtom2127 chi ∧
      ¬Fin15AnchoredAtom1126 chi) ∨
      (¬Fin15AnchoredAtom2127 chi ∧
      Fin15AnchoredAtom0536 chi ∧
      Fin15AnchoredAtom0538 chi ∧
      Fin15AnchoredAtom0565 chi ∧
      Fin15AnchoredAtom0620 chi ∧
      Fin15AnchoredAtom1126 chi)) ∨
      ((Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom0536 chi) ∨
      (Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom0539 chi))) ∨
      (((Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom0566 chi) ∨
      (Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom0621 chi)) ∨
      ((Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom1127 chi) ∨
      (¬Fin15AnchoredAtom2128 chi ∧
      Fin15AnchoredAtom0536 chi ∧
      Fin15AnchoredAtom0539 chi ∧
      Fin15AnchoredAtom0566 chi ∧
      Fin15AnchoredAtom0621 chi ∧
      Fin15AnchoredAtom1127 chi))))))) ∨
      ((((((Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom0536 chi) ∨
      ((Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom0540 chi) ∨
      (Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom0567 chi))) ∨
      (((Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom0622 chi) ∨
      (Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom1128 chi)) ∨
      ((¬Fin15AnchoredAtom2129 chi ∧
      Fin15AnchoredAtom0536 chi ∧
      Fin15AnchoredAtom0540 chi ∧
      Fin15AnchoredAtom0567 chi ∧
      Fin15AnchoredAtom0622 chi ∧
      Fin15AnchoredAtom1128 chi) ∨
      (Fin15AnchoredAtom2130 chi ∧
      ¬Fin15AnchoredAtom0536 chi)))) ∨
      ((((Fin15AnchoredAtom2130 chi ∧
      ¬Fin15AnchoredAtom0541 chi) ∨
      (Fin15AnchoredAtom2130 chi ∧
      ¬Fin15AnchoredAtom0568 chi)) ∨
      ((Fin15AnchoredAtom2130 chi ∧
      ¬Fin15AnchoredAtom1129 chi) ∨
      (¬Fin15AnchoredAtom2130 chi ∧
      Fin15AnchoredAtom0536 chi ∧
      Fin15AnchoredAtom0541 chi ∧
      Fin15AnchoredAtom0568 chi ∧
      Fin15AnchoredAtom0623 chi ∧
      Fin15AnchoredAtom1129 chi))) ∨
      (((Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom0536 chi) ∨
      (Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom0542 chi)) ∨
      ((Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom0569 chi) ∨
      (Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom0624 chi))))) ∨
      (((((Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom1130 chi) ∨
      (¬Fin15AnchoredAtom2131 chi ∧
      Fin15AnchoredAtom0536 chi ∧
      Fin15AnchoredAtom0542 chi ∧
      Fin15AnchoredAtom0569 chi ∧
      Fin15AnchoredAtom0624 chi ∧
      Fin15AnchoredAtom1130 chi)) ∨
      ((Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom0536 chi) ∨
      (Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom0543 chi))) ∨
      (((Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom0570 chi) ∨
      (Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom0625 chi)) ∨
      ((Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom1131 chi) ∨
      (¬Fin15AnchoredAtom2132 chi ∧
      Fin15AnchoredAtom0536 chi ∧
      Fin15AnchoredAtom0543 chi ∧
      Fin15AnchoredAtom0570 chi ∧
      Fin15AnchoredAtom0625 chi ∧
      Fin15AnchoredAtom1131 chi)))) ∨
      ((((Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom0536 chi) ∨
      (Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom0544 chi)) ∨
      ((Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom0571 chi) ∨
      (Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom0626 chi))) ∨
      (((Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom1132 chi) ∨
      (¬Fin15AnchoredAtom2133 chi ∧
      Fin15AnchoredAtom0536 chi ∧
      Fin15AnchoredAtom0544 chi ∧
      Fin15AnchoredAtom0571 chi ∧
      Fin15AnchoredAtom0626 chi ∧
      Fin15AnchoredAtom1132 chi)) ∨
      ((Fin15AnchoredAtom2134 chi ∧
      ¬Fin15AnchoredAtom0537 chi) ∨
      (Fin15AnchoredAtom2134 chi ∧
      ¬Fin15AnchoredAtom0538 chi)))))) ∨
      ((((((Fin15AnchoredAtom2134 chi ∧
      ¬Fin15AnchoredAtom0572 chi) ∨
      (Fin15AnchoredAtom2134 chi ∧
      ¬Fin15AnchoredAtom0627 chi)) ∨
      ((Fin15AnchoredAtom2134 chi ∧
      ¬Fin15AnchoredAtom1133 chi) ∨
      (¬Fin15AnchoredAtom2134 chi ∧
      Fin15AnchoredAtom0537 chi ∧
      Fin15AnchoredAtom0538 chi ∧
      Fin15AnchoredAtom0572 chi ∧
      Fin15AnchoredAtom0627 chi ∧
      Fin15AnchoredAtom1133 chi))) ∨
      (((Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom0537 chi) ∨
      (Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom0539 chi)) ∨
      ((Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom0573 chi) ∨
      (Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom0628 chi)))) ∨
      ((((Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom1134 chi) ∨
      (¬Fin15AnchoredAtom2135 chi ∧
      Fin15AnchoredAtom0537 chi ∧
      Fin15AnchoredAtom0539 chi ∧
      Fin15AnchoredAtom0573 chi ∧
      Fin15AnchoredAtom0628 chi ∧
      Fin15AnchoredAtom1134 chi)) ∨
      ((Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom0537 chi) ∨
      (Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom0540 chi))) ∨
      (((Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom0574 chi) ∨
      (Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom0629 chi)) ∨
      ((Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom1135 chi) ∨
      (¬Fin15AnchoredAtom2136 chi ∧
      Fin15AnchoredAtom0537 chi ∧
      Fin15AnchoredAtom0540 chi ∧
      Fin15AnchoredAtom0574 chi ∧
      Fin15AnchoredAtom0629 chi ∧
      Fin15AnchoredAtom1135 chi))))) ∨
      (((((Fin15AnchoredAtom2137 chi ∧
      ¬Fin15AnchoredAtom0537 chi) ∨
      (Fin15AnchoredAtom2137 chi ∧
      ¬Fin15AnchoredAtom1136 chi)) ∨
      ((¬Fin15AnchoredAtom2137 chi ∧
      Fin15AnchoredAtom0537 chi ∧
      Fin15AnchoredAtom0541 chi ∧
      Fin15AnchoredAtom0575 chi ∧
      Fin15AnchoredAtom0630 chi ∧
      Fin15AnchoredAtom1136 chi) ∨
      (Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom0537 chi))) ∨
      (((Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom0542 chi) ∨
      (Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom0576 chi)) ∨
      ((Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom0631 chi) ∨
      (Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom1137 chi)))) ∨
      ((((¬Fin15AnchoredAtom2138 chi ∧
      Fin15AnchoredAtom0537 chi ∧
      Fin15AnchoredAtom0542 chi ∧
      Fin15AnchoredAtom0576 chi ∧
      Fin15AnchoredAtom0631 chi ∧
      Fin15AnchoredAtom1137 chi) ∨
      (Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom0537 chi)) ∨
      ((Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom0543 chi) ∨
      (Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom0577 chi))) ∨
      (((Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom0632 chi) ∨
      (Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom1138 chi)) ∨
      ((¬Fin15AnchoredAtom2139 chi ∧
      Fin15AnchoredAtom0537 chi ∧
      Fin15AnchoredAtom0543 chi ∧
      Fin15AnchoredAtom0577 chi ∧
      Fin15AnchoredAtom0632 chi ∧
      Fin15AnchoredAtom1138 chi) ∨
      (Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom0537 chi)))))))) ∨
      (((((((Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom0544 chi) ∨
      ((Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom0578 chi) ∨
      (Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom0633 chi))) ∨
      (((Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom1139 chi) ∨
      (¬Fin15AnchoredAtom2140 chi ∧
      Fin15AnchoredAtom0537 chi ∧
      Fin15AnchoredAtom0544 chi ∧
      Fin15AnchoredAtom0578 chi ∧
      Fin15AnchoredAtom0633 chi ∧
      Fin15AnchoredAtom1139 chi)) ∨
      ((Fin15AnchoredAtom2141 chi ∧
      ¬Fin15AnchoredAtom0538 chi) ∨
      (Fin15AnchoredAtom2141 chi ∧
      ¬Fin15AnchoredAtom0539 chi)))) ∨
      ((((Fin15AnchoredAtom2141 chi ∧
      ¬Fin15AnchoredAtom0579 chi) ∨
      (Fin15AnchoredAtom2141 chi ∧
      ¬Fin15AnchoredAtom1140 chi)) ∨
      ((¬Fin15AnchoredAtom2141 chi ∧
      Fin15AnchoredAtom0538 chi ∧
      Fin15AnchoredAtom0539 chi ∧
      Fin15AnchoredAtom0579 chi ∧
      Fin15AnchoredAtom0634 chi ∧
      Fin15AnchoredAtom1140 chi) ∨
      (Fin15AnchoredAtom2142 chi ∧
      ¬Fin15AnchoredAtom0538 chi))) ∨
      (((Fin15AnchoredAtom2142 chi ∧
      ¬Fin15AnchoredAtom0540 chi) ∨
      (Fin15AnchoredAtom2142 chi ∧
      ¬Fin15AnchoredAtom0580 chi)) ∨
      ((Fin15AnchoredAtom2142 chi ∧
      ¬Fin15AnchoredAtom0635 chi) ∨
      (Fin15AnchoredAtom2142 chi ∧
      ¬Fin15AnchoredAtom1141 chi))))) ∨
      (((((¬Fin15AnchoredAtom2142 chi ∧
      Fin15AnchoredAtom0538 chi ∧
      Fin15AnchoredAtom0540 chi ∧
      Fin15AnchoredAtom0580 chi ∧
      Fin15AnchoredAtom0635 chi ∧
      Fin15AnchoredAtom1141 chi) ∨
      (Fin15AnchoredAtom2144 chi ∧
      ¬Fin15AnchoredAtom0538 chi)) ∨
      ((Fin15AnchoredAtom2144 chi ∧
      ¬Fin15AnchoredAtom0542 chi) ∨
      (Fin15AnchoredAtom2144 chi ∧
      ¬Fin15AnchoredAtom0582 chi))) ∨
      (((Fin15AnchoredAtom2144 chi ∧
      ¬Fin15AnchoredAtom0637 chi) ∨
      (Fin15AnchoredAtom2144 chi ∧
      ¬Fin15AnchoredAtom1143 chi)) ∨
      ((¬Fin15AnchoredAtom2144 chi ∧
      Fin15AnchoredAtom0538 chi ∧
      Fin15AnchoredAtom0542 chi ∧
      Fin15AnchoredAtom0582 chi ∧
      Fin15AnchoredAtom0637 chi ∧
      Fin15AnchoredAtom1143 chi) ∨
      (Fin15AnchoredAtom2145 chi ∧
      ¬Fin15AnchoredAtom0543 chi)))) ∨
      ((((Fin15AnchoredAtom2146 chi ∧
      ¬Fin15AnchoredAtom0584 chi) ∨
      (Fin15AnchoredAtom2146 chi ∧
      ¬Fin15AnchoredAtom1145 chi)) ∨
      ((¬Fin15AnchoredAtom2146 chi ∧
      Fin15AnchoredAtom0538 chi ∧
      Fin15AnchoredAtom0544 chi ∧
      Fin15AnchoredAtom0584 chi ∧
      Fin15AnchoredAtom0639 chi ∧
      Fin15AnchoredAtom1145 chi) ∨
      (Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom0539 chi))) ∨
      (((Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom0540 chi) ∨
      (Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom0585 chi)) ∨
      ((Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom0640 chi) ∨
      (Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom1146 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom2147 chi ∧
      Fin15AnchoredAtom0539 chi ∧
      Fin15AnchoredAtom0540 chi ∧
      Fin15AnchoredAtom0585 chi ∧
      Fin15AnchoredAtom0640 chi ∧
      Fin15AnchoredAtom1146 chi) ∨
      (Fin15AnchoredAtom2148 chi ∧
      ¬Fin15AnchoredAtom0539 chi)) ∨
      ((Fin15AnchoredAtom2148 chi ∧
      ¬Fin15AnchoredAtom1147 chi) ∨
      (¬Fin15AnchoredAtom2148 chi ∧
      Fin15AnchoredAtom0539 chi ∧
      Fin15AnchoredAtom0541 chi ∧
      Fin15AnchoredAtom0586 chi ∧
      Fin15AnchoredAtom0641 chi ∧
      Fin15AnchoredAtom1147 chi))) ∨
      (((Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom0539 chi) ∨
      (Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom0542 chi)) ∨
      ((Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom0587 chi) ∨
      (Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom0642 chi)))) ∨
      ((((Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom1148 chi) ∨
      (¬Fin15AnchoredAtom2149 chi ∧
      Fin15AnchoredAtom0539 chi ∧
      Fin15AnchoredAtom0542 chi ∧
      Fin15AnchoredAtom0587 chi ∧
      Fin15AnchoredAtom0642 chi ∧
      Fin15AnchoredAtom1148 chi)) ∨
      ((Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom0539 chi) ∨
      (Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom0543 chi))) ∨
      (((Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom0588 chi) ∨
      (Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom0643 chi)) ∨
      ((Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom1149 chi) ∨
      (¬Fin15AnchoredAtom2150 chi ∧
      Fin15AnchoredAtom0539 chi ∧
      Fin15AnchoredAtom0543 chi ∧
      Fin15AnchoredAtom0588 chi ∧
      Fin15AnchoredAtom0643 chi ∧
      Fin15AnchoredAtom1149 chi))))) ∨
      (((((Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom0539 chi) ∨
      (Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom0544 chi)) ∨
      ((Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom0589 chi) ∨
      (Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom0644 chi))) ∨
      (((Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom1150 chi) ∨
      (¬Fin15AnchoredAtom2151 chi ∧
      Fin15AnchoredAtom0539 chi ∧
      Fin15AnchoredAtom0544 chi ∧
      Fin15AnchoredAtom0589 chi ∧
      Fin15AnchoredAtom0644 chi ∧
      Fin15AnchoredAtom1150 chi)) ∨
      ((Fin15AnchoredAtom2152 chi ∧
      ¬Fin15AnchoredAtom0540 chi) ∨
      (Fin15AnchoredAtom2152 chi ∧
      ¬Fin15AnchoredAtom0541 chi)))) ∨
      ((((Fin15AnchoredAtom2152 chi ∧
      ¬Fin15AnchoredAtom0590 chi) ∨
      (Fin15AnchoredAtom2152 chi ∧
      ¬Fin15AnchoredAtom0645 chi)) ∨
      ((Fin15AnchoredAtom2152 chi ∧
      ¬Fin15AnchoredAtom1151 chi) ∨
      (¬Fin15AnchoredAtom2152 chi ∧
      Fin15AnchoredAtom0540 chi ∧
      Fin15AnchoredAtom0541 chi ∧
      Fin15AnchoredAtom0590 chi ∧
      Fin15AnchoredAtom0645 chi ∧
      Fin15AnchoredAtom1151 chi))) ∨
      (((Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom0540 chi) ∨
      (Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom0542 chi)) ∨
      ((Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom0591 chi) ∨
      (Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom0646 chi))))))) ∨
      (((((((Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom1152 chi) ∨
      (¬Fin15AnchoredAtom2153 chi ∧
      Fin15AnchoredAtom0540 chi ∧
      Fin15AnchoredAtom0542 chi ∧
      Fin15AnchoredAtom0591 chi ∧
      Fin15AnchoredAtom0646 chi ∧
      Fin15AnchoredAtom1152 chi)) ∨
      ((Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom0540 chi) ∨
      (Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom0543 chi))) ∨
      (((Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom0592 chi) ∨
      (Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom0647 chi)) ∨
      ((Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom1153 chi) ∨
      (¬Fin15AnchoredAtom2154 chi ∧
      Fin15AnchoredAtom0540 chi ∧
      Fin15AnchoredAtom0543 chi ∧
      Fin15AnchoredAtom0592 chi ∧
      Fin15AnchoredAtom0647 chi ∧
      Fin15AnchoredAtom1153 chi)))) ∨
      ((((Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom0540 chi) ∨
      (Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom0544 chi)) ∨
      ((Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom0593 chi) ∨
      (Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom0648 chi))) ∨
      (((Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom1154 chi) ∨
      (¬Fin15AnchoredAtom2155 chi ∧
      Fin15AnchoredAtom0540 chi ∧
      Fin15AnchoredAtom0544 chi ∧
      Fin15AnchoredAtom0593 chi ∧
      Fin15AnchoredAtom0648 chi ∧
      Fin15AnchoredAtom1154 chi)) ∨
      ((Fin15AnchoredAtom2156 chi ∧
      ¬Fin15AnchoredAtom0542 chi) ∨
      (¬Fin15AnchoredAtom2156 chi ∧
      Fin15AnchoredAtom0541 chi ∧
      Fin15AnchoredAtom0542 chi ∧
      Fin15AnchoredAtom0594 chi ∧
      Fin15AnchoredAtom0649 chi ∧
      Fin15AnchoredAtom1155 chi))))) ∨
      (((((Fin15AnchoredAtom2157 chi ∧
      ¬Fin15AnchoredAtom0541 chi) ∨
      (Fin15AnchoredAtom2157 chi ∧
      ¬Fin15AnchoredAtom0543 chi)) ∨
      ((Fin15AnchoredAtom2157 chi ∧
      ¬Fin15AnchoredAtom0595 chi) ∨
      (Fin15AnchoredAtom2157 chi ∧
      ¬Fin15AnchoredAtom1156 chi))) ∨
      (((¬Fin15AnchoredAtom2157 chi ∧
      Fin15AnchoredAtom0541 chi ∧
      Fin15AnchoredAtom0543 chi ∧
      Fin15AnchoredAtom0595 chi ∧
      Fin15AnchoredAtom0650 chi ∧
      Fin15AnchoredAtom1156 chi) ∨
      (Fin15AnchoredAtom2158 chi ∧
      ¬Fin15AnchoredAtom0541 chi)) ∨
      ((Fin15AnchoredAtom2158 chi ∧
      ¬Fin15AnchoredAtom0544 chi) ∨
      (Fin15AnchoredAtom2158 chi ∧
      ¬Fin15AnchoredAtom0596 chi)))) ∨
      ((((Fin15AnchoredAtom2158 chi ∧
      ¬Fin15AnchoredAtom0651 chi) ∨
      (Fin15AnchoredAtom2158 chi ∧
      ¬Fin15AnchoredAtom1157 chi)) ∨
      ((¬Fin15AnchoredAtom2158 chi ∧
      Fin15AnchoredAtom0541 chi ∧
      Fin15AnchoredAtom0544 chi ∧
      Fin15AnchoredAtom0596 chi ∧
      Fin15AnchoredAtom0651 chi ∧
      Fin15AnchoredAtom1157 chi) ∨
      (Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom0542 chi))) ∨
      (((Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom0543 chi) ∨
      (Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom0597 chi)) ∨
      ((Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom0652 chi) ∨
      (Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom1158 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom2159 chi ∧
      Fin15AnchoredAtom0542 chi ∧
      Fin15AnchoredAtom0543 chi ∧
      Fin15AnchoredAtom0597 chi ∧
      Fin15AnchoredAtom0652 chi ∧
      Fin15AnchoredAtom1158 chi) ∨
      (Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom0542 chi)) ∨
      ((Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom0544 chi) ∨
      (Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom0598 chi))) ∨
      (((Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom0653 chi) ∨
      (Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom1159 chi)) ∨
      ((¬Fin15AnchoredAtom2160 chi ∧
      Fin15AnchoredAtom0542 chi ∧
      Fin15AnchoredAtom0544 chi ∧
      Fin15AnchoredAtom0598 chi ∧
      Fin15AnchoredAtom0653 chi ∧
      Fin15AnchoredAtom1159 chi) ∨
      (Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom0543 chi)))) ∨
      ((((Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom0544 chi) ∨
      (Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom0599 chi)) ∨
      ((Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom0654 chi) ∨
      (Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom1160 chi))) ∨
      (((¬Fin15AnchoredAtom2161 chi ∧
      Fin15AnchoredAtom0543 chi ∧
      Fin15AnchoredAtom0544 chi ∧
      Fin15AnchoredAtom0599 chi ∧
      Fin15AnchoredAtom0654 chi ∧
      Fin15AnchoredAtom1160 chi) ∨
      (Fin15AnchoredAtom2162 chi ∧
      ¬Fin15AnchoredAtom0545 chi)) ∨
      ((Fin15AnchoredAtom2162 chi ∧
      ¬Fin15AnchoredAtom0546 chi) ∨
      (Fin15AnchoredAtom2162 chi ∧
      ¬Fin15AnchoredAtom0555 chi))))) ∨
      (((((Fin15AnchoredAtom2162 chi ∧
      ¬Fin15AnchoredAtom0655 chi) ∨
      (Fin15AnchoredAtom2162 chi ∧
      ¬Fin15AnchoredAtom1161 chi)) ∨
      ((¬Fin15AnchoredAtom2162 chi ∧
      Fin15AnchoredAtom0545 chi ∧
      Fin15AnchoredAtom0546 chi ∧
      Fin15AnchoredAtom0555 chi ∧
      Fin15AnchoredAtom0655 chi ∧
      Fin15AnchoredAtom1161 chi) ∨
      (Fin15AnchoredAtom2163 chi ∧
      ¬Fin15AnchoredAtom0545 chi))) ∨
      (((Fin15AnchoredAtom2163 chi ∧
      ¬Fin15AnchoredAtom0547 chi) ∨
      (Fin15AnchoredAtom2163 chi ∧
      ¬Fin15AnchoredAtom0556 chi)) ∨
      ((Fin15AnchoredAtom2163 chi ∧
      ¬Fin15AnchoredAtom0656 chi) ∨
      (Fin15AnchoredAtom2163 chi ∧
      ¬Fin15AnchoredAtom1162 chi)))) ∨
      ((((¬Fin15AnchoredAtom2163 chi ∧
      Fin15AnchoredAtom0545 chi ∧
      Fin15AnchoredAtom0547 chi ∧
      Fin15AnchoredAtom0556 chi ∧
      Fin15AnchoredAtom0656 chi ∧
      Fin15AnchoredAtom1162 chi) ∨
      (Fin15AnchoredAtom2164 chi ∧
      ¬Fin15AnchoredAtom0545 chi)) ∨
      ((Fin15AnchoredAtom2165 chi ∧
      ¬Fin15AnchoredAtom0545 chi) ∨
      (Fin15AnchoredAtom2165 chi ∧
      ¬Fin15AnchoredAtom0549 chi))) ∨
      (((Fin15AnchoredAtom2165 chi ∧
      ¬Fin15AnchoredAtom0558 chi) ∨
      (Fin15AnchoredAtom2165 chi ∧
      ¬Fin15AnchoredAtom0658 chi)) ∨
      ((Fin15AnchoredAtom2165 chi ∧
      ¬Fin15AnchoredAtom1164 chi) ∨
      (¬Fin15AnchoredAtom2165 chi ∧
      Fin15AnchoredAtom0545 chi ∧
      Fin15AnchoredAtom0549 chi ∧
      Fin15AnchoredAtom0558 chi ∧
      Fin15AnchoredAtom0658 chi ∧
      Fin15AnchoredAtom1164 chi)))))))))) := by
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
                exact fin15Anchored_clause16910 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16911 chi hbad
                ·
                  exact fin15Anchored_clause16912 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16913 chi hbad
                ·
                  exact fin15Anchored_clause16914 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16915 chi hbad
                ·
                  exact fin15Anchored_clause16916 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16917 chi hbad
                ·
                  exact fin15Anchored_clause16918 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16919 chi hbad
                ·
                  exact fin15Anchored_clause16920 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16921 chi hbad
                ·
                  exact fin15Anchored_clause16922 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16923 chi hbad
                ·
                  exact fin15Anchored_clause16924 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16925 chi hbad
                ·
                  exact fin15Anchored_clause16926 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16927 chi hbad
                ·
                  exact fin15Anchored_clause16928 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16929 chi hbad
                ·
                  exact fin15Anchored_clause16930 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16931 chi hbad
                ·
                  exact fin15Anchored_clause16932 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16933 chi hbad
                ·
                  exact fin15Anchored_clause16934 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16935 chi hbad
                ·
                  exact fin15Anchored_clause16936 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16937 chi hbad
                ·
                  exact fin15Anchored_clause16938 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16939 chi hbad
                ·
                  exact fin15Anchored_clause16940 chi hbad
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
                  exact fin15Anchored_clause16941 chi hbad
                ·
                  exact fin15Anchored_clause16942 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16943 chi hbad
                ·
                  exact fin15Anchored_clause16944 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16945 chi hbad
                ·
                  exact fin15Anchored_clause16946 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16947 chi hbad
                ·
                  exact fin15Anchored_clause16948 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16949 chi hbad
                ·
                  exact fin15Anchored_clause16950 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16951 chi hbad
                ·
                  exact fin15Anchored_clause16952 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16953 chi hbad
                ·
                  exact fin15Anchored_clause16954 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16955 chi hbad
                ·
                  exact fin15Anchored_clause16956 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16957 chi hbad
                ·
                  exact fin15Anchored_clause16958 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16959 chi hbad
                ·
                  exact fin15Anchored_clause16960 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16961 chi hbad
                ·
                  exact fin15Anchored_clause16962 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16963 chi hbad
                ·
                  exact fin15Anchored_clause16964 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16965 chi hbad
                ·
                  exact fin15Anchored_clause16966 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16967 chi hbad
                ·
                  exact fin15Anchored_clause16968 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16969 chi hbad
                ·
                  exact fin15Anchored_clause16970 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16971 chi hbad
                ·
                  exact fin15Anchored_clause16972 chi hbad
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
                exact fin15Anchored_clause16973 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16974 chi hbad
                ·
                  exact fin15Anchored_clause16975 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16976 chi hbad
                ·
                  exact fin15Anchored_clause16977 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16978 chi hbad
                ·
                  exact fin15Anchored_clause16979 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16980 chi hbad
                ·
                  exact fin15Anchored_clause16981 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16982 chi hbad
                ·
                  exact fin15Anchored_clause16983 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16984 chi hbad
                ·
                  exact fin15Anchored_clause16985 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16986 chi hbad
                ·
                  exact fin15Anchored_clause16987 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16988 chi hbad
                ·
                  exact fin15Anchored_clause16989 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16990 chi hbad
                ·
                  exact fin15Anchored_clause16991 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16992 chi hbad
                ·
                  exact fin15Anchored_clause16993 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16994 chi hbad
                ·
                  exact fin15Anchored_clause16995 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16996 chi hbad
                ·
                  exact fin15Anchored_clause16997 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause16998 chi hbad
                ·
                  exact fin15Anchored_clause16999 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17000 chi hbad
                ·
                  exact fin15Anchored_clause17001 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17002 chi hbad
                ·
                  exact fin15Anchored_clause17003 chi hbad
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
                  exact fin15Anchored_clause17004 chi hbad
                ·
                  exact fin15Anchored_clause17005 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17006 chi hbad
                ·
                  exact fin15Anchored_clause17007 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17008 chi hbad
                ·
                  exact fin15Anchored_clause17009 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17010 chi hbad
                ·
                  exact fin15Anchored_clause17011 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17012 chi hbad
                ·
                  exact fin15Anchored_clause17013 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17014 chi hbad
                ·
                  exact fin15Anchored_clause17015 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17016 chi hbad
                ·
                  exact fin15Anchored_clause17017 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17018 chi hbad
                ·
                  exact fin15Anchored_clause17019 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17020 chi hbad
                ·
                  exact fin15Anchored_clause17021 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17022 chi hbad
                ·
                  exact fin15Anchored_clause17023 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17024 chi hbad
                ·
                  exact fin15Anchored_clause17025 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17026 chi hbad
                ·
                  exact fin15Anchored_clause17027 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17028 chi hbad
                ·
                  exact fin15Anchored_clause17029 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17030 chi hbad
                ·
                  exact fin15Anchored_clause17031 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17032 chi hbad
                ·
                  exact fin15Anchored_clause17033 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17034 chi hbad
                ·
                  exact fin15Anchored_clause17035 chi hbad
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
                exact fin15Anchored_clause17036 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17037 chi hbad
                ·
                  exact fin15Anchored_clause17038 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17039 chi hbad
                ·
                  exact fin15Anchored_clause17040 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17041 chi hbad
                ·
                  exact fin15Anchored_clause17042 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17043 chi hbad
                ·
                  exact fin15Anchored_clause17044 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17045 chi hbad
                ·
                  exact fin15Anchored_clause17046 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17047 chi hbad
                ·
                  exact fin15Anchored_clause17048 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17049 chi hbad
                ·
                  exact fin15Anchored_clause17050 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17051 chi hbad
                ·
                  exact fin15Anchored_clause17052 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17053 chi hbad
                ·
                  exact fin15Anchored_clause17054 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17055 chi hbad
                ·
                  exact fin15Anchored_clause17056 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17057 chi hbad
                ·
                  exact fin15Anchored_clause17058 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17059 chi hbad
                ·
                  exact fin15Anchored_clause17060 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17061 chi hbad
                ·
                  exact fin15Anchored_clause17062 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17063 chi hbad
                ·
                  exact fin15Anchored_clause17064 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17065 chi hbad
                ·
                  exact fin15Anchored_clause17066 chi hbad
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
                  exact fin15Anchored_clause17067 chi hbad
                ·
                  exact fin15Anchored_clause17068 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17069 chi hbad
                ·
                  exact fin15Anchored_clause17070 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17071 chi hbad
                ·
                  exact fin15Anchored_clause17072 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17073 chi hbad
                ·
                  exact fin15Anchored_clause17074 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17075 chi hbad
                ·
                  exact fin15Anchored_clause17076 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17077 chi hbad
                ·
                  exact fin15Anchored_clause17078 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17079 chi hbad
                ·
                  exact fin15Anchored_clause17080 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17081 chi hbad
                ·
                  exact fin15Anchored_clause17082 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17083 chi hbad
                ·
                  exact fin15Anchored_clause17084 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17085 chi hbad
                ·
                  exact fin15Anchored_clause17086 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17087 chi hbad
                ·
                  exact fin15Anchored_clause17088 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17089 chi hbad
                ·
                  exact fin15Anchored_clause17090 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17091 chi hbad
                ·
                  exact fin15Anchored_clause17092 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17093 chi hbad
                ·
                  exact fin15Anchored_clause17094 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17095 chi hbad
                ·
                  exact fin15Anchored_clause17096 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17097 chi hbad
                ·
                  exact fin15Anchored_clause17098 chi hbad
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
                  exact fin15Anchored_clause17099 chi hbad
                ·
                  exact fin15Anchored_clause17100 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17101 chi hbad
                ·
                  exact fin15Anchored_clause17102 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17103 chi hbad
                ·
                  exact fin15Anchored_clause17104 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17105 chi hbad
                ·
                  exact fin15Anchored_clause17106 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17107 chi hbad
                ·
                  exact fin15Anchored_clause17108 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17109 chi hbad
                ·
                  exact fin15Anchored_clause17110 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17111 chi hbad
                ·
                  exact fin15Anchored_clause17112 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17113 chi hbad
                ·
                  exact fin15Anchored_clause17114 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17115 chi hbad
                ·
                  exact fin15Anchored_clause17116 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17117 chi hbad
                ·
                  exact fin15Anchored_clause17118 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17119 chi hbad
                ·
                  exact fin15Anchored_clause17120 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17121 chi hbad
                ·
                  exact fin15Anchored_clause17122 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17123 chi hbad
                ·
                  exact fin15Anchored_clause17124 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17125 chi hbad
                ·
                  exact fin15Anchored_clause17126 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17127 chi hbad
                ·
                  exact fin15Anchored_clause17128 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17129 chi hbad
                ·
                  exact fin15Anchored_clause17130 chi hbad
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
                  exact fin15Anchored_clause17131 chi hbad
                ·
                  exact fin15Anchored_clause17132 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17133 chi hbad
                ·
                  exact fin15Anchored_clause17134 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17135 chi hbad
                ·
                  exact fin15Anchored_clause17136 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17137 chi hbad
                ·
                  exact fin15Anchored_clause17138 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17139 chi hbad
                ·
                  exact fin15Anchored_clause17140 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17141 chi hbad
                ·
                  exact fin15Anchored_clause17142 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17143 chi hbad
                ·
                  exact fin15Anchored_clause17144 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17145 chi hbad
                ·
                  exact fin15Anchored_clause17146 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17147 chi hbad
                ·
                  exact fin15Anchored_clause17148 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17149 chi hbad
                ·
                  exact fin15Anchored_clause17150 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17151 chi hbad
                ·
                  exact fin15Anchored_clause17152 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17153 chi hbad
                ·
                  exact fin15Anchored_clause17154 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17155 chi hbad
                ·
                  exact fin15Anchored_clause17156 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17157 chi hbad
                ·
                  exact fin15Anchored_clause17158 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17159 chi hbad
                ·
                  exact fin15Anchored_clause17160 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17161 chi hbad
                ·
                  exact fin15Anchored_clause17162 chi hbad

end ErdosSzekeres

end
