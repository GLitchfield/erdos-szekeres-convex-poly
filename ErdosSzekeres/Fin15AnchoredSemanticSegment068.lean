module

public import ErdosSzekeres.Fin15AnchoredClauseChunk134
public import ErdosSzekeres.Fin15AnchoredClauseChunk135
public import ErdosSzekeres.Fin15AnchoredClauseChunk136

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 068. -/

theorem fin15Anchored_rejectSemanticSegment068
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom2166 chi ∧
      ¬Fin15AnchoredAtom0545 chi) ∨
      ((Fin15AnchoredAtom2166 chi ∧
      ¬Fin15AnchoredAtom0550 chi) ∨
      (Fin15AnchoredAtom2166 chi ∧
      ¬Fin15AnchoredAtom0559 chi))) ∨
      (((Fin15AnchoredAtom2166 chi ∧
      ¬Fin15AnchoredAtom0659 chi) ∨
      (Fin15AnchoredAtom2166 chi ∧
      ¬Fin15AnchoredAtom1165 chi)) ∨
      ((¬Fin15AnchoredAtom2166 chi ∧
      Fin15AnchoredAtom0545 chi ∧
      Fin15AnchoredAtom0550 chi ∧
      Fin15AnchoredAtom0559 chi ∧
      Fin15AnchoredAtom0659 chi ∧
      Fin15AnchoredAtom1165 chi) ∨
      (Fin15AnchoredAtom2167 chi ∧
      ¬Fin15AnchoredAtom0545 chi)))) ∨
      ((((Fin15AnchoredAtom2167 chi ∧
      ¬Fin15AnchoredAtom0660 chi) ∨
      (Fin15AnchoredAtom2167 chi ∧
      ¬Fin15AnchoredAtom1166 chi)) ∨
      ((¬Fin15AnchoredAtom2167 chi ∧
      Fin15AnchoredAtom0545 chi ∧
      Fin15AnchoredAtom0551 chi ∧
      Fin15AnchoredAtom0560 chi ∧
      Fin15AnchoredAtom0660 chi ∧
      Fin15AnchoredAtom1166 chi) ∨
      (Fin15AnchoredAtom2168 chi ∧
      ¬Fin15AnchoredAtom0545 chi))) ∨
      (((Fin15AnchoredAtom2168 chi ∧
      ¬Fin15AnchoredAtom0552 chi) ∨
      (Fin15AnchoredAtom2168 chi ∧
      ¬Fin15AnchoredAtom0561 chi)) ∨
      ((Fin15AnchoredAtom2168 chi ∧
      ¬Fin15AnchoredAtom0661 chi) ∨
      (Fin15AnchoredAtom2168 chi ∧
      ¬Fin15AnchoredAtom1167 chi))))) ∨
      (((((¬Fin15AnchoredAtom2168 chi ∧
      Fin15AnchoredAtom0545 chi ∧
      Fin15AnchoredAtom0552 chi ∧
      Fin15AnchoredAtom0561 chi ∧
      Fin15AnchoredAtom0661 chi ∧
      Fin15AnchoredAtom1167 chi) ∨
      (Fin15AnchoredAtom2169 chi ∧
      ¬Fin15AnchoredAtom0545 chi)) ∨
      ((Fin15AnchoredAtom2169 chi ∧
      ¬Fin15AnchoredAtom0553 chi) ∨
      (Fin15AnchoredAtom2169 chi ∧
      ¬Fin15AnchoredAtom0562 chi))) ∨
      (((Fin15AnchoredAtom2169 chi ∧
      ¬Fin15AnchoredAtom0662 chi) ∨
      (Fin15AnchoredAtom2169 chi ∧
      ¬Fin15AnchoredAtom1168 chi)) ∨
      ((¬Fin15AnchoredAtom2169 chi ∧
      Fin15AnchoredAtom0545 chi ∧
      Fin15AnchoredAtom0553 chi ∧
      Fin15AnchoredAtom0562 chi ∧
      Fin15AnchoredAtom0662 chi ∧
      Fin15AnchoredAtom1168 chi) ∨
      (Fin15AnchoredAtom2170 chi ∧
      ¬Fin15AnchoredAtom0545 chi)))) ∨
      ((((Fin15AnchoredAtom2170 chi ∧
      ¬Fin15AnchoredAtom0554 chi) ∨
      (Fin15AnchoredAtom2170 chi ∧
      ¬Fin15AnchoredAtom0563 chi)) ∨
      ((Fin15AnchoredAtom2170 chi ∧
      ¬Fin15AnchoredAtom0663 chi) ∨
      (Fin15AnchoredAtom2170 chi ∧
      ¬Fin15AnchoredAtom1169 chi))) ∨
      (((¬Fin15AnchoredAtom2170 chi ∧
      Fin15AnchoredAtom0545 chi ∧
      Fin15AnchoredAtom0554 chi ∧
      Fin15AnchoredAtom0563 chi ∧
      Fin15AnchoredAtom0663 chi ∧
      Fin15AnchoredAtom1169 chi) ∨
      (Fin15AnchoredAtom2171 chi ∧
      ¬Fin15AnchoredAtom0546 chi)) ∨
      ((Fin15AnchoredAtom2171 chi ∧
      ¬Fin15AnchoredAtom0547 chi) ∨
      (Fin15AnchoredAtom2171 chi ∧
      ¬Fin15AnchoredAtom0564 chi)))))) ∨
      ((((((Fin15AnchoredAtom2171 chi ∧
      ¬Fin15AnchoredAtom0664 chi) ∨
      (Fin15AnchoredAtom2171 chi ∧
      ¬Fin15AnchoredAtom1170 chi)) ∨
      ((¬Fin15AnchoredAtom2171 chi ∧
      Fin15AnchoredAtom0546 chi ∧
      Fin15AnchoredAtom0547 chi ∧
      Fin15AnchoredAtom0564 chi ∧
      Fin15AnchoredAtom0664 chi ∧
      Fin15AnchoredAtom1170 chi) ∨
      (Fin15AnchoredAtom2172 chi ∧
      ¬Fin15AnchoredAtom0565 chi))) ∨
      (((Fin15AnchoredAtom2172 chi ∧
      ¬Fin15AnchoredAtom0665 chi) ∨
      (¬Fin15AnchoredAtom2172 chi ∧
      Fin15AnchoredAtom0546 chi ∧
      Fin15AnchoredAtom0548 chi ∧
      Fin15AnchoredAtom0565 chi ∧
      Fin15AnchoredAtom0665 chi ∧
      Fin15AnchoredAtom1171 chi)) ∨
      ((Fin15AnchoredAtom2173 chi ∧
      ¬Fin15AnchoredAtom0546 chi) ∨
      (Fin15AnchoredAtom2173 chi ∧
      ¬Fin15AnchoredAtom0549 chi)))) ∨
      ((((Fin15AnchoredAtom2173 chi ∧
      ¬Fin15AnchoredAtom0566 chi) ∨
      (Fin15AnchoredAtom2173 chi ∧
      ¬Fin15AnchoredAtom0666 chi)) ∨
      ((Fin15AnchoredAtom2173 chi ∧
      ¬Fin15AnchoredAtom1172 chi) ∨
      (¬Fin15AnchoredAtom2173 chi ∧
      Fin15AnchoredAtom0546 chi ∧
      Fin15AnchoredAtom0549 chi ∧
      Fin15AnchoredAtom0566 chi ∧
      Fin15AnchoredAtom0666 chi ∧
      Fin15AnchoredAtom1172 chi))) ∨
      (((Fin15AnchoredAtom2174 chi ∧
      ¬Fin15AnchoredAtom0546 chi) ∨
      (Fin15AnchoredAtom2174 chi ∧
      ¬Fin15AnchoredAtom0550 chi)) ∨
      ((Fin15AnchoredAtom2174 chi ∧
      ¬Fin15AnchoredAtom0567 chi) ∨
      (Fin15AnchoredAtom2174 chi ∧
      ¬Fin15AnchoredAtom0667 chi))))) ∨
      (((((Fin15AnchoredAtom2174 chi ∧
      ¬Fin15AnchoredAtom1173 chi) ∨
      (¬Fin15AnchoredAtom2174 chi ∧
      Fin15AnchoredAtom0546 chi ∧
      Fin15AnchoredAtom0550 chi ∧
      Fin15AnchoredAtom0567 chi ∧
      Fin15AnchoredAtom0667 chi ∧
      Fin15AnchoredAtom1173 chi)) ∨
      ((Fin15AnchoredAtom2175 chi ∧
      ¬Fin15AnchoredAtom0546 chi) ∨
      (Fin15AnchoredAtom2176 chi ∧
      ¬Fin15AnchoredAtom0546 chi))) ∨
      (((Fin15AnchoredAtom2176 chi ∧
      ¬Fin15AnchoredAtom0552 chi) ∨
      (Fin15AnchoredAtom2176 chi ∧
      ¬Fin15AnchoredAtom0569 chi)) ∨
      ((Fin15AnchoredAtom2176 chi ∧
      ¬Fin15AnchoredAtom0669 chi) ∨
      (Fin15AnchoredAtom2176 chi ∧
      ¬Fin15AnchoredAtom1175 chi)))) ∨
      ((((¬Fin15AnchoredAtom2176 chi ∧
      Fin15AnchoredAtom0546 chi ∧
      Fin15AnchoredAtom0552 chi ∧
      Fin15AnchoredAtom0569 chi ∧
      Fin15AnchoredAtom0669 chi ∧
      Fin15AnchoredAtom1175 chi) ∨
      (Fin15AnchoredAtom2177 chi ∧
      ¬Fin15AnchoredAtom0546 chi)) ∨
      ((Fin15AnchoredAtom2177 chi ∧
      ¬Fin15AnchoredAtom0553 chi) ∨
      (Fin15AnchoredAtom2177 chi ∧
      ¬Fin15AnchoredAtom0570 chi))) ∨
      (((Fin15AnchoredAtom2177 chi ∧
      ¬Fin15AnchoredAtom0670 chi) ∨
      (Fin15AnchoredAtom2177 chi ∧
      ¬Fin15AnchoredAtom1176 chi)) ∨
      ((¬Fin15AnchoredAtom2177 chi ∧
      Fin15AnchoredAtom0546 chi ∧
      Fin15AnchoredAtom0553 chi ∧
      Fin15AnchoredAtom0570 chi ∧
      Fin15AnchoredAtom0670 chi ∧
      Fin15AnchoredAtom1176 chi) ∨
      (Fin15AnchoredAtom2178 chi ∧
      ¬Fin15AnchoredAtom0546 chi))))))) ∨
      ((((((Fin15AnchoredAtom2178 chi ∧
      ¬Fin15AnchoredAtom0554 chi) ∨
      ((Fin15AnchoredAtom2178 chi ∧
      ¬Fin15AnchoredAtom0571 chi) ∨
      (Fin15AnchoredAtom2178 chi ∧
      ¬Fin15AnchoredAtom0671 chi))) ∨
      (((Fin15AnchoredAtom2178 chi ∧
      ¬Fin15AnchoredAtom1177 chi) ∨
      (¬Fin15AnchoredAtom2178 chi ∧
      Fin15AnchoredAtom0546 chi ∧
      Fin15AnchoredAtom0554 chi ∧
      Fin15AnchoredAtom0571 chi ∧
      Fin15AnchoredAtom0671 chi ∧
      Fin15AnchoredAtom1177 chi)) ∨
      ((Fin15AnchoredAtom2179 chi ∧
      ¬Fin15AnchoredAtom0547 chi) ∨
      (Fin15AnchoredAtom2179 chi ∧
      ¬Fin15AnchoredAtom0672 chi)))) ∨
      ((((Fin15AnchoredAtom2179 chi ∧
      ¬Fin15AnchoredAtom1178 chi) ∨
      (¬Fin15AnchoredAtom2179 chi ∧
      Fin15AnchoredAtom0547 chi ∧
      Fin15AnchoredAtom0548 chi ∧
      Fin15AnchoredAtom0572 chi ∧
      Fin15AnchoredAtom0672 chi ∧
      Fin15AnchoredAtom1178 chi)) ∨
      ((Fin15AnchoredAtom2180 chi ∧
      ¬Fin15AnchoredAtom0547 chi) ∨
      (Fin15AnchoredAtom2180 chi ∧
      ¬Fin15AnchoredAtom0549 chi))) ∨
      (((Fin15AnchoredAtom2180 chi ∧
      ¬Fin15AnchoredAtom0573 chi) ∨
      (Fin15AnchoredAtom2180 chi ∧
      ¬Fin15AnchoredAtom0673 chi)) ∨
      ((Fin15AnchoredAtom2180 chi ∧
      ¬Fin15AnchoredAtom1179 chi) ∨
      (¬Fin15AnchoredAtom2180 chi ∧
      Fin15AnchoredAtom0547 chi ∧
      Fin15AnchoredAtom0549 chi ∧
      Fin15AnchoredAtom0573 chi ∧
      Fin15AnchoredAtom0673 chi ∧
      Fin15AnchoredAtom1179 chi))))) ∨
      (((((Fin15AnchoredAtom2181 chi ∧
      ¬Fin15AnchoredAtom0547 chi) ∨
      (Fin15AnchoredAtom2181 chi ∧
      ¬Fin15AnchoredAtom0550 chi)) ∨
      ((Fin15AnchoredAtom2181 chi ∧
      ¬Fin15AnchoredAtom0574 chi) ∨
      (Fin15AnchoredAtom2181 chi ∧
      ¬Fin15AnchoredAtom0674 chi))) ∨
      (((Fin15AnchoredAtom2181 chi ∧
      ¬Fin15AnchoredAtom1180 chi) ∨
      (¬Fin15AnchoredAtom2181 chi ∧
      Fin15AnchoredAtom0547 chi ∧
      Fin15AnchoredAtom0550 chi ∧
      Fin15AnchoredAtom0574 chi ∧
      Fin15AnchoredAtom0674 chi ∧
      Fin15AnchoredAtom1180 chi)) ∨
      ((Fin15AnchoredAtom2182 chi ∧
      ¬Fin15AnchoredAtom0547 chi) ∨
      (Fin15AnchoredAtom2182 chi ∧
      ¬Fin15AnchoredAtom0675 chi)))) ∨
      ((((¬Fin15AnchoredAtom2182 chi ∧
      Fin15AnchoredAtom0547 chi ∧
      Fin15AnchoredAtom0551 chi ∧
      Fin15AnchoredAtom0575 chi ∧
      Fin15AnchoredAtom0675 chi ∧
      Fin15AnchoredAtom1181 chi) ∨
      (Fin15AnchoredAtom2183 chi ∧
      ¬Fin15AnchoredAtom0547 chi)) ∨
      ((Fin15AnchoredAtom2183 chi ∧
      ¬Fin15AnchoredAtom0552 chi) ∨
      (Fin15AnchoredAtom2183 chi ∧
      ¬Fin15AnchoredAtom0576 chi))) ∨
      (((Fin15AnchoredAtom2183 chi ∧
      ¬Fin15AnchoredAtom0676 chi) ∨
      (Fin15AnchoredAtom2183 chi ∧
      ¬Fin15AnchoredAtom1182 chi)) ∨
      ((¬Fin15AnchoredAtom2183 chi ∧
      Fin15AnchoredAtom0547 chi ∧
      Fin15AnchoredAtom0552 chi ∧
      Fin15AnchoredAtom0576 chi ∧
      Fin15AnchoredAtom0676 chi ∧
      Fin15AnchoredAtom1182 chi) ∨
      (Fin15AnchoredAtom2184 chi ∧
      ¬Fin15AnchoredAtom0547 chi)))))) ∨
      ((((((Fin15AnchoredAtom2184 chi ∧
      ¬Fin15AnchoredAtom0553 chi) ∨
      (Fin15AnchoredAtom2184 chi ∧
      ¬Fin15AnchoredAtom0577 chi)) ∨
      ((Fin15AnchoredAtom2184 chi ∧
      ¬Fin15AnchoredAtom0677 chi) ∨
      (Fin15AnchoredAtom2184 chi ∧
      ¬Fin15AnchoredAtom1183 chi))) ∨
      (((¬Fin15AnchoredAtom2184 chi ∧
      Fin15AnchoredAtom0547 chi ∧
      Fin15AnchoredAtom0553 chi ∧
      Fin15AnchoredAtom0577 chi ∧
      Fin15AnchoredAtom0677 chi ∧
      Fin15AnchoredAtom1183 chi) ∨
      (Fin15AnchoredAtom2185 chi ∧
      ¬Fin15AnchoredAtom0547 chi)) ∨
      ((Fin15AnchoredAtom2185 chi ∧
      ¬Fin15AnchoredAtom0554 chi) ∨
      (Fin15AnchoredAtom2185 chi ∧
      ¬Fin15AnchoredAtom0578 chi)))) ∨
      ((((Fin15AnchoredAtom2185 chi ∧
      ¬Fin15AnchoredAtom0678 chi) ∨
      (Fin15AnchoredAtom2185 chi ∧
      ¬Fin15AnchoredAtom1184 chi)) ∨
      ((¬Fin15AnchoredAtom2185 chi ∧
      Fin15AnchoredAtom0547 chi ∧
      Fin15AnchoredAtom0554 chi ∧
      Fin15AnchoredAtom0578 chi ∧
      Fin15AnchoredAtom0678 chi ∧
      Fin15AnchoredAtom1184 chi) ∨
      (Fin15AnchoredAtom2186 chi ∧
      ¬Fin15AnchoredAtom0549 chi))) ∨
      (((Fin15AnchoredAtom2186 chi ∧
      ¬Fin15AnchoredAtom0579 chi) ∨
      (Fin15AnchoredAtom2186 chi ∧
      ¬Fin15AnchoredAtom1185 chi)) ∨
      ((¬Fin15AnchoredAtom2186 chi ∧
      Fin15AnchoredAtom0548 chi ∧
      Fin15AnchoredAtom0549 chi ∧
      Fin15AnchoredAtom0579 chi ∧
      Fin15AnchoredAtom0679 chi ∧
      Fin15AnchoredAtom1185 chi) ∨
      (Fin15AnchoredAtom2187 chi ∧
      ¬Fin15AnchoredAtom0550 chi))))) ∨
      (((((Fin15AnchoredAtom2187 chi ∧
      ¬Fin15AnchoredAtom1186 chi) ∨
      (¬Fin15AnchoredAtom2187 chi ∧
      Fin15AnchoredAtom0548 chi ∧
      Fin15AnchoredAtom0550 chi ∧
      Fin15AnchoredAtom0580 chi ∧
      Fin15AnchoredAtom0680 chi ∧
      Fin15AnchoredAtom1186 chi)) ∨
      ((Fin15AnchoredAtom2189 chi ∧
      ¬Fin15AnchoredAtom0552 chi) ∨
      (¬Fin15AnchoredAtom2189 chi ∧
      Fin15AnchoredAtom0548 chi ∧
      Fin15AnchoredAtom0552 chi ∧
      Fin15AnchoredAtom0582 chi ∧
      Fin15AnchoredAtom0682 chi ∧
      Fin15AnchoredAtom1188 chi))) ∨
      (((Fin15AnchoredAtom2190 chi ∧
      ¬Fin15AnchoredAtom0583 chi) ∨
      (Fin15AnchoredAtom2191 chi ∧
      ¬Fin15AnchoredAtom0548 chi)) ∨
      ((Fin15AnchoredAtom2191 chi ∧
      ¬Fin15AnchoredAtom0554 chi) ∨
      (Fin15AnchoredAtom2191 chi ∧
      ¬Fin15AnchoredAtom0584 chi)))) ∨
      ((((Fin15AnchoredAtom2191 chi ∧
      ¬Fin15AnchoredAtom0684 chi) ∨
      (Fin15AnchoredAtom2191 chi ∧
      ¬Fin15AnchoredAtom1190 chi)) ∨
      ((¬Fin15AnchoredAtom2191 chi ∧
      Fin15AnchoredAtom0548 chi ∧
      Fin15AnchoredAtom0554 chi ∧
      Fin15AnchoredAtom0584 chi ∧
      Fin15AnchoredAtom0684 chi ∧
      Fin15AnchoredAtom1190 chi) ∨
      (Fin15AnchoredAtom2192 chi ∧
      ¬Fin15AnchoredAtom0549 chi))) ∨
      (((Fin15AnchoredAtom2192 chi ∧
      ¬Fin15AnchoredAtom0550 chi) ∨
      (Fin15AnchoredAtom2192 chi ∧
      ¬Fin15AnchoredAtom0585 chi)) ∨
      ((Fin15AnchoredAtom2192 chi ∧
      ¬Fin15AnchoredAtom0685 chi) ∨
      (Fin15AnchoredAtom2192 chi ∧
      ¬Fin15AnchoredAtom1191 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom2192 chi ∧
      Fin15AnchoredAtom0549 chi ∧
      Fin15AnchoredAtom0550 chi ∧
      Fin15AnchoredAtom0585 chi ∧
      Fin15AnchoredAtom0685 chi ∧
      Fin15AnchoredAtom1191 chi) ∨
      ((Fin15AnchoredAtom2193 chi ∧
      ¬Fin15AnchoredAtom0549 chi) ∨
      (Fin15AnchoredAtom2193 chi ∧
      ¬Fin15AnchoredAtom0551 chi))) ∨
      (((Fin15AnchoredAtom2193 chi ∧
      ¬Fin15AnchoredAtom0686 chi) ∨
      (Fin15AnchoredAtom2194 chi ∧
      ¬Fin15AnchoredAtom0549 chi)) ∨
      ((Fin15AnchoredAtom2194 chi ∧
      ¬Fin15AnchoredAtom0552 chi) ∨
      (Fin15AnchoredAtom2194 chi ∧
      ¬Fin15AnchoredAtom0587 chi)))) ∨
      ((((Fin15AnchoredAtom2194 chi ∧
      ¬Fin15AnchoredAtom0687 chi) ∨
      (Fin15AnchoredAtom2194 chi ∧
      ¬Fin15AnchoredAtom1193 chi)) ∨
      ((¬Fin15AnchoredAtom2194 chi ∧
      Fin15AnchoredAtom0549 chi ∧
      Fin15AnchoredAtom0552 chi ∧
      Fin15AnchoredAtom0587 chi ∧
      Fin15AnchoredAtom0687 chi ∧
      Fin15AnchoredAtom1193 chi) ∨
      (Fin15AnchoredAtom2195 chi ∧
      ¬Fin15AnchoredAtom0549 chi))) ∨
      (((Fin15AnchoredAtom2195 chi ∧
      ¬Fin15AnchoredAtom0553 chi) ∨
      (Fin15AnchoredAtom2195 chi ∧
      ¬Fin15AnchoredAtom0588 chi)) ∨
      ((Fin15AnchoredAtom2195 chi ∧
      ¬Fin15AnchoredAtom0688 chi) ∨
      (Fin15AnchoredAtom2195 chi ∧
      ¬Fin15AnchoredAtom1194 chi))))) ∨
      (((((¬Fin15AnchoredAtom2195 chi ∧
      Fin15AnchoredAtom0549 chi ∧
      Fin15AnchoredAtom0553 chi ∧
      Fin15AnchoredAtom0588 chi ∧
      Fin15AnchoredAtom0688 chi ∧
      Fin15AnchoredAtom1194 chi) ∨
      (Fin15AnchoredAtom2196 chi ∧
      ¬Fin15AnchoredAtom0549 chi)) ∨
      ((Fin15AnchoredAtom2196 chi ∧
      ¬Fin15AnchoredAtom0554 chi) ∨
      (Fin15AnchoredAtom2196 chi ∧
      ¬Fin15AnchoredAtom0589 chi))) ∨
      (((Fin15AnchoredAtom2196 chi ∧
      ¬Fin15AnchoredAtom0689 chi) ∨
      (Fin15AnchoredAtom2196 chi ∧
      ¬Fin15AnchoredAtom1195 chi)) ∨
      ((¬Fin15AnchoredAtom2196 chi ∧
      Fin15AnchoredAtom0549 chi ∧
      Fin15AnchoredAtom0554 chi ∧
      Fin15AnchoredAtom0589 chi ∧
      Fin15AnchoredAtom0689 chi ∧
      Fin15AnchoredAtom1195 chi) ∨
      (Fin15AnchoredAtom2197 chi ∧
      ¬Fin15AnchoredAtom0550 chi)))) ∨
      ((((Fin15AnchoredAtom2198 chi ∧
      ¬Fin15AnchoredAtom0550 chi) ∨
      (Fin15AnchoredAtom2198 chi ∧
      ¬Fin15AnchoredAtom0552 chi)) ∨
      ((Fin15AnchoredAtom2198 chi ∧
      ¬Fin15AnchoredAtom0591 chi) ∨
      (Fin15AnchoredAtom2198 chi ∧
      ¬Fin15AnchoredAtom0691 chi))) ∨
      (((Fin15AnchoredAtom2198 chi ∧
      ¬Fin15AnchoredAtom1197 chi) ∨
      (¬Fin15AnchoredAtom2198 chi ∧
      Fin15AnchoredAtom0550 chi ∧
      Fin15AnchoredAtom0552 chi ∧
      Fin15AnchoredAtom0591 chi ∧
      Fin15AnchoredAtom0691 chi ∧
      Fin15AnchoredAtom1197 chi)) ∨
      ((Fin15AnchoredAtom2199 chi ∧
      ¬Fin15AnchoredAtom0550 chi) ∨
      (Fin15AnchoredAtom2199 chi ∧
      ¬Fin15AnchoredAtom0553 chi)))))) ∨
      ((((((Fin15AnchoredAtom2199 chi ∧
      ¬Fin15AnchoredAtom0592 chi) ∨
      (Fin15AnchoredAtom2199 chi ∧
      ¬Fin15AnchoredAtom0692 chi)) ∨
      ((Fin15AnchoredAtom2199 chi ∧
      ¬Fin15AnchoredAtom1198 chi) ∨
      (¬Fin15AnchoredAtom2199 chi ∧
      Fin15AnchoredAtom0550 chi ∧
      Fin15AnchoredAtom0553 chi ∧
      Fin15AnchoredAtom0592 chi ∧
      Fin15AnchoredAtom0692 chi ∧
      Fin15AnchoredAtom1198 chi))) ∨
      (((Fin15AnchoredAtom2200 chi ∧
      ¬Fin15AnchoredAtom0550 chi) ∨
      (Fin15AnchoredAtom2200 chi ∧
      ¬Fin15AnchoredAtom0554 chi)) ∨
      ((Fin15AnchoredAtom2200 chi ∧
      ¬Fin15AnchoredAtom0593 chi) ∨
      (Fin15AnchoredAtom2200 chi ∧
      ¬Fin15AnchoredAtom0693 chi)))) ∨
      ((((Fin15AnchoredAtom2200 chi ∧
      ¬Fin15AnchoredAtom1199 chi) ∨
      (¬Fin15AnchoredAtom2200 chi ∧
      Fin15AnchoredAtom0550 chi ∧
      Fin15AnchoredAtom0554 chi ∧
      Fin15AnchoredAtom0593 chi ∧
      Fin15AnchoredAtom0693 chi ∧
      Fin15AnchoredAtom1199 chi)) ∨
      ((Fin15AnchoredAtom2201 chi ∧
      ¬Fin15AnchoredAtom0551 chi) ∨
      (Fin15AnchoredAtom2201 chi ∧
      ¬Fin15AnchoredAtom0552 chi))) ∨
      (((Fin15AnchoredAtom2201 chi ∧
      ¬Fin15AnchoredAtom0694 chi) ∨
      (Fin15AnchoredAtom2201 chi ∧
      ¬Fin15AnchoredAtom1200 chi)) ∨
      ((¬Fin15AnchoredAtom2201 chi ∧
      Fin15AnchoredAtom0551 chi ∧
      Fin15AnchoredAtom0552 chi ∧
      Fin15AnchoredAtom0594 chi ∧
      Fin15AnchoredAtom0694 chi ∧
      Fin15AnchoredAtom1200 chi) ∨
      (Fin15AnchoredAtom2202 chi ∧
      ¬Fin15AnchoredAtom0551 chi))))) ∨
      (((((Fin15AnchoredAtom2202 chi ∧
      ¬Fin15AnchoredAtom0553 chi) ∨
      (Fin15AnchoredAtom2203 chi ∧
      ¬Fin15AnchoredAtom0554 chi)) ∨
      ((Fin15AnchoredAtom2204 chi ∧
      ¬Fin15AnchoredAtom0552 chi) ∨
      (Fin15AnchoredAtom2204 chi ∧
      ¬Fin15AnchoredAtom0553 chi))) ∨
      (((Fin15AnchoredAtom2204 chi ∧
      ¬Fin15AnchoredAtom0597 chi) ∨
      (Fin15AnchoredAtom2204 chi ∧
      ¬Fin15AnchoredAtom0697 chi)) ∨
      ((Fin15AnchoredAtom2204 chi ∧
      ¬Fin15AnchoredAtom1203 chi) ∨
      (¬Fin15AnchoredAtom2204 chi ∧
      Fin15AnchoredAtom0552 chi ∧
      Fin15AnchoredAtom0553 chi ∧
      Fin15AnchoredAtom0597 chi ∧
      Fin15AnchoredAtom0697 chi ∧
      Fin15AnchoredAtom1203 chi)))) ∨
      ((((Fin15AnchoredAtom2205 chi ∧
      ¬Fin15AnchoredAtom0552 chi) ∨
      (Fin15AnchoredAtom2205 chi ∧
      ¬Fin15AnchoredAtom0554 chi)) ∨
      ((Fin15AnchoredAtom2205 chi ∧
      ¬Fin15AnchoredAtom0598 chi) ∨
      (Fin15AnchoredAtom2205 chi ∧
      ¬Fin15AnchoredAtom0698 chi))) ∨
      (((Fin15AnchoredAtom2205 chi ∧
      ¬Fin15AnchoredAtom1204 chi) ∨
      (¬Fin15AnchoredAtom2205 chi ∧
      Fin15AnchoredAtom0552 chi ∧
      Fin15AnchoredAtom0554 chi ∧
      Fin15AnchoredAtom0598 chi ∧
      Fin15AnchoredAtom0698 chi ∧
      Fin15AnchoredAtom1204 chi)) ∨
      ((Fin15AnchoredAtom2206 chi ∧
      ¬Fin15AnchoredAtom0553 chi) ∨
      (Fin15AnchoredAtom2206 chi ∧
      ¬Fin15AnchoredAtom0554 chi))))))) ∨
      ((((((Fin15AnchoredAtom2206 chi ∧
      ¬Fin15AnchoredAtom0599 chi) ∨
      ((Fin15AnchoredAtom2206 chi ∧
      ¬Fin15AnchoredAtom0699 chi) ∨
      (Fin15AnchoredAtom2206 chi ∧
      ¬Fin15AnchoredAtom1205 chi))) ∨
      (((¬Fin15AnchoredAtom2206 chi ∧
      Fin15AnchoredAtom0553 chi ∧
      Fin15AnchoredAtom0554 chi ∧
      Fin15AnchoredAtom0599 chi ∧
      Fin15AnchoredAtom0699 chi ∧
      Fin15AnchoredAtom1205 chi) ∨
      (Fin15AnchoredAtom2207 chi ∧
      ¬Fin15AnchoredAtom0555 chi)) ∨
      ((Fin15AnchoredAtom2207 chi ∧
      ¬Fin15AnchoredAtom0556 chi) ∨
      (Fin15AnchoredAtom2207 chi ∧
      ¬Fin15AnchoredAtom0564 chi)))) ∨
      ((((Fin15AnchoredAtom2207 chi ∧
      ¬Fin15AnchoredAtom0700 chi) ∨
      (Fin15AnchoredAtom2207 chi ∧
      ¬Fin15AnchoredAtom1206 chi)) ∨
      ((¬Fin15AnchoredAtom2207 chi ∧
      Fin15AnchoredAtom0555 chi ∧
      Fin15AnchoredAtom0556 chi ∧
      Fin15AnchoredAtom0564 chi ∧
      Fin15AnchoredAtom0700 chi ∧
      Fin15AnchoredAtom1206 chi) ∨
      (Fin15AnchoredAtom2208 chi ∧
      ¬Fin15AnchoredAtom0701 chi))) ∨
      (((¬Fin15AnchoredAtom2208 chi ∧
      Fin15AnchoredAtom0555 chi ∧
      Fin15AnchoredAtom0557 chi ∧
      Fin15AnchoredAtom0565 chi ∧
      Fin15AnchoredAtom0701 chi ∧
      Fin15AnchoredAtom1207 chi) ∨
      (Fin15AnchoredAtom2209 chi ∧
      ¬Fin15AnchoredAtom0555 chi)) ∨
      ((Fin15AnchoredAtom2209 chi ∧
      ¬Fin15AnchoredAtom0558 chi) ∨
      (Fin15AnchoredAtom2209 chi ∧
      ¬Fin15AnchoredAtom0566 chi))))) ∨
      (((((Fin15AnchoredAtom2209 chi ∧
      ¬Fin15AnchoredAtom0702 chi) ∨
      (Fin15AnchoredAtom2209 chi ∧
      ¬Fin15AnchoredAtom1208 chi)) ∨
      ((¬Fin15AnchoredAtom2209 chi ∧
      Fin15AnchoredAtom0555 chi ∧
      Fin15AnchoredAtom0558 chi ∧
      Fin15AnchoredAtom0566 chi ∧
      Fin15AnchoredAtom0702 chi ∧
      Fin15AnchoredAtom1208 chi) ∨
      (Fin15AnchoredAtom2210 chi ∧
      ¬Fin15AnchoredAtom0555 chi))) ∨
      (((Fin15AnchoredAtom2210 chi ∧
      ¬Fin15AnchoredAtom0559 chi) ∨
      (Fin15AnchoredAtom2210 chi ∧
      ¬Fin15AnchoredAtom0567 chi)) ∨
      ((Fin15AnchoredAtom2210 chi ∧
      ¬Fin15AnchoredAtom0703 chi) ∨
      (Fin15AnchoredAtom2210 chi ∧
      ¬Fin15AnchoredAtom1209 chi)))) ∨
      ((((¬Fin15AnchoredAtom2210 chi ∧
      Fin15AnchoredAtom0555 chi ∧
      Fin15AnchoredAtom0559 chi ∧
      Fin15AnchoredAtom0567 chi ∧
      Fin15AnchoredAtom0703 chi ∧
      Fin15AnchoredAtom1209 chi) ∨
      (Fin15AnchoredAtom2211 chi ∧
      ¬Fin15AnchoredAtom0555 chi)) ∨
      ((Fin15AnchoredAtom2211 chi ∧
      ¬Fin15AnchoredAtom0560 chi) ∨
      (Fin15AnchoredAtom2211 chi ∧
      ¬Fin15AnchoredAtom0704 chi))) ∨
      (((Fin15AnchoredAtom2211 chi ∧
      ¬Fin15AnchoredAtom1210 chi) ∨
      (¬Fin15AnchoredAtom2211 chi ∧
      Fin15AnchoredAtom0555 chi ∧
      Fin15AnchoredAtom0560 chi ∧
      Fin15AnchoredAtom0568 chi ∧
      Fin15AnchoredAtom0704 chi ∧
      Fin15AnchoredAtom1210 chi)) ∨
      ((Fin15AnchoredAtom2212 chi ∧
      ¬Fin15AnchoredAtom0555 chi) ∨
      (Fin15AnchoredAtom2212 chi ∧
      ¬Fin15AnchoredAtom0561 chi)))))) ∨
      ((((((Fin15AnchoredAtom2212 chi ∧
      ¬Fin15AnchoredAtom0569 chi) ∨
      (Fin15AnchoredAtom2212 chi ∧
      ¬Fin15AnchoredAtom0705 chi)) ∨
      ((Fin15AnchoredAtom2212 chi ∧
      ¬Fin15AnchoredAtom1211 chi) ∨
      (¬Fin15AnchoredAtom2212 chi ∧
      Fin15AnchoredAtom0555 chi ∧
      Fin15AnchoredAtom0561 chi ∧
      Fin15AnchoredAtom0569 chi ∧
      Fin15AnchoredAtom0705 chi ∧
      Fin15AnchoredAtom1211 chi))) ∨
      (((Fin15AnchoredAtom2213 chi ∧
      ¬Fin15AnchoredAtom0555 chi) ∨
      (Fin15AnchoredAtom2213 chi ∧
      ¬Fin15AnchoredAtom0562 chi)) ∨
      ((Fin15AnchoredAtom2213 chi ∧
      ¬Fin15AnchoredAtom0570 chi) ∨
      (Fin15AnchoredAtom2213 chi ∧
      ¬Fin15AnchoredAtom0706 chi)))) ∨
      ((((Fin15AnchoredAtom2213 chi ∧
      ¬Fin15AnchoredAtom1212 chi) ∨
      (¬Fin15AnchoredAtom2213 chi ∧
      Fin15AnchoredAtom0555 chi ∧
      Fin15AnchoredAtom0562 chi ∧
      Fin15AnchoredAtom0570 chi ∧
      Fin15AnchoredAtom0706 chi ∧
      Fin15AnchoredAtom1212 chi)) ∨
      ((Fin15AnchoredAtom2214 chi ∧
      ¬Fin15AnchoredAtom0555 chi) ∨
      (Fin15AnchoredAtom2214 chi ∧
      ¬Fin15AnchoredAtom0563 chi))) ∨
      (((Fin15AnchoredAtom2214 chi ∧
      ¬Fin15AnchoredAtom0571 chi) ∨
      (Fin15AnchoredAtom2214 chi ∧
      ¬Fin15AnchoredAtom0707 chi)) ∨
      ((Fin15AnchoredAtom2214 chi ∧
      ¬Fin15AnchoredAtom1213 chi) ∨
      (¬Fin15AnchoredAtom2214 chi ∧
      Fin15AnchoredAtom0555 chi ∧
      Fin15AnchoredAtom0563 chi ∧
      Fin15AnchoredAtom0571 chi ∧
      Fin15AnchoredAtom0707 chi ∧
      Fin15AnchoredAtom1213 chi))))) ∨
      (((((Fin15AnchoredAtom2215 chi ∧
      ¬Fin15AnchoredAtom0572 chi) ∨
      (Fin15AnchoredAtom2215 chi ∧
      ¬Fin15AnchoredAtom0708 chi)) ∨
      ((Fin15AnchoredAtom2215 chi ∧
      ¬Fin15AnchoredAtom1214 chi) ∨
      (¬Fin15AnchoredAtom2215 chi ∧
      Fin15AnchoredAtom0556 chi ∧
      Fin15AnchoredAtom0557 chi ∧
      Fin15AnchoredAtom0572 chi ∧
      Fin15AnchoredAtom0708 chi ∧
      Fin15AnchoredAtom1214 chi))) ∨
      (((Fin15AnchoredAtom2216 chi ∧
      ¬Fin15AnchoredAtom0556 chi) ∨
      (Fin15AnchoredAtom2216 chi ∧
      ¬Fin15AnchoredAtom0558 chi)) ∨
      ((Fin15AnchoredAtom2216 chi ∧
      ¬Fin15AnchoredAtom0573 chi) ∨
      (Fin15AnchoredAtom2216 chi ∧
      ¬Fin15AnchoredAtom0709 chi)))) ∨
      ((((Fin15AnchoredAtom2216 chi ∧
      ¬Fin15AnchoredAtom1215 chi) ∨
      (¬Fin15AnchoredAtom2216 chi ∧
      Fin15AnchoredAtom0556 chi ∧
      Fin15AnchoredAtom0558 chi ∧
      Fin15AnchoredAtom0573 chi ∧
      Fin15AnchoredAtom0709 chi ∧
      Fin15AnchoredAtom1215 chi)) ∨
      ((Fin15AnchoredAtom2217 chi ∧
      ¬Fin15AnchoredAtom0556 chi) ∨
      (Fin15AnchoredAtom2217 chi ∧
      ¬Fin15AnchoredAtom0559 chi))) ∨
      (((Fin15AnchoredAtom2217 chi ∧
      ¬Fin15AnchoredAtom0574 chi) ∨
      (Fin15AnchoredAtom2217 chi ∧
      ¬Fin15AnchoredAtom0710 chi)) ∨
      ((Fin15AnchoredAtom2217 chi ∧
      ¬Fin15AnchoredAtom1216 chi) ∨
      (¬Fin15AnchoredAtom2217 chi ∧
      Fin15AnchoredAtom0556 chi ∧
      Fin15AnchoredAtom0559 chi ∧
      Fin15AnchoredAtom0574 chi ∧
      Fin15AnchoredAtom0710 chi ∧
      Fin15AnchoredAtom1216 chi)))))))))) := by
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
                exact fin15Anchored_clause17163 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17164 chi hbad
                ·
                  exact fin15Anchored_clause17165 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17166 chi hbad
                ·
                  exact fin15Anchored_clause17167 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17168 chi hbad
                ·
                  exact fin15Anchored_clause17169 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17170 chi hbad
                ·
                  exact fin15Anchored_clause17171 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17172 chi hbad
                ·
                  exact fin15Anchored_clause17173 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17174 chi hbad
                ·
                  exact fin15Anchored_clause17175 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17176 chi hbad
                ·
                  exact fin15Anchored_clause17177 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17178 chi hbad
                ·
                  exact fin15Anchored_clause17179 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17180 chi hbad
                ·
                  exact fin15Anchored_clause17181 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17182 chi hbad
                ·
                  exact fin15Anchored_clause17183 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17184 chi hbad
                ·
                  exact fin15Anchored_clause17185 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17186 chi hbad
                ·
                  exact fin15Anchored_clause17187 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17188 chi hbad
                ·
                  exact fin15Anchored_clause17189 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17190 chi hbad
                ·
                  exact fin15Anchored_clause17191 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17192 chi hbad
                ·
                  exact fin15Anchored_clause17193 chi hbad
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
                  exact fin15Anchored_clause17194 chi hbad
                ·
                  exact fin15Anchored_clause17195 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17196 chi hbad
                ·
                  exact fin15Anchored_clause17197 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17198 chi hbad
                ·
                  exact fin15Anchored_clause17199 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17200 chi hbad
                ·
                  exact fin15Anchored_clause17201 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17202 chi hbad
                ·
                  exact fin15Anchored_clause17203 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17204 chi hbad
                ·
                  exact fin15Anchored_clause17205 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17206 chi hbad
                ·
                  exact fin15Anchored_clause17207 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17208 chi hbad
                ·
                  exact fin15Anchored_clause17209 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17210 chi hbad
                ·
                  exact fin15Anchored_clause17211 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17212 chi hbad
                ·
                  exact fin15Anchored_clause17213 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17214 chi hbad
                ·
                  exact fin15Anchored_clause17215 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17216 chi hbad
                ·
                  exact fin15Anchored_clause17217 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17218 chi hbad
                ·
                  exact fin15Anchored_clause17219 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17220 chi hbad
                ·
                  exact fin15Anchored_clause17221 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17222 chi hbad
                ·
                  exact fin15Anchored_clause17223 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17224 chi hbad
                ·
                  exact fin15Anchored_clause17225 chi hbad
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
                exact fin15Anchored_clause17226 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17227 chi hbad
                ·
                  exact fin15Anchored_clause17228 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17229 chi hbad
                ·
                  exact fin15Anchored_clause17230 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17231 chi hbad
                ·
                  exact fin15Anchored_clause17232 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17233 chi hbad
                ·
                  exact fin15Anchored_clause17234 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17235 chi hbad
                ·
                  exact fin15Anchored_clause17236 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17237 chi hbad
                ·
                  exact fin15Anchored_clause17238 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17239 chi hbad
                ·
                  exact fin15Anchored_clause17240 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17241 chi hbad
                ·
                  exact fin15Anchored_clause17242 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17243 chi hbad
                ·
                  exact fin15Anchored_clause17244 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17245 chi hbad
                ·
                  exact fin15Anchored_clause17246 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17247 chi hbad
                ·
                  exact fin15Anchored_clause17248 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17249 chi hbad
                ·
                  exact fin15Anchored_clause17250 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17251 chi hbad
                ·
                  exact fin15Anchored_clause17252 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17253 chi hbad
                ·
                  exact fin15Anchored_clause17254 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17255 chi hbad
                ·
                  exact fin15Anchored_clause17256 chi hbad
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
                  exact fin15Anchored_clause17257 chi hbad
                ·
                  exact fin15Anchored_clause17258 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17259 chi hbad
                ·
                  exact fin15Anchored_clause17260 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17261 chi hbad
                ·
                  exact fin15Anchored_clause17262 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17263 chi hbad
                ·
                  exact fin15Anchored_clause17264 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17265 chi hbad
                ·
                  exact fin15Anchored_clause17266 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17267 chi hbad
                ·
                  exact fin15Anchored_clause17268 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17269 chi hbad
                ·
                  exact fin15Anchored_clause17270 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17271 chi hbad
                ·
                  exact fin15Anchored_clause17272 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17273 chi hbad
                ·
                  exact fin15Anchored_clause17274 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17275 chi hbad
                ·
                  exact fin15Anchored_clause17276 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17277 chi hbad
                ·
                  exact fin15Anchored_clause17278 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17279 chi hbad
                ·
                  exact fin15Anchored_clause17280 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17281 chi hbad
                ·
                  exact fin15Anchored_clause17282 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17283 chi hbad
                ·
                  exact fin15Anchored_clause17284 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17285 chi hbad
                ·
                  exact fin15Anchored_clause17286 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17287 chi hbad
                ·
                  exact fin15Anchored_clause17288 chi hbad
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
                exact fin15Anchored_clause17289 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17290 chi hbad
                ·
                  exact fin15Anchored_clause17291 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17292 chi hbad
                ·
                  exact fin15Anchored_clause17293 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17294 chi hbad
                ·
                  exact fin15Anchored_clause17295 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17296 chi hbad
                ·
                  exact fin15Anchored_clause17297 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17298 chi hbad
                ·
                  exact fin15Anchored_clause17299 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17300 chi hbad
                ·
                  exact fin15Anchored_clause17301 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17302 chi hbad
                ·
                  exact fin15Anchored_clause17303 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17304 chi hbad
                ·
                  exact fin15Anchored_clause17305 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17306 chi hbad
                ·
                  exact fin15Anchored_clause17307 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17308 chi hbad
                ·
                  exact fin15Anchored_clause17309 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17310 chi hbad
                ·
                  exact fin15Anchored_clause17311 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17312 chi hbad
                ·
                  exact fin15Anchored_clause17313 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17314 chi hbad
                ·
                  exact fin15Anchored_clause17315 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17316 chi hbad
                ·
                  exact fin15Anchored_clause17317 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17318 chi hbad
                ·
                  exact fin15Anchored_clause17319 chi hbad
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
                  exact fin15Anchored_clause17320 chi hbad
                ·
                  exact fin15Anchored_clause17321 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17322 chi hbad
                ·
                  exact fin15Anchored_clause17323 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17324 chi hbad
                ·
                  exact fin15Anchored_clause17325 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17326 chi hbad
                ·
                  exact fin15Anchored_clause17327 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17328 chi hbad
                ·
                  exact fin15Anchored_clause17329 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17330 chi hbad
                ·
                  exact fin15Anchored_clause17331 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17332 chi hbad
                ·
                  exact fin15Anchored_clause17333 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17334 chi hbad
                ·
                  exact fin15Anchored_clause17335 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17336 chi hbad
                ·
                  exact fin15Anchored_clause17337 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17338 chi hbad
                ·
                  exact fin15Anchored_clause17339 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17340 chi hbad
                ·
                  exact fin15Anchored_clause17341 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17342 chi hbad
                ·
                  exact fin15Anchored_clause17343 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17344 chi hbad
                ·
                  exact fin15Anchored_clause17345 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17346 chi hbad
                ·
                  exact fin15Anchored_clause17347 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17348 chi hbad
                ·
                  exact fin15Anchored_clause17349 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17350 chi hbad
                ·
                  exact fin15Anchored_clause17351 chi hbad
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
                exact fin15Anchored_clause17352 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17353 chi hbad
                ·
                  exact fin15Anchored_clause17354 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17355 chi hbad
                ·
                  exact fin15Anchored_clause17356 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17357 chi hbad
                ·
                  exact fin15Anchored_clause17358 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17359 chi hbad
                ·
                  exact fin15Anchored_clause17360 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17361 chi hbad
                ·
                  exact fin15Anchored_clause17362 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17363 chi hbad
                ·
                  exact fin15Anchored_clause17364 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17365 chi hbad
                ·
                  exact fin15Anchored_clause17366 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17367 chi hbad
                ·
                  exact fin15Anchored_clause17368 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17369 chi hbad
                ·
                  exact fin15Anchored_clause17370 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17371 chi hbad
                ·
                  exact fin15Anchored_clause17372 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17373 chi hbad
                ·
                  exact fin15Anchored_clause17374 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17375 chi hbad
                ·
                  exact fin15Anchored_clause17376 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17377 chi hbad
                ·
                  exact fin15Anchored_clause17378 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17379 chi hbad
                ·
                  exact fin15Anchored_clause17380 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17381 chi hbad
                ·
                  exact fin15Anchored_clause17382 chi hbad
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
                  exact fin15Anchored_clause17383 chi hbad
                ·
                  exact fin15Anchored_clause17384 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17385 chi hbad
                ·
                  exact fin15Anchored_clause17386 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17387 chi hbad
                ·
                  exact fin15Anchored_clause17388 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17389 chi hbad
                ·
                  exact fin15Anchored_clause17390 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17391 chi hbad
                ·
                  exact fin15Anchored_clause17392 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17393 chi hbad
                ·
                  exact fin15Anchored_clause17394 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17395 chi hbad
                ·
                  exact fin15Anchored_clause17396 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17397 chi hbad
                ·
                  exact fin15Anchored_clause17398 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17399 chi hbad
                ·
                  exact fin15Anchored_clause17400 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17401 chi hbad
                ·
                  exact fin15Anchored_clause17402 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17403 chi hbad
                ·
                  exact fin15Anchored_clause17404 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17405 chi hbad
                ·
                  exact fin15Anchored_clause17406 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17407 chi hbad
                ·
                  exact fin15Anchored_clause17408 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17409 chi hbad
                ·
                  exact fin15Anchored_clause17410 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17411 chi hbad
                ·
                  exact fin15Anchored_clause17412 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17413 chi hbad
                ·
                  exact fin15Anchored_clause17414 chi hbad

end ErdosSzekeres

end
