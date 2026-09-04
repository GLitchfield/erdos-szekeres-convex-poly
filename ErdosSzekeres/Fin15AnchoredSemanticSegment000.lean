module

public import ErdosSzekeres.Fin15AnchoredClauseChunk000
public import ErdosSzekeres.Fin15AnchoredClauseChunk001

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 000. -/

theorem fin15Anchored_rejectSemanticSegment000
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0170 chi) ∨
      ((¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0170 chi) ∨
      (¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0170 chi))) ∨
      (((¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0170 chi) ∨
      (Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0170 chi)) ∨
      ((Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0170 chi) ∨
      (Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0170 chi)))) ∨
      ((((Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0170 chi) ∨
      (¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0171 chi)) ∨
      ((¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0171 chi) ∨
      (¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0171 chi))) ∨
      (((¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0171 chi) ∨
      (Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0171 chi)) ∨
      ((Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0171 chi) ∨
      (Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0171 chi))))) ∨
      (((((Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0171 chi) ∨
      (¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0172 chi)) ∨
      ((¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0172 chi) ∨
      (¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0172 chi))) ∨
      (((¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0172 chi) ∨
      (Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0172 chi)) ∨
      ((Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0172 chi) ∨
      (Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0172 chi)))) ∨
      ((((Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0172 chi) ∨
      (¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0173 chi)) ∨
      ((¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0173 chi) ∨
      (¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0173 chi))) ∨
      (((¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0173 chi) ∨
      (Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0173 chi)) ∨
      ((Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0173 chi) ∨
      (Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0173 chi)))))) ∨
      ((((((Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0173 chi) ∨
      (¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0174 chi)) ∨
      ((¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0174 chi) ∨
      (¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0174 chi))) ∨
      (((¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0174 chi) ∨
      (Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0174 chi)) ∨
      ((¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0175 chi) ∨
      (¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0175 chi)))) ∨
      ((((¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0175 chi) ∨
      (¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0175 chi)) ∨
      ((Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0175 chi) ∨
      (Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0175 chi))) ∨
      (((Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0175 chi) ∨
      (Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0175 chi)) ∨
      ((¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0176 chi) ∨
      (¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0176 chi))))) ∨
      (((((¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0176 chi) ∨
      (¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0176 chi)) ∨
      ((Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0176 chi) ∨
      (Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0176 chi))) ∨
      (((Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0176 chi) ∨
      (Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0176 chi)) ∨
      ((¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0177 chi) ∨
      (¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0177 chi)))) ∨
      ((((¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0177 chi) ∨
      (¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0177 chi)) ∨
      ((Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0177 chi) ∨
      (Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0177 chi))) ∨
      (((Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0177 chi) ∨
      (¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0178 chi)) ∨
      ((¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0178 chi) ∨
      (¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0178 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0178 chi) ∨
      ((Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0178 chi) ∨
      (Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0178 chi))) ∨
      (((Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0178 chi) ∨
      (Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0178 chi)) ∨
      ((¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0179 chi) ∨
      (¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0179 chi)))) ∨
      ((((¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0179 chi) ∨
      (¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0179 chi)) ∨
      ((Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0179 chi) ∨
      (Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0179 chi))) ∨
      (((Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0179 chi) ∨
      (Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0179 chi)) ∨
      ((¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0180 chi) ∨
      (¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0180 chi))))) ∨
      (((((¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0180 chi) ∨
      (¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0180 chi)) ∨
      ((Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0180 chi) ∨
      (Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0180 chi))) ∨
      (((Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0180 chi) ∨
      (Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0180 chi)) ∨
      ((¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0181 chi) ∨
      (¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0181 chi)))) ∨
      ((((¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0181 chi) ∨
      (¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0181 chi)) ∨
      ((Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0181 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0181 chi))) ∨
      (((Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0181 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0181 chi)) ∨
      ((¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0182 chi) ∨
      (¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0182 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0182 chi) ∨
      (¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0182 chi)) ∨
      ((Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0182 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0182 chi))) ∨
      (((Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0182 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0182 chi)) ∨
      ((¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0183 chi) ∨
      (¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0183 chi)))) ∨
      ((((¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0183 chi) ∨
      (¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0183 chi)) ∨
      ((Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0183 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0183 chi))) ∨
      (((Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0183 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0183 chi)) ∨
      ((¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0184 chi) ∨
      (¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0184 chi))))) ∨
      (((((¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0184 chi) ∨
      (¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0184 chi)) ∨
      ((Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0184 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0184 chi))) ∨
      (((Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0184 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0184 chi)) ∨
      ((¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0185 chi) ∨
      (¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0185 chi)))) ∨
      ((((¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0185 chi) ∨
      (¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0185 chi)) ∨
      ((Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0185 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0185 chi))) ∨
      (((Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0185 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0185 chi)) ∨
      ((¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0186 chi) ∨
      (¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0186 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0186 chi) ∨
      ((¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0186 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0186 chi))) ∨
      (((Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0186 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0186 chi)) ∨
      ((Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0186 chi) ∨
      (¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0187 chi)))) ∨
      ((((¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0187 chi) ∨
      (¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0187 chi)) ∨
      ((¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0187 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0187 chi))) ∨
      (((Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0187 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0187 chi)) ∨
      ((Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0187 chi) ∨
      (¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0188 chi))))) ∨
      (((((¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0188 chi) ∨
      (¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0188 chi)) ∨
      ((¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0188 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0188 chi))) ∨
      (((Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0188 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0188 chi)) ∨
      ((Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0188 chi) ∨
      (¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0189 chi)))) ∨
      ((((¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0189 chi) ∨
      (¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0189 chi)) ∨
      ((¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0189 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0189 chi))) ∨
      (((Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0189 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0189 chi)) ∨
      ((Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0189 chi) ∨
      (¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0190 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0190 chi) ∨
      (¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0190 chi)) ∨
      ((¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0190 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0190 chi))) ∨
      (((Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0190 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0190 chi)) ∨
      ((Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0190 chi) ∨
      (¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0191 chi)))) ∨
      ((((¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0191 chi) ∨
      (¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0191 chi)) ∨
      ((¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0191 chi) ∨
      (Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0191 chi))) ∨
      (((Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0191 chi) ∨
      (Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0191 chi)) ∨
      ((Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0191 chi) ∨
      (¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0192 chi))))) ∨
      (((((¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0192 chi) ∨
      (¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0192 chi)) ∨
      ((¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0192 chi) ∨
      (Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0192 chi))) ∨
      (((Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0192 chi) ∨
      (Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0192 chi)) ∨
      ((Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0192 chi) ∨
      (¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0193 chi)))) ∨
      ((((¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0193 chi) ∨
      (¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0193 chi)) ∨
      ((¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0193 chi) ∨
      (Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0193 chi))) ∨
      (((Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0193 chi) ∨
      (¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0194 chi)) ∨
      ((¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0194 chi) ∨
      (¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0194 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0194 chi) ∨
      ((Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0194 chi) ∨
      (Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0194 chi))) ∨
      (((Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0194 chi) ∨
      (Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0194 chi)) ∨
      ((¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0195 chi) ∨
      (¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0195 chi)))) ∨
      ((((¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0195 chi) ∨
      (¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0195 chi)) ∨
      ((Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0195 chi) ∨
      (Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0195 chi))) ∨
      (((Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0195 chi) ∨
      (Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0195 chi)) ∨
      ((¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0196 chi) ∨
      (¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0196 chi))))) ∨
      (((((¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0196 chi) ∨
      (¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0196 chi)) ∨
      ((Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0196 chi) ∨
      (Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0196 chi))) ∨
      (((Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0196 chi) ∨
      (Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0196 chi)) ∨
      ((¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0197 chi) ∨
      (¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0197 chi)))) ∨
      ((((¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0197 chi) ∨
      (¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0197 chi)) ∨
      ((Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0197 chi) ∨
      (Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0197 chi))) ∨
      (((Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0197 chi) ∨
      (Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0197 chi)) ∨
      ((¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0198 chi) ∨
      (¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0198 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0198 chi) ∨
      (¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0198 chi)) ∨
      ((Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0198 chi) ∨
      (Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0198 chi))) ∨
      (((Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0198 chi) ∨
      (Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0198 chi)) ∨
      ((¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0199 chi) ∨
      (¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0199 chi)))) ∨
      ((((¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0199 chi) ∨
      (¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0199 chi)) ∨
      ((Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0199 chi) ∨
      (Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0199 chi))) ∨
      (((Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0199 chi) ∨
      (Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0199 chi)) ∨
      ((¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0200 chi) ∨
      (¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0200 chi))))) ∨
      (((((¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0200 chi) ∨
      (¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0200 chi)) ∨
      ((Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0200 chi) ∨
      (Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0200 chi))) ∨
      (((Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0200 chi) ∨
      (Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0200 chi)) ∨
      ((¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0201 chi) ∨
      (¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0201 chi)))) ∨
      ((((¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0201 chi) ∨
      (¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0201 chi)) ∨
      ((Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0201 chi) ∨
      (Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0201 chi))) ∨
      (((Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0201 chi) ∨
      (Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0201 chi)) ∨
      ((¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0202 chi) ∨
      (¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0202 chi)))))))))) := by
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
                exact fin15Anchored_clause00000 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00001 chi hone hbad
                ·
                  exact fin15Anchored_clause00002 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00003 chi hone hbad
                ·
                  exact fin15Anchored_clause00004 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00005 chi hone hbad
                ·
                  exact fin15Anchored_clause00006 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00007 chi hone hbad
                ·
                  exact fin15Anchored_clause00008 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00009 chi hone hbad
                ·
                  exact fin15Anchored_clause00010 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00011 chi hone hbad
                ·
                  exact fin15Anchored_clause00012 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00013 chi hone hbad
                ·
                  exact fin15Anchored_clause00014 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00015 chi hone hbad
                ·
                  exact fin15Anchored_clause00016 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00017 chi hone hbad
                ·
                  exact fin15Anchored_clause00018 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00019 chi hone hbad
                ·
                  exact fin15Anchored_clause00020 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00021 chi hone hbad
                ·
                  exact fin15Anchored_clause00022 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00023 chi hone hbad
                ·
                  exact fin15Anchored_clause00024 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00025 chi hone hbad
                ·
                  exact fin15Anchored_clause00026 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00027 chi hone hbad
                ·
                  exact fin15Anchored_clause00028 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00029 chi hone hbad
                ·
                  exact fin15Anchored_clause00030 chi hone hbad
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
                  exact fin15Anchored_clause00031 chi hone hbad
                ·
                  exact fin15Anchored_clause00032 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00033 chi hone hbad
                ·
                  exact fin15Anchored_clause00034 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00035 chi hone hbad
                ·
                  exact fin15Anchored_clause00036 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00037 chi hone hbad
                ·
                  exact fin15Anchored_clause00038 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00039 chi hone hbad
                ·
                  exact fin15Anchored_clause00040 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00041 chi hone hbad
                ·
                  exact fin15Anchored_clause00042 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00043 chi hone hbad
                ·
                  exact fin15Anchored_clause00044 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00045 chi hone hbad
                ·
                  exact fin15Anchored_clause00046 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00047 chi hone hbad
                ·
                  exact fin15Anchored_clause00048 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00049 chi hone hbad
                ·
                  exact fin15Anchored_clause00050 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00051 chi hone hbad
                ·
                  exact fin15Anchored_clause00052 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00053 chi hone hbad
                ·
                  exact fin15Anchored_clause00054 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00055 chi hone hbad
                ·
                  exact fin15Anchored_clause00056 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00057 chi hone hbad
                ·
                  exact fin15Anchored_clause00058 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00059 chi hone hbad
                ·
                  exact fin15Anchored_clause00060 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00061 chi hone hbad
                ·
                  exact fin15Anchored_clause00062 chi hone hbad
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
                exact fin15Anchored_clause00063 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00064 chi hone hbad
                ·
                  exact fin15Anchored_clause00065 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00066 chi hone hbad
                ·
                  exact fin15Anchored_clause00067 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00068 chi hone hbad
                ·
                  exact fin15Anchored_clause00069 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00070 chi hone hbad
                ·
                  exact fin15Anchored_clause00071 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00072 chi hone hbad
                ·
                  exact fin15Anchored_clause00073 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00074 chi hone hbad
                ·
                  exact fin15Anchored_clause00075 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00076 chi hone hbad
                ·
                  exact fin15Anchored_clause00077 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00078 chi hone hbad
                ·
                  exact fin15Anchored_clause00079 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00080 chi hone hbad
                ·
                  exact fin15Anchored_clause00081 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00082 chi hone hbad
                ·
                  exact fin15Anchored_clause00083 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00084 chi hone hbad
                ·
                  exact fin15Anchored_clause00085 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00086 chi hone hbad
                ·
                  exact fin15Anchored_clause00087 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00088 chi hone hbad
                ·
                  exact fin15Anchored_clause00089 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00090 chi hone hbad
                ·
                  exact fin15Anchored_clause00091 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00092 chi hone hbad
                ·
                  exact fin15Anchored_clause00093 chi hone hbad
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
                  exact fin15Anchored_clause00094 chi hone hbad
                ·
                  exact fin15Anchored_clause00095 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00096 chi hone hbad
                ·
                  exact fin15Anchored_clause00097 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00098 chi hone hbad
                ·
                  exact fin15Anchored_clause00099 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00100 chi hone hbad
                ·
                  exact fin15Anchored_clause00101 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00102 chi hone hbad
                ·
                  exact fin15Anchored_clause00103 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00104 chi hone hbad
                ·
                  exact fin15Anchored_clause00105 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00106 chi hone hbad
                ·
                  exact fin15Anchored_clause00107 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00108 chi hone hbad
                ·
                  exact fin15Anchored_clause00109 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00110 chi hone hbad
                ·
                  exact fin15Anchored_clause00111 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00112 chi hone hbad
                ·
                  exact fin15Anchored_clause00113 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00114 chi hone hbad
                ·
                  exact fin15Anchored_clause00115 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00116 chi hone hbad
                ·
                  exact fin15Anchored_clause00117 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00118 chi hone hbad
                ·
                  exact fin15Anchored_clause00119 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00120 chi hone hbad
                ·
                  exact fin15Anchored_clause00121 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00122 chi hone hbad
                ·
                  exact fin15Anchored_clause00123 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00124 chi hone hbad
                ·
                  exact fin15Anchored_clause00125 chi hone hbad
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
                exact fin15Anchored_clause00126 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00127 chi hone hbad
                ·
                  exact fin15Anchored_clause00128 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00129 chi hone hbad
                ·
                  exact fin15Anchored_clause00130 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00131 chi hone hbad
                ·
                  exact fin15Anchored_clause00132 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00133 chi hone hbad
                ·
                  exact fin15Anchored_clause00134 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00135 chi hone hbad
                ·
                  exact fin15Anchored_clause00136 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00137 chi hone hbad
                ·
                  exact fin15Anchored_clause00138 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00139 chi hone hbad
                ·
                  exact fin15Anchored_clause00140 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00141 chi hone hbad
                ·
                  exact fin15Anchored_clause00142 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00143 chi hone hbad
                ·
                  exact fin15Anchored_clause00144 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00145 chi hone hbad
                ·
                  exact fin15Anchored_clause00146 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00147 chi hone hbad
                ·
                  exact fin15Anchored_clause00148 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00149 chi hone hbad
                ·
                  exact fin15Anchored_clause00150 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00151 chi hone hbad
                ·
                  exact fin15Anchored_clause00152 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00153 chi hone hbad
                ·
                  exact fin15Anchored_clause00154 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00155 chi hone hbad
                ·
                  exact fin15Anchored_clause00156 chi hone hbad
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
                  exact fin15Anchored_clause00157 chi hone hbad
                ·
                  exact fin15Anchored_clause00158 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00159 chi hone hbad
                ·
                  exact fin15Anchored_clause00160 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00161 chi hone hbad
                ·
                  exact fin15Anchored_clause00162 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00163 chi hone hbad
                ·
                  exact fin15Anchored_clause00164 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00165 chi hone hbad
                ·
                  exact fin15Anchored_clause00166 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00167 chi hone hbad
                ·
                  exact fin15Anchored_clause00168 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00169 chi hone hbad
                ·
                  exact fin15Anchored_clause00170 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00171 chi hone hbad
                ·
                  exact fin15Anchored_clause00172 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00173 chi hone hbad
                ·
                  exact fin15Anchored_clause00174 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00175 chi hone hbad
                ·
                  exact fin15Anchored_clause00176 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00177 chi hone hbad
                ·
                  exact fin15Anchored_clause00178 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00179 chi hone hbad
                ·
                  exact fin15Anchored_clause00180 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00181 chi hone hbad
                ·
                  exact fin15Anchored_clause00182 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00183 chi hone hbad
                ·
                  exact fin15Anchored_clause00184 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00185 chi hone hbad
                ·
                  exact fin15Anchored_clause00186 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00187 chi hone hbad
                ·
                  exact fin15Anchored_clause00188 chi hone hbad
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
                exact fin15Anchored_clause00189 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00190 chi hone hbad
                ·
                  exact fin15Anchored_clause00191 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00192 chi hone hbad
                ·
                  exact fin15Anchored_clause00193 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00194 chi hone hbad
                ·
                  exact fin15Anchored_clause00195 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00196 chi hone hbad
                ·
                  exact fin15Anchored_clause00197 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00198 chi hone hbad
                ·
                  exact fin15Anchored_clause00199 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00200 chi hone hbad
                ·
                  exact fin15Anchored_clause00201 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00202 chi hone hbad
                ·
                  exact fin15Anchored_clause00203 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00204 chi hone hbad
                ·
                  exact fin15Anchored_clause00205 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00206 chi hone hbad
                ·
                  exact fin15Anchored_clause00207 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00208 chi hone hbad
                ·
                  exact fin15Anchored_clause00209 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00210 chi hone hbad
                ·
                  exact fin15Anchored_clause00211 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00212 chi hone hbad
                ·
                  exact fin15Anchored_clause00213 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00214 chi hone hbad
                ·
                  exact fin15Anchored_clause00215 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00216 chi hone hbad
                ·
                  exact fin15Anchored_clause00217 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00218 chi hone hbad
                ·
                  exact fin15Anchored_clause00219 chi hone hbad
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
                  exact fin15Anchored_clause00220 chi hone hbad
                ·
                  exact fin15Anchored_clause00221 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00222 chi hone hbad
                ·
                  exact fin15Anchored_clause00223 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00224 chi hone hbad
                ·
                  exact fin15Anchored_clause00225 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00226 chi hone hbad
                ·
                  exact fin15Anchored_clause00227 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00228 chi hone hbad
                ·
                  exact fin15Anchored_clause00229 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00230 chi hone hbad
                ·
                  exact fin15Anchored_clause00231 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00232 chi hone hbad
                ·
                  exact fin15Anchored_clause00233 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00234 chi hone hbad
                ·
                  exact fin15Anchored_clause00235 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00236 chi hone hbad
                ·
                  exact fin15Anchored_clause00237 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00238 chi hone hbad
                ·
                  exact fin15Anchored_clause00239 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00240 chi hone hbad
                ·
                  exact fin15Anchored_clause00241 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00242 chi hone hbad
                ·
                  exact fin15Anchored_clause00243 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00244 chi hone hbad
                ·
                  exact fin15Anchored_clause00245 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00246 chi hone hbad
                ·
                  exact fin15Anchored_clause00247 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00248 chi hone hbad
                ·
                  exact fin15Anchored_clause00249 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00250 chi hone hbad
                ·
                  exact fin15Anchored_clause00251 chi hone hbad

end ErdosSzekeres

end
