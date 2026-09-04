module

public import ErdosSzekeres.Fin15AnchoredClauseChunk001
public import ErdosSzekeres.Fin15AnchoredClauseChunk002
public import ErdosSzekeres.Fin15AnchoredClauseChunk003

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 001. -/

theorem fin15Anchored_rejectSemanticSegment001
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0202 chi) ∨
      ((¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0202 chi) ∨
      (Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0202 chi))) ∨
      (((Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0202 chi) ∨
      (Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0202 chi)) ∨
      ((Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0202 chi) ∨
      (¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0203 chi)))) ∨
      ((((¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0203 chi) ∨
      (¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0203 chi)) ∨
      ((¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0203 chi) ∨
      (Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0203 chi))) ∨
      (((Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0203 chi) ∨
      (Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0203 chi)) ∨
      ((Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0203 chi) ∨
      (¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0204 chi))))) ∨
      (((((¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0204 chi) ∨
      (¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0204 chi)) ∨
      ((¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0204 chi) ∨
      (Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0204 chi))) ∨
      (((Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0204 chi) ∨
      (Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0204 chi)) ∨
      ((Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0204 chi) ∨
      (¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0205 chi)))) ∨
      ((((¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0205 chi) ∨
      (¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0205 chi)) ∨
      ((¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0205 chi) ∨
      (Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0205 chi))) ∨
      (((Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0205 chi) ∨
      (Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0205 chi)) ∨
      ((Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0205 chi) ∨
      (¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0206 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0206 chi) ∨
      (¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0206 chi)) ∨
      ((¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0206 chi) ∨
      (Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0206 chi))) ∨
      (((Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0206 chi) ∨
      (Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0206 chi)) ∨
      ((Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0206 chi) ∨
      (¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0207 chi)))) ∨
      ((((¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0207 chi) ∨
      (¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0207 chi)) ∨
      ((¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0207 chi) ∨
      (Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0207 chi))) ∨
      (((Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0207 chi) ∨
      (Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0207 chi)) ∨
      ((Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0207 chi) ∨
      (¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0208 chi))))) ∨
      (((((¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0208 chi) ∨
      (¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0208 chi)) ∨
      ((¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0208 chi) ∨
      (Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0208 chi))) ∨
      (((Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0208 chi) ∨
      (¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0209 chi)) ∨
      ((¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0209 chi) ∨
      (¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0209 chi)))) ∨
      ((((¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0209 chi) ∨
      (Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0209 chi)) ∨
      ((Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0209 chi) ∨
      (Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0209 chi))) ∨
      (((Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0209 chi) ∨
      (¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0210 chi)) ∨
      ((¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0210 chi) ∨
      (¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0210 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0210 chi) ∨
      ((Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0210 chi) ∨
      (Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0210 chi))) ∨
      (((Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0210 chi) ∨
      (Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0210 chi)) ∨
      ((Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0211 chi) ∨
      (Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0211 chi)))) ∨
      ((((¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0212 chi) ∨
      (¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0212 chi)) ∨
      ((¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0212 chi) ∨
      (¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0212 chi))) ∨
      (((Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0212 chi) ∨
      (Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0212 chi)) ∨
      ((Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0212 chi) ∨
      (Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0212 chi))))) ∨
      (((((¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0213 chi) ∨
      (¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0213 chi)) ∨
      ((¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0213 chi) ∨
      (¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0213 chi))) ∨
      (((Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0213 chi) ∨
      (Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0213 chi)) ∨
      ((Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0213 chi) ∨
      (Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0213 chi)))) ∨
      ((((¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0214 chi) ∨
      (¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0214 chi)) ∨
      ((¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0214 chi) ∨
      (¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0214 chi))) ∨
      (((Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0214 chi) ∨
      (Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0214 chi)) ∨
      ((Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0214 chi) ∨
      (Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0214 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0215 chi) ∨
      (¬Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0215 chi)) ∨
      ((¬Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0215 chi) ∨
      (¬Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0215 chi))) ∨
      (((Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0215 chi) ∨
      (Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0215 chi)) ∨
      ((Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0215 chi) ∨
      (¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0216 chi)))) ∨
      ((((¬Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0216 chi) ∨
      (¬Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0216 chi)) ∨
      ((Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0216 chi) ∨
      (Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0216 chi))) ∨
      (((Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0216 chi) ∨
      (¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0218 chi)) ∨
      ((¬Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0218 chi) ∨
      (¬Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0218 chi))))) ∨
      (((((Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0218 chi) ∨
      (Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0218 chi)) ∨
      ((Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0218 chi) ∨
      (¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0220 chi))) ∨
      (((¬Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0220 chi) ∨
      (¬Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0220 chi)) ∨
      ((Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0220 chi) ∨
      (¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0221 chi)))) ∨
      ((((¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0221 chi) ∨
      (¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0221 chi)) ∨
      ((¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0221 chi) ∨
      (Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0221 chi))) ∨
      (((Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0221 chi) ∨
      (Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0221 chi)) ∨
      ((Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0221 chi) ∨
      (¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0222 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0222 chi) ∨
      ((¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0222 chi) ∨
      (¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0222 chi))) ∨
      (((Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0222 chi) ∨
      (Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0222 chi)) ∨
      ((Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0222 chi) ∨
      (Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0222 chi)))) ∨
      ((((¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0223 chi) ∨
      (¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0223 chi)) ∨
      ((¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0223 chi) ∨
      (¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0223 chi))) ∨
      (((Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0223 chi) ∨
      (Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0223 chi)) ∨
      ((Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0223 chi) ∨
      (Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0223 chi))))) ∨
      (((((¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0224 chi) ∨
      (¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0224 chi)) ∨
      ((¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0224 chi) ∨
      (¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0224 chi))) ∨
      (((Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0224 chi) ∨
      (Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0224 chi)) ∨
      ((Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0224 chi) ∨
      (Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0224 chi)))) ∨
      ((((¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0225 chi) ∨
      (¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0225 chi)) ∨
      ((¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0225 chi) ∨
      (¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0225 chi))) ∨
      (((Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0225 chi) ∨
      (Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0225 chi)) ∨
      ((Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0225 chi) ∨
      (Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0225 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0226 chi) ∨
      (¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0226 chi)) ∨
      ((¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0226 chi) ∨
      (¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0226 chi))) ∨
      (((Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0226 chi) ∨
      (Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0226 chi)) ∨
      ((Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0226 chi) ∨
      (Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0226 chi)))) ∨
      ((((¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0227 chi) ∨
      (¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0227 chi)) ∨
      ((¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0227 chi) ∨
      (¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0227 chi))) ∨
      (((Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0227 chi) ∨
      (Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0227 chi)) ∨
      ((Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0227 chi) ∨
      (Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0227 chi))))) ∨
      (((((¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0228 chi) ∨
      (¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0228 chi)) ∨
      ((¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0228 chi) ∨
      (¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0228 chi))) ∨
      (((Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0228 chi) ∨
      (Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0228 chi)) ∨
      ((Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0228 chi) ∨
      (Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0228 chi)))) ∨
      ((((¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0229 chi) ∨
      (¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0229 chi)) ∨
      ((¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0229 chi) ∨
      (¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0229 chi))) ∨
      (((Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0229 chi) ∨
      (Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0229 chi)) ∨
      ((Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0229 chi) ∨
      (Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0229 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0230 chi) ∨
      ((¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0230 chi) ∨
      (¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0230 chi))) ∨
      (((¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0230 chi) ∨
      (Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0230 chi)) ∨
      ((Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0230 chi) ∨
      (Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0230 chi)))) ∨
      ((((Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0230 chi) ∨
      (¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0231 chi)) ∨
      ((¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0231 chi) ∨
      (Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0231 chi))) ∨
      (((¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0232 chi) ∨
      (¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0232 chi)) ∨
      ((¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0232 chi) ∨
      (¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0232 chi))))) ∨
      (((((Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0232 chi) ∨
      (Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0232 chi)) ∨
      ((Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0232 chi) ∨
      (Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0232 chi))) ∨
      (((¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0233 chi) ∨
      (¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0233 chi)) ∨
      ((¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0233 chi) ∨
      (¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0233 chi)))) ∨
      ((((Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0233 chi) ∨
      (Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0233 chi)) ∨
      ((Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0233 chi) ∨
      (Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0233 chi))) ∨
      (((¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0234 chi) ∨
      (¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0234 chi)) ∨
      ((¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0234 chi) ∨
      (¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0234 chi)))))) ∨
      ((((((Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0234 chi) ∨
      (Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0234 chi)) ∨
      ((Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0234 chi) ∨
      (Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0234 chi))) ∨
      (((¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0235 chi) ∨
      (¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0235 chi)) ∨
      ((¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0235 chi) ∨
      (¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0235 chi)))) ∨
      ((((Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0235 chi) ∨
      (Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0235 chi)) ∨
      ((Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0235 chi) ∨
      (Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0235 chi))) ∨
      (((¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0236 chi) ∨
      (¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0236 chi)) ∨
      ((¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0236 chi) ∨
      (¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0236 chi))))) ∨
      (((((Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0236 chi) ∨
      (Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0236 chi)) ∨
      ((Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0236 chi) ∨
      (Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0236 chi))) ∨
      (((¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0237 chi) ∨
      (¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0237 chi)) ∨
      ((¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0237 chi) ∨
      (¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0237 chi)))) ∨
      ((((Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0237 chi) ∨
      (Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0237 chi)) ∨
      ((Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0237 chi) ∨
      (Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0237 chi))) ∨
      (((¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0238 chi) ∨
      (¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0238 chi)) ∨
      ((¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0238 chi) ∨
      (¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0238 chi)))))))))) := by
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
                exact fin15Anchored_clause00252 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00253 chi hone hbad
                ·
                  exact fin15Anchored_clause00254 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00255 chi hone hbad
                ·
                  exact fin15Anchored_clause00256 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00257 chi hone hbad
                ·
                  exact fin15Anchored_clause00258 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00259 chi hone hbad
                ·
                  exact fin15Anchored_clause00260 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00261 chi hone hbad
                ·
                  exact fin15Anchored_clause00262 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00263 chi hone hbad
                ·
                  exact fin15Anchored_clause00264 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00265 chi hone hbad
                ·
                  exact fin15Anchored_clause00266 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00267 chi hone hbad
                ·
                  exact fin15Anchored_clause00268 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00269 chi hone hbad
                ·
                  exact fin15Anchored_clause00270 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00271 chi hone hbad
                ·
                  exact fin15Anchored_clause00272 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00273 chi hone hbad
                ·
                  exact fin15Anchored_clause00274 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00275 chi hone hbad
                ·
                  exact fin15Anchored_clause00276 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00277 chi hone hbad
                ·
                  exact fin15Anchored_clause00278 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00279 chi hone hbad
                ·
                  exact fin15Anchored_clause00280 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00281 chi hone hbad
                ·
                  exact fin15Anchored_clause00282 chi hone hbad
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
                  exact fin15Anchored_clause00283 chi hone hbad
                ·
                  exact fin15Anchored_clause00284 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00285 chi hone hbad
                ·
                  exact fin15Anchored_clause00286 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00287 chi hone hbad
                ·
                  exact fin15Anchored_clause00288 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00289 chi hone hbad
                ·
                  exact fin15Anchored_clause00290 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00291 chi hone hbad
                ·
                  exact fin15Anchored_clause00292 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00293 chi hone hbad
                ·
                  exact fin15Anchored_clause00294 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00295 chi hone hbad
                ·
                  exact fin15Anchored_clause00296 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00297 chi hone hbad
                ·
                  exact fin15Anchored_clause00298 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00299 chi hone hbad
                ·
                  exact fin15Anchored_clause00300 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00301 chi hone hbad
                ·
                  exact fin15Anchored_clause00302 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00303 chi hone hbad
                ·
                  exact fin15Anchored_clause00304 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00305 chi hone hbad
                ·
                  exact fin15Anchored_clause00306 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00307 chi hone hbad
                ·
                  exact fin15Anchored_clause00308 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00309 chi hone hbad
                ·
                  exact fin15Anchored_clause00310 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00311 chi hone hbad
                ·
                  exact fin15Anchored_clause00312 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00313 chi hone hbad
                ·
                  exact fin15Anchored_clause00314 chi hone hbad
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
                exact fin15Anchored_clause00315 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00316 chi hone hbad
                ·
                  exact fin15Anchored_clause00317 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00318 chi hone hbad
                ·
                  exact fin15Anchored_clause00319 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00320 chi hone hbad
                ·
                  exact fin15Anchored_clause00321 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00322 chi hone hbad
                ·
                  exact fin15Anchored_clause00323 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00324 chi hone hbad
                ·
                  exact fin15Anchored_clause00325 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00326 chi hone hbad
                ·
                  exact fin15Anchored_clause00327 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00328 chi hone hbad
                ·
                  exact fin15Anchored_clause00329 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00330 chi hone hbad
                ·
                  exact fin15Anchored_clause00331 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00332 chi hone hbad
                ·
                  exact fin15Anchored_clause00333 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00334 chi hone hbad
                ·
                  exact fin15Anchored_clause00335 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00336 chi hone hbad
                ·
                  exact fin15Anchored_clause00337 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00338 chi hone hbad
                ·
                  exact fin15Anchored_clause00339 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00340 chi hone hbad
                ·
                  exact fin15Anchored_clause00341 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00342 chi hone hbad
                ·
                  exact fin15Anchored_clause00343 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00344 chi hone hbad
                ·
                  exact fin15Anchored_clause00345 chi hone hbad
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
                  exact fin15Anchored_clause00346 chi hone hbad
                ·
                  exact fin15Anchored_clause00347 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00348 chi hone hbad
                ·
                  exact fin15Anchored_clause00349 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00350 chi hone hbad
                ·
                  exact fin15Anchored_clause00351 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00352 chi hone hbad
                ·
                  exact fin15Anchored_clause00353 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00354 chi hone hbad
                ·
                  exact fin15Anchored_clause00355 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00356 chi hone hbad
                ·
                  exact fin15Anchored_clause00357 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00358 chi hone hbad
                ·
                  exact fin15Anchored_clause00359 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00360 chi hone hbad
                ·
                  exact fin15Anchored_clause00361 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00362 chi hone hbad
                ·
                  exact fin15Anchored_clause00363 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00364 chi hone hbad
                ·
                  exact fin15Anchored_clause00365 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00366 chi hone hbad
                ·
                  exact fin15Anchored_clause00367 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00368 chi hone hbad
                ·
                  exact fin15Anchored_clause00369 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00370 chi hone hbad
                ·
                  exact fin15Anchored_clause00371 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00372 chi hone hbad
                ·
                  exact fin15Anchored_clause00373 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00374 chi hone hbad
                ·
                  exact fin15Anchored_clause00375 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00376 chi hone hbad
                ·
                  exact fin15Anchored_clause00377 chi hone hbad
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
                exact fin15Anchored_clause00378 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00379 chi hone hbad
                ·
                  exact fin15Anchored_clause00380 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00381 chi hone hbad
                ·
                  exact fin15Anchored_clause00382 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00383 chi hone hbad
                ·
                  exact fin15Anchored_clause00384 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00385 chi hone hbad
                ·
                  exact fin15Anchored_clause00386 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00387 chi hone hbad
                ·
                  exact fin15Anchored_clause00388 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00389 chi hone hbad
                ·
                  exact fin15Anchored_clause00390 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00391 chi hone hbad
                ·
                  exact fin15Anchored_clause00392 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00393 chi hone hbad
                ·
                  exact fin15Anchored_clause00394 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00395 chi hone hbad
                ·
                  exact fin15Anchored_clause00396 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00397 chi hone hbad
                ·
                  exact fin15Anchored_clause00398 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00399 chi hone hbad
                ·
                  exact fin15Anchored_clause00400 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00401 chi hone hbad
                ·
                  exact fin15Anchored_clause00402 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00403 chi hone hbad
                ·
                  exact fin15Anchored_clause00404 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00405 chi hone hbad
                ·
                  exact fin15Anchored_clause00406 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00407 chi hone hbad
                ·
                  exact fin15Anchored_clause00408 chi hone hbad
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
                  exact fin15Anchored_clause00409 chi hone hbad
                ·
                  exact fin15Anchored_clause00410 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00411 chi hone hbad
                ·
                  exact fin15Anchored_clause00412 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00413 chi hone hbad
                ·
                  exact fin15Anchored_clause00414 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00415 chi hone hbad
                ·
                  exact fin15Anchored_clause00416 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00417 chi hone hbad
                ·
                  exact fin15Anchored_clause00418 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00419 chi hone hbad
                ·
                  exact fin15Anchored_clause00420 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00421 chi hone hbad
                ·
                  exact fin15Anchored_clause00422 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00423 chi hone hbad
                ·
                  exact fin15Anchored_clause00424 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00425 chi hone hbad
                ·
                  exact fin15Anchored_clause00426 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00427 chi hone hbad
                ·
                  exact fin15Anchored_clause00428 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00429 chi hone hbad
                ·
                  exact fin15Anchored_clause00430 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00431 chi hone hbad
                ·
                  exact fin15Anchored_clause00432 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00433 chi hone hbad
                ·
                  exact fin15Anchored_clause00434 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00435 chi hone hbad
                ·
                  exact fin15Anchored_clause00436 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00437 chi hone hbad
                ·
                  exact fin15Anchored_clause00438 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00439 chi hone hbad
                ·
                  exact fin15Anchored_clause00440 chi hone hbad
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
                exact fin15Anchored_clause00441 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00442 chi hone hbad
                ·
                  exact fin15Anchored_clause00443 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00444 chi hone hbad
                ·
                  exact fin15Anchored_clause00445 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00446 chi hone hbad
                ·
                  exact fin15Anchored_clause00447 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00448 chi hone hbad
                ·
                  exact fin15Anchored_clause00449 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00450 chi hone hbad
                ·
                  exact fin15Anchored_clause00451 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00452 chi hone hbad
                ·
                  exact fin15Anchored_clause00453 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00454 chi hone hbad
                ·
                  exact fin15Anchored_clause00455 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00456 chi hone hbad
                ·
                  exact fin15Anchored_clause00457 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00458 chi hone hbad
                ·
                  exact fin15Anchored_clause00459 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00460 chi hone hbad
                ·
                  exact fin15Anchored_clause00461 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00462 chi hone hbad
                ·
                  exact fin15Anchored_clause00463 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00464 chi hone hbad
                ·
                  exact fin15Anchored_clause00465 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00466 chi hone hbad
                ·
                  exact fin15Anchored_clause00467 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00468 chi hone hbad
                ·
                  exact fin15Anchored_clause00469 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00470 chi hone hbad
                ·
                  exact fin15Anchored_clause00471 chi hone hbad
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
                  exact fin15Anchored_clause00472 chi hone hbad
                ·
                  exact fin15Anchored_clause00473 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00474 chi hone hbad
                ·
                  exact fin15Anchored_clause00475 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00476 chi hone hbad
                ·
                  exact fin15Anchored_clause00477 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00478 chi hone hbad
                ·
                  exact fin15Anchored_clause00479 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00480 chi hone hbad
                ·
                  exact fin15Anchored_clause00481 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00482 chi hone hbad
                ·
                  exact fin15Anchored_clause00483 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00484 chi hone hbad
                ·
                  exact fin15Anchored_clause00485 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00486 chi hone hbad
                ·
                  exact fin15Anchored_clause00487 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00488 chi hone hbad
                ·
                  exact fin15Anchored_clause00489 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00490 chi hone hbad
                ·
                  exact fin15Anchored_clause00491 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00492 chi hone hbad
                ·
                  exact fin15Anchored_clause00493 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00494 chi hone hbad
                ·
                  exact fin15Anchored_clause00495 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00496 chi hone hbad
                ·
                  exact fin15Anchored_clause00497 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00498 chi hone hbad
                ·
                  exact fin15Anchored_clause00499 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00500 chi hone hbad
                ·
                  exact fin15Anchored_clause00501 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00502 chi hone hbad
                ·
                  exact fin15Anchored_clause00503 chi hone hbad

end ErdosSzekeres

end
