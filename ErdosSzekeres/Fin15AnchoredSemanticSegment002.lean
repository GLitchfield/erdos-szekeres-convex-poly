module

public import ErdosSzekeres.Fin15AnchoredClauseChunk003
public import ErdosSzekeres.Fin15AnchoredClauseChunk004
public import ErdosSzekeres.Fin15AnchoredClauseChunk005

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 002. -/

theorem fin15Anchored_rejectSemanticSegment002
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0238 chi) ∨
      ((Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0238 chi) ∨
      (Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0238 chi))) ∨
      (((Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0238 chi) ∨
      (¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0239 chi)) ∨
      ((¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0239 chi) ∨
      (¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0239 chi)))) ∨
      ((((¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0239 chi) ∨
      (Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0239 chi)) ∨
      ((Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0239 chi) ∨
      (Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0239 chi))) ∨
      (((Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0239 chi) ∨
      (¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0240 chi)) ∨
      ((¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0240 chi) ∨
      (¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0240 chi))))) ∨
      (((((¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0240 chi) ∨
      (Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0240 chi)) ∨
      ((Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0240 chi) ∨
      (Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0240 chi))) ∨
      (((Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0240 chi) ∨
      (¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0241 chi)) ∨
      ((¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0241 chi) ∨
      (¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0241 chi)))) ∨
      ((((¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0241 chi) ∨
      (Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0241 chi)) ∨
      ((Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0241 chi) ∨
      (Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0241 chi))) ∨
      (((Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0241 chi) ∨
      (¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0242 chi)) ∨
      ((¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0242 chi) ∨
      (¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0242 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0242 chi) ∨
      (Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0242 chi)) ∨
      ((Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0242 chi) ∨
      (Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0242 chi))) ∨
      (((¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0243 chi) ∨
      (¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0243 chi)) ∨
      ((¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0243 chi) ∨
      (¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0243 chi)))) ∨
      ((((Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0243 chi) ∨
      (Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0243 chi)) ∨
      ((Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0243 chi) ∨
      (Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0243 chi))) ∨
      (((¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0244 chi) ∨
      (¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0244 chi)) ∨
      ((¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0244 chi) ∨
      (¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0244 chi))))) ∨
      (((((Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0244 chi) ∨
      (Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0244 chi)) ∨
      ((Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0244 chi) ∨
      (Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0244 chi))) ∨
      (((¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0245 chi) ∨
      (¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0245 chi)) ∨
      ((¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0245 chi) ∨
      (¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0245 chi)))) ∨
      ((((Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0245 chi) ∨
      (Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0245 chi)) ∨
      ((Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0245 chi) ∨
      (Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0245 chi))) ∨
      (((¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0246 chi) ∨
      (¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0246 chi)) ∨
      ((¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0246 chi) ∨
      (¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0246 chi))))))) ∨
      ((((((Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0246 chi) ∨
      ((Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0246 chi) ∨
      (Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0246 chi))) ∨
      (((Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0246 chi) ∨
      (¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0247 chi)) ∨
      ((¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0247 chi) ∨
      (¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0247 chi)))) ∨
      ((((¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0247 chi) ∨
      (Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0247 chi)) ∨
      ((Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0247 chi) ∨
      (Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0247 chi))) ∨
      (((Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0247 chi) ∨
      (¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0248 chi)) ∨
      ((¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0248 chi) ∨
      (¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0248 chi))))) ∨
      (((((¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0248 chi) ∨
      (Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0248 chi)) ∨
      ((Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0248 chi) ∨
      (Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0248 chi))) ∨
      (((Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0248 chi) ∨
      (¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0249 chi)) ∨
      ((¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0249 chi) ∨
      (¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0249 chi)))) ∨
      ((((¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0249 chi) ∨
      (Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0249 chi)) ∨
      ((Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0249 chi) ∨
      (Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0249 chi))) ∨
      (((Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0249 chi) ∨
      (¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0250 chi)) ∨
      ((¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0250 chi) ∨
      (¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0250 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0250 chi) ∨
      (Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0250 chi)) ∨
      ((Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0250 chi) ∨
      (Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0250 chi))) ∨
      (((Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0250 chi) ∨
      (¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0251 chi)) ∨
      ((¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0251 chi) ∨
      (¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0251 chi)))) ∨
      ((((Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0251 chi) ∨
      (Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0251 chi)) ∨
      ((Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0251 chi) ∨
      (Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0251 chi))) ∨
      (((¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0252 chi) ∨
      (¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0252 chi)) ∨
      ((¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0252 chi) ∨
      (¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0252 chi))))) ∨
      (((((Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0252 chi) ∨
      (Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0252 chi)) ∨
      ((Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0252 chi) ∨
      (Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0252 chi))) ∨
      (((¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0253 chi) ∨
      (¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0253 chi)) ∨
      ((¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0253 chi) ∨
      (¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0253 chi)))) ∨
      ((((Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0253 chi) ∨
      (Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0253 chi)) ∨
      ((Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0253 chi) ∨
      (Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0253 chi))) ∨
      (((¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0254 chi) ∨
      (¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0254 chi)) ∨
      ((¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0254 chi) ∨
      (¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0254 chi)))))))) ∨
      (((((((Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0254 chi) ∨
      ((Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0254 chi) ∨
      (Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0254 chi))) ∨
      (((Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0254 chi) ∨
      (¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0255 chi)) ∨
      ((¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0255 chi) ∨
      (¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0255 chi)))) ∨
      ((((¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0255 chi) ∨
      (Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0255 chi)) ∨
      ((Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0255 chi) ∨
      (Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0255 chi))) ∨
      (((Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0255 chi) ∨
      (¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0256 chi)) ∨
      ((¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0256 chi) ∨
      (¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0256 chi))))) ∨
      (((((¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0256 chi) ∨
      (Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0256 chi)) ∨
      ((Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0256 chi) ∨
      (Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0256 chi))) ∨
      (((Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0256 chi) ∨
      (¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0257 chi)) ∨
      ((¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0257 chi) ∨
      (¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0257 chi)))) ∨
      ((((¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0257 chi) ∨
      (Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0257 chi)) ∨
      ((Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0257 chi) ∨
      (Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0257 chi))) ∨
      (((Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0257 chi) ∨
      (¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0258 chi)) ∨
      ((¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0258 chi) ∨
      (¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0258 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0258 chi) ∨
      (Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0258 chi)) ∨
      ((Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0258 chi) ∨
      (Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0258 chi))) ∨
      (((Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0258 chi) ∨
      (¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0259 chi)) ∨
      ((¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0259 chi) ∨
      (¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0259 chi)))) ∨
      ((((¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0259 chi) ∨
      (Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0259 chi)) ∨
      ((Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0259 chi) ∨
      (Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0259 chi))) ∨
      (((Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0259 chi) ∨
      (¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0260 chi)) ∨
      ((¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0260 chi) ∨
      (¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0260 chi))))) ∨
      (((((¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0260 chi) ∨
      (Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0260 chi)) ∨
      ((Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0260 chi) ∨
      (Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0260 chi))) ∨
      (((Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0260 chi) ∨
      (¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0261 chi)) ∨
      ((¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0261 chi) ∨
      (¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0261 chi)))) ∨
      ((((¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0261 chi) ∨
      (Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0261 chi)) ∨
      ((Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0261 chi) ∨
      (Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0261 chi))) ∨
      (((Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0261 chi) ∨
      (¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0262 chi)) ∨
      ((¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0262 chi) ∨
      (¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0262 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0262 chi) ∨
      ((Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0262 chi) ∨
      (Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0262 chi))) ∨
      (((Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0262 chi) ∨
      (Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0262 chi)) ∨
      ((¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0263 chi) ∨
      (¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0263 chi)))) ∨
      ((((¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0263 chi) ∨
      (¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0263 chi)) ∨
      ((Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0263 chi) ∨
      (Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0263 chi))) ∨
      (((Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0263 chi) ∨
      (Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0263 chi)) ∨
      ((¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0264 chi) ∨
      (¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0264 chi))))) ∨
      (((((¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0264 chi) ∨
      (¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0264 chi)) ∨
      ((Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0264 chi) ∨
      (Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0264 chi))) ∨
      (((Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0264 chi) ∨
      (Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0264 chi)) ∨
      ((¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0265 chi) ∨
      (¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0265 chi)))) ∨
      ((((¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0265 chi) ∨
      (¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0265 chi)) ∨
      ((Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0265 chi) ∨
      (Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0265 chi))) ∨
      (((Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0265 chi) ∨
      (Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0265 chi)) ∨
      ((Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0266 chi) ∨
      (Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0266 chi)))))) ∨
      ((((((Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0266 chi) ∨
      (Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0266 chi)) ∨
      ((¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0267 chi) ∨
      (¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0267 chi))) ∨
      (((¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0267 chi) ∨
      (¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0267 chi)) ∨
      ((Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0267 chi) ∨
      (Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0267 chi)))) ∨
      ((((Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0267 chi) ∨
      (Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0267 chi)) ∨
      ((¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0268 chi) ∨
      (¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0268 chi))) ∨
      (((¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0268 chi) ∨
      (¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0268 chi)) ∨
      ((Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0268 chi) ∨
      (Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0268 chi))))) ∨
      (((((Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0268 chi) ∨
      (Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0268 chi)) ∨
      ((¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0269 chi) ∨
      (¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0269 chi))) ∨
      (((¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0269 chi) ∨
      (¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0269 chi)) ∨
      ((Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0269 chi) ∨
      (Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0269 chi)))) ∨
      ((((Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0269 chi) ∨
      (Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0269 chi)) ∨
      ((¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0270 chi) ∨
      (¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0270 chi))) ∨
      (((¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0270 chi) ∨
      (¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0270 chi)) ∨
      ((Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0270 chi) ∨
      (Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0270 chi)))))))))) := by
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
                exact fin15Anchored_clause00504 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00505 chi hone hbad
                ·
                  exact fin15Anchored_clause00506 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00507 chi hone hbad
                ·
                  exact fin15Anchored_clause00508 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00509 chi hone hbad
                ·
                  exact fin15Anchored_clause00510 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00511 chi hone hbad
                ·
                  exact fin15Anchored_clause00512 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00513 chi hone hbad
                ·
                  exact fin15Anchored_clause00514 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00515 chi hone hbad
                ·
                  exact fin15Anchored_clause00516 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00517 chi hone hbad
                ·
                  exact fin15Anchored_clause00518 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00519 chi hone hbad
                ·
                  exact fin15Anchored_clause00520 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00521 chi hone hbad
                ·
                  exact fin15Anchored_clause00522 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00523 chi hone hbad
                ·
                  exact fin15Anchored_clause00524 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00525 chi hone hbad
                ·
                  exact fin15Anchored_clause00526 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00527 chi hone hbad
                ·
                  exact fin15Anchored_clause00528 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00529 chi hone hbad
                ·
                  exact fin15Anchored_clause00530 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00531 chi hone hbad
                ·
                  exact fin15Anchored_clause00532 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00533 chi hone hbad
                ·
                  exact fin15Anchored_clause00534 chi hone hbad
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
                  exact fin15Anchored_clause00535 chi hone hbad
                ·
                  exact fin15Anchored_clause00536 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00537 chi hone hbad
                ·
                  exact fin15Anchored_clause00538 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00539 chi hone hbad
                ·
                  exact fin15Anchored_clause00540 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00541 chi hone hbad
                ·
                  exact fin15Anchored_clause00542 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00543 chi hone hbad
                ·
                  exact fin15Anchored_clause00544 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00545 chi hone hbad
                ·
                  exact fin15Anchored_clause00546 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00547 chi hone hbad
                ·
                  exact fin15Anchored_clause00548 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00549 chi hone hbad
                ·
                  exact fin15Anchored_clause00550 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00551 chi hone hbad
                ·
                  exact fin15Anchored_clause00552 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00553 chi hone hbad
                ·
                  exact fin15Anchored_clause00554 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00555 chi hone hbad
                ·
                  exact fin15Anchored_clause00556 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00557 chi hone hbad
                ·
                  exact fin15Anchored_clause00558 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00559 chi hone hbad
                ·
                  exact fin15Anchored_clause00560 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00561 chi hone hbad
                ·
                  exact fin15Anchored_clause00562 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00563 chi hone hbad
                ·
                  exact fin15Anchored_clause00564 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00565 chi hone hbad
                ·
                  exact fin15Anchored_clause00566 chi hone hbad
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
                exact fin15Anchored_clause00567 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00568 chi hone hbad
                ·
                  exact fin15Anchored_clause00569 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00570 chi hone hbad
                ·
                  exact fin15Anchored_clause00571 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00572 chi hone hbad
                ·
                  exact fin15Anchored_clause00573 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00574 chi hone hbad
                ·
                  exact fin15Anchored_clause00575 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00576 chi hone hbad
                ·
                  exact fin15Anchored_clause00577 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00578 chi hone hbad
                ·
                  exact fin15Anchored_clause00579 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00580 chi hone hbad
                ·
                  exact fin15Anchored_clause00581 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00582 chi hone hbad
                ·
                  exact fin15Anchored_clause00583 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00584 chi hone hbad
                ·
                  exact fin15Anchored_clause00585 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00586 chi hone hbad
                ·
                  exact fin15Anchored_clause00587 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00588 chi hone hbad
                ·
                  exact fin15Anchored_clause00589 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00590 chi hone hbad
                ·
                  exact fin15Anchored_clause00591 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00592 chi hone hbad
                ·
                  exact fin15Anchored_clause00593 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00594 chi hone hbad
                ·
                  exact fin15Anchored_clause00595 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00596 chi hone hbad
                ·
                  exact fin15Anchored_clause00597 chi hone hbad
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
                  exact fin15Anchored_clause00598 chi hone hbad
                ·
                  exact fin15Anchored_clause00599 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00600 chi hone hbad
                ·
                  exact fin15Anchored_clause00601 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00602 chi hone hbad
                ·
                  exact fin15Anchored_clause00603 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00604 chi hone hbad
                ·
                  exact fin15Anchored_clause00605 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00606 chi hone hbad
                ·
                  exact fin15Anchored_clause00607 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00608 chi hone hbad
                ·
                  exact fin15Anchored_clause00609 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00610 chi hone hbad
                ·
                  exact fin15Anchored_clause00611 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00612 chi hone hbad
                ·
                  exact fin15Anchored_clause00613 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00614 chi hone hbad
                ·
                  exact fin15Anchored_clause00615 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00616 chi hone hbad
                ·
                  exact fin15Anchored_clause00617 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00618 chi hone hbad
                ·
                  exact fin15Anchored_clause00619 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00620 chi hone hbad
                ·
                  exact fin15Anchored_clause00621 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00622 chi hone hbad
                ·
                  exact fin15Anchored_clause00623 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00624 chi hone hbad
                ·
                  exact fin15Anchored_clause00625 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00626 chi hone hbad
                ·
                  exact fin15Anchored_clause00627 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00628 chi hone hbad
                ·
                  exact fin15Anchored_clause00629 chi hone hbad
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
                exact fin15Anchored_clause00630 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00631 chi hone hbad
                ·
                  exact fin15Anchored_clause00632 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00633 chi hone hbad
                ·
                  exact fin15Anchored_clause00634 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00635 chi hone hbad
                ·
                  exact fin15Anchored_clause00636 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00637 chi hone hbad
                ·
                  exact fin15Anchored_clause00638 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00639 chi hone hbad
                ·
                  exact fin15Anchored_clause00640 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00641 chi hone hbad
                ·
                  exact fin15Anchored_clause00642 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00643 chi hone hbad
                ·
                  exact fin15Anchored_clause00644 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00645 chi hone hbad
                ·
                  exact fin15Anchored_clause00646 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00647 chi hone hbad
                ·
                  exact fin15Anchored_clause00648 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00649 chi hone hbad
                ·
                  exact fin15Anchored_clause00650 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00651 chi hone hbad
                ·
                  exact fin15Anchored_clause00652 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00653 chi hone hbad
                ·
                  exact fin15Anchored_clause00654 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00655 chi hone hbad
                ·
                  exact fin15Anchored_clause00656 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00657 chi hone hbad
                ·
                  exact fin15Anchored_clause00658 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00659 chi hone hbad
                ·
                  exact fin15Anchored_clause00660 chi hone hbad
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
                  exact fin15Anchored_clause00661 chi hone hbad
                ·
                  exact fin15Anchored_clause00662 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00663 chi hone hbad
                ·
                  exact fin15Anchored_clause00664 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00665 chi hone hbad
                ·
                  exact fin15Anchored_clause00666 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00667 chi hone hbad
                ·
                  exact fin15Anchored_clause00668 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00669 chi hone hbad
                ·
                  exact fin15Anchored_clause00670 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00671 chi hone hbad
                ·
                  exact fin15Anchored_clause00672 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00673 chi hone hbad
                ·
                  exact fin15Anchored_clause00674 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00675 chi hone hbad
                ·
                  exact fin15Anchored_clause00676 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00677 chi hone hbad
                ·
                  exact fin15Anchored_clause00678 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00679 chi hone hbad
                ·
                  exact fin15Anchored_clause00680 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00681 chi hone hbad
                ·
                  exact fin15Anchored_clause00682 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00683 chi hone hbad
                ·
                  exact fin15Anchored_clause00684 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00685 chi hone hbad
                ·
                  exact fin15Anchored_clause00686 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00687 chi hone hbad
                ·
                  exact fin15Anchored_clause00688 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00689 chi hone hbad
                ·
                  exact fin15Anchored_clause00690 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00691 chi hone hbad
                ·
                  exact fin15Anchored_clause00692 chi hone hbad
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
                exact fin15Anchored_clause00693 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00694 chi hone hbad
                ·
                  exact fin15Anchored_clause00695 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00696 chi hone hbad
                ·
                  exact fin15Anchored_clause00697 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00698 chi hone hbad
                ·
                  exact fin15Anchored_clause00699 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00700 chi hone hbad
                ·
                  exact fin15Anchored_clause00701 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00702 chi hone hbad
                ·
                  exact fin15Anchored_clause00703 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00704 chi hone hbad
                ·
                  exact fin15Anchored_clause00705 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00706 chi hone hbad
                ·
                  exact fin15Anchored_clause00707 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00708 chi hone hbad
                ·
                  exact fin15Anchored_clause00709 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00710 chi hone hbad
                ·
                  exact fin15Anchored_clause00711 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00712 chi hone hbad
                ·
                  exact fin15Anchored_clause00713 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00714 chi hone hbad
                ·
                  exact fin15Anchored_clause00715 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00716 chi hone hbad
                ·
                  exact fin15Anchored_clause00717 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00718 chi hone hbad
                ·
                  exact fin15Anchored_clause00719 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00720 chi hone hbad
                ·
                  exact fin15Anchored_clause00721 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00722 chi hone hbad
                ·
                  exact fin15Anchored_clause00723 chi hone hbad
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
                  exact fin15Anchored_clause00724 chi hone hbad
                ·
                  exact fin15Anchored_clause00725 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00726 chi hone hbad
                ·
                  exact fin15Anchored_clause00727 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00728 chi hone hbad
                ·
                  exact fin15Anchored_clause00729 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00730 chi hone hbad
                ·
                  exact fin15Anchored_clause00731 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00732 chi hone hbad
                ·
                  exact fin15Anchored_clause00733 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00734 chi hone hbad
                ·
                  exact fin15Anchored_clause00735 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00736 chi hone hbad
                ·
                  exact fin15Anchored_clause00737 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00738 chi hone hbad
                ·
                  exact fin15Anchored_clause00739 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00740 chi hone hbad
                ·
                  exact fin15Anchored_clause00741 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00742 chi hone hbad
                ·
                  exact fin15Anchored_clause00743 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00744 chi hone hbad
                ·
                  exact fin15Anchored_clause00745 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00746 chi hone hbad
                ·
                  exact fin15Anchored_clause00747 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00748 chi hone hbad
                ·
                  exact fin15Anchored_clause00749 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00750 chi hone hbad
                ·
                  exact fin15Anchored_clause00751 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00752 chi hone hbad
                ·
                  exact fin15Anchored_clause00753 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00754 chi hone hbad
                ·
                  exact fin15Anchored_clause00755 chi hone hbad

end ErdosSzekeres

end
