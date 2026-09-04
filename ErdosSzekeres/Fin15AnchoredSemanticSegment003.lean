module

public import ErdosSzekeres.Fin15AnchoredClauseChunk005
public import ErdosSzekeres.Fin15AnchoredClauseChunk006
public import ErdosSzekeres.Fin15AnchoredClauseChunk007

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 003. -/

theorem fin15Anchored_rejectSemanticSegment003
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0270 chi) ∨
      ((Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0270 chi) ∨
      (¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0271 chi))) ∨
      (((¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0271 chi) ∨
      (¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0271 chi)) ∨
      ((¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0271 chi) ∨
      (Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0271 chi)))) ∨
      ((((Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0271 chi) ∨
      (Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0271 chi)) ∨
      ((Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0271 chi) ∨
      (¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0273 chi))) ∨
      (((¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0273 chi) ∨
      (¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0273 chi)) ∨
      ((¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0273 chi) ∨
      (Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0273 chi))))) ∨
      (((((Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0273 chi) ∨
      (Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0273 chi)) ∨
      ((Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0273 chi) ∨
      (¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0274 chi))) ∨
      (((¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0274 chi) ∨
      (¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0274 chi)) ∨
      ((¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0274 chi) ∨
      (Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0274 chi)))) ∨
      ((((Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0274 chi) ∨
      (Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0274 chi)) ∨
      ((Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0274 chi) ∨
      (¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0275 chi))) ∨
      (((¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0275 chi) ∨
      (¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0275 chi)) ∨
      ((¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0275 chi) ∨
      (Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0275 chi)))))) ∨
      ((((((Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0275 chi) ∨
      (Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0275 chi)) ∨
      ((Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0275 chi) ∨
      (¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0276 chi))) ∨
      (((¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0276 chi) ∨
      (¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0276 chi)) ∨
      ((¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0276 chi) ∨
      (Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0276 chi)))) ∨
      ((((Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0276 chi) ∨
      (Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0276 chi)) ∨
      ((Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0276 chi) ∨
      (¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0277 chi))) ∨
      (((¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0277 chi) ∨
      (¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0277 chi)) ∨
      ((Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0277 chi) ∨
      (Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0277 chi))))) ∨
      (((((Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0277 chi) ∨
      (¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0278 chi)) ∨
      ((¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0278 chi) ∨
      (¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0278 chi))) ∨
      (((¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0278 chi) ∨
      (Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0278 chi)) ∨
      ((Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0278 chi) ∨
      (Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0278 chi)))) ∨
      ((((Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0278 chi) ∨
      (¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0279 chi)) ∨
      ((¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0279 chi) ∨
      (¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0279 chi))) ∨
      (((¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0279 chi) ∨
      (Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0279 chi)) ∨
      ((Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0279 chi) ∨
      (Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0279 chi))))))) ∨
      ((((((Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0279 chi) ∨
      ((¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0280 chi) ∨
      (¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0280 chi))) ∨
      (((¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0280 chi) ∨
      (¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0280 chi)) ∨
      ((Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0280 chi) ∨
      (Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0280 chi)))) ∨
      ((((Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0280 chi) ∨
      (Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0280 chi)) ∨
      ((¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0281 chi) ∨
      (¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0281 chi))) ∨
      (((¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0281 chi) ∨
      (¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0281 chi)) ∨
      ((Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0281 chi) ∨
      (¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0282 chi))))) ∨
      (((((¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0282 chi) ∨
      (¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0282 chi)) ∨
      ((¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0282 chi) ∨
      (Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0282 chi))) ∨
      (((Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0282 chi) ∨
      (Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0282 chi)) ∨
      ((Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0282 chi) ∨
      (¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0283 chi)))) ∨
      ((((¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0283 chi) ∨
      (¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0283 chi)) ∨
      ((¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0283 chi) ∨
      (Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0283 chi))) ∨
      (((Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0283 chi) ∨
      (Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0283 chi)) ∨
      ((Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0283 chi) ∨
      (¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0284 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0284 chi) ∨
      (¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0284 chi)) ∨
      ((¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0284 chi) ∨
      (Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0284 chi))) ∨
      (((Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0284 chi) ∨
      (Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0284 chi)) ∨
      ((Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0284 chi) ∨
      (¬Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0285 chi)))) ∨
      ((((¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0285 chi) ∨
      (¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0285 chi)) ∨
      ((¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0285 chi) ∨
      (Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0285 chi))) ∨
      (((Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0285 chi) ∨
      (Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0285 chi)) ∨
      ((Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0285 chi) ∨
      (¬Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0286 chi))))) ∨
      (((((¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0286 chi) ∨
      (¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0286 chi)) ∨
      ((¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0286 chi) ∨
      (Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0286 chi))) ∨
      (((Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0286 chi) ∨
      (Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0286 chi)) ∨
      ((Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0286 chi) ∨
      (¬Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0287 chi)))) ∨
      ((((¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0287 chi) ∨
      (¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0287 chi)) ∨
      ((¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0288 chi) ∨
      (¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0288 chi))) ∨
      (((¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0288 chi) ∨
      (¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0288 chi)) ∨
      ((Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0288 chi) ∨
      (Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0288 chi)))))))) ∨
      (((((((Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0288 chi) ∨
      ((Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0288 chi) ∨
      (¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0289 chi))) ∨
      (((¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0289 chi) ∨
      (¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0289 chi)) ∨
      ((¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0289 chi) ∨
      (Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0289 chi)))) ∨
      ((((Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0289 chi) ∨
      (Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0289 chi)) ∨
      ((Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0289 chi) ∨
      (¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0290 chi))) ∨
      (((¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0290 chi) ∨
      (¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0290 chi)) ∨
      ((¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0290 chi) ∨
      (Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0290 chi))))) ∨
      (((((Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0290 chi) ∨
      (Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0290 chi)) ∨
      ((Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0290 chi) ∨
      (¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0291 chi))) ∨
      (((¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0291 chi) ∨
      (¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0291 chi)) ∨
      ((¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0291 chi) ∨
      (Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0291 chi)))) ∨
      ((((Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0291 chi) ∨
      (Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0291 chi)) ∨
      ((Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0291 chi) ∨
      (¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0292 chi))) ∨
      (((¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0292 chi) ∨
      (¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0292 chi)) ∨
      ((¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0292 chi) ∨
      (Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0292 chi)))))) ∨
      ((((((Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0292 chi) ∨
      (Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0292 chi)) ∨
      ((Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0292 chi) ∨
      (¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0293 chi))) ∨
      (((¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0293 chi) ∨
      (¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0293 chi)) ∨
      ((¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0293 chi) ∨
      (Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0293 chi)))) ∨
      ((((Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0293 chi) ∨
      (Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0293 chi)) ∨
      ((Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0293 chi) ∨
      (¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0294 chi))) ∨
      (((¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0294 chi) ∨
      (¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0294 chi)) ∨
      ((¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0294 chi) ∨
      (Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0294 chi))))) ∨
      (((((Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0294 chi) ∨
      (Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0294 chi)) ∨
      ((Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0294 chi) ∨
      (¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0295 chi))) ∨
      (((¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0295 chi) ∨
      (¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0295 chi)) ∨
      ((¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0295 chi) ∨
      (Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0295 chi)))) ∨
      ((((Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0295 chi) ∨
      (Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0295 chi)) ∨
      ((Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0295 chi) ∨
      (¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0296 chi))) ∨
      (((¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0296 chi) ∨
      (¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0296 chi)) ∨
      ((¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0296 chi) ∨
      (Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0296 chi))))))) ∨
      (((((((Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0296 chi) ∨
      (Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0296 chi)) ∨
      ((Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0296 chi) ∨
      (¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0297 chi))) ∨
      (((¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0297 chi) ∨
      (¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0297 chi)) ∨
      ((¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0297 chi) ∨
      (Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0297 chi)))) ∨
      ((((Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0297 chi) ∨
      (Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0297 chi)) ∨
      ((Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0297 chi) ∨
      (¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0298 chi))) ∨
      (((¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0298 chi) ∨
      (¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0298 chi)) ∨
      ((¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0298 chi) ∨
      (Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0298 chi))))) ∨
      (((((Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0298 chi) ∨
      (Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0298 chi)) ∨
      ((Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0298 chi) ∨
      (¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0299 chi))) ∨
      (((¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0299 chi) ∨
      (¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0299 chi)) ∨
      ((¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0299 chi) ∨
      (Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0299 chi)))) ∨
      ((((Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0299 chi) ∨
      (Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0299 chi)) ∨
      ((Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0299 chi) ∨
      (¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0300 chi))) ∨
      (((¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0300 chi) ∨
      (¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0300 chi)) ∨
      ((¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0300 chi) ∨
      (Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0300 chi)))))) ∨
      ((((((Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0300 chi) ∨
      (Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0300 chi)) ∨
      ((Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0300 chi) ∨
      (¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0301 chi))) ∨
      (((¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0301 chi) ∨
      (¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0301 chi)) ∨
      ((¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0301 chi) ∨
      (Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0301 chi)))) ∨
      ((((Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0301 chi) ∨
      (Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0301 chi)) ∨
      ((Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0301 chi) ∨
      (¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0302 chi))) ∨
      (((¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0302 chi) ∨
      (¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0302 chi)) ∨
      ((¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0302 chi) ∨
      (Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0302 chi))))) ∨
      (((((Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0302 chi) ∨
      (Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0302 chi)) ∨
      ((Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0302 chi) ∨
      (¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0303 chi))) ∨
      (((¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0303 chi) ∨
      (¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0303 chi)) ∨
      ((¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0303 chi) ∨
      (Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0303 chi)))) ∨
      ((((Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0303 chi) ∨
      (Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0303 chi)) ∨
      ((Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0303 chi) ∨
      (¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0304 chi))) ∨
      (((¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0304 chi) ∨
      (Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0304 chi)) ∨
      ((Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0304 chi) ∨
      (¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0305 chi)))))))))) := by
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
                exact fin15Anchored_clause00756 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00757 chi hone hbad
                ·
                  exact fin15Anchored_clause00758 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00759 chi hone hbad
                ·
                  exact fin15Anchored_clause00760 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00761 chi hone hbad
                ·
                  exact fin15Anchored_clause00762 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00763 chi hone hbad
                ·
                  exact fin15Anchored_clause00764 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00765 chi hone hbad
                ·
                  exact fin15Anchored_clause00766 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00767 chi hone hbad
                ·
                  exact fin15Anchored_clause00768 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00769 chi hone hbad
                ·
                  exact fin15Anchored_clause00770 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00771 chi hone hbad
                ·
                  exact fin15Anchored_clause00772 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00773 chi hone hbad
                ·
                  exact fin15Anchored_clause00774 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00775 chi hone hbad
                ·
                  exact fin15Anchored_clause00776 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00777 chi hone hbad
                ·
                  exact fin15Anchored_clause00778 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00779 chi hone hbad
                ·
                  exact fin15Anchored_clause00780 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00781 chi hone hbad
                ·
                  exact fin15Anchored_clause00782 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00783 chi hone hbad
                ·
                  exact fin15Anchored_clause00784 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00785 chi hone hbad
                ·
                  exact fin15Anchored_clause00786 chi hone hbad
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
                  exact fin15Anchored_clause00787 chi hone hbad
                ·
                  exact fin15Anchored_clause00788 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00789 chi hone hbad
                ·
                  exact fin15Anchored_clause00790 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00791 chi hone hbad
                ·
                  exact fin15Anchored_clause00792 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00793 chi hone hbad
                ·
                  exact fin15Anchored_clause00794 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00795 chi hone hbad
                ·
                  exact fin15Anchored_clause00796 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00797 chi hone hbad
                ·
                  exact fin15Anchored_clause00798 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00799 chi hone hbad
                ·
                  exact fin15Anchored_clause00800 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00801 chi hone hbad
                ·
                  exact fin15Anchored_clause00802 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00803 chi hone hbad
                ·
                  exact fin15Anchored_clause00804 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00805 chi hone hbad
                ·
                  exact fin15Anchored_clause00806 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00807 chi hone hbad
                ·
                  exact fin15Anchored_clause00808 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00809 chi hone hbad
                ·
                  exact fin15Anchored_clause00810 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00811 chi hone hbad
                ·
                  exact fin15Anchored_clause00812 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00813 chi hone hbad
                ·
                  exact fin15Anchored_clause00814 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00815 chi hone hbad
                ·
                  exact fin15Anchored_clause00816 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00817 chi hone hbad
                ·
                  exact fin15Anchored_clause00818 chi hone hbad
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
                exact fin15Anchored_clause00819 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00820 chi hone hbad
                ·
                  exact fin15Anchored_clause00821 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00822 chi hone hbad
                ·
                  exact fin15Anchored_clause00823 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00824 chi hone hbad
                ·
                  exact fin15Anchored_clause00825 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00826 chi hone hbad
                ·
                  exact fin15Anchored_clause00827 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00828 chi hone hbad
                ·
                  exact fin15Anchored_clause00829 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00830 chi hone hbad
                ·
                  exact fin15Anchored_clause00831 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00832 chi hone hbad
                ·
                  exact fin15Anchored_clause00833 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00834 chi hone hbad
                ·
                  exact fin15Anchored_clause00835 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00836 chi hone hbad
                ·
                  exact fin15Anchored_clause00837 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00838 chi hone hbad
                ·
                  exact fin15Anchored_clause00839 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00840 chi hone hbad
                ·
                  exact fin15Anchored_clause00841 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00842 chi hone hbad
                ·
                  exact fin15Anchored_clause00843 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00844 chi hone hbad
                ·
                  exact fin15Anchored_clause00845 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00846 chi hone hbad
                ·
                  exact fin15Anchored_clause00847 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00848 chi hone hbad
                ·
                  exact fin15Anchored_clause00849 chi hone hbad
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
                  exact fin15Anchored_clause00850 chi hone hbad
                ·
                  exact fin15Anchored_clause00851 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00852 chi hone hbad
                ·
                  exact fin15Anchored_clause00853 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00854 chi hone hbad
                ·
                  exact fin15Anchored_clause00855 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00856 chi hone hbad
                ·
                  exact fin15Anchored_clause00857 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00858 chi hone hbad
                ·
                  exact fin15Anchored_clause00859 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00860 chi hone hbad
                ·
                  exact fin15Anchored_clause00861 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00862 chi hone hbad
                ·
                  exact fin15Anchored_clause00863 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00864 chi hone hbad
                ·
                  exact fin15Anchored_clause00865 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00866 chi hone hbad
                ·
                  exact fin15Anchored_clause00867 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00868 chi hone hbad
                ·
                  exact fin15Anchored_clause00869 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00870 chi hone hbad
                ·
                  exact fin15Anchored_clause00871 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00872 chi hone hbad
                ·
                  exact fin15Anchored_clause00873 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00874 chi hone hbad
                ·
                  exact fin15Anchored_clause00875 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00876 chi hone hbad
                ·
                  exact fin15Anchored_clause00877 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00878 chi hone hbad
                ·
                  exact fin15Anchored_clause00879 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00880 chi hone hbad
                ·
                  exact fin15Anchored_clause00881 chi hone hbad
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
                exact fin15Anchored_clause00882 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00883 chi hone hbad
                ·
                  exact fin15Anchored_clause00884 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00885 chi hone hbad
                ·
                  exact fin15Anchored_clause00886 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00887 chi hone hbad
                ·
                  exact fin15Anchored_clause00888 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00889 chi hone hbad
                ·
                  exact fin15Anchored_clause00890 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00891 chi hone hbad
                ·
                  exact fin15Anchored_clause00892 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00893 chi hone hbad
                ·
                  exact fin15Anchored_clause00894 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00895 chi hone hbad
                ·
                  exact fin15Anchored_clause00896 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00897 chi hone hbad
                ·
                  exact fin15Anchored_clause00898 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00899 chi hone hbad
                ·
                  exact fin15Anchored_clause00900 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00901 chi hone hbad
                ·
                  exact fin15Anchored_clause00902 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00903 chi hone hbad
                ·
                  exact fin15Anchored_clause00904 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00905 chi hone hbad
                ·
                  exact fin15Anchored_clause00906 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00907 chi hone hbad
                ·
                  exact fin15Anchored_clause00908 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00909 chi hone hbad
                ·
                  exact fin15Anchored_clause00910 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00911 chi hone hbad
                ·
                  exact fin15Anchored_clause00912 chi hone hbad
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
                  exact fin15Anchored_clause00913 chi hone hbad
                ·
                  exact fin15Anchored_clause00914 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00915 chi hone hbad
                ·
                  exact fin15Anchored_clause00916 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00917 chi hone hbad
                ·
                  exact fin15Anchored_clause00918 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00919 chi hone hbad
                ·
                  exact fin15Anchored_clause00920 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00921 chi hone hbad
                ·
                  exact fin15Anchored_clause00922 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00923 chi hone hbad
                ·
                  exact fin15Anchored_clause00924 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00925 chi hone hbad
                ·
                  exact fin15Anchored_clause00926 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00927 chi hone hbad
                ·
                  exact fin15Anchored_clause00928 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00929 chi hone hbad
                ·
                  exact fin15Anchored_clause00930 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00931 chi hone hbad
                ·
                  exact fin15Anchored_clause00932 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00933 chi hone hbad
                ·
                  exact fin15Anchored_clause00934 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00935 chi hone hbad
                ·
                  exact fin15Anchored_clause00936 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00937 chi hone hbad
                ·
                  exact fin15Anchored_clause00938 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00939 chi hone hbad
                ·
                  exact fin15Anchored_clause00940 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00941 chi hone hbad
                ·
                  exact fin15Anchored_clause00942 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00943 chi hone hbad
                ·
                  exact fin15Anchored_clause00944 chi hone hbad
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
                  exact fin15Anchored_clause00945 chi hone hbad
                ·
                  exact fin15Anchored_clause00946 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00947 chi hone hbad
                ·
                  exact fin15Anchored_clause00948 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00949 chi hone hbad
                ·
                  exact fin15Anchored_clause00950 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00951 chi hone hbad
                ·
                  exact fin15Anchored_clause00952 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00953 chi hone hbad
                ·
                  exact fin15Anchored_clause00954 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00955 chi hone hbad
                ·
                  exact fin15Anchored_clause00956 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00957 chi hone hbad
                ·
                  exact fin15Anchored_clause00958 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00959 chi hone hbad
                ·
                  exact fin15Anchored_clause00960 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00961 chi hone hbad
                ·
                  exact fin15Anchored_clause00962 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00963 chi hone hbad
                ·
                  exact fin15Anchored_clause00964 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00965 chi hone hbad
                ·
                  exact fin15Anchored_clause00966 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00967 chi hone hbad
                ·
                  exact fin15Anchored_clause00968 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00969 chi hone hbad
                ·
                  exact fin15Anchored_clause00970 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00971 chi hone hbad
                ·
                  exact fin15Anchored_clause00972 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00973 chi hone hbad
                ·
                  exact fin15Anchored_clause00974 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00975 chi hone hbad
                ·
                  exact fin15Anchored_clause00976 chi hone hbad
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
                  exact fin15Anchored_clause00977 chi hone hbad
                ·
                  exact fin15Anchored_clause00978 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00979 chi hone hbad
                ·
                  exact fin15Anchored_clause00980 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00981 chi hone hbad
                ·
                  exact fin15Anchored_clause00982 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00983 chi hone hbad
                ·
                  exact fin15Anchored_clause00984 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00985 chi hone hbad
                ·
                  exact fin15Anchored_clause00986 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00987 chi hone hbad
                ·
                  exact fin15Anchored_clause00988 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00989 chi hone hbad
                ·
                  exact fin15Anchored_clause00990 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00991 chi hone hbad
                ·
                  exact fin15Anchored_clause00992 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00993 chi hone hbad
                ·
                  exact fin15Anchored_clause00994 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00995 chi hone hbad
                ·
                  exact fin15Anchored_clause00996 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00997 chi hone hbad
                ·
                  exact fin15Anchored_clause00998 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause00999 chi hone hbad
                ·
                  exact fin15Anchored_clause01000 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01001 chi hone hbad
                ·
                  exact fin15Anchored_clause01002 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01003 chi hone hbad
                ·
                  exact fin15Anchored_clause01004 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01005 chi hone hbad
                ·
                  exact fin15Anchored_clause01006 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01007 chi hone hbad
                ·
                  exact fin15Anchored_clause01008 chi hone hbad

end ErdosSzekeres

end
