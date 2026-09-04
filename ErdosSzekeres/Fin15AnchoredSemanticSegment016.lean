module

public import ErdosSzekeres.Fin15AnchoredClauseChunk031
public import ErdosSzekeres.Fin15AnchoredClauseChunk032
public import ErdosSzekeres.Fin15AnchoredClauseChunk033

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 016. -/

theorem fin15Anchored_rejectSemanticSegment016
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0345 chi) ∨
      ((¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0345 chi) ∨
      (¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0345 chi))) ∨
      (((Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0345 chi) ∨
      (Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0345 chi)) ∨
      ((Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0345 chi) ∨
      (Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0345 chi)))) ∨
      ((((¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0346 chi) ∨
      (¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0346 chi)) ∨
      ((¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0346 chi) ∨
      (¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0346 chi))) ∨
      (((Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0346 chi) ∨
      (Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0346 chi)) ∨
      ((Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0346 chi) ∨
      (Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0346 chi))))) ∨
      (((((¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0347 chi) ∨
      (¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0347 chi)) ∨
      ((¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0347 chi) ∨
      (¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0347 chi))) ∨
      (((Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0347 chi) ∨
      (Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0347 chi)) ∨
      ((Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0347 chi) ∨
      (Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0347 chi)))) ∨
      ((((¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0348 chi) ∨
      (¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0348 chi)) ∨
      ((¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0348 chi) ∨
      (¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0348 chi))) ∨
      (((Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0348 chi) ∨
      (Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0348 chi)) ∨
      ((Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0348 chi) ∨
      (Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0348 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0349 chi) ∨
      (¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0349 chi)) ∨
      ((¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0349 chi) ∨
      (¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0349 chi))) ∨
      (((Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0349 chi) ∨
      (Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0349 chi)) ∨
      ((Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0349 chi) ∨
      (Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0349 chi)))) ∨
      ((((¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0350 chi) ∨
      (¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0350 chi)) ∨
      ((¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0350 chi) ∨
      (¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0350 chi))) ∨
      (((Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0350 chi) ∨
      (Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0350 chi)) ∨
      ((Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0350 chi) ∨
      (Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0350 chi))))) ∨
      (((((¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0351 chi) ∨
      (¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0351 chi)) ∨
      ((¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0351 chi) ∨
      (¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0351 chi))) ∨
      (((Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0351 chi) ∨
      (Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0351 chi)) ∨
      ((Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0351 chi) ∨
      (Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0351 chi)))) ∨
      ((((¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0352 chi) ∨
      (¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0352 chi)) ∨
      ((¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0352 chi) ∨
      (¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0352 chi))) ∨
      (((Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0352 chi) ∨
      (Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0352 chi)) ∨
      ((Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0352 chi) ∨
      (Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0352 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0354 chi) ∨
      ((¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0354 chi) ∨
      (¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0354 chi))) ∨
      (((¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0354 chi) ∨
      (Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0354 chi)) ∨
      ((Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0354 chi) ∨
      (Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0354 chi)))) ∨
      ((((Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0354 chi) ∨
      (¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0355 chi)) ∨
      ((¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0355 chi) ∨
      (¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0355 chi))) ∨
      (((¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0355 chi) ∨
      (Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0355 chi)) ∨
      ((Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0355 chi) ∨
      (Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0355 chi))))) ∨
      (((((Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0355 chi) ∨
      (¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0356 chi)) ∨
      ((¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0356 chi) ∨
      (¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0356 chi))) ∨
      (((¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0356 chi) ∨
      (Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0356 chi)) ∨
      ((Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0356 chi) ∨
      (Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0356 chi)))) ∨
      ((((Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0356 chi) ∨
      (¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0357 chi)) ∨
      ((¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0357 chi) ∨
      (¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0357 chi))) ∨
      (((¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0357 chi) ∨
      (Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0357 chi)) ∨
      ((Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0357 chi) ∨
      (Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0357 chi)))))) ∨
      ((((((Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0357 chi) ∨
      (¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0358 chi)) ∨
      ((¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0358 chi) ∨
      (¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0358 chi))) ∨
      (((¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0358 chi) ∨
      (Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0358 chi)) ∨
      ((Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0358 chi) ∨
      (Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0358 chi)))) ∨
      ((((¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0359 chi) ∨
      (¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0359 chi)) ∨
      ((¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0359 chi) ∨
      (¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0359 chi))) ∨
      (((Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0359 chi) ∨
      (Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0359 chi)) ∨
      ((Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0359 chi) ∨
      (Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0359 chi))))) ∨
      (((((¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0360 chi) ∨
      (¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0360 chi)) ∨
      ((¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0360 chi) ∨
      (¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0360 chi))) ∨
      (((Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0360 chi) ∨
      (Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0360 chi)) ∨
      ((Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0360 chi) ∨
      (Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0360 chi)))) ∨
      ((((¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0361 chi) ∨
      (¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0361 chi)) ∨
      ((¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0361 chi) ∨
      (¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0361 chi))) ∨
      (((Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0361 chi) ∨
      (Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0361 chi)) ∨
      ((Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0361 chi) ∨
      (Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0361 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0362 chi) ∨
      ((¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0362 chi) ∨
      (¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0362 chi))) ∨
      (((Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0362 chi) ∨
      (Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0362 chi)) ∨
      ((Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0362 chi) ∨
      (Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0362 chi)))) ∨
      ((((¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0363 chi) ∨
      (¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0363 chi)) ∨
      ((¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0363 chi) ∨
      (¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0363 chi))) ∨
      (((Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0363 chi) ∨
      (Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0363 chi)) ∨
      ((Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0363 chi) ∨
      (Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0363 chi))))) ∨
      (((((¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0364 chi) ∨
      (¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0364 chi)) ∨
      ((¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0364 chi) ∨
      (¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0364 chi))) ∨
      (((Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0364 chi) ∨
      (Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0364 chi)) ∨
      ((Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0364 chi) ∨
      (Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0364 chi)))) ∨
      ((((¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0365 chi) ∨
      (¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0365 chi)) ∨
      ((¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0365 chi) ∨
      (¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0365 chi))) ∨
      (((Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0365 chi) ∨
      (Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0365 chi)) ∨
      ((Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0365 chi) ∨
      (Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0365 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0366 chi) ∨
      (¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0366 chi)) ∨
      ((¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0366 chi) ∨
      (¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0366 chi))) ∨
      (((Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0366 chi) ∨
      (Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0366 chi)) ∨
      ((Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0366 chi) ∨
      (Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0366 chi)))) ∨
      ((((¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0367 chi) ∨
      (¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0367 chi)) ∨
      ((¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0367 chi) ∨
      (Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0367 chi))) ∨
      (((Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0367 chi) ∨
      (Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0367 chi)) ∨
      ((¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0368 chi) ∨
      (¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0368 chi))))) ∨
      (((((¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0368 chi) ∨
      (¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0369 chi)) ∨
      ((¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0369 chi) ∨
      (¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0369 chi))) ∨
      (((¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0369 chi) ∨
      (Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0369 chi)) ∨
      ((Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0369 chi) ∨
      (Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0369 chi)))) ∨
      ((((Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0369 chi) ∨
      (¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0370 chi)) ∨
      ((¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0370 chi) ∨
      (¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0370 chi))) ∨
      (((¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0370 chi) ∨
      (Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0370 chi)) ∨
      ((Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0370 chi) ∨
      (Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0370 chi))))))) ∨
      ((((((Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0370 chi) ∨
      ((¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0371 chi) ∨
      (¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0371 chi))) ∨
      (((¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0371 chi) ∨
      (¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0371 chi)) ∨
      ((Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0371 chi) ∨
      (Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0371 chi)))) ∨
      ((((Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0371 chi) ∨
      (Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0371 chi)) ∨
      ((¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0372 chi) ∨
      (¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0372 chi))) ∨
      (((¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0372 chi) ∨
      (¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0372 chi)) ∨
      ((Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0372 chi) ∨
      (Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0372 chi))))) ∨
      (((((Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0372 chi) ∨
      (Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0372 chi)) ∨
      ((¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0373 chi) ∨
      (¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0373 chi))) ∨
      (((¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0373 chi) ∨
      (¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0373 chi)) ∨
      ((Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0373 chi) ∨
      (Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0373 chi)))) ∨
      ((((Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0373 chi) ∨
      (Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0373 chi)) ∨
      ((¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0374 chi) ∨
      (¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0374 chi))) ∨
      (((¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0374 chi) ∨
      (¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0374 chi)) ∨
      ((Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0374 chi) ∨
      (Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0374 chi)))))) ∨
      ((((((Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0374 chi) ∨
      (Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0374 chi)) ∨
      ((¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0375 chi) ∨
      (¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0375 chi))) ∨
      (((¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0375 chi) ∨
      (Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0375 chi)) ∨
      ((Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0375 chi) ∨
      (¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0376 chi)))) ∨
      ((((¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0376 chi) ∨
      (¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0376 chi)) ∨
      ((¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0376 chi) ∨
      (Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0376 chi))) ∨
      (((Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0376 chi) ∨
      (Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0376 chi)) ∨
      ((Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0376 chi) ∨
      (¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0377 chi))))) ∨
      (((((¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0377 chi) ∨
      (¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0377 chi)) ∨
      ((¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0377 chi) ∨
      (Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0377 chi))) ∨
      (((Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0377 chi) ∨
      (Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0377 chi)) ∨
      ((Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0377 chi) ∨
      (¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0378 chi)))) ∨
      ((((¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0378 chi) ∨
      (¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0378 chi)) ∨
      ((¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0378 chi) ∨
      (Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0378 chi))) ∨
      (((Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0378 chi) ∨
      (Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0378 chi)) ∨
      ((Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0378 chi) ∨
      (¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0379 chi)))))))))) := by
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
                exact fin15Anchored_clause04038 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04039 chi hone hbad
                ·
                  exact fin15Anchored_clause04040 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04041 chi hone hbad
                ·
                  exact fin15Anchored_clause04042 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04043 chi hone hbad
                ·
                  exact fin15Anchored_clause04044 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04045 chi hone hbad
                ·
                  exact fin15Anchored_clause04046 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04047 chi hone hbad
                ·
                  exact fin15Anchored_clause04048 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04049 chi hone hbad
                ·
                  exact fin15Anchored_clause04050 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04051 chi hone hbad
                ·
                  exact fin15Anchored_clause04052 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04053 chi hone hbad
                ·
                  exact fin15Anchored_clause04054 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04055 chi hone hbad
                ·
                  exact fin15Anchored_clause04056 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04057 chi hone hbad
                ·
                  exact fin15Anchored_clause04058 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04059 chi hone hbad
                ·
                  exact fin15Anchored_clause04060 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04061 chi hone hbad
                ·
                  exact fin15Anchored_clause04062 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04063 chi hone hbad
                ·
                  exact fin15Anchored_clause04064 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04065 chi hone hbad
                ·
                  exact fin15Anchored_clause04066 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04067 chi hone hbad
                ·
                  exact fin15Anchored_clause04068 chi hone hbad
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
                  exact fin15Anchored_clause04069 chi hone hbad
                ·
                  exact fin15Anchored_clause04070 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04071 chi hone hbad
                ·
                  exact fin15Anchored_clause04072 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04073 chi hone hbad
                ·
                  exact fin15Anchored_clause04074 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04075 chi hone hbad
                ·
                  exact fin15Anchored_clause04076 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04077 chi hone hbad
                ·
                  exact fin15Anchored_clause04078 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04079 chi hone hbad
                ·
                  exact fin15Anchored_clause04080 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04081 chi hone hbad
                ·
                  exact fin15Anchored_clause04082 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04083 chi hone hbad
                ·
                  exact fin15Anchored_clause04084 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04085 chi hone hbad
                ·
                  exact fin15Anchored_clause04086 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04087 chi hone hbad
                ·
                  exact fin15Anchored_clause04088 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04089 chi hone hbad
                ·
                  exact fin15Anchored_clause04090 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04091 chi hone hbad
                ·
                  exact fin15Anchored_clause04092 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04093 chi hone hbad
                ·
                  exact fin15Anchored_clause04094 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04095 chi hone hbad
                ·
                  exact fin15Anchored_clause04096 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04097 chi hone hbad
                ·
                  exact fin15Anchored_clause04098 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04099 chi hone hbad
                ·
                  exact fin15Anchored_clause04100 chi hone hbad
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
                exact fin15Anchored_clause04101 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04102 chi hone hbad
                ·
                  exact fin15Anchored_clause04103 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04104 chi hone hbad
                ·
                  exact fin15Anchored_clause04105 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04106 chi hone hbad
                ·
                  exact fin15Anchored_clause04107 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04108 chi hone hbad
                ·
                  exact fin15Anchored_clause04109 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04110 chi hone hbad
                ·
                  exact fin15Anchored_clause04111 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04112 chi hone hbad
                ·
                  exact fin15Anchored_clause04113 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04114 chi hone hbad
                ·
                  exact fin15Anchored_clause04115 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04116 chi hone hbad
                ·
                  exact fin15Anchored_clause04117 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04118 chi hone hbad
                ·
                  exact fin15Anchored_clause04119 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04120 chi hone hbad
                ·
                  exact fin15Anchored_clause04121 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04122 chi hone hbad
                ·
                  exact fin15Anchored_clause04123 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04124 chi hone hbad
                ·
                  exact fin15Anchored_clause04125 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04126 chi hone hbad
                ·
                  exact fin15Anchored_clause04127 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04128 chi hone hbad
                ·
                  exact fin15Anchored_clause04129 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04130 chi hone hbad
                ·
                  exact fin15Anchored_clause04131 chi hone hbad
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
                  exact fin15Anchored_clause04132 chi hone hbad
                ·
                  exact fin15Anchored_clause04133 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04134 chi hone hbad
                ·
                  exact fin15Anchored_clause04135 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04136 chi hone hbad
                ·
                  exact fin15Anchored_clause04137 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04138 chi hone hbad
                ·
                  exact fin15Anchored_clause04139 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04140 chi hone hbad
                ·
                  exact fin15Anchored_clause04141 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04142 chi hone hbad
                ·
                  exact fin15Anchored_clause04143 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04144 chi hone hbad
                ·
                  exact fin15Anchored_clause04145 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04146 chi hone hbad
                ·
                  exact fin15Anchored_clause04147 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04148 chi hone hbad
                ·
                  exact fin15Anchored_clause04149 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04150 chi hone hbad
                ·
                  exact fin15Anchored_clause04151 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04152 chi hone hbad
                ·
                  exact fin15Anchored_clause04153 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04154 chi hone hbad
                ·
                  exact fin15Anchored_clause04155 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04156 chi hone hbad
                ·
                  exact fin15Anchored_clause04157 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04158 chi hone hbad
                ·
                  exact fin15Anchored_clause04159 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04160 chi hone hbad
                ·
                  exact fin15Anchored_clause04161 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04162 chi hone hbad
                ·
                  exact fin15Anchored_clause04163 chi hone hbad
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
                exact fin15Anchored_clause04164 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04165 chi hone hbad
                ·
                  exact fin15Anchored_clause04166 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04167 chi hone hbad
                ·
                  exact fin15Anchored_clause04168 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04169 chi hone hbad
                ·
                  exact fin15Anchored_clause04170 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04171 chi hone hbad
                ·
                  exact fin15Anchored_clause04172 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04173 chi hone hbad
                ·
                  exact fin15Anchored_clause04174 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04175 chi hone hbad
                ·
                  exact fin15Anchored_clause04176 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04177 chi hone hbad
                ·
                  exact fin15Anchored_clause04178 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04179 chi hone hbad
                ·
                  exact fin15Anchored_clause04180 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04181 chi hone hbad
                ·
                  exact fin15Anchored_clause04182 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04183 chi hone hbad
                ·
                  exact fin15Anchored_clause04184 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04185 chi hone hbad
                ·
                  exact fin15Anchored_clause04186 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04187 chi hone hbad
                ·
                  exact fin15Anchored_clause04188 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04189 chi hone hbad
                ·
                  exact fin15Anchored_clause04190 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04191 chi hone hbad
                ·
                  exact fin15Anchored_clause04192 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04193 chi hone hbad
                ·
                  exact fin15Anchored_clause04194 chi hone hbad
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
                  exact fin15Anchored_clause04195 chi hone hbad
                ·
                  exact fin15Anchored_clause04196 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04197 chi hone hbad
                ·
                  exact fin15Anchored_clause04198 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04199 chi hone hbad
                ·
                  exact fin15Anchored_clause04200 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04201 chi hone hbad
                ·
                  exact fin15Anchored_clause04202 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04203 chi hone hbad
                ·
                  exact fin15Anchored_clause04204 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04205 chi hone hbad
                ·
                  exact fin15Anchored_clause04206 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04207 chi hone hbad
                ·
                  exact fin15Anchored_clause04208 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04209 chi hone hbad
                ·
                  exact fin15Anchored_clause04210 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04211 chi hone hbad
                ·
                  exact fin15Anchored_clause04212 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04213 chi hone hbad
                ·
                  exact fin15Anchored_clause04214 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04215 chi hone hbad
                ·
                  exact fin15Anchored_clause04216 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04217 chi hone hbad
                ·
                  exact fin15Anchored_clause04218 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04219 chi hone hbad
                ·
                  exact fin15Anchored_clause04220 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04221 chi hone hbad
                ·
                  exact fin15Anchored_clause04222 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04223 chi hone hbad
                ·
                  exact fin15Anchored_clause04224 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04225 chi hone hbad
                ·
                  exact fin15Anchored_clause04226 chi hone hbad
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
                exact fin15Anchored_clause04227 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04228 chi hone hbad
                ·
                  exact fin15Anchored_clause04229 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04230 chi hone hbad
                ·
                  exact fin15Anchored_clause04231 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04232 chi hone hbad
                ·
                  exact fin15Anchored_clause04233 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04234 chi hone hbad
                ·
                  exact fin15Anchored_clause04235 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04236 chi hone hbad
                ·
                  exact fin15Anchored_clause04237 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04238 chi hone hbad
                ·
                  exact fin15Anchored_clause04239 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04240 chi hone hbad
                ·
                  exact fin15Anchored_clause04241 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04242 chi hone hbad
                ·
                  exact fin15Anchored_clause04243 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04244 chi hone hbad
                ·
                  exact fin15Anchored_clause04245 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04246 chi hone hbad
                ·
                  exact fin15Anchored_clause04247 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04248 chi hone hbad
                ·
                  exact fin15Anchored_clause04249 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04250 chi hone hbad
                ·
                  exact fin15Anchored_clause04251 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04252 chi hone hbad
                ·
                  exact fin15Anchored_clause04253 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04254 chi hone hbad
                ·
                  exact fin15Anchored_clause04255 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04256 chi hone hbad
                ·
                  exact fin15Anchored_clause04257 chi hone hbad
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
                  exact fin15Anchored_clause04258 chi hone hbad
                ·
                  exact fin15Anchored_clause04259 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04260 chi hone hbad
                ·
                  exact fin15Anchored_clause04261 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04262 chi hone hbad
                ·
                  exact fin15Anchored_clause04263 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04264 chi hone hbad
                ·
                  exact fin15Anchored_clause04265 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04266 chi hone hbad
                ·
                  exact fin15Anchored_clause04267 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04268 chi hone hbad
                ·
                  exact fin15Anchored_clause04269 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04270 chi hone hbad
                ·
                  exact fin15Anchored_clause04271 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04272 chi hone hbad
                ·
                  exact fin15Anchored_clause04273 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04274 chi hone hbad
                ·
                  exact fin15Anchored_clause04275 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04276 chi hone hbad
                ·
                  exact fin15Anchored_clause04277 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04278 chi hone hbad
                ·
                  exact fin15Anchored_clause04279 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04280 chi hone hbad
                ·
                  exact fin15Anchored_clause04281 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04282 chi hone hbad
                ·
                  exact fin15Anchored_clause04283 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04284 chi hone hbad
                ·
                  exact fin15Anchored_clause04285 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04286 chi hone hbad
                ·
                  exact fin15Anchored_clause04287 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04288 chi hone hbad
                ·
                  exact fin15Anchored_clause04289 chi hone hbad

end ErdosSzekeres

end
