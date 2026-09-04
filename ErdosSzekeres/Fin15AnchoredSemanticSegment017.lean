module

public import ErdosSzekeres.Fin15AnchoredClauseChunk033
public import ErdosSzekeres.Fin15AnchoredClauseChunk034
public import ErdosSzekeres.Fin15AnchoredClauseChunk035

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 017. -/

theorem fin15Anchored_rejectSemanticSegment017
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0379 chi) ∨
      ((¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0379 chi) ∨
      (¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0379 chi))) ∨
      (((Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0379 chi) ∨
      (Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0379 chi)) ∨
      ((Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0379 chi) ∨
      (Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0379 chi)))) ∨
      ((((¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0380 chi) ∨
      (¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0380 chi)) ∨
      ((¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0380 chi) ∨
      (¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0380 chi))) ∨
      (((Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0380 chi) ∨
      (Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0380 chi)) ∨
      ((Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0380 chi) ∨
      (Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0380 chi))))) ∨
      (((((¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0382 chi) ∨
      (¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0382 chi)) ∨
      ((¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0382 chi) ∨
      (¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0382 chi))) ∨
      (((Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0382 chi) ∨
      (Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0382 chi)) ∨
      ((Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0382 chi) ∨
      (Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0382 chi)))) ∨
      ((((¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0383 chi) ∨
      (¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0383 chi)) ∨
      ((¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0383 chi) ∨
      (¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0383 chi))) ∨
      (((Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0383 chi) ∨
      (Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0383 chi)) ∨
      ((Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0383 chi) ∨
      (Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0383 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0384 chi) ∨
      (¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0384 chi)) ∨
      ((¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0384 chi) ∨
      (¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0384 chi))) ∨
      (((Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0384 chi) ∨
      (Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0384 chi)) ∨
      ((Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0384 chi) ∨
      (Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0384 chi)))) ∨
      ((((¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0385 chi) ∨
      (¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0385 chi)) ∨
      ((¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0385 chi) ∨
      (¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0385 chi))) ∨
      (((Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0385 chi) ∨
      (Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0385 chi)) ∨
      ((Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0385 chi) ∨
      (Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0385 chi))))) ∨
      (((((¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0386 chi) ∨
      (¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0386 chi)) ∨
      ((¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0386 chi) ∨
      (¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0386 chi))) ∨
      (((Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0386 chi) ∨
      (Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0386 chi)) ∨
      ((Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0386 chi) ∨
      (Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0386 chi)))) ∨
      ((((¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0387 chi) ∨
      (¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0387 chi)) ∨
      ((¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0387 chi) ∨
      (¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0387 chi))) ∨
      (((Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0387 chi) ∨
      (Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0387 chi)) ∨
      ((Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0387 chi) ∨
      (Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0387 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0388 chi) ∨
      ((¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0388 chi) ∨
      (¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0388 chi))) ∨
      (((¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0388 chi) ∨
      (Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0388 chi)) ∨
      ((Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0388 chi) ∨
      (Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0388 chi)))) ∨
      ((((Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0388 chi) ∨
      (¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0389 chi)) ∨
      ((¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0389 chi) ∨
      (¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0389 chi))) ∨
      (((¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0389 chi) ∨
      (Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0389 chi)) ∨
      ((Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0389 chi) ∨
      (Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0389 chi))))) ∨
      (((((Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0389 chi) ∨
      (¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0390 chi)) ∨
      ((¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0390 chi) ∨
      (¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0390 chi))) ∨
      (((¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0390 chi) ∨
      (Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0390 chi)) ∨
      ((Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0390 chi) ∨
      (Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0390 chi)))) ∨
      ((((Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0390 chi) ∨
      (¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0391 chi)) ∨
      ((¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0391 chi) ∨
      (¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0391 chi))) ∨
      (((¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0391 chi) ∨
      (Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0391 chi)) ∨
      ((Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0391 chi) ∨
      (Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0391 chi)))))) ∨
      ((((((Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0391 chi) ∨
      (¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0392 chi)) ∨
      ((¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0392 chi) ∨
      (¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0392 chi))) ∨
      (((¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0392 chi) ∨
      (Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0392 chi)) ∨
      ((Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0392 chi) ∨
      (Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0392 chi)))) ∨
      ((((Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0392 chi) ∨
      (¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0393 chi)) ∨
      ((¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0393 chi) ∨
      (¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0393 chi))) ∨
      (((¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0393 chi) ∨
      (Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0393 chi)) ∨
      ((Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0393 chi) ∨
      (Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0393 chi))))) ∨
      (((((Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0393 chi) ∨
      (¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0394 chi)) ∨
      ((¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0394 chi) ∨
      (¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0394 chi))) ∨
      (((¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0394 chi) ∨
      (Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0394 chi)) ∨
      ((Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0394 chi) ∨
      (Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0394 chi)))) ∨
      ((((¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0395 chi) ∨
      (¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0395 chi)) ∨
      ((¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0395 chi) ∨
      (¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0395 chi))) ∨
      (((Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0395 chi) ∨
      (Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0395 chi)) ∨
      ((Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0395 chi) ∨
      (Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0395 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0397 chi) ∨
      ((¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0397 chi) ∨
      (¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0397 chi))) ∨
      (((¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0397 chi) ∨
      (Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0397 chi)) ∨
      ((Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0397 chi) ∨
      (Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0397 chi)))) ∨
      ((((Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0397 chi) ∨
      (¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0398 chi)) ∨
      ((¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0398 chi) ∨
      (¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0398 chi))) ∨
      (((¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0398 chi) ∨
      (Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0398 chi)) ∨
      ((Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0398 chi) ∨
      (Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0398 chi))))) ∨
      (((((Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0398 chi) ∨
      (¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0399 chi)) ∨
      ((¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0399 chi) ∨
      (¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0399 chi))) ∨
      (((¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0399 chi) ∨
      (Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0399 chi)) ∨
      ((Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0399 chi) ∨
      (Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0399 chi)))) ∨
      ((((Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0399 chi) ∨
      (¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0400 chi)) ∨
      ((¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0400 chi) ∨
      (¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0400 chi))) ∨
      (((¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0400 chi) ∨
      (Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0400 chi)) ∨
      ((Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0400 chi) ∨
      (Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0400 chi)))))) ∨
      ((((((Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0400 chi) ∨
      (¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0401 chi)) ∨
      ((¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0401 chi) ∨
      (¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0401 chi))) ∨
      (((¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0401 chi) ∨
      (Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0401 chi)) ∨
      ((Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0401 chi) ∨
      (Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0401 chi)))) ∨
      ((((Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0401 chi) ∨
      (¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0403 chi)) ∨
      ((¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0403 chi) ∨
      (¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0403 chi))) ∨
      (((¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0403 chi) ∨
      (Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0403 chi)) ∨
      ((Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0403 chi) ∨
      (Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0403 chi))))) ∨
      (((((Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0403 chi) ∨
      (¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0404 chi)) ∨
      ((¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0404 chi) ∨
      (¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0404 chi))) ∨
      (((¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0404 chi) ∨
      (Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0404 chi)) ∨
      ((Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0404 chi) ∨
      (Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0404 chi)))) ∨
      ((((Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0404 chi) ∨
      (¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0405 chi)) ∨
      ((¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0405 chi) ∨
      (¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0405 chi))) ∨
      (((¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0405 chi) ∨
      (Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0405 chi)) ∨
      ((Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0405 chi) ∨
      (Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0405 chi))))))) ∨
      ((((((Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0405 chi) ∨
      ((¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0406 chi) ∨
      (¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0406 chi))) ∨
      (((¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0406 chi) ∨
      (¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0406 chi)) ∨
      ((Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0406 chi) ∨
      (Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0406 chi)))) ∨
      ((((Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0406 chi) ∨
      (Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0406 chi)) ∨
      ((¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0407 chi) ∨
      (¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0407 chi))) ∨
      (((¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0407 chi) ∨
      (¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0407 chi)) ∨
      ((Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0407 chi) ∨
      (Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0407 chi))))) ∨
      (((((Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0407 chi) ∨
      (¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0408 chi)) ∨
      ((¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0408 chi) ∨
      (¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0408 chi))) ∨
      (((¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0408 chi) ∨
      (Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0408 chi)) ∨
      ((Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0408 chi) ∨
      (Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0408 chi)))) ∨
      ((((Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0408 chi) ∨
      (¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0409 chi)) ∨
      ((¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0409 chi) ∨
      (¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0409 chi))) ∨
      (((¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0409 chi) ∨
      (Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0409 chi)) ∨
      ((Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0409 chi) ∨
      (Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0409 chi)))))) ∨
      ((((((Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0409 chi) ∨
      (¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0410 chi)) ∨
      ((¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0410 chi) ∨
      (¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0410 chi))) ∨
      (((¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0410 chi) ∨
      (Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0410 chi)) ∨
      ((Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0410 chi) ∨
      (Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0410 chi)))) ∨
      ((((Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0410 chi) ∨
      (¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0411 chi)) ∨
      ((¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0411 chi) ∨
      (¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0411 chi))) ∨
      (((¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0411 chi) ∨
      (Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0411 chi)) ∨
      ((Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0411 chi) ∨
      (Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0411 chi))))) ∨
      (((((Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0411 chi) ∨
      (¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0412 chi)) ∨
      ((¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0412 chi) ∨
      (¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0412 chi))) ∨
      (((¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0412 chi) ∨
      (Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0412 chi)) ∨
      ((Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0412 chi) ∨
      (Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0412 chi)))) ∨
      ((((Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0412 chi) ∨
      (¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0413 chi)) ∨
      ((¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0413 chi) ∨
      (¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0413 chi))) ∨
      (((¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0413 chi) ∨
      (Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0413 chi)) ∨
      ((Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0413 chi) ∨
      (Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0413 chi)))))))))) := by
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
                exact fin15Anchored_clause04290 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04291 chi hone hbad
                ·
                  exact fin15Anchored_clause04292 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04293 chi hone hbad
                ·
                  exact fin15Anchored_clause04294 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04295 chi hone hbad
                ·
                  exact fin15Anchored_clause04296 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04297 chi hone hbad
                ·
                  exact fin15Anchored_clause04298 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04299 chi hone hbad
                ·
                  exact fin15Anchored_clause04300 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04301 chi hone hbad
                ·
                  exact fin15Anchored_clause04302 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04303 chi hone hbad
                ·
                  exact fin15Anchored_clause04304 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04305 chi hone hbad
                ·
                  exact fin15Anchored_clause04306 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04307 chi hone hbad
                ·
                  exact fin15Anchored_clause04308 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04309 chi hone hbad
                ·
                  exact fin15Anchored_clause04310 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04311 chi hone hbad
                ·
                  exact fin15Anchored_clause04312 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04313 chi hone hbad
                ·
                  exact fin15Anchored_clause04314 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04315 chi hone hbad
                ·
                  exact fin15Anchored_clause04316 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04317 chi hone hbad
                ·
                  exact fin15Anchored_clause04318 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04319 chi hone hbad
                ·
                  exact fin15Anchored_clause04320 chi hone hbad
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
                  exact fin15Anchored_clause04321 chi hone hbad
                ·
                  exact fin15Anchored_clause04322 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04323 chi hone hbad
                ·
                  exact fin15Anchored_clause04324 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04325 chi hone hbad
                ·
                  exact fin15Anchored_clause04326 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04327 chi hone hbad
                ·
                  exact fin15Anchored_clause04328 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04329 chi hone hbad
                ·
                  exact fin15Anchored_clause04330 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04331 chi hone hbad
                ·
                  exact fin15Anchored_clause04332 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04333 chi hone hbad
                ·
                  exact fin15Anchored_clause04334 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04335 chi hone hbad
                ·
                  exact fin15Anchored_clause04336 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04337 chi hone hbad
                ·
                  exact fin15Anchored_clause04338 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04339 chi hone hbad
                ·
                  exact fin15Anchored_clause04340 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04341 chi hone hbad
                ·
                  exact fin15Anchored_clause04342 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04343 chi hone hbad
                ·
                  exact fin15Anchored_clause04344 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04345 chi hone hbad
                ·
                  exact fin15Anchored_clause04346 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04347 chi hone hbad
                ·
                  exact fin15Anchored_clause04348 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04349 chi hone hbad
                ·
                  exact fin15Anchored_clause04350 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04351 chi hone hbad
                ·
                  exact fin15Anchored_clause04352 chi hone hbad
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
                exact fin15Anchored_clause04353 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04354 chi hone hbad
                ·
                  exact fin15Anchored_clause04355 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04356 chi hone hbad
                ·
                  exact fin15Anchored_clause04357 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04358 chi hone hbad
                ·
                  exact fin15Anchored_clause04359 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04360 chi hone hbad
                ·
                  exact fin15Anchored_clause04361 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04362 chi hone hbad
                ·
                  exact fin15Anchored_clause04363 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04364 chi hone hbad
                ·
                  exact fin15Anchored_clause04365 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04366 chi hone hbad
                ·
                  exact fin15Anchored_clause04367 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04368 chi hone hbad
                ·
                  exact fin15Anchored_clause04369 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04370 chi hone hbad
                ·
                  exact fin15Anchored_clause04371 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04372 chi hone hbad
                ·
                  exact fin15Anchored_clause04373 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04374 chi hone hbad
                ·
                  exact fin15Anchored_clause04375 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04376 chi hone hbad
                ·
                  exact fin15Anchored_clause04377 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04378 chi hone hbad
                ·
                  exact fin15Anchored_clause04379 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04380 chi hone hbad
                ·
                  exact fin15Anchored_clause04381 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04382 chi hone hbad
                ·
                  exact fin15Anchored_clause04383 chi hone hbad
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
                  exact fin15Anchored_clause04384 chi hone hbad
                ·
                  exact fin15Anchored_clause04385 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04386 chi hone hbad
                ·
                  exact fin15Anchored_clause04387 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04388 chi hone hbad
                ·
                  exact fin15Anchored_clause04389 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04390 chi hone hbad
                ·
                  exact fin15Anchored_clause04391 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04392 chi hone hbad
                ·
                  exact fin15Anchored_clause04393 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04394 chi hone hbad
                ·
                  exact fin15Anchored_clause04395 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04396 chi hone hbad
                ·
                  exact fin15Anchored_clause04397 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04398 chi hone hbad
                ·
                  exact fin15Anchored_clause04399 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04400 chi hone hbad
                ·
                  exact fin15Anchored_clause04401 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04402 chi hone hbad
                ·
                  exact fin15Anchored_clause04403 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04404 chi hone hbad
                ·
                  exact fin15Anchored_clause04405 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04406 chi hone hbad
                ·
                  exact fin15Anchored_clause04407 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04408 chi hone hbad
                ·
                  exact fin15Anchored_clause04409 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04410 chi hone hbad
                ·
                  exact fin15Anchored_clause04411 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04412 chi hone hbad
                ·
                  exact fin15Anchored_clause04413 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04414 chi hone hbad
                ·
                  exact fin15Anchored_clause04415 chi hone hbad
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
                exact fin15Anchored_clause04416 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04417 chi hone hbad
                ·
                  exact fin15Anchored_clause04418 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04419 chi hone hbad
                ·
                  exact fin15Anchored_clause04420 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04421 chi hone hbad
                ·
                  exact fin15Anchored_clause04422 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04423 chi hone hbad
                ·
                  exact fin15Anchored_clause04424 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04425 chi hone hbad
                ·
                  exact fin15Anchored_clause04426 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04427 chi hone hbad
                ·
                  exact fin15Anchored_clause04428 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04429 chi hone hbad
                ·
                  exact fin15Anchored_clause04430 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04431 chi hone hbad
                ·
                  exact fin15Anchored_clause04432 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04433 chi hone hbad
                ·
                  exact fin15Anchored_clause04434 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04435 chi hone hbad
                ·
                  exact fin15Anchored_clause04436 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04437 chi hone hbad
                ·
                  exact fin15Anchored_clause04438 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04439 chi hone hbad
                ·
                  exact fin15Anchored_clause04440 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04441 chi hone hbad
                ·
                  exact fin15Anchored_clause04442 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04443 chi hone hbad
                ·
                  exact fin15Anchored_clause04444 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04445 chi hone hbad
                ·
                  exact fin15Anchored_clause04446 chi hone hbad
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
                  exact fin15Anchored_clause04447 chi hone hbad
                ·
                  exact fin15Anchored_clause04448 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04449 chi hone hbad
                ·
                  exact fin15Anchored_clause04450 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04451 chi hone hbad
                ·
                  exact fin15Anchored_clause04452 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04453 chi hone hbad
                ·
                  exact fin15Anchored_clause04454 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04455 chi hone hbad
                ·
                  exact fin15Anchored_clause04456 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04457 chi hone hbad
                ·
                  exact fin15Anchored_clause04458 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04459 chi hone hbad
                ·
                  exact fin15Anchored_clause04460 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04461 chi hone hbad
                ·
                  exact fin15Anchored_clause04462 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04463 chi hone hbad
                ·
                  exact fin15Anchored_clause04464 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04465 chi hone hbad
                ·
                  exact fin15Anchored_clause04466 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04467 chi hone hbad
                ·
                  exact fin15Anchored_clause04468 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04469 chi hone hbad
                ·
                  exact fin15Anchored_clause04470 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04471 chi hone hbad
                ·
                  exact fin15Anchored_clause04472 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04473 chi hone hbad
                ·
                  exact fin15Anchored_clause04474 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04475 chi hone hbad
                ·
                  exact fin15Anchored_clause04476 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04477 chi hone hbad
                ·
                  exact fin15Anchored_clause04478 chi hone hbad
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
                exact fin15Anchored_clause04479 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04480 chi hone hbad
                ·
                  exact fin15Anchored_clause04481 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04482 chi hone hbad
                ·
                  exact fin15Anchored_clause04483 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04484 chi hone hbad
                ·
                  exact fin15Anchored_clause04485 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04486 chi hone hbad
                ·
                  exact fin15Anchored_clause04487 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04488 chi hone hbad
                ·
                  exact fin15Anchored_clause04489 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04490 chi hone hbad
                ·
                  exact fin15Anchored_clause04491 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04492 chi hone hbad
                ·
                  exact fin15Anchored_clause04493 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04494 chi hone hbad
                ·
                  exact fin15Anchored_clause04495 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04496 chi hone hbad
                ·
                  exact fin15Anchored_clause04497 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04498 chi hone hbad
                ·
                  exact fin15Anchored_clause04499 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04500 chi hone hbad
                ·
                  exact fin15Anchored_clause04501 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04502 chi hone hbad
                ·
                  exact fin15Anchored_clause04503 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04504 chi hone hbad
                ·
                  exact fin15Anchored_clause04505 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04506 chi hone hbad
                ·
                  exact fin15Anchored_clause04507 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04508 chi hone hbad
                ·
                  exact fin15Anchored_clause04509 chi hone hbad
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
                  exact fin15Anchored_clause04510 chi hone hbad
                ·
                  exact fin15Anchored_clause04511 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04512 chi hone hbad
                ·
                  exact fin15Anchored_clause04513 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04514 chi hone hbad
                ·
                  exact fin15Anchored_clause04515 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04516 chi hone hbad
                ·
                  exact fin15Anchored_clause04517 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04518 chi hone hbad
                ·
                  exact fin15Anchored_clause04519 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04520 chi hone hbad
                ·
                  exact fin15Anchored_clause04521 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04522 chi hone hbad
                ·
                  exact fin15Anchored_clause04523 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04524 chi hone hbad
                ·
                  exact fin15Anchored_clause04525 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04526 chi hone hbad
                ·
                  exact fin15Anchored_clause04527 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04528 chi hone hbad
                ·
                  exact fin15Anchored_clause04529 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04530 chi hone hbad
                ·
                  exact fin15Anchored_clause04531 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04532 chi hone hbad
                ·
                  exact fin15Anchored_clause04533 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04534 chi hone hbad
                ·
                  exact fin15Anchored_clause04535 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04536 chi hone hbad
                ·
                  exact fin15Anchored_clause04537 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04538 chi hone hbad
                ·
                  exact fin15Anchored_clause04539 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04540 chi hone hbad
                ·
                  exact fin15Anchored_clause04541 chi hone hbad

end ErdosSzekeres

end
