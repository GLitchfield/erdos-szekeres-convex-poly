module

public import ErdosSzekeres.Fin15AnchoredClauseChunk041
public import ErdosSzekeres.Fin15AnchoredClauseChunk042
public import ErdosSzekeres.Fin15AnchoredClauseChunk043

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 021. -/

theorem fin15Anchored_rejectSemanticSegment021
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0398 chi) ∨
      ((Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0398 chi) ∨
      (Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0398 chi))) ∨
      (((Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0398 chi) ∨
      (¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0399 chi)) ∨
      ((¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0399 chi) ∨
      (¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0399 chi)))) ∨
      ((((¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0399 chi) ∨
      (Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0399 chi)) ∨
      ((Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0399 chi) ∨
      (Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0399 chi))) ∨
      (((Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0399 chi) ∨
      (¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0400 chi)) ∨
      ((¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0400 chi) ∨
      (¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0400 chi))))) ∨
      (((((¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0400 chi) ∨
      (Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0400 chi)) ∨
      ((Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0400 chi) ∨
      (Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0400 chi))) ∨
      (((Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0400 chi) ∨
      (¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0401 chi)) ∨
      ((¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0401 chi) ∨
      (¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0401 chi)))) ∨
      ((((¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0401 chi) ∨
      (Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0401 chi)) ∨
      ((Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0401 chi) ∨
      (Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0401 chi))) ∨
      (((Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0401 chi) ∨
      (¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0403 chi)) ∨
      ((¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0403 chi) ∨
      (¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0403 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0403 chi) ∨
      (Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0403 chi)) ∨
      ((Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0403 chi) ∨
      (Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0403 chi))) ∨
      (((Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0403 chi) ∨
      (¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0404 chi)) ∨
      ((¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0404 chi) ∨
      (¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0404 chi)))) ∨
      ((((¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0404 chi) ∨
      (Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0404 chi)) ∨
      ((Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0404 chi) ∨
      (Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0404 chi))) ∨
      (((Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0404 chi) ∨
      (¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0405 chi)) ∨
      ((¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0405 chi) ∨
      (¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0405 chi))))) ∨
      (((((¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0405 chi) ∨
      (Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0405 chi)) ∨
      ((Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0405 chi) ∨
      (Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0405 chi))) ∨
      (((Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0405 chi) ∨
      (¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0406 chi)) ∨
      ((¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0406 chi) ∨
      (¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0406 chi)))) ∨
      ((((¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0406 chi) ∨
      (Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0406 chi)) ∨
      ((Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0406 chi) ∨
      (Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0406 chi))) ∨
      (((Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0406 chi) ∨
      (¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0407 chi)) ∨
      ((¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0407 chi) ∨
      (¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0407 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0407 chi) ∨
      ((Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0407 chi) ∨
      (Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0407 chi))) ∨
      (((Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0407 chi) ∨
      (Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0407 chi)) ∨
      ((¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0408 chi) ∨
      (¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0408 chi)))) ∨
      ((((¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0408 chi) ∨
      (¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0408 chi)) ∨
      ((Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0408 chi) ∨
      (Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0408 chi))) ∨
      (((Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0408 chi) ∨
      (Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0408 chi)) ∨
      ((¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0409 chi) ∨
      (¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0409 chi))))) ∨
      (((((¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0409 chi) ∨
      (¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0409 chi)) ∨
      ((Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0409 chi) ∨
      (Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0409 chi))) ∨
      (((Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0409 chi) ∨
      (Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0409 chi)) ∨
      ((¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0410 chi) ∨
      (¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0410 chi)))) ∨
      ((((¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0410 chi) ∨
      (¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0410 chi)) ∨
      ((Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0410 chi) ∨
      (Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0410 chi))) ∨
      (((Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0410 chi) ∨
      (Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0410 chi)) ∨
      ((¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0411 chi) ∨
      (¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0411 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0411 chi) ∨
      (¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0411 chi)) ∨
      ((Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0411 chi) ∨
      (Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0411 chi))) ∨
      (((Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0411 chi) ∨
      (Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0411 chi)) ∨
      ((¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0412 chi) ∨
      (¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0412 chi)))) ∨
      ((((¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0412 chi) ∨
      (¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0412 chi)) ∨
      ((Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0412 chi) ∨
      (Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0412 chi))) ∨
      (((Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0412 chi) ∨
      (Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0412 chi)) ∨
      ((¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0413 chi) ∨
      (¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0413 chi))))) ∨
      (((((¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0413 chi) ∨
      (¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0413 chi)) ∨
      ((Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0413 chi) ∨
      (Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0413 chi))) ∨
      (((Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0413 chi) ∨
      (Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0413 chi)) ∨
      ((¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0414 chi) ∨
      (¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0414 chi)))) ∨
      ((((¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0414 chi) ∨
      (¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0414 chi)) ∨
      ((Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0414 chi) ∨
      (Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0414 chi))) ∨
      (((Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0414 chi) ∨
      (Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0414 chi)) ∨
      ((¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0415 chi) ∨
      (¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0415 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0415 chi) ∨
      ((¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0415 chi) ∨
      (Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0415 chi))) ∨
      (((Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0415 chi) ∨
      (Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0415 chi)) ∨
      ((Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0415 chi) ∨
      (¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0416 chi)))) ∨
      ((((Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0416 chi) ∨
      (Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0416 chi)) ∨
      ((Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0416 chi) ∨
      (¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0417 chi))) ∨
      (((¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0417 chi) ∨
      (¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0417 chi)) ∨
      ((Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0417 chi) ∨
      (Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0417 chi))))) ∨
      (((((Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0417 chi) ∨
      (Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0417 chi)) ∨
      ((¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0418 chi) ∨
      (¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0418 chi))) ∨
      (((¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0418 chi) ∨
      (¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0418 chi)) ∨
      ((Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0418 chi) ∨
      (Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0418 chi)))) ∨
      ((((Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0418 chi) ∨
      (Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0418 chi)) ∨
      ((¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0419 chi) ∨
      (¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0419 chi))) ∨
      (((¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0419 chi) ∨
      (¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0419 chi)) ∨
      ((Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0419 chi) ∨
      (Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0419 chi)))))) ∨
      ((((((Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0419 chi) ∨
      (Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0419 chi)) ∨
      ((¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0420 chi) ∨
      (¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0420 chi))) ∨
      (((¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0420 chi) ∨
      (¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0420 chi)) ∨
      ((Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0420 chi) ∨
      (Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0420 chi)))) ∨
      ((((Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0420 chi) ∨
      (Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0420 chi)) ∨
      ((¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0421 chi) ∨
      (¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0421 chi))) ∨
      (((¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0421 chi) ∨
      (¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0421 chi)) ∨
      ((Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0421 chi) ∨
      (Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0421 chi))))) ∨
      (((((Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0421 chi) ∨
      (Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0421 chi)) ∨
      ((¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0423 chi) ∨
      (¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0423 chi))) ∨
      (((¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0423 chi) ∨
      (¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0423 chi)) ∨
      ((Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0423 chi) ∨
      (Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0423 chi)))) ∨
      ((((Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0423 chi) ∨
      (Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0423 chi)) ∨
      ((¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0424 chi) ∨
      (¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0424 chi))) ∨
      (((¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0424 chi) ∨
      (¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0424 chi)) ∨
      ((Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0424 chi) ∨
      (Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0424 chi))))))) ∨
      (((((((Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0424 chi) ∨
      (Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0424 chi)) ∨
      ((¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0425 chi) ∨
      (¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0425 chi))) ∨
      (((¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0425 chi) ∨
      (¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0425 chi)) ∨
      ((Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0425 chi) ∨
      (Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0425 chi)))) ∨
      ((((Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0425 chi) ∨
      (Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0425 chi)) ∨
      ((¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0427 chi) ∨
      (¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0427 chi))) ∨
      (((¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0427 chi) ∨
      (¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0427 chi)) ∨
      ((Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0427 chi) ∨
      (Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0427 chi))))) ∨
      (((((Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0427 chi) ∨
      (Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0427 chi)) ∨
      ((¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0428 chi) ∨
      (¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0428 chi))) ∨
      (((¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0428 chi) ∨
      (¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0428 chi)) ∨
      ((Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0428 chi) ∨
      (Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0428 chi)))) ∨
      ((((Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0428 chi) ∨
      (Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0428 chi)) ∨
      ((¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0429 chi) ∨
      (¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0429 chi))) ∨
      (((¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0429 chi) ∨
      (¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0429 chi)) ∨
      ((Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0429 chi) ∨
      (Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0429 chi)))))) ∨
      ((((((Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0429 chi) ∨
      (Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0429 chi)) ∨
      ((¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0433 chi) ∨
      (¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0433 chi))) ∨
      (((¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0433 chi) ∨
      (¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0433 chi)) ∨
      ((Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0433 chi) ∨
      (Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0433 chi)))) ∨
      ((((Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0433 chi) ∨
      (Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0433 chi)) ∨
      ((¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0434 chi) ∨
      (¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0434 chi))) ∨
      (((¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0434 chi) ∨
      (¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0434 chi)) ∨
      ((Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0434 chi) ∨
      (Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0434 chi))))) ∨
      (((((Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0434 chi) ∨
      (Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0434 chi)) ∨
      ((¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0435 chi) ∨
      (¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0435 chi))) ∨
      (((¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0435 chi) ∨
      (¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0435 chi)) ∨
      ((Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0435 chi) ∨
      (Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0435 chi)))) ∨
      ((((Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0435 chi) ∨
      (Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0435 chi)) ∨
      ((¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0436 chi) ∨
      (¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0436 chi))) ∨
      (((¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0436 chi) ∨
      (¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0436 chi)) ∨
      ((Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0436 chi) ∨
      (Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0436 chi)))))))))) := by
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
                exact fin15Anchored_clause05299 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05300 chi hone hbad
                ·
                  exact fin15Anchored_clause05301 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05302 chi hone hbad
                ·
                  exact fin15Anchored_clause05303 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05304 chi hone hbad
                ·
                  exact fin15Anchored_clause05305 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05306 chi hone hbad
                ·
                  exact fin15Anchored_clause05307 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05308 chi hone hbad
                ·
                  exact fin15Anchored_clause05309 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05310 chi hone hbad
                ·
                  exact fin15Anchored_clause05311 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05312 chi hone hbad
                ·
                  exact fin15Anchored_clause05313 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05314 chi hone hbad
                ·
                  exact fin15Anchored_clause05315 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05316 chi hone hbad
                ·
                  exact fin15Anchored_clause05317 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05318 chi hone hbad
                ·
                  exact fin15Anchored_clause05319 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05320 chi hone hbad
                ·
                  exact fin15Anchored_clause05321 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05322 chi hone hbad
                ·
                  exact fin15Anchored_clause05323 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05324 chi hone hbad
                ·
                  exact fin15Anchored_clause05325 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05326 chi hone hbad
                ·
                  exact fin15Anchored_clause05327 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05328 chi hone hbad
                ·
                  exact fin15Anchored_clause05329 chi hone hbad
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
                  exact fin15Anchored_clause05330 chi hone hbad
                ·
                  exact fin15Anchored_clause05331 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05332 chi hone hbad
                ·
                  exact fin15Anchored_clause05333 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05334 chi hone hbad
                ·
                  exact fin15Anchored_clause05335 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05336 chi hone hbad
                ·
                  exact fin15Anchored_clause05337 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05338 chi hone hbad
                ·
                  exact fin15Anchored_clause05339 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05340 chi hone hbad
                ·
                  exact fin15Anchored_clause05341 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05342 chi hone hbad
                ·
                  exact fin15Anchored_clause05343 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05344 chi hone hbad
                ·
                  exact fin15Anchored_clause05345 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05346 chi hone hbad
                ·
                  exact fin15Anchored_clause05347 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05348 chi hone hbad
                ·
                  exact fin15Anchored_clause05349 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05350 chi hone hbad
                ·
                  exact fin15Anchored_clause05351 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05352 chi hone hbad
                ·
                  exact fin15Anchored_clause05353 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05354 chi hone hbad
                ·
                  exact fin15Anchored_clause05355 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05356 chi hone hbad
                ·
                  exact fin15Anchored_clause05357 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05358 chi hone hbad
                ·
                  exact fin15Anchored_clause05359 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05360 chi hone hbad
                ·
                  exact fin15Anchored_clause05361 chi hone hbad
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
                exact fin15Anchored_clause05362 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05363 chi hone hbad
                ·
                  exact fin15Anchored_clause05364 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05365 chi hone hbad
                ·
                  exact fin15Anchored_clause05366 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05367 chi hone hbad
                ·
                  exact fin15Anchored_clause05368 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05369 chi hone hbad
                ·
                  exact fin15Anchored_clause05370 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05371 chi hone hbad
                ·
                  exact fin15Anchored_clause05372 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05373 chi hone hbad
                ·
                  exact fin15Anchored_clause05374 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05375 chi hone hbad
                ·
                  exact fin15Anchored_clause05376 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05377 chi hone hbad
                ·
                  exact fin15Anchored_clause05378 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05379 chi hone hbad
                ·
                  exact fin15Anchored_clause05380 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05381 chi hone hbad
                ·
                  exact fin15Anchored_clause05382 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05383 chi hone hbad
                ·
                  exact fin15Anchored_clause05384 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05385 chi hone hbad
                ·
                  exact fin15Anchored_clause05386 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05387 chi hone hbad
                ·
                  exact fin15Anchored_clause05388 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05389 chi hone hbad
                ·
                  exact fin15Anchored_clause05390 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05391 chi hone hbad
                ·
                  exact fin15Anchored_clause05392 chi hone hbad
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
                  exact fin15Anchored_clause05393 chi hone hbad
                ·
                  exact fin15Anchored_clause05394 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05395 chi hone hbad
                ·
                  exact fin15Anchored_clause05396 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05397 chi hone hbad
                ·
                  exact fin15Anchored_clause05398 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05399 chi hone hbad
                ·
                  exact fin15Anchored_clause05400 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05401 chi hone hbad
                ·
                  exact fin15Anchored_clause05402 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05403 chi hone hbad
                ·
                  exact fin15Anchored_clause05404 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05405 chi hone hbad
                ·
                  exact fin15Anchored_clause05406 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05407 chi hone hbad
                ·
                  exact fin15Anchored_clause05408 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05409 chi hone hbad
                ·
                  exact fin15Anchored_clause05410 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05411 chi hone hbad
                ·
                  exact fin15Anchored_clause05412 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05413 chi hone hbad
                ·
                  exact fin15Anchored_clause05414 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05415 chi hone hbad
                ·
                  exact fin15Anchored_clause05416 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05417 chi hone hbad
                ·
                  exact fin15Anchored_clause05418 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05419 chi hone hbad
                ·
                  exact fin15Anchored_clause05420 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05421 chi hone hbad
                ·
                  exact fin15Anchored_clause05422 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05423 chi hone hbad
                ·
                  exact fin15Anchored_clause05424 chi hone hbad
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
                exact fin15Anchored_clause05425 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05426 chi hone hbad
                ·
                  exact fin15Anchored_clause05427 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05428 chi hone hbad
                ·
                  exact fin15Anchored_clause05429 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05430 chi hone hbad
                ·
                  exact fin15Anchored_clause05431 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05432 chi hone hbad
                ·
                  exact fin15Anchored_clause05433 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05434 chi hone hbad
                ·
                  exact fin15Anchored_clause05435 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05436 chi hone hbad
                ·
                  exact fin15Anchored_clause05437 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05438 chi hone hbad
                ·
                  exact fin15Anchored_clause05439 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05440 chi hone hbad
                ·
                  exact fin15Anchored_clause05441 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05442 chi hone hbad
                ·
                  exact fin15Anchored_clause05443 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05444 chi hone hbad
                ·
                  exact fin15Anchored_clause05445 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05446 chi hone hbad
                ·
                  exact fin15Anchored_clause05447 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05448 chi hone hbad
                ·
                  exact fin15Anchored_clause05449 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05450 chi hone hbad
                ·
                  exact fin15Anchored_clause05451 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05452 chi hone hbad
                ·
                  exact fin15Anchored_clause05453 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05454 chi hone hbad
                ·
                  exact fin15Anchored_clause05455 chi hone hbad
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
                  exact fin15Anchored_clause05456 chi hone hbad
                ·
                  exact fin15Anchored_clause05457 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05458 chi hone hbad
                ·
                  exact fin15Anchored_clause05459 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05460 chi hone hbad
                ·
                  exact fin15Anchored_clause05461 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05462 chi hone hbad
                ·
                  exact fin15Anchored_clause05463 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05464 chi hone hbad
                ·
                  exact fin15Anchored_clause05465 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05466 chi hone hbad
                ·
                  exact fin15Anchored_clause05467 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05468 chi hone hbad
                ·
                  exact fin15Anchored_clause05469 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05470 chi hone hbad
                ·
                  exact fin15Anchored_clause05471 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05472 chi hone hbad
                ·
                  exact fin15Anchored_clause05473 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05474 chi hone hbad
                ·
                  exact fin15Anchored_clause05475 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05476 chi hone hbad
                ·
                  exact fin15Anchored_clause05477 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05478 chi hone hbad
                ·
                  exact fin15Anchored_clause05479 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05480 chi hone hbad
                ·
                  exact fin15Anchored_clause05481 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05482 chi hone hbad
                ·
                  exact fin15Anchored_clause05483 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05484 chi hone hbad
                ·
                  exact fin15Anchored_clause05485 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05486 chi hone hbad
                ·
                  exact fin15Anchored_clause05487 chi hone hbad
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
                  exact fin15Anchored_clause05488 chi hone hbad
                ·
                  exact fin15Anchored_clause05489 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05490 chi hone hbad
                ·
                  exact fin15Anchored_clause05491 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05492 chi hone hbad
                ·
                  exact fin15Anchored_clause05493 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05494 chi hone hbad
                ·
                  exact fin15Anchored_clause05495 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05496 chi hone hbad
                ·
                  exact fin15Anchored_clause05497 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05498 chi hone hbad
                ·
                  exact fin15Anchored_clause05499 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05500 chi hone hbad
                ·
                  exact fin15Anchored_clause05501 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05502 chi hone hbad
                ·
                  exact fin15Anchored_clause05503 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05504 chi hone hbad
                ·
                  exact fin15Anchored_clause05505 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05506 chi hone hbad
                ·
                  exact fin15Anchored_clause05507 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05508 chi hone hbad
                ·
                  exact fin15Anchored_clause05509 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05510 chi hone hbad
                ·
                  exact fin15Anchored_clause05511 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05512 chi hone hbad
                ·
                  exact fin15Anchored_clause05513 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05514 chi hone hbad
                ·
                  exact fin15Anchored_clause05515 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05516 chi hone hbad
                ·
                  exact fin15Anchored_clause05517 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05518 chi hone hbad
                ·
                  exact fin15Anchored_clause05519 chi hone hbad
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
                  exact fin15Anchored_clause05520 chi hone hbad
                ·
                  exact fin15Anchored_clause05521 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05522 chi hone hbad
                ·
                  exact fin15Anchored_clause05523 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05524 chi hone hbad
                ·
                  exact fin15Anchored_clause05525 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05526 chi hone hbad
                ·
                  exact fin15Anchored_clause05527 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05528 chi hone hbad
                ·
                  exact fin15Anchored_clause05529 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05530 chi hone hbad
                ·
                  exact fin15Anchored_clause05531 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05532 chi hone hbad
                ·
                  exact fin15Anchored_clause05533 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05534 chi hone hbad
                ·
                  exact fin15Anchored_clause05535 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05536 chi hone hbad
                ·
                  exact fin15Anchored_clause05537 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05538 chi hone hbad
                ·
                  exact fin15Anchored_clause05539 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05540 chi hone hbad
                ·
                  exact fin15Anchored_clause05541 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05542 chi hone hbad
                ·
                  exact fin15Anchored_clause05543 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05544 chi hone hbad
                ·
                  exact fin15Anchored_clause05545 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05546 chi hone hbad
                ·
                  exact fin15Anchored_clause05547 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05548 chi hone hbad
                ·
                  exact fin15Anchored_clause05549 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05550 chi hone hbad
                ·
                  exact fin15Anchored_clause05551 chi hone hbad

end ErdosSzekeres

end
