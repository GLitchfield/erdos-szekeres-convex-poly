module

public import ErdosSzekeres.Fin15AnchoredClauseChunk104
public import ErdosSzekeres.Fin15AnchoredClauseChunk105
public import ErdosSzekeres.Fin15AnchoredClauseChunk106

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 053. -/

theorem fin15Anchored_rejectSemanticSegment053
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom1562 chi) ∨
      ((Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom1562 chi) ∨
      (Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom1562 chi))) ∨
      (((Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom1562 chi) ∨
      (¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1563 chi)) ∨
      ((¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1563 chi) ∨
      (¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1563 chi)))) ∨
      ((((¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1563 chi) ∨
      (Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1563 chi)) ∨
      ((Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1563 chi) ∨
      (Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1563 chi))) ∨
      (((Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1563 chi) ∨
      (Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1563 chi)) ∨
      ((¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1564 chi) ∨
      (¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1564 chi))))) ∨
      (((((¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1564 chi) ∨
      (¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1564 chi)) ∨
      ((¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1564 chi) ∨
      (Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1564 chi))) ∨
      (((Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1564 chi) ∨
      (Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1564 chi)) ∨
      ((Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1564 chi) ∨
      (Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1564 chi)))) ∨
      ((((Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1564 chi) ∨
      (Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1564 chi)) ∨
      ((¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1565 chi) ∨
      (¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1565 chi))) ∨
      (((¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1565 chi) ∨
      (¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1565 chi)) ∨
      ((¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1565 chi) ∨
      (¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1565 chi)))))) ∨
      ((((((Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1565 chi) ∨
      (Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1565 chi)) ∨
      ((Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1565 chi) ∨
      (Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1565 chi))) ∨
      (((Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1565 chi) ∨
      (¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom1566 chi)) ∨
      ((¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1566 chi) ∨
      (¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1566 chi)))) ∨
      ((((¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom1566 chi) ∨
      (Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1566 chi)) ∨
      ((Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom1566 chi) ∨
      (Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom1566 chi))) ∨
      (((¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1567 chi) ∨
      (¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1567 chi)) ∨
      ((¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1567 chi) ∨
      (¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1567 chi))))) ∨
      (((((¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1567 chi) ∨
      (Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1567 chi)) ∨
      ((Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1567 chi) ∨
      (Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1567 chi))) ∨
      (((Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1567 chi) ∨
      (Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1567 chi)) ∨
      ((¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1568 chi) ∨
      (¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1568 chi)))) ∨
      ((((¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1568 chi) ∨
      (¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1568 chi)) ∨
      ((¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1568 chi) ∨
      (Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1568 chi))) ∨
      (((Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1568 chi) ∨
      (Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1568 chi)) ∨
      ((Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1568 chi) ∨
      (Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1568 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1569 chi) ∨
      ((¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1569 chi) ∨
      (¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1569 chi))) ∨
      (((¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1569 chi) ∨
      (Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1569 chi)) ∨
      ((Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1569 chi) ∨
      (Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1569 chi)))) ∨
      ((((Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1569 chi) ∨
      (Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1569 chi)) ∨
      ((¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom1570 chi) ∨
      (¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1570 chi))) ∨
      (((¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom1570 chi) ∨
      (Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1570 chi)) ∨
      ((Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1570 chi) ∨
      (Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1570 chi))))) ∨
      (((((Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom1570 chi) ∨
      (Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom1570 chi)) ∨
      ((Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom1571 chi) ∨
      (Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom1571 chi))) ∨
      (((¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom1572 chi) ∨
      (Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom1572 chi)) ∨
      ((Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom1572 chi) ∨
      (Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom1572 chi)))) ∨
      ((((Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom1572 chi) ∨
      (Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom1572 chi)) ∨
      ((¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1573 chi) ∨
      (¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1573 chi))) ∨
      (((¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1573 chi) ∨
      (¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1573 chi)) ∨
      ((¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1573 chi) ∨
      (Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1573 chi)))))) ∨
      ((((((Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1573 chi) ∨
      (Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1573 chi)) ∨
      ((Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1573 chi) ∨
      (¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1574 chi))) ∨
      (((¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1574 chi) ∨
      (¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1574 chi)) ∨
      ((¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1574 chi) ∨
      (¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1574 chi)))) ∨
      ((((¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1574 chi) ∨
      (Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1574 chi)) ∨
      ((Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1574 chi) ∨
      (Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1574 chi))) ∨
      (((Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1574 chi) ∨
      (¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1575 chi)) ∨
      ((¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1575 chi) ∨
      (¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1575 chi))))) ∨
      (((((¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1575 chi) ∨
      (¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1575 chi)) ∨
      ((¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1575 chi) ∨
      (Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1575 chi))) ∨
      (((Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1575 chi) ∨
      (Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1575 chi)) ∨
      ((Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1575 chi) ∨
      (Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1575 chi)))) ∨
      ((((Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1575 chi) ∨
      (¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1576 chi)) ∨
      ((¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1576 chi) ∨
      (¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1576 chi))) ∨
      (((¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1576 chi) ∨
      (¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1576 chi)) ∨
      ((¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1576 chi) ∨
      (Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1576 chi)))))))) ∨
      (((((((Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1576 chi) ∨
      ((Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1576 chi) ∨
      (Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1576 chi))) ∨
      (((Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1576 chi) ∨
      (Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1576 chi)) ∨
      ((Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1576 chi) ∨
      (¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1578 chi)))) ∨
      ((((¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1578 chi) ∨
      (¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1578 chi)) ∨
      ((¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1578 chi) ∨
      (¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1578 chi))) ∨
      (((Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1578 chi) ∨
      (Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1578 chi)) ∨
      ((Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1578 chi) ∨
      (Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1578 chi))))) ∨
      (((((Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1578 chi) ∨
      (¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1579 chi)) ∨
      ((¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1579 chi) ∨
      (¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1579 chi))) ∨
      (((¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1579 chi) ∨
      (¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1579 chi)) ∨
      ((¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1579 chi) ∨
      (Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1579 chi)))) ∨
      ((((Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1579 chi) ∨
      (Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1579 chi)) ∨
      ((Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1579 chi) ∨
      (Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1579 chi))) ∨
      (((¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1580 chi) ∨
      (¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1580 chi)) ∨
      ((¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1580 chi) ∨
      (¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1580 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1580 chi) ∨
      (¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1580 chi)) ∨
      ((¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1580 chi) ∨
      (¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1580 chi))) ∨
      (((Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1580 chi) ∨
      (Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1580 chi)) ∨
      ((Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1580 chi) ∨
      (Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1580 chi)))) ∨
      ((((¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1582 chi) ∨
      (¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1582 chi)) ∨
      ((¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1582 chi) ∨
      (¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1582 chi))) ∨
      (((¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1582 chi) ∨
      (¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1582 chi)) ∨
      ((Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1582 chi) ∨
      (Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1582 chi))))) ∨
      (((((Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1582 chi) ∨
      (Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1582 chi)) ∨
      ((¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1583 chi) ∨
      (¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1583 chi))) ∨
      (((¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1583 chi) ∨
      (¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1583 chi)) ∨
      ((¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1583 chi) ∨
      (¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1583 chi)))) ∨
      ((((Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1583 chi) ∨
      (Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1583 chi)) ∨
      ((Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1583 chi) ∨
      (Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1583 chi))) ∨
      (((Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1583 chi) ∨
      (Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1583 chi)) ∨
      ((¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1584 chi) ∨
      (¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1584 chi))))))) ∨
      (((((((¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1584 chi) ∨
      (¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1584 chi)) ∨
      ((¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1584 chi) ∨
      (Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1584 chi))) ∨
      (((Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1584 chi) ∨
      (Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1584 chi)) ∨
      ((Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1584 chi) ∨
      (Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1584 chi)))) ∨
      ((((Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1584 chi) ∨
      (¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1588 chi)) ∨
      ((¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1588 chi) ∨
      (¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1588 chi))) ∨
      (((¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1588 chi) ∨
      (¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1588 chi)) ∨
      ((¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1588 chi) ∨
      (Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1588 chi))))) ∨
      (((((Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1588 chi) ∨
      (Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1588 chi)) ∨
      ((Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1588 chi) ∨
      (¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1589 chi))) ∨
      (((¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1589 chi) ∨
      (¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1589 chi)) ∨
      ((¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1589 chi) ∨
      (¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1589 chi)))) ∨
      ((((Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1589 chi) ∨
      (Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1589 chi)) ∨
      ((Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1589 chi) ∨
      (Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1589 chi))) ∨
      (((Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1589 chi) ∨
      (¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1590 chi)) ∨
      ((¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1590 chi) ∨
      (¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1590 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1590 chi) ∨
      (¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1590 chi)) ∨
      ((¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1590 chi) ∨
      (Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1590 chi))) ∨
      (((Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1590 chi) ∨
      (Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1590 chi)) ∨
      ((Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1590 chi) ∨
      (Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1590 chi)))) ∨
      ((((¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom1591 chi) ∨
      (¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1591 chi)) ∨
      ((¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom1591 chi) ∨
      (¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1591 chi))) ∨
      (((¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1591 chi) ∨
      (Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1591 chi)) ∨
      ((Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1591 chi) ∨
      (Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1591 chi))))) ∨
      (((((Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom1591 chi) ∨
      (Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1591 chi)) ∨
      ((Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom1591 chi) ∨
      (¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1592 chi))) ∨
      (((¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1592 chi) ∨
      (¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1592 chi)) ∨
      ((¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1592 chi) ∨
      (¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1592 chi)))) ∨
      ((((¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1592 chi) ∨
      (¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1592 chi)) ∨
      ((Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1592 chi) ∨
      (Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1592 chi))) ∨
      (((Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1592 chi) ∨
      (Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1592 chi)) ∨
      ((Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1592 chi) ∨
      (¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1593 chi)))))))))) := by
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
                exact fin15Anchored_clause13376 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13377 chi hbad
                ·
                  exact fin15Anchored_clause13378 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13379 chi hbad
                ·
                  exact fin15Anchored_clause13380 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13381 chi hbad
                ·
                  exact fin15Anchored_clause13382 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13383 chi hbad
                ·
                  exact fin15Anchored_clause13384 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13385 chi hbad
                ·
                  exact fin15Anchored_clause13386 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13387 chi hbad
                ·
                  exact fin15Anchored_clause13388 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13389 chi hbad
                ·
                  exact fin15Anchored_clause13390 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13391 chi hbad
                ·
                  exact fin15Anchored_clause13392 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13393 chi hbad
                ·
                  exact fin15Anchored_clause13394 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13395 chi hbad
                ·
                  exact fin15Anchored_clause13396 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13397 chi hbad
                ·
                  exact fin15Anchored_clause13398 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13399 chi hbad
                ·
                  exact fin15Anchored_clause13400 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13401 chi hbad
                ·
                  exact fin15Anchored_clause13402 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13403 chi hbad
                ·
                  exact fin15Anchored_clause13404 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13405 chi hbad
                ·
                  exact fin15Anchored_clause13406 chi hbad
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
                  exact fin15Anchored_clause13407 chi hbad
                ·
                  exact fin15Anchored_clause13408 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13409 chi hbad
                ·
                  exact fin15Anchored_clause13410 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13411 chi hbad
                ·
                  exact fin15Anchored_clause13412 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13413 chi hbad
                ·
                  exact fin15Anchored_clause13414 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13415 chi hbad
                ·
                  exact fin15Anchored_clause13416 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13417 chi hbad
                ·
                  exact fin15Anchored_clause13418 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13419 chi hbad
                ·
                  exact fin15Anchored_clause13420 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13421 chi hbad
                ·
                  exact fin15Anchored_clause13422 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13423 chi hbad
                ·
                  exact fin15Anchored_clause13424 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13425 chi hbad
                ·
                  exact fin15Anchored_clause13426 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13427 chi hbad
                ·
                  exact fin15Anchored_clause13428 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13429 chi hbad
                ·
                  exact fin15Anchored_clause13430 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13431 chi hbad
                ·
                  exact fin15Anchored_clause13432 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13433 chi hbad
                ·
                  exact fin15Anchored_clause13434 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13435 chi hbad
                ·
                  exact fin15Anchored_clause13436 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13437 chi hbad
                ·
                  exact fin15Anchored_clause13438 chi hbad
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
                exact fin15Anchored_clause13439 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13440 chi hbad
                ·
                  exact fin15Anchored_clause13441 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13442 chi hbad
                ·
                  exact fin15Anchored_clause13443 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13444 chi hbad
                ·
                  exact fin15Anchored_clause13445 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13446 chi hbad
                ·
                  exact fin15Anchored_clause13447 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13448 chi hbad
                ·
                  exact fin15Anchored_clause13449 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13450 chi hbad
                ·
                  exact fin15Anchored_clause13451 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13452 chi hbad
                ·
                  exact fin15Anchored_clause13453 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13454 chi hbad
                ·
                  exact fin15Anchored_clause13455 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13456 chi hbad
                ·
                  exact fin15Anchored_clause13457 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13458 chi hbad
                ·
                  exact fin15Anchored_clause13459 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13460 chi hbad
                ·
                  exact fin15Anchored_clause13461 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13462 chi hbad
                ·
                  exact fin15Anchored_clause13463 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13464 chi hbad
                ·
                  exact fin15Anchored_clause13465 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13466 chi hbad
                ·
                  exact fin15Anchored_clause13467 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13468 chi hbad
                ·
                  exact fin15Anchored_clause13469 chi hbad
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
                  exact fin15Anchored_clause13470 chi hbad
                ·
                  exact fin15Anchored_clause13471 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13472 chi hbad
                ·
                  exact fin15Anchored_clause13473 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13474 chi hbad
                ·
                  exact fin15Anchored_clause13475 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13476 chi hbad
                ·
                  exact fin15Anchored_clause13477 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13478 chi hbad
                ·
                  exact fin15Anchored_clause13479 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13480 chi hbad
                ·
                  exact fin15Anchored_clause13481 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13482 chi hbad
                ·
                  exact fin15Anchored_clause13483 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13484 chi hbad
                ·
                  exact fin15Anchored_clause13485 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13486 chi hbad
                ·
                  exact fin15Anchored_clause13487 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13488 chi hbad
                ·
                  exact fin15Anchored_clause13489 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13490 chi hbad
                ·
                  exact fin15Anchored_clause13491 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13492 chi hbad
                ·
                  exact fin15Anchored_clause13493 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13494 chi hbad
                ·
                  exact fin15Anchored_clause13495 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13496 chi hbad
                ·
                  exact fin15Anchored_clause13497 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13498 chi hbad
                ·
                  exact fin15Anchored_clause13499 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13500 chi hbad
                ·
                  exact fin15Anchored_clause13501 chi hbad
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
                exact fin15Anchored_clause13502 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13503 chi hbad
                ·
                  exact fin15Anchored_clause13504 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13505 chi hbad
                ·
                  exact fin15Anchored_clause13506 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13507 chi hbad
                ·
                  exact fin15Anchored_clause13508 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13509 chi hbad
                ·
                  exact fin15Anchored_clause13510 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13511 chi hbad
                ·
                  exact fin15Anchored_clause13512 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13513 chi hbad
                ·
                  exact fin15Anchored_clause13514 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13515 chi hbad
                ·
                  exact fin15Anchored_clause13516 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13517 chi hbad
                ·
                  exact fin15Anchored_clause13518 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13519 chi hbad
                ·
                  exact fin15Anchored_clause13520 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13521 chi hbad
                ·
                  exact fin15Anchored_clause13522 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13523 chi hbad
                ·
                  exact fin15Anchored_clause13524 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13525 chi hbad
                ·
                  exact fin15Anchored_clause13526 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13527 chi hbad
                ·
                  exact fin15Anchored_clause13528 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13529 chi hbad
                ·
                  exact fin15Anchored_clause13530 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13531 chi hbad
                ·
                  exact fin15Anchored_clause13532 chi hbad
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
                  exact fin15Anchored_clause13533 chi hbad
                ·
                  exact fin15Anchored_clause13534 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13535 chi hbad
                ·
                  exact fin15Anchored_clause13536 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13537 chi hbad
                ·
                  exact fin15Anchored_clause13538 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13539 chi hbad
                ·
                  exact fin15Anchored_clause13540 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13541 chi hbad
                ·
                  exact fin15Anchored_clause13542 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13543 chi hbad
                ·
                  exact fin15Anchored_clause13544 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13545 chi hbad
                ·
                  exact fin15Anchored_clause13546 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13547 chi hbad
                ·
                  exact fin15Anchored_clause13548 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13549 chi hbad
                ·
                  exact fin15Anchored_clause13550 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13551 chi hbad
                ·
                  exact fin15Anchored_clause13552 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13553 chi hbad
                ·
                  exact fin15Anchored_clause13554 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13555 chi hbad
                ·
                  exact fin15Anchored_clause13556 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13557 chi hbad
                ·
                  exact fin15Anchored_clause13558 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13559 chi hbad
                ·
                  exact fin15Anchored_clause13560 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13561 chi hbad
                ·
                  exact fin15Anchored_clause13562 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13563 chi hbad
                ·
                  exact fin15Anchored_clause13564 chi hbad
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
                  exact fin15Anchored_clause13565 chi hbad
                ·
                  exact fin15Anchored_clause13566 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13567 chi hbad
                ·
                  exact fin15Anchored_clause13568 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13569 chi hbad
                ·
                  exact fin15Anchored_clause13570 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13571 chi hbad
                ·
                  exact fin15Anchored_clause13572 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13573 chi hbad
                ·
                  exact fin15Anchored_clause13574 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13575 chi hbad
                ·
                  exact fin15Anchored_clause13576 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13577 chi hbad
                ·
                  exact fin15Anchored_clause13578 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13579 chi hbad
                ·
                  exact fin15Anchored_clause13580 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13581 chi hbad
                ·
                  exact fin15Anchored_clause13582 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13583 chi hbad
                ·
                  exact fin15Anchored_clause13584 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13585 chi hbad
                ·
                  exact fin15Anchored_clause13586 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13587 chi hbad
                ·
                  exact fin15Anchored_clause13588 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13589 chi hbad
                ·
                  exact fin15Anchored_clause13590 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13591 chi hbad
                ·
                  exact fin15Anchored_clause13592 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13593 chi hbad
                ·
                  exact fin15Anchored_clause13594 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13595 chi hbad
                ·
                  exact fin15Anchored_clause13596 chi hbad
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
                  exact fin15Anchored_clause13597 chi hbad
                ·
                  exact fin15Anchored_clause13598 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13599 chi hbad
                ·
                  exact fin15Anchored_clause13600 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13601 chi hbad
                ·
                  exact fin15Anchored_clause13602 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13603 chi hbad
                ·
                  exact fin15Anchored_clause13604 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13605 chi hbad
                ·
                  exact fin15Anchored_clause13606 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13607 chi hbad
                ·
                  exact fin15Anchored_clause13608 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13609 chi hbad
                ·
                  exact fin15Anchored_clause13610 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13611 chi hbad
                ·
                  exact fin15Anchored_clause13612 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13613 chi hbad
                ·
                  exact fin15Anchored_clause13614 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13615 chi hbad
                ·
                  exact fin15Anchored_clause13616 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13617 chi hbad
                ·
                  exact fin15Anchored_clause13618 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13619 chi hbad
                ·
                  exact fin15Anchored_clause13620 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13621 chi hbad
                ·
                  exact fin15Anchored_clause13622 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13623 chi hbad
                ·
                  exact fin15Anchored_clause13624 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13625 chi hbad
                ·
                  exact fin15Anchored_clause13626 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13627 chi hbad
                ·
                  exact fin15Anchored_clause13628 chi hbad

end ErdosSzekeres

end
