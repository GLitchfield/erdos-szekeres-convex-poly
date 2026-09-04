module

public import ErdosSzekeres.Fin15AnchoredClauseChunk116
public import ErdosSzekeres.Fin15AnchoredClauseChunk117
public import ErdosSzekeres.Fin15AnchoredClauseChunk118

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 059. -/

theorem fin15Anchored_rejectSemanticSegment059
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1748 chi) ∨
      ((¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1750 chi) ∨
      (¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1750 chi))) ∨
      (((¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1750 chi) ∨
      (¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1750 chi)) ∨
      ((¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1750 chi) ∨
      (¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1750 chi)))) ∨
      ((((¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1750 chi) ∨
      (Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1750 chi)) ∨
      ((Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1750 chi) ∨
      (Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1750 chi))) ∨
      (((Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1750 chi) ∨
      (Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1750 chi)) ∨
      ((¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1751 chi) ∨
      (¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1751 chi))))) ∨
      (((((¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1751 chi) ∨
      (¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1751 chi)) ∨
      ((¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1751 chi) ∨
      (Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1751 chi))) ∨
      (((Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1751 chi) ∨
      (Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1751 chi)) ∨
      ((Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1751 chi) ∨
      (Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1751 chi)))) ∨
      ((((¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1753 chi) ∨
      (¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1753 chi)) ∨
      ((¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1753 chi) ∨
      (¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1753 chi))) ∨
      (((¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1753 chi) ∨
      (¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1753 chi)) ∨
      ((Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1753 chi) ∨
      (Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1753 chi)))))) ∨
      ((((((Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1753 chi) ∨
      (Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1753 chi)) ∨
      ((Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1753 chi) ∨
      (¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1754 chi))) ∨
      (((¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1754 chi) ∨
      (¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1754 chi)) ∨
      ((¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1754 chi) ∨
      (¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1754 chi)))) ∨
      ((((¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1754 chi) ∨
      (Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1754 chi)) ∨
      ((Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1754 chi) ∨
      (Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1754 chi))) ∨
      (((Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1754 chi) ∨
      (¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1755 chi)) ∨
      ((¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1755 chi) ∨
      (¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1755 chi))))) ∨
      (((((¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1755 chi) ∨
      (Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1755 chi)) ∨
      ((Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1755 chi) ∨
      (Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1755 chi))) ∨
      (((Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1755 chi) ∨
      (Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1755 chi)) ∨
      ((¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1757 chi) ∨
      (¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1757 chi)))) ∨
      ((((¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1757 chi) ∨
      (¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1757 chi)) ∨
      ((¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1757 chi) ∨
      (Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1757 chi))) ∨
      (((Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1757 chi) ∨
      (Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1757 chi)) ∨
      ((Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1757 chi) ∨
      (Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1757 chi))))))) ∨
      ((((((Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1757 chi) ∨
      ((¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1758 chi) ∨
      (¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1758 chi))) ∨
      (((¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1758 chi) ∨
      (¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1758 chi)) ∨
      ((¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1758 chi) ∨
      (¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1758 chi)))) ∨
      ((((Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1758 chi) ∨
      (Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1758 chi)) ∨
      ((Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1758 chi) ∨
      (Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1758 chi))) ∨
      (((Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1758 chi) ∨
      (¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1759 chi)) ∨
      ((¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1759 chi) ∨
      (¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1759 chi))))) ∨
      (((((¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1759 chi) ∨
      (¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1759 chi)) ∨
      ((Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1759 chi) ∨
      (Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1759 chi))) ∨
      (((Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1759 chi) ∨
      (Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1759 chi)) ∨
      ((Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1759 chi) ∨
      (Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1759 chi)))) ∨
      ((((¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1763 chi) ∨
      (¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1763 chi)) ∨
      ((¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1763 chi) ∨
      (¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1763 chi))) ∨
      (((¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1763 chi) ∨
      (Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1763 chi)) ∨
      ((Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1763 chi) ∨
      (Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1763 chi)))))) ∨
      ((((((Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1763 chi) ∨
      (Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1763 chi)) ∨
      ((Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1763 chi) ∨
      (¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1764 chi))) ∨
      (((¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1764 chi) ∨
      (¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1764 chi)) ∨
      ((¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1764 chi) ∨
      (¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1764 chi)))) ∨
      ((((¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1764 chi) ∨
      (Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1764 chi)) ∨
      ((Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1764 chi) ∨
      (Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1764 chi))) ∨
      (((Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1764 chi) ∨
      (¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1765 chi)) ∨
      ((¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1765 chi) ∨
      (¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1765 chi))))) ∨
      (((((¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1765 chi) ∨
      (¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1765 chi)) ∨
      ((¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1765 chi) ∨
      (Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1765 chi))) ∨
      (((Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1765 chi) ∨
      (Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1765 chi)) ∨
      ((Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1765 chi) ∨
      (¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom1766 chi)))) ∨
      ((((¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1766 chi) ∨
      (¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom1766 chi)) ∨
      ((¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1766 chi) ∨
      (Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1766 chi))) ∨
      (((Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom1766 chi) ∨
      (¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1767 chi)) ∨
      ((¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1767 chi) ∨
      (¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1767 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1767 chi) ∨
      ((¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1767 chi) ∨
      (Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1767 chi))) ∨
      (((Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1767 chi) ∨
      (Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1767 chi)) ∨
      ((Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1767 chi) ∨
      (¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1768 chi)))) ∨
      ((((¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1768 chi) ∨
      (¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1768 chi)) ∨
      ((¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1768 chi) ∨
      (¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1768 chi))) ∨
      (((Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1768 chi) ∨
      (Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1768 chi)) ∨
      ((Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1768 chi) ∨
      (Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1768 chi))))) ∨
      (((((Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1768 chi) ∨
      (Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1768 chi)) ∨
      ((¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1769 chi) ∨
      (¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1769 chi))) ∨
      (((¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1769 chi) ∨
      (¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1769 chi)) ∨
      ((¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1769 chi) ∨
      (¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1769 chi)))) ∨
      ((((Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1769 chi) ∨
      (Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1769 chi)) ∨
      ((Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1769 chi) ∨
      (Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1769 chi))) ∨
      (((Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1769 chi) ∨
      (¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1770 chi)) ∨
      ((¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1770 chi) ∨
      (¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1770 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1770 chi) ∨
      (Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1770 chi)) ∨
      ((Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1770 chi) ∨
      (Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1770 chi))) ∨
      (((Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1770 chi) ∨
      (¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom1771 chi)) ∨
      ((¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom1771 chi) ∨
      (¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom1771 chi)))) ∨
      ((((Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom1771 chi) ∨
      (Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom1771 chi)) ∨
      ((¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom1772 chi) ∨
      (¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1773 chi))) ∨
      (((¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1773 chi) ∨
      (¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1773 chi)) ∨
      ((¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1773 chi) ∨
      (Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1773 chi))))) ∨
      (((((Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1773 chi) ∨
      (Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1773 chi)) ∨
      ((Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1773 chi) ∨
      (Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1773 chi))) ∨
      (((¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1774 chi) ∨
      (¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1774 chi)) ∨
      ((¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1774 chi) ∨
      (¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1774 chi)))) ∨
      ((((¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1774 chi) ∨
      (¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1774 chi)) ∨
      ((Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1774 chi) ∨
      (Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1774 chi))) ∨
      (((Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1774 chi) ∨
      (Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1774 chi)) ∨
      ((¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1775 chi) ∨
      (¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1775 chi))))))) ∨
      (((((((¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1775 chi) ∨
      (¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1775 chi)) ∨
      ((¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1775 chi) ∨
      (Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1775 chi))) ∨
      (((Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1775 chi) ∨
      (Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1775 chi)) ∨
      ((Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1775 chi) ∨
      (Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1775 chi)))) ∨
      ((((Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1775 chi) ∨
      (¬Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1776 chi)) ∨
      ((¬Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1776 chi) ∨
      (Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1776 chi))) ∨
      (((Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1776 chi) ∨
      (Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1776 chi)) ∨
      ((Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1776 chi) ∨
      (Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1776 chi))))) ∨
      (((((Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1776 chi) ∨
      (Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1776 chi)) ∨
      ((¬Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1777 chi) ∨
      (¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1777 chi))) ∨
      (((¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1777 chi) ∨
      (Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1777 chi)) ∨
      ((Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1777 chi) ∨
      (Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1777 chi)))) ∨
      ((((Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1777 chi) ∨
      (Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1777 chi)) ∨
      ((Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1777 chi) ∨
      (¬Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom1778 chi))) ∨
      (((¬Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom1778 chi) ∨
      (¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom1778 chi)) ∨
      ((Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom1778 chi) ∨
      (Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom1778 chi)))))) ∨
      ((((((Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom1778 chi) ∨
      (Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom1778 chi)) ∨
      ((¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1779 chi) ∨
      (¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1779 chi))) ∨
      (((¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1779 chi) ∨
      (¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1779 chi)) ∨
      ((¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1779 chi) ∨
      (¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1779 chi)))) ∨
      ((((Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1779 chi) ∨
      (Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1779 chi)) ∨
      ((Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1779 chi) ∨
      (Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1779 chi))) ∨
      (((¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1780 chi) ∨
      (¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1780 chi)) ∨
      ((¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1780 chi) ∨
      (¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1780 chi))))) ∨
      (((((¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1780 chi) ∨
      (Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1780 chi)) ∨
      ((Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1780 chi) ∨
      (Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1780 chi))) ∨
      (((Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1780 chi) ∨
      (Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1780 chi)) ∨
      ((¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1781 chi) ∨
      (¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1781 chi)))) ∨
      ((((¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1781 chi) ∨
      (¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1781 chi)) ∨
      ((¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1781 chi) ∨
      (Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1781 chi))) ∨
      (((Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1781 chi) ∨
      (Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1781 chi)) ∨
      ((Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1781 chi) ∨
      (Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1781 chi)))))))))) := by
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
                exact fin15Anchored_clause14891 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14892 chi hbad
                ·
                  exact fin15Anchored_clause14893 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14894 chi hbad
                ·
                  exact fin15Anchored_clause14895 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14896 chi hbad
                ·
                  exact fin15Anchored_clause14897 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14898 chi hbad
                ·
                  exact fin15Anchored_clause14899 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14900 chi hbad
                ·
                  exact fin15Anchored_clause14901 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14902 chi hbad
                ·
                  exact fin15Anchored_clause14903 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14904 chi hbad
                ·
                  exact fin15Anchored_clause14905 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14906 chi hbad
                ·
                  exact fin15Anchored_clause14907 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14908 chi hbad
                ·
                  exact fin15Anchored_clause14909 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14910 chi hbad
                ·
                  exact fin15Anchored_clause14911 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14912 chi hbad
                ·
                  exact fin15Anchored_clause14913 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14914 chi hbad
                ·
                  exact fin15Anchored_clause14915 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14916 chi hbad
                ·
                  exact fin15Anchored_clause14917 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14918 chi hbad
                ·
                  exact fin15Anchored_clause14919 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14920 chi hbad
                ·
                  exact fin15Anchored_clause14921 chi hbad
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
                  exact fin15Anchored_clause14922 chi hbad
                ·
                  exact fin15Anchored_clause14923 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14924 chi hbad
                ·
                  exact fin15Anchored_clause14925 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14926 chi hbad
                ·
                  exact fin15Anchored_clause14927 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14928 chi hbad
                ·
                  exact fin15Anchored_clause14929 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14930 chi hbad
                ·
                  exact fin15Anchored_clause14931 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14932 chi hbad
                ·
                  exact fin15Anchored_clause14933 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14934 chi hbad
                ·
                  exact fin15Anchored_clause14935 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14936 chi hbad
                ·
                  exact fin15Anchored_clause14937 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14938 chi hbad
                ·
                  exact fin15Anchored_clause14939 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14940 chi hbad
                ·
                  exact fin15Anchored_clause14941 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14942 chi hbad
                ·
                  exact fin15Anchored_clause14943 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14944 chi hbad
                ·
                  exact fin15Anchored_clause14945 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14946 chi hbad
                ·
                  exact fin15Anchored_clause14947 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14948 chi hbad
                ·
                  exact fin15Anchored_clause14949 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14950 chi hbad
                ·
                  exact fin15Anchored_clause14951 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14952 chi hbad
                ·
                  exact fin15Anchored_clause14953 chi hbad
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
                exact fin15Anchored_clause14954 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14955 chi hbad
                ·
                  exact fin15Anchored_clause14956 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14957 chi hbad
                ·
                  exact fin15Anchored_clause14958 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14959 chi hbad
                ·
                  exact fin15Anchored_clause14960 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14961 chi hbad
                ·
                  exact fin15Anchored_clause14962 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14963 chi hbad
                ·
                  exact fin15Anchored_clause14964 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14965 chi hbad
                ·
                  exact fin15Anchored_clause14966 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14967 chi hbad
                ·
                  exact fin15Anchored_clause14968 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14969 chi hbad
                ·
                  exact fin15Anchored_clause14970 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14971 chi hbad
                ·
                  exact fin15Anchored_clause14972 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14973 chi hbad
                ·
                  exact fin15Anchored_clause14974 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14975 chi hbad
                ·
                  exact fin15Anchored_clause14976 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14977 chi hbad
                ·
                  exact fin15Anchored_clause14978 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14979 chi hbad
                ·
                  exact fin15Anchored_clause14980 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14981 chi hbad
                ·
                  exact fin15Anchored_clause14982 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14983 chi hbad
                ·
                  exact fin15Anchored_clause14984 chi hbad
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
                  exact fin15Anchored_clause14985 chi hbad
                ·
                  exact fin15Anchored_clause14986 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14987 chi hbad
                ·
                  exact fin15Anchored_clause14988 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14989 chi hbad
                ·
                  exact fin15Anchored_clause14990 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14991 chi hbad
                ·
                  exact fin15Anchored_clause14992 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14993 chi hbad
                ·
                  exact fin15Anchored_clause14994 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14995 chi hbad
                ·
                  exact fin15Anchored_clause14996 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14997 chi hbad
                ·
                  exact fin15Anchored_clause14998 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14999 chi hbad
                ·
                  exact fin15Anchored_clause15000 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15001 chi hbad
                ·
                  exact fin15Anchored_clause15002 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15003 chi hbad
                ·
                  exact fin15Anchored_clause15004 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15005 chi hbad
                ·
                  exact fin15Anchored_clause15006 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15007 chi hbad
                ·
                  exact fin15Anchored_clause15008 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15009 chi hbad
                ·
                  exact fin15Anchored_clause15010 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15011 chi hbad
                ·
                  exact fin15Anchored_clause15012 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15013 chi hbad
                ·
                  exact fin15Anchored_clause15014 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15015 chi hbad
                ·
                  exact fin15Anchored_clause15016 chi hbad
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
                exact fin15Anchored_clause15017 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15018 chi hbad
                ·
                  exact fin15Anchored_clause15019 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15020 chi hbad
                ·
                  exact fin15Anchored_clause15021 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15022 chi hbad
                ·
                  exact fin15Anchored_clause15023 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15024 chi hbad
                ·
                  exact fin15Anchored_clause15025 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15026 chi hbad
                ·
                  exact fin15Anchored_clause15027 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15028 chi hbad
                ·
                  exact fin15Anchored_clause15029 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15030 chi hbad
                ·
                  exact fin15Anchored_clause15031 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15032 chi hbad
                ·
                  exact fin15Anchored_clause15033 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15034 chi hbad
                ·
                  exact fin15Anchored_clause15035 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15036 chi hbad
                ·
                  exact fin15Anchored_clause15037 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15038 chi hbad
                ·
                  exact fin15Anchored_clause15039 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15040 chi hbad
                ·
                  exact fin15Anchored_clause15041 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15042 chi hbad
                ·
                  exact fin15Anchored_clause15043 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15044 chi hbad
                ·
                  exact fin15Anchored_clause15045 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15046 chi hbad
                ·
                  exact fin15Anchored_clause15047 chi hbad
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
                  exact fin15Anchored_clause15048 chi hbad
                ·
                  exact fin15Anchored_clause15049 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15050 chi hbad
                ·
                  exact fin15Anchored_clause15051 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15052 chi hbad
                ·
                  exact fin15Anchored_clause15053 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15054 chi hbad
                ·
                  exact fin15Anchored_clause15055 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15056 chi hbad
                ·
                  exact fin15Anchored_clause15057 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15058 chi hbad
                ·
                  exact fin15Anchored_clause15059 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15060 chi hbad
                ·
                  exact fin15Anchored_clause15061 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15062 chi hbad
                ·
                  exact fin15Anchored_clause15063 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15064 chi hbad
                ·
                  exact fin15Anchored_clause15065 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15066 chi hbad
                ·
                  exact fin15Anchored_clause15067 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15068 chi hbad
                ·
                  exact fin15Anchored_clause15069 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15070 chi hbad
                ·
                  exact fin15Anchored_clause15071 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15072 chi hbad
                ·
                  exact fin15Anchored_clause15073 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15074 chi hbad
                ·
                  exact fin15Anchored_clause15075 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15076 chi hbad
                ·
                  exact fin15Anchored_clause15077 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15078 chi hbad
                ·
                  exact fin15Anchored_clause15079 chi hbad
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
                  exact fin15Anchored_clause15080 chi hbad
                ·
                  exact fin15Anchored_clause15081 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15082 chi hbad
                ·
                  exact fin15Anchored_clause15083 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15084 chi hbad
                ·
                  exact fin15Anchored_clause15085 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15086 chi hbad
                ·
                  exact fin15Anchored_clause15087 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15088 chi hbad
                ·
                  exact fin15Anchored_clause15089 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15090 chi hbad
                ·
                  exact fin15Anchored_clause15091 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15092 chi hbad
                ·
                  exact fin15Anchored_clause15093 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15094 chi hbad
                ·
                  exact fin15Anchored_clause15095 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15096 chi hbad
                ·
                  exact fin15Anchored_clause15097 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15098 chi hbad
                ·
                  exact fin15Anchored_clause15099 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15100 chi hbad
                ·
                  exact fin15Anchored_clause15101 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15102 chi hbad
                ·
                  exact fin15Anchored_clause15103 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15104 chi hbad
                ·
                  exact fin15Anchored_clause15105 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15106 chi hbad
                ·
                  exact fin15Anchored_clause15107 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15108 chi hbad
                ·
                  exact fin15Anchored_clause15109 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15110 chi hbad
                ·
                  exact fin15Anchored_clause15111 chi hbad
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
                  exact fin15Anchored_clause15112 chi hbad
                ·
                  exact fin15Anchored_clause15113 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15114 chi hbad
                ·
                  exact fin15Anchored_clause15115 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15116 chi hbad
                ·
                  exact fin15Anchored_clause15117 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15118 chi hbad
                ·
                  exact fin15Anchored_clause15119 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15120 chi hbad
                ·
                  exact fin15Anchored_clause15121 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15122 chi hbad
                ·
                  exact fin15Anchored_clause15123 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15124 chi hbad
                ·
                  exact fin15Anchored_clause15125 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15126 chi hbad
                ·
                  exact fin15Anchored_clause15127 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15128 chi hbad
                ·
                  exact fin15Anchored_clause15129 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15130 chi hbad
                ·
                  exact fin15Anchored_clause15131 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15132 chi hbad
                ·
                  exact fin15Anchored_clause15133 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15134 chi hbad
                ·
                  exact fin15Anchored_clause15135 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15136 chi hbad
                ·
                  exact fin15Anchored_clause15137 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15138 chi hbad
                ·
                  exact fin15Anchored_clause15139 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15140 chi hbad
                ·
                  exact fin15Anchored_clause15141 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15142 chi hbad
                ·
                  exact fin15Anchored_clause15143 chi hbad

end ErdosSzekeres

end
