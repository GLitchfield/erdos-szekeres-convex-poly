module

public import ErdosSzekeres.Fin15AnchoredClauseChunk118
public import ErdosSzekeres.Fin15AnchoredClauseChunk119
public import ErdosSzekeres.Fin15AnchoredClauseChunk120

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 060. -/

theorem fin15Anchored_rejectSemanticSegment060
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1782 chi) ∨
      ((¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1782 chi) ∨
      (¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1782 chi))) ∨
      (((¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1782 chi) ∨
      (¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1782 chi)) ∨
      ((Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1782 chi) ∨
      (Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1782 chi)))) ∨
      ((((Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1782 chi) ∨
      (¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1783 chi)) ∨
      ((¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1783 chi) ∨
      (¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1783 chi))) ∨
      (((¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1783 chi) ∨
      (¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1783 chi)) ∨
      ((Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1783 chi) ∨
      (Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1783 chi))))) ∨
      (((((Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1783 chi) ∨
      (Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1783 chi)) ∨
      ((¬Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0454 chi ∧
      Fin15AnchoredAtom1784 chi) ∨
      (¬Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom1784 chi))) ∨
      (((Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      Fin15AnchoredAtom1784 chi) ∨
      (Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom1784 chi)) ∨
      ((¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1785 chi) ∨
      (¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1785 chi)))) ∨
      ((((¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1785 chi) ∨
      (¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1785 chi)) ∨
      ((¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1785 chi) ∨
      (¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1785 chi))) ∨
      (((Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1785 chi) ∨
      (Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1785 chi)) ∨
      ((Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1785 chi) ∨
      (Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1785 chi)))))) ∨
      ((((((Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1785 chi) ∨
      (Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1785 chi)) ∨
      ((¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1787 chi) ∨
      (¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1787 chi))) ∨
      (((¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1787 chi) ∨
      (¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1787 chi)) ∨
      ((Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1787 chi) ∨
      (Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1787 chi)))) ∨
      ((((Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1787 chi) ∨
      (Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1787 chi)) ∨
      ((Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1787 chi) ∨
      (Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1787 chi))) ∨
      (((Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1787 chi) ∨
      (¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1788 chi)) ∨
      ((¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1788 chi) ∨
      (¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1788 chi))))) ∨
      (((((¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1788 chi) ∨
      (¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1788 chi)) ∨
      ((Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1788 chi) ∨
      (Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1788 chi))) ∨
      (((Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1788 chi) ∨
      (Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1788 chi)) ∨
      ((¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1789 chi) ∨
      (¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1789 chi)))) ∨
      ((((¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1789 chi) ∨
      (¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1789 chi)) ∨
      ((Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1789 chi) ∨
      (Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1789 chi))) ∨
      (((Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1789 chi) ∨
      (Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1789 chi)) ∨
      ((¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1793 chi) ∨
      (¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1793 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1793 chi) ∨
      ((¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1793 chi) ∨
      (¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1793 chi))) ∨
      (((¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1793 chi) ∨
      (Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1793 chi)) ∨
      ((Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1793 chi) ∨
      (Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1793 chi)))) ∨
      ((((Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1793 chi) ∨
      (Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1793 chi)) ∨
      ((¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1794 chi) ∨
      (¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1794 chi))) ∨
      (((¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1794 chi) ∨
      (Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1794 chi)) ∨
      ((Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1794 chi) ∨
      (Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1794 chi))))) ∨
      (((((Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1794 chi) ∨
      (Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1794 chi)) ∨
      ((¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1795 chi) ∨
      (¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1795 chi))) ∨
      (((¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1795 chi) ∨
      (¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1795 chi)) ∨
      ((¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1795 chi) ∨
      (Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1795 chi)))) ∨
      ((((Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1795 chi) ∨
      (Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1795 chi)) ∨
      ((Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1795 chi) ∨
      (¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1799 chi))) ∨
      (((¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1799 chi) ∨
      (¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1799 chi)) ∨
      ((¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1799 chi) ∨
      (Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1799 chi)))))) ∨
      ((((((Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1799 chi) ∨
      (Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1799 chi)) ∨
      ((Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1799 chi) ∨
      (Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1799 chi))) ∨
      (((¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1800 chi) ∨
      (¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1800 chi)) ∨
      ((¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1800 chi) ∨
      (¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1800 chi)))) ∨
      ((((¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1800 chi) ∨
      (¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1800 chi)) ∨
      ((Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1800 chi) ∨
      (Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1800 chi))) ∨
      (((Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1800 chi) ∨
      (¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1801 chi)) ∨
      ((¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1801 chi) ∨
      (¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1801 chi))))) ∨
      (((((¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1801 chi) ∨
      (Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1801 chi)) ∨
      ((Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1801 chi) ∨
      (Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1801 chi))) ∨
      (((Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1801 chi) ∨
      (Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1801 chi)) ∨
      ((Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1801 chi) ∨
      (¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1805 chi)))) ∨
      ((((¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1805 chi) ∨
      (¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1805 chi)) ∨
      ((¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1805 chi) ∨
      (¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1805 chi))) ∨
      (((¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1805 chi) ∨
      (Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1805 chi)) ∨
      ((Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1805 chi) ∨
      (Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1805 chi)))))))) ∨
      (((((((Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1805 chi) ∨
      ((Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1805 chi) ∨
      (¬Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1806 chi))) ∨
      (((¬Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1806 chi) ∨
      (¬Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1806 chi)) ∨
      ((¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1806 chi) ∨
      (¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1806 chi)))) ∨
      ((((Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1806 chi) ∨
      (Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1806 chi)) ∨
      ((Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1806 chi) ∨
      (Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1806 chi))) ∨
      (((¬Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1807 chi) ∨
      (¬Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1807 chi)) ∨
      ((¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1807 chi) ∨
      (Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1807 chi))))) ∨
      (((((Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1807 chi) ∨
      (Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1807 chi)) ∨
      ((¬Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom1808 chi) ∨
      (¬Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom1808 chi))) ∨
      (((Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom1808 chi) ∨
      (¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1809 chi)) ∨
      ((¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1809 chi) ∨
      (¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1809 chi)))) ∨
      ((((¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1809 chi) ∨
      (Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1809 chi)) ∨
      ((Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1809 chi) ∨
      (Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1809 chi))) ∨
      (((Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1809 chi) ∨
      (Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1809 chi)) ∨
      ((¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1810 chi) ∨
      (¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1810 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1810 chi) ∨
      (¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1810 chi)) ∨
      ((Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1810 chi) ∨
      (Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1810 chi))) ∨
      (((Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1810 chi) ∨
      (Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1810 chi)) ∨
      ((Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1810 chi) ∨
      (Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1810 chi)))) ∨
      ((((¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1811 chi) ∨
      (¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1811 chi)) ∨
      ((¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1811 chi) ∨
      (¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1811 chi))) ∨
      (((¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1811 chi) ∨
      (Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1811 chi)) ∨
      ((Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1811 chi) ∨
      (Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1811 chi))))) ∨
      (((((Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1811 chi) ∨
      (Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1811 chi)) ∨
      ((¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1812 chi) ∨
      (¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1812 chi))) ∨
      (((¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1812 chi) ∨
      (¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1812 chi)) ∨
      ((Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1812 chi) ∨
      (Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1812 chi)))) ∨
      ((((¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1813 chi) ∨
      (¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1813 chi)) ∨
      ((¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1813 chi) ∨
      (Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1813 chi))) ∨
      (((Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1813 chi) ∨
      (Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1813 chi)) ∨
      ((¬Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom1814 chi) ∨
      (Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      Fin15AnchoredAtom1814 chi))))))) ∨
      ((((((Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom1814 chi) ∨
      ((¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1815 chi) ∨
      (¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1815 chi))) ∨
      (((¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1815 chi) ∨
      (¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1815 chi)) ∨
      ((¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1815 chi) ∨
      (¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1815 chi)))) ∨
      ((((Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1815 chi) ∨
      (Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1815 chi)) ∨
      ((Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1815 chi) ∨
      (Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1815 chi))) ∨
      (((Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1815 chi) ∨
      (¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1816 chi)) ∨
      ((¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1816 chi) ∨
      (¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1816 chi))))) ∨
      (((((¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1816 chi) ∨
      (¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1816 chi)) ∨
      ((Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1816 chi) ∨
      (Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1816 chi))) ∨
      (((Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1816 chi) ∨
      (Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1816 chi)) ∨
      ((¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1817 chi) ∨
      (¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1817 chi)))) ∨
      ((((¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1817 chi) ∨
      (¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1817 chi)) ∨
      ((¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1817 chi) ∨
      (Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1817 chi))) ∨
      (((Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1817 chi) ∨
      (Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1817 chi)) ∨
      ((Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1817 chi) ∨
      (¬Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom1818 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom1818 chi) ∨
      (Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      Fin15AnchoredAtom1818 chi)) ∨
      ((Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom0454 chi ∧
      Fin15AnchoredAtom1818 chi) ∨
      (Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom1818 chi))) ∨
      (((Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      Fin15AnchoredAtom1818 chi) ∨
      (Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom1818 chi)) ∨
      ((¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1819 chi) ∨
      (¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1819 chi)))) ∨
      ((((¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1819 chi) ∨
      (¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1819 chi)) ∨
      ((¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1819 chi) ∨
      (Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1819 chi))) ∨
      (((Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1819 chi) ∨
      (Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1819 chi)) ∨
      ((Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1819 chi) ∨
      (¬Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1820 chi))))) ∨
      (((((¬Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom0454 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1820 chi) ∨
      (Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1820 chi)) ∨
      ((Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom0456 chi) ∨
      (Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom0457 chi))) ∨
      (((Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom0468 chi) ∨
      (Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom0534 chi)) ∨
      ((Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom0820 chi) ∨
      (¬Fin15AnchoredAtom1821 chi ∧
      Fin15AnchoredAtom0456 chi ∧
      Fin15AnchoredAtom0457 chi ∧
      Fin15AnchoredAtom0468 chi ∧
      Fin15AnchoredAtom0534 chi ∧
      Fin15AnchoredAtom0820 chi)))) ∨
      ((((Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom0456 chi) ∨
      (Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom0458 chi)) ∨
      ((Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom0469 chi) ∨
      (Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom0535 chi))) ∨
      (((Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom0821 chi) ∨
      (¬Fin15AnchoredAtom1822 chi ∧
      Fin15AnchoredAtom0456 chi ∧
      Fin15AnchoredAtom0458 chi ∧
      Fin15AnchoredAtom0469 chi ∧
      Fin15AnchoredAtom0535 chi ∧
      Fin15AnchoredAtom0821 chi)) ∨
      ((Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom0456 chi) ∨
      (Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom0459 chi)))))))))) := by
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
                exact fin15Anchored_clause15144 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15145 chi hbad
                ·
                  exact fin15Anchored_clause15146 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15147 chi hbad
                ·
                  exact fin15Anchored_clause15148 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15149 chi hbad
                ·
                  exact fin15Anchored_clause15150 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15151 chi hbad
                ·
                  exact fin15Anchored_clause15152 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15153 chi hbad
                ·
                  exact fin15Anchored_clause15154 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15155 chi hbad
                ·
                  exact fin15Anchored_clause15156 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15157 chi hbad
                ·
                  exact fin15Anchored_clause15158 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15159 chi hbad
                ·
                  exact fin15Anchored_clause15160 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15161 chi hbad
                ·
                  exact fin15Anchored_clause15162 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15163 chi hbad
                ·
                  exact fin15Anchored_clause15164 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15165 chi hbad
                ·
                  exact fin15Anchored_clause15166 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15167 chi hbad
                ·
                  exact fin15Anchored_clause15168 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15169 chi hbad
                ·
                  exact fin15Anchored_clause15170 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15171 chi hbad
                ·
                  exact fin15Anchored_clause15172 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15173 chi hbad
                ·
                  exact fin15Anchored_clause15174 chi hbad
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
                  exact fin15Anchored_clause15175 chi hbad
                ·
                  exact fin15Anchored_clause15176 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15177 chi hbad
                ·
                  exact fin15Anchored_clause15178 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15179 chi hbad
                ·
                  exact fin15Anchored_clause15180 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15181 chi hbad
                ·
                  exact fin15Anchored_clause15182 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15183 chi hbad
                ·
                  exact fin15Anchored_clause15184 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15185 chi hbad
                ·
                  exact fin15Anchored_clause15186 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15187 chi hbad
                ·
                  exact fin15Anchored_clause15188 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15189 chi hbad
                ·
                  exact fin15Anchored_clause15190 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15191 chi hbad
                ·
                  exact fin15Anchored_clause15192 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15193 chi hbad
                ·
                  exact fin15Anchored_clause15194 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15195 chi hbad
                ·
                  exact fin15Anchored_clause15196 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15197 chi hbad
                ·
                  exact fin15Anchored_clause15198 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15199 chi hbad
                ·
                  exact fin15Anchored_clause15200 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15201 chi hbad
                ·
                  exact fin15Anchored_clause15202 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15203 chi hbad
                ·
                  exact fin15Anchored_clause15204 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15205 chi hbad
                ·
                  exact fin15Anchored_clause15206 chi hbad
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
                exact fin15Anchored_clause15207 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15208 chi hbad
                ·
                  exact fin15Anchored_clause15209 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15210 chi hbad
                ·
                  exact fin15Anchored_clause15211 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15212 chi hbad
                ·
                  exact fin15Anchored_clause15213 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15214 chi hbad
                ·
                  exact fin15Anchored_clause15215 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15216 chi hbad
                ·
                  exact fin15Anchored_clause15217 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15218 chi hbad
                ·
                  exact fin15Anchored_clause15219 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15220 chi hbad
                ·
                  exact fin15Anchored_clause15221 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15222 chi hbad
                ·
                  exact fin15Anchored_clause15223 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15224 chi hbad
                ·
                  exact fin15Anchored_clause15225 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15226 chi hbad
                ·
                  exact fin15Anchored_clause15227 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15228 chi hbad
                ·
                  exact fin15Anchored_clause15229 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15230 chi hbad
                ·
                  exact fin15Anchored_clause15231 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15232 chi hbad
                ·
                  exact fin15Anchored_clause15233 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15234 chi hbad
                ·
                  exact fin15Anchored_clause15235 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15236 chi hbad
                ·
                  exact fin15Anchored_clause15237 chi hbad
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
                  exact fin15Anchored_clause15238 chi hbad
                ·
                  exact fin15Anchored_clause15239 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15240 chi hbad
                ·
                  exact fin15Anchored_clause15241 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15242 chi hbad
                ·
                  exact fin15Anchored_clause15243 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15244 chi hbad
                ·
                  exact fin15Anchored_clause15245 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15246 chi hbad
                ·
                  exact fin15Anchored_clause15247 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15248 chi hbad
                ·
                  exact fin15Anchored_clause15249 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15250 chi hbad
                ·
                  exact fin15Anchored_clause15251 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15252 chi hbad
                ·
                  exact fin15Anchored_clause15253 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15254 chi hbad
                ·
                  exact fin15Anchored_clause15255 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15256 chi hbad
                ·
                  exact fin15Anchored_clause15257 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15258 chi hbad
                ·
                  exact fin15Anchored_clause15259 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15260 chi hbad
                ·
                  exact fin15Anchored_clause15261 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15262 chi hbad
                ·
                  exact fin15Anchored_clause15263 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15264 chi hbad
                ·
                  exact fin15Anchored_clause15265 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15266 chi hbad
                ·
                  exact fin15Anchored_clause15267 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15268 chi hbad
                ·
                  exact fin15Anchored_clause15269 chi hbad
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
                exact fin15Anchored_clause15270 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15271 chi hbad
                ·
                  exact fin15Anchored_clause15272 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15273 chi hbad
                ·
                  exact fin15Anchored_clause15274 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15275 chi hbad
                ·
                  exact fin15Anchored_clause15276 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15277 chi hbad
                ·
                  exact fin15Anchored_clause15278 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15279 chi hbad
                ·
                  exact fin15Anchored_clause15280 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15281 chi hbad
                ·
                  exact fin15Anchored_clause15282 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15283 chi hbad
                ·
                  exact fin15Anchored_clause15284 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15285 chi hbad
                ·
                  exact fin15Anchored_clause15286 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15287 chi hbad
                ·
                  exact fin15Anchored_clause15288 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15289 chi hbad
                ·
                  exact fin15Anchored_clause15290 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15291 chi hbad
                ·
                  exact fin15Anchored_clause15292 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15293 chi hbad
                ·
                  exact fin15Anchored_clause15294 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15295 chi hbad
                ·
                  exact fin15Anchored_clause15296 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15297 chi hbad
                ·
                  exact fin15Anchored_clause15298 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15299 chi hbad
                ·
                  exact fin15Anchored_clause15300 chi hbad
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
                  exact fin15Anchored_clause15301 chi hbad
                ·
                  exact fin15Anchored_clause15302 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15303 chi hbad
                ·
                  exact fin15Anchored_clause15304 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15305 chi hbad
                ·
                  exact fin15Anchored_clause15306 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15307 chi hbad
                ·
                  exact fin15Anchored_clause15308 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15309 chi hbad
                ·
                  exact fin15Anchored_clause15310 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15311 chi hbad
                ·
                  exact fin15Anchored_clause15312 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15313 chi hbad
                ·
                  exact fin15Anchored_clause15314 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15315 chi hbad
                ·
                  exact fin15Anchored_clause15316 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15317 chi hbad
                ·
                  exact fin15Anchored_clause15318 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15319 chi hbad
                ·
                  exact fin15Anchored_clause15320 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15321 chi hbad
                ·
                  exact fin15Anchored_clause15322 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15323 chi hbad
                ·
                  exact fin15Anchored_clause15324 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15325 chi hbad
                ·
                  exact fin15Anchored_clause15326 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15327 chi hbad
                ·
                  exact fin15Anchored_clause15328 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15329 chi hbad
                ·
                  exact fin15Anchored_clause15330 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15331 chi hbad
                ·
                  exact fin15Anchored_clause15332 chi hbad
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
                exact fin15Anchored_clause15333 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15334 chi hbad
                ·
                  exact fin15Anchored_clause15335 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15336 chi hbad
                ·
                  exact fin15Anchored_clause15337 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15338 chi hbad
                ·
                  exact fin15Anchored_clause15339 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15340 chi hbad
                ·
                  exact fin15Anchored_clause15341 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15342 chi hbad
                ·
                  exact fin15Anchored_clause15343 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15344 chi hbad
                ·
                  exact fin15Anchored_clause15345 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15346 chi hbad
                ·
                  exact fin15Anchored_clause15347 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15348 chi hbad
                ·
                  exact fin15Anchored_clause15349 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15350 chi hbad
                ·
                  exact fin15Anchored_clause15351 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15352 chi hbad
                ·
                  exact fin15Anchored_clause15353 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15354 chi hbad
                ·
                  exact fin15Anchored_clause15355 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15356 chi hbad
                ·
                  exact fin15Anchored_clause15357 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15358 chi hbad
                ·
                  exact fin15Anchored_clause15359 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15360 chi hbad
                ·
                  exact fin15Anchored_clause15361 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15362 chi hbad
                ·
                  exact fin15Anchored_clause15363 chi hbad
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
                  exact fin15Anchored_clause15364 chi hbad
                ·
                  exact fin15Anchored_clause15365 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15366 chi hbad
                ·
                  exact fin15Anchored_clause15367 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15368 chi hbad
                ·
                  exact fin15Anchored_clause15369 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15370 chi hbad
                ·
                  exact fin15Anchored_clause15371 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15372 chi hbad
                ·
                  exact fin15Anchored_clause15373 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15374 chi hbad
                ·
                  exact fin15Anchored_clause15375 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15376 chi hbad
                ·
                  exact fin15Anchored_clause15377 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15378 chi hbad
                ·
                  exact fin15Anchored_clause15379 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15380 chi hbad
                ·
                  exact fin15Anchored_clause15381 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15382 chi hbad
                ·
                  exact fin15Anchored_clause15383 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15384 chi hbad
                ·
                  exact fin15Anchored_clause15385 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15386 chi hbad
                ·
                  exact fin15Anchored_clause15387 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15388 chi hbad
                ·
                  exact fin15Anchored_clause15389 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15390 chi hbad
                ·
                  exact fin15Anchored_clause15391 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15392 chi hbad
                ·
                  exact fin15Anchored_clause15393 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause15394 chi hbad
                ·
                  exact fin15Anchored_clause15395 chi hbad

end ErdosSzekeres

end
