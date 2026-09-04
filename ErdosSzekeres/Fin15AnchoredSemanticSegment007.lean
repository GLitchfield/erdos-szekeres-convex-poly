module

public import ErdosSzekeres.Fin15AnchoredClauseChunk013
public import ErdosSzekeres.Fin15AnchoredClauseChunk014
public import ErdosSzekeres.Fin15AnchoredClauseChunk015

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 007. -/

theorem fin15Anchored_rejectSemanticSegment007
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0409 chi) ∨
      ((¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0409 chi) ∨
      (¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0409 chi))) ∨
      (((¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0409 chi) ∨
      (Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0409 chi)) ∨
      ((Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0409 chi) ∨
      (Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0409 chi)))) ∨
      ((((Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0409 chi) ∨
      (¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0410 chi)) ∨
      ((¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0410 chi) ∨
      (¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0410 chi))) ∨
      (((¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0410 chi) ∨
      (Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0410 chi)) ∨
      ((Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0410 chi) ∨
      (Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0410 chi))))) ∨
      (((((Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0410 chi) ∨
      (¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0411 chi)) ∨
      ((¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0411 chi) ∨
      (¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0411 chi))) ∨
      (((Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0411 chi) ∨
      (Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0411 chi)) ∨
      ((Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0411 chi) ∨
      (Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0411 chi)))) ∨
      ((((¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0412 chi) ∨
      (¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0412 chi)) ∨
      ((¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0412 chi) ∨
      (¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0412 chi))) ∨
      (((Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0412 chi) ∨
      (Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0412 chi)) ∨
      ((Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0412 chi) ∨
      (Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0412 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0413 chi) ∨
      (¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0413 chi)) ∨
      ((¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0413 chi) ∨
      (¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0413 chi))) ∨
      (((Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0413 chi) ∨
      (Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0413 chi)) ∨
      ((Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0413 chi) ∨
      (Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0413 chi)))) ∨
      ((((¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0414 chi) ∨
      (¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0414 chi)) ∨
      ((¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0414 chi) ∨
      (¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0414 chi))) ∨
      (((Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0414 chi) ∨
      (Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0414 chi)) ∨
      ((Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0414 chi) ∨
      (Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0414 chi))))) ∨
      (((((¬Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0415 chi) ∨
      (¬Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0415 chi)) ∨
      ((¬Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0415 chi) ∨
      (¬Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0415 chi))) ∨
      (((Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0415 chi) ∨
      (Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0415 chi)) ∨
      ((Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0415 chi) ∨
      (Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0415 chi)))) ∨
      ((((¬Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0416 chi) ∨
      (¬Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0416 chi)) ∨
      ((Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0416 chi) ∨
      (Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0416 chi))) ∨
      (((Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0416 chi) ∨
      (Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0416 chi)) ∨
      ((¬Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0417 chi) ∨
      (¬Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0417 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0417 chi) ∨
      ((¬Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0417 chi) ∨
      (Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0417 chi))) ∨
      (((Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0417 chi) ∨
      (Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0417 chi)) ∨
      ((¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0418 chi) ∨
      (¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0418 chi)))) ∨
      ((((¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0418 chi) ∨
      (¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0418 chi)) ∨
      ((Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0418 chi) ∨
      (Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0418 chi))) ∨
      (((Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0418 chi) ∨
      (Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0418 chi)) ∨
      ((¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0419 chi) ∨
      (¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0419 chi))))) ∨
      (((((¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0419 chi) ∨
      (¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0419 chi)) ∨
      ((Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0419 chi) ∨
      (Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0419 chi))) ∨
      (((Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0419 chi) ∨
      (Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0419 chi)) ∨
      ((¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0420 chi) ∨
      (¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0420 chi)))) ∨
      ((((¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0420 chi) ∨
      (¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0420 chi)) ∨
      ((Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0420 chi) ∨
      (Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0420 chi))) ∨
      (((Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0420 chi) ∨
      (Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0420 chi)) ∨
      ((¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0421 chi) ∨
      (¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0421 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0421 chi) ∨
      (¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0421 chi)) ∨
      ((Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0421 chi) ∨
      (Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0421 chi))) ∨
      (((Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0421 chi) ∨
      (Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0421 chi)) ∨
      ((¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0423 chi) ∨
      (¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0423 chi)))) ∨
      ((((¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0423 chi) ∨
      (¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0423 chi)) ∨
      ((Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0423 chi) ∨
      (Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0423 chi))) ∨
      (((Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0423 chi) ∨
      (Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0423 chi)) ∨
      ((¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0424 chi) ∨
      (¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0424 chi))))) ∨
      (((((¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0424 chi) ∨
      (¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0424 chi)) ∨
      ((Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0424 chi) ∨
      (Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0424 chi))) ∨
      (((Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0424 chi) ∨
      (Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0424 chi)) ∨
      ((¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0425 chi) ∨
      (¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0425 chi)))) ∨
      ((((¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0425 chi) ∨
      (¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0425 chi)) ∨
      ((Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0425 chi) ∨
      (Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0425 chi))) ∨
      (((Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0425 chi) ∨
      (Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0425 chi)) ∨
      ((¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0427 chi) ∨
      (¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0427 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0427 chi) ∨
      ((¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0427 chi) ∨
      (Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0427 chi))) ∨
      (((Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0427 chi) ∨
      (Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0427 chi)) ∨
      ((Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0427 chi) ∨
      (¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0428 chi)))) ∨
      ((((¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0428 chi) ∨
      (¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0428 chi)) ∨
      ((¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0428 chi) ∨
      (Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0428 chi))) ∨
      (((Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0428 chi) ∨
      (Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0428 chi)) ∨
      ((Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0428 chi) ∨
      (¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0429 chi))))) ∨
      (((((¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0429 chi) ∨
      (¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0429 chi)) ∨
      ((¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0429 chi) ∨
      (Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0429 chi))) ∨
      (((Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0429 chi) ∨
      (Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0429 chi)) ∨
      ((Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0429 chi) ∨
      (¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0433 chi)))) ∨
      ((((¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0433 chi) ∨
      (¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0433 chi)) ∨
      ((¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0433 chi) ∨
      (Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0433 chi))) ∨
      (((Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0433 chi) ∨
      (Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0433 chi)) ∨
      ((Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0433 chi) ∨
      (¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0434 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0434 chi) ∨
      (¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0434 chi)) ∨
      ((¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0434 chi) ∨
      (Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0434 chi))) ∨
      (((Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0434 chi) ∨
      (Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0434 chi)) ∨
      ((Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0434 chi) ∨
      (¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0435 chi)))) ∨
      ((((¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0435 chi) ∨
      (¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0435 chi)) ∨
      ((¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0435 chi) ∨
      (Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0435 chi))) ∨
      (((Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0435 chi) ∨
      (Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0435 chi)) ∨
      ((Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0435 chi) ∨
      (¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0436 chi))))) ∨
      (((((¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0436 chi) ∨
      (¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0436 chi)) ∨
      ((¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0436 chi) ∨
      (Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0436 chi))) ∨
      (((Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0436 chi) ∨
      (Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0436 chi)) ∨
      ((Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0436 chi) ∨
      (¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0437 chi)))) ∨
      ((((¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0437 chi) ∨
      (¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0437 chi)) ∨
      ((¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0437 chi) ∨
      (Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0437 chi))) ∨
      (((Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0437 chi) ∨
      (Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0437 chi)) ∨
      ((Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0437 chi) ∨
      (¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0438 chi))))))) ∨
      (((((((¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0438 chi) ∨
      (¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0438 chi)) ∨
      ((¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0438 chi) ∨
      (Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0438 chi))) ∨
      (((Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0438 chi) ∨
      (Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0438 chi)) ∨
      ((Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0438 chi) ∨
      (¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0439 chi)))) ∨
      ((((¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0439 chi) ∨
      (¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0439 chi)) ∨
      ((¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0439 chi) ∨
      (Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0439 chi))) ∨
      (((Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0439 chi) ∨
      (Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0439 chi)) ∨
      ((Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0439 chi) ∨
      (¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0440 chi))))) ∨
      (((((¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0440 chi) ∨
      (¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0440 chi)) ∨
      ((¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0440 chi) ∨
      (Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0440 chi))) ∨
      (((Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0440 chi) ∨
      (Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0440 chi)) ∨
      ((Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0440 chi) ∨
      (¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0441 chi)))) ∨
      ((((¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0441 chi) ∨
      (¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0441 chi)) ∨
      ((¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0441 chi) ∨
      (Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0441 chi))) ∨
      (((Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0441 chi) ∨
      (Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0441 chi)) ∨
      ((¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0442 chi) ∨
      (¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0442 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0442 chi) ∨
      (Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0442 chi)) ∨
      ((Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0442 chi) ∨
      (Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0442 chi))) ∨
      (((¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0443 chi) ∨
      (¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0443 chi)) ∨
      ((¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0443 chi) ∨
      (¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0443 chi)))) ∨
      ((((Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0443 chi) ∨
      (Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0443 chi)) ∨
      ((Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0443 chi) ∨
      (Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0443 chi))) ∨
      (((¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0444 chi) ∨
      (¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0444 chi)) ∨
      ((¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0444 chi) ∨
      (¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0444 chi))))) ∨
      (((((Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0444 chi) ∨
      (Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0444 chi)) ∨
      ((Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0444 chi) ∨
      (Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0444 chi))) ∨
      (((¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0445 chi) ∨
      (¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0445 chi)) ∨
      ((¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0445 chi) ∨
      (¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0445 chi)))) ∨
      ((((Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0445 chi) ∨
      (Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0445 chi)) ∨
      ((Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0445 chi) ∨
      (Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0445 chi))) ∨
      (((¬Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0446 chi) ∨
      (¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0446 chi)) ∨
      ((¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0446 chi) ∨
      (¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0446 chi)))))))))) := by
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
                exact fin15Anchored_clause01766 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01767 chi hone hbad
                ·
                  exact fin15Anchored_clause01768 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01769 chi hone hbad
                ·
                  exact fin15Anchored_clause01770 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01771 chi hone hbad
                ·
                  exact fin15Anchored_clause01772 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01773 chi hone hbad
                ·
                  exact fin15Anchored_clause01774 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01775 chi hone hbad
                ·
                  exact fin15Anchored_clause01776 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01777 chi hone hbad
                ·
                  exact fin15Anchored_clause01778 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01779 chi hone hbad
                ·
                  exact fin15Anchored_clause01780 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01781 chi hone hbad
                ·
                  exact fin15Anchored_clause01782 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01783 chi hone hbad
                ·
                  exact fin15Anchored_clause01784 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01785 chi hone hbad
                ·
                  exact fin15Anchored_clause01786 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01787 chi hone hbad
                ·
                  exact fin15Anchored_clause01788 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01789 chi hone hbad
                ·
                  exact fin15Anchored_clause01790 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01791 chi hone hbad
                ·
                  exact fin15Anchored_clause01792 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01793 chi hone hbad
                ·
                  exact fin15Anchored_clause01794 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01795 chi hone hbad
                ·
                  exact fin15Anchored_clause01796 chi hone hbad
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
                  exact fin15Anchored_clause01797 chi hone hbad
                ·
                  exact fin15Anchored_clause01798 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01799 chi hone hbad
                ·
                  exact fin15Anchored_clause01800 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01801 chi hone hbad
                ·
                  exact fin15Anchored_clause01802 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01803 chi hone hbad
                ·
                  exact fin15Anchored_clause01804 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01805 chi hone hbad
                ·
                  exact fin15Anchored_clause01806 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01807 chi hone hbad
                ·
                  exact fin15Anchored_clause01808 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01809 chi hone hbad
                ·
                  exact fin15Anchored_clause01810 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01811 chi hone hbad
                ·
                  exact fin15Anchored_clause01812 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01813 chi hone hbad
                ·
                  exact fin15Anchored_clause01814 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01815 chi hone hbad
                ·
                  exact fin15Anchored_clause01816 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01817 chi hone hbad
                ·
                  exact fin15Anchored_clause01818 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01819 chi hone hbad
                ·
                  exact fin15Anchored_clause01820 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01821 chi hone hbad
                ·
                  exact fin15Anchored_clause01822 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01823 chi hone hbad
                ·
                  exact fin15Anchored_clause01824 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01825 chi hone hbad
                ·
                  exact fin15Anchored_clause01826 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01827 chi hone hbad
                ·
                  exact fin15Anchored_clause01828 chi hone hbad
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
                exact fin15Anchored_clause01829 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01830 chi hone hbad
                ·
                  exact fin15Anchored_clause01831 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01832 chi hone hbad
                ·
                  exact fin15Anchored_clause01833 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01834 chi hone hbad
                ·
                  exact fin15Anchored_clause01835 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01836 chi hone hbad
                ·
                  exact fin15Anchored_clause01837 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01838 chi hone hbad
                ·
                  exact fin15Anchored_clause01839 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01840 chi hone hbad
                ·
                  exact fin15Anchored_clause01841 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01842 chi hone hbad
                ·
                  exact fin15Anchored_clause01843 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01844 chi hone hbad
                ·
                  exact fin15Anchored_clause01845 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01846 chi hone hbad
                ·
                  exact fin15Anchored_clause01847 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01848 chi hone hbad
                ·
                  exact fin15Anchored_clause01849 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01850 chi hone hbad
                ·
                  exact fin15Anchored_clause01851 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01852 chi hone hbad
                ·
                  exact fin15Anchored_clause01853 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01854 chi hone hbad
                ·
                  exact fin15Anchored_clause01855 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01856 chi hone hbad
                ·
                  exact fin15Anchored_clause01857 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01858 chi hone hbad
                ·
                  exact fin15Anchored_clause01859 chi hone hbad
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
                  exact fin15Anchored_clause01860 chi hone hbad
                ·
                  exact fin15Anchored_clause01861 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01862 chi hone hbad
                ·
                  exact fin15Anchored_clause01863 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01864 chi hone hbad
                ·
                  exact fin15Anchored_clause01865 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01866 chi hone hbad
                ·
                  exact fin15Anchored_clause01867 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01868 chi hone hbad
                ·
                  exact fin15Anchored_clause01869 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01870 chi hone hbad
                ·
                  exact fin15Anchored_clause01871 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01872 chi hone hbad
                ·
                  exact fin15Anchored_clause01873 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01874 chi hone hbad
                ·
                  exact fin15Anchored_clause01875 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01876 chi hone hbad
                ·
                  exact fin15Anchored_clause01877 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01878 chi hone hbad
                ·
                  exact fin15Anchored_clause01879 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01880 chi hone hbad
                ·
                  exact fin15Anchored_clause01881 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01882 chi hone hbad
                ·
                  exact fin15Anchored_clause01883 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01884 chi hone hbad
                ·
                  exact fin15Anchored_clause01885 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01886 chi hone hbad
                ·
                  exact fin15Anchored_clause01887 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01888 chi hone hbad
                ·
                  exact fin15Anchored_clause01889 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01890 chi hone hbad
                ·
                  exact fin15Anchored_clause01891 chi hone hbad
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
                exact fin15Anchored_clause01892 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01893 chi hone hbad
                ·
                  exact fin15Anchored_clause01894 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01895 chi hone hbad
                ·
                  exact fin15Anchored_clause01896 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01897 chi hone hbad
                ·
                  exact fin15Anchored_clause01898 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01899 chi hone hbad
                ·
                  exact fin15Anchored_clause01900 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01901 chi hone hbad
                ·
                  exact fin15Anchored_clause01902 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01903 chi hone hbad
                ·
                  exact fin15Anchored_clause01904 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01905 chi hone hbad
                ·
                  exact fin15Anchored_clause01906 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01907 chi hone hbad
                ·
                  exact fin15Anchored_clause01908 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01909 chi hone hbad
                ·
                  exact fin15Anchored_clause01910 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01911 chi hone hbad
                ·
                  exact fin15Anchored_clause01912 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01913 chi hone hbad
                ·
                  exact fin15Anchored_clause01914 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01915 chi hone hbad
                ·
                  exact fin15Anchored_clause01916 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01917 chi hone hbad
                ·
                  exact fin15Anchored_clause01918 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01919 chi hone hbad
                ·
                  exact fin15Anchored_clause01920 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01921 chi hone hbad
                ·
                  exact fin15Anchored_clause01922 chi hone hbad
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
                  exact fin15Anchored_clause01923 chi hone hbad
                ·
                  exact fin15Anchored_clause01924 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01925 chi hone hbad
                ·
                  exact fin15Anchored_clause01926 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01927 chi hone hbad
                ·
                  exact fin15Anchored_clause01928 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01929 chi hone hbad
                ·
                  exact fin15Anchored_clause01930 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01931 chi hone hbad
                ·
                  exact fin15Anchored_clause01932 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01933 chi hone hbad
                ·
                  exact fin15Anchored_clause01934 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01935 chi hone hbad
                ·
                  exact fin15Anchored_clause01936 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01937 chi hone hbad
                ·
                  exact fin15Anchored_clause01938 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01939 chi hone hbad
                ·
                  exact fin15Anchored_clause01940 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01941 chi hone hbad
                ·
                  exact fin15Anchored_clause01942 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01943 chi hone hbad
                ·
                  exact fin15Anchored_clause01944 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01945 chi hone hbad
                ·
                  exact fin15Anchored_clause01946 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01947 chi hone hbad
                ·
                  exact fin15Anchored_clause01948 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01949 chi hone hbad
                ·
                  exact fin15Anchored_clause01950 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01951 chi hone hbad
                ·
                  exact fin15Anchored_clause01952 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01953 chi hone hbad
                ·
                  exact fin15Anchored_clause01954 chi hone hbad
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
                  exact fin15Anchored_clause01955 chi hone hbad
                ·
                  exact fin15Anchored_clause01956 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01957 chi hone hbad
                ·
                  exact fin15Anchored_clause01958 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01959 chi hone hbad
                ·
                  exact fin15Anchored_clause01960 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01961 chi hone hbad
                ·
                  exact fin15Anchored_clause01962 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01963 chi hone hbad
                ·
                  exact fin15Anchored_clause01964 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01965 chi hone hbad
                ·
                  exact fin15Anchored_clause01966 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01967 chi hone hbad
                ·
                  exact fin15Anchored_clause01968 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01969 chi hone hbad
                ·
                  exact fin15Anchored_clause01970 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01971 chi hone hbad
                ·
                  exact fin15Anchored_clause01972 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01973 chi hone hbad
                ·
                  exact fin15Anchored_clause01974 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01975 chi hone hbad
                ·
                  exact fin15Anchored_clause01976 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01977 chi hone hbad
                ·
                  exact fin15Anchored_clause01978 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01979 chi hone hbad
                ·
                  exact fin15Anchored_clause01980 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01981 chi hone hbad
                ·
                  exact fin15Anchored_clause01982 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01983 chi hone hbad
                ·
                  exact fin15Anchored_clause01984 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01985 chi hone hbad
                ·
                  exact fin15Anchored_clause01986 chi hone hbad
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
                  exact fin15Anchored_clause01987 chi hone hbad
                ·
                  exact fin15Anchored_clause01988 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01989 chi hone hbad
                ·
                  exact fin15Anchored_clause01990 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01991 chi hone hbad
                ·
                  exact fin15Anchored_clause01992 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01993 chi hone hbad
                ·
                  exact fin15Anchored_clause01994 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01995 chi hone hbad
                ·
                  exact fin15Anchored_clause01996 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01997 chi hone hbad
                ·
                  exact fin15Anchored_clause01998 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause01999 chi hone hbad
                ·
                  exact fin15Anchored_clause02000 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02001 chi hone hbad
                ·
                  exact fin15Anchored_clause02002 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02003 chi hone hbad
                ·
                  exact fin15Anchored_clause02004 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02005 chi hone hbad
                ·
                  exact fin15Anchored_clause02006 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02007 chi hone hbad
                ·
                  exact fin15Anchored_clause02008 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02009 chi hone hbad
                ·
                  exact fin15Anchored_clause02010 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02011 chi hone hbad
                ·
                  exact fin15Anchored_clause02012 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02013 chi hone hbad
                ·
                  exact fin15Anchored_clause02014 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02015 chi hone hbad
                ·
                  exact fin15Anchored_clause02016 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02017 chi hone hbad
                ·
                  exact fin15Anchored_clause02018 chi hone hbad

end ErdosSzekeres

end
