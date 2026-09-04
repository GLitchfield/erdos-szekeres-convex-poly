module

public import ErdosSzekeres.Fin15AnchoredClauseChunk015
public import ErdosSzekeres.Fin15AnchoredClauseChunk016
public import ErdosSzekeres.Fin15AnchoredClauseChunk017

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 008. -/

theorem fin15Anchored_rejectSemanticSegment008
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0446 chi) ∨
      ((Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0446 chi) ∨
      (Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0446 chi))) ∨
      (((Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0446 chi) ∨
      (¬Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0447 chi)) ∨
      ((¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0447 chi) ∨
      (¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0447 chi)))) ∨
      ((((¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0447 chi) ∨
      (Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0447 chi)) ∨
      ((Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0447 chi) ∨
      (Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0447 chi))) ∨
      (((Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0447 chi) ∨
      (¬Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0448 chi)) ∨
      ((¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0448 chi) ∨
      (¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0448 chi))))) ∨
      (((((¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0448 chi) ∨
      (Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0448 chi)) ∨
      ((¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0449 chi) ∨
      (¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0449 chi))) ∨
      (((¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0449 chi) ∨
      (¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0449 chi)) ∨
      ((Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0449 chi) ∨
      (Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0449 chi)))) ∨
      ((((Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0449 chi) ∨
      (Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0449 chi)) ∨
      ((¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0450 chi) ∨
      (¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0450 chi))) ∨
      (((¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0450 chi) ∨
      (¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0450 chi)) ∨
      ((Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0450 chi) ∨
      (Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0450 chi)))))) ∨
      ((((((Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0450 chi) ∨
      (Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0450 chi)) ∨
      ((¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0451 chi) ∨
      (¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0451 chi))) ∨
      (((¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0451 chi) ∨
      (¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0451 chi)) ∨
      ((Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0451 chi) ∨
      (Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0451 chi)))) ∨
      ((((Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0451 chi) ∨
      (Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0451 chi)) ∨
      ((¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0452 chi) ∨
      (¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0452 chi))) ∨
      (((¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0452 chi) ∨
      (¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0452 chi)) ∨
      ((Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0452 chi) ∨
      (Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0452 chi))))) ∨
      (((((Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0452 chi) ∨
      (Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0452 chi)) ∨
      ((¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0453 chi) ∨
      (¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0453 chi))) ∨
      (((¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0453 chi) ∨
      (¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0453 chi)) ∨
      ((Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0453 chi) ∨
      (Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0453 chi)))) ∨
      ((((Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0453 chi) ∨
      (Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0453 chi)) ∨
      ((¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0454 chi) ∨
      (Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0454 chi))) ∨
      (((Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0454 chi) ∨
      (Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0454 chi)) ∨
      ((Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0454 chi) ∨
      (¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0455 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0455 chi) ∨
      ((¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0455 chi) ∨
      (¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0455 chi))) ∨
      (((Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0455 chi) ∨
      (Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0455 chi)) ∨
      ((Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0455 chi) ∨
      (Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0455 chi)))) ∨
      ((((¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0236 chi) ∨
      (¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0236 chi)) ∨
      ((¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0236 chi) ∨
      (¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0236 chi))) ∨
      (((Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0236 chi) ∨
      (Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0236 chi)) ∨
      ((Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0236 chi) ∨
      (Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0236 chi))))) ∨
      (((((¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0237 chi) ∨
      (¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0237 chi)) ∨
      ((¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0237 chi) ∨
      (¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0237 chi))) ∨
      (((Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0237 chi) ∨
      (Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0237 chi)) ∨
      ((Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0237 chi) ∨
      (Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0237 chi)))) ∨
      ((((¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0238 chi) ∨
      (¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0238 chi)) ∨
      ((¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0238 chi) ∨
      (¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0238 chi))) ∨
      (((Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0238 chi) ∨
      (Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0238 chi)) ∨
      ((Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0238 chi) ∨
      (Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0238 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0239 chi) ∨
      (¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0239 chi)) ∨
      ((¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0239 chi) ∨
      (Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0239 chi))) ∨
      (((¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0240 chi) ∨
      (¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0240 chi)) ∨
      ((¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0240 chi) ∨
      (¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0240 chi)))) ∨
      ((((Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0240 chi) ∨
      (Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0240 chi)) ∨
      ((Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0240 chi) ∨
      (Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0240 chi))) ∨
      (((¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0241 chi) ∨
      (¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0241 chi)) ∨
      ((¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0241 chi) ∨
      (¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0241 chi))))) ∨
      (((((Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0241 chi) ∨
      (Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0241 chi)) ∨
      ((Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0241 chi) ∨
      (Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0241 chi))) ∨
      (((¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0242 chi) ∨
      (¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0242 chi)) ∨
      ((¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0242 chi) ∨
      (¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0242 chi)))) ∨
      ((((Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0242 chi) ∨
      (Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0242 chi)) ∨
      ((Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0242 chi) ∨
      (¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0243 chi))) ∨
      (((¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0243 chi) ∨
      (¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0243 chi)) ∨
      ((¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0243 chi) ∨
      (Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0243 chi)))))))) ∨
      (((((((Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0243 chi) ∨
      ((Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0243 chi) ∨
      (Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0243 chi))) ∨
      (((¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0244 chi) ∨
      (¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0244 chi)) ∨
      ((¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0244 chi) ∨
      (¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0244 chi)))) ∨
      ((((Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0244 chi) ∨
      (Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0244 chi)) ∨
      ((Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0244 chi) ∨
      (Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0244 chi))) ∨
      (((¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0245 chi) ∨
      (¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0245 chi)) ∨
      ((¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0245 chi) ∨
      (¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0245 chi))))) ∨
      (((((Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0245 chi) ∨
      (Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0245 chi)) ∨
      ((Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0245 chi) ∨
      (Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0245 chi))) ∨
      (((¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0246 chi) ∨
      (¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0246 chi)) ∨
      ((¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0246 chi) ∨
      (¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0246 chi)))) ∨
      ((((Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0246 chi) ∨
      (Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0246 chi)) ∨
      ((Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0246 chi) ∨
      (Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0246 chi))) ∨
      (((¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0247 chi) ∨
      (¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0247 chi)) ∨
      ((¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0247 chi) ∨
      (¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0247 chi)))))) ∨
      ((((((Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0247 chi) ∨
      (Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0247 chi)) ∨
      ((Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0247 chi) ∨
      (Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0247 chi))) ∨
      (((¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0248 chi) ∨
      (¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0248 chi)) ∨
      ((¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0248 chi) ∨
      (¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0248 chi)))) ∨
      ((((Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0248 chi) ∨
      (¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0249 chi)) ∨
      ((¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0249 chi) ∨
      (¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0249 chi))) ∨
      (((¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0249 chi) ∨
      (Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0249 chi)) ∨
      ((Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0249 chi) ∨
      (Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0249 chi))))) ∨
      (((((Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0249 chi) ∨
      (¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0250 chi)) ∨
      ((¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0250 chi) ∨
      (¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0250 chi))) ∨
      (((¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0250 chi) ∨
      (Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0250 chi)) ∨
      ((Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0250 chi) ∨
      (Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0250 chi)))) ∨
      ((((Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0250 chi) ∨
      (¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0251 chi)) ∨
      ((¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0251 chi) ∨
      (¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0251 chi))) ∨
      (((¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0251 chi) ∨
      (Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0251 chi)) ∨
      ((Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0251 chi) ∨
      (Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0251 chi))))))) ∨
      ((((((Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0251 chi) ∨
      ((¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0252 chi) ∨
      (¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0252 chi))) ∨
      (((¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0252 chi) ∨
      (¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0252 chi)) ∨
      ((Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0252 chi) ∨
      (Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0252 chi)))) ∨
      ((((Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0252 chi) ∨
      (Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0252 chi)) ∨
      ((¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0253 chi) ∨
      (¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0253 chi))) ∨
      (((¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0253 chi) ∨
      (¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0253 chi)) ∨
      ((Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0253 chi) ∨
      (Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0253 chi))))) ∨
      (((((Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0253 chi) ∨
      (Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0253 chi)) ∨
      ((¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0254 chi) ∨
      (¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0254 chi))) ∨
      (((¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0254 chi) ∨
      (¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0254 chi)) ∨
      ((Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0254 chi) ∨
      (Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0254 chi)))) ∨
      ((((Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0254 chi) ∨
      (Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0254 chi)) ∨
      ((¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0255 chi) ∨
      (¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0255 chi))) ∨
      (((¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0255 chi) ∨
      (¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0255 chi)) ∨
      ((Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0255 chi) ∨
      (Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0255 chi)))))) ∨
      ((((((Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0255 chi) ∨
      (Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0255 chi)) ∨
      ((¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0256 chi) ∨
      (¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0256 chi))) ∨
      (((¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0256 chi) ∨
      (¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0256 chi)) ∨
      ((Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0256 chi) ∨
      (Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0256 chi)))) ∨
      ((((Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0256 chi) ∨
      (Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0256 chi)) ∨
      ((¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0257 chi) ∨
      (¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0257 chi))) ∨
      (((¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0257 chi) ∨
      (¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0257 chi)) ∨
      ((Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0257 chi) ∨
      (Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0257 chi))))) ∨
      (((((Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0257 chi) ∨
      (Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0257 chi)) ∨
      ((¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0258 chi) ∨
      (¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0258 chi))) ∨
      (((¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0258 chi) ∨
      (¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0258 chi)) ∨
      ((Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0258 chi) ∨
      (Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0258 chi)))) ∨
      ((((Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0258 chi) ∨
      (Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0258 chi)) ∨
      ((¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0259 chi) ∨
      (¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0259 chi))) ∨
      (((¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0259 chi) ∨
      (¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0259 chi)) ∨
      ((Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0259 chi) ∨
      (Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0259 chi)))))))))) := by
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
                exact fin15Anchored_clause02019 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02020 chi hone hbad
                ·
                  exact fin15Anchored_clause02021 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02022 chi hone hbad
                ·
                  exact fin15Anchored_clause02023 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02024 chi hone hbad
                ·
                  exact fin15Anchored_clause02025 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02026 chi hone hbad
                ·
                  exact fin15Anchored_clause02027 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02028 chi hone hbad
                ·
                  exact fin15Anchored_clause02029 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02030 chi hone hbad
                ·
                  exact fin15Anchored_clause02031 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02032 chi hone hbad
                ·
                  exact fin15Anchored_clause02033 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02034 chi hone hbad
                ·
                  exact fin15Anchored_clause02035 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02036 chi hone hbad
                ·
                  exact fin15Anchored_clause02037 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02038 chi hone hbad
                ·
                  exact fin15Anchored_clause02039 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02040 chi hone hbad
                ·
                  exact fin15Anchored_clause02041 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02042 chi hone hbad
                ·
                  exact fin15Anchored_clause02043 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02044 chi hone hbad
                ·
                  exact fin15Anchored_clause02045 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02046 chi hone hbad
                ·
                  exact fin15Anchored_clause02047 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02048 chi hone hbad
                ·
                  exact fin15Anchored_clause02049 chi hone hbad
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
                  exact fin15Anchored_clause02050 chi hone hbad
                ·
                  exact fin15Anchored_clause02051 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02052 chi hone hbad
                ·
                  exact fin15Anchored_clause02053 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02054 chi hone hbad
                ·
                  exact fin15Anchored_clause02055 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02056 chi hone hbad
                ·
                  exact fin15Anchored_clause02057 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02058 chi hone hbad
                ·
                  exact fin15Anchored_clause02059 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02060 chi hone hbad
                ·
                  exact fin15Anchored_clause02061 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02062 chi hone hbad
                ·
                  exact fin15Anchored_clause02063 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02064 chi hone hbad
                ·
                  exact fin15Anchored_clause02065 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02066 chi hone hbad
                ·
                  exact fin15Anchored_clause02067 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02068 chi hone hbad
                ·
                  exact fin15Anchored_clause02069 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02070 chi hone hbad
                ·
                  exact fin15Anchored_clause02071 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02072 chi hone hbad
                ·
                  exact fin15Anchored_clause02073 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02074 chi hone hbad
                ·
                  exact fin15Anchored_clause02075 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02076 chi hone hbad
                ·
                  exact fin15Anchored_clause02077 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02078 chi hone hbad
                ·
                  exact fin15Anchored_clause02079 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02080 chi hone hbad
                ·
                  exact fin15Anchored_clause02081 chi hone hbad
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
                exact fin15Anchored_clause02082 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02083 chi hone hbad
                ·
                  exact fin15Anchored_clause02084 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02085 chi hone hbad
                ·
                  exact fin15Anchored_clause02086 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02087 chi hone hbad
                ·
                  exact fin15Anchored_clause02088 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02089 chi hone hbad
                ·
                  exact fin15Anchored_clause02090 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02091 chi hone hbad
                ·
                  exact fin15Anchored_clause02092 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02093 chi hone hbad
                ·
                  exact fin15Anchored_clause02094 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02095 chi hone hbad
                ·
                  exact fin15Anchored_clause02096 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02097 chi hone hbad
                ·
                  exact fin15Anchored_clause02098 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02099 chi hone hbad
                ·
                  exact fin15Anchored_clause02100 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02101 chi hone hbad
                ·
                  exact fin15Anchored_clause02102 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02103 chi hone hbad
                ·
                  exact fin15Anchored_clause02104 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02105 chi hone hbad
                ·
                  exact fin15Anchored_clause02106 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02107 chi hone hbad
                ·
                  exact fin15Anchored_clause02108 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02109 chi hone hbad
                ·
                  exact fin15Anchored_clause02110 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02111 chi hone hbad
                ·
                  exact fin15Anchored_clause02112 chi hone hbad
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
                  exact fin15Anchored_clause02113 chi hone hbad
                ·
                  exact fin15Anchored_clause02114 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02115 chi hone hbad
                ·
                  exact fin15Anchored_clause02116 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02117 chi hone hbad
                ·
                  exact fin15Anchored_clause02118 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02119 chi hone hbad
                ·
                  exact fin15Anchored_clause02120 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02121 chi hone hbad
                ·
                  exact fin15Anchored_clause02122 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02123 chi hone hbad
                ·
                  exact fin15Anchored_clause02124 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02125 chi hone hbad
                ·
                  exact fin15Anchored_clause02126 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02127 chi hone hbad
                ·
                  exact fin15Anchored_clause02128 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02129 chi hone hbad
                ·
                  exact fin15Anchored_clause02130 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02131 chi hone hbad
                ·
                  exact fin15Anchored_clause02132 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02133 chi hone hbad
                ·
                  exact fin15Anchored_clause02134 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02135 chi hone hbad
                ·
                  exact fin15Anchored_clause02136 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02137 chi hone hbad
                ·
                  exact fin15Anchored_clause02138 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02139 chi hone hbad
                ·
                  exact fin15Anchored_clause02140 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02141 chi hone hbad
                ·
                  exact fin15Anchored_clause02142 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02143 chi hone hbad
                ·
                  exact fin15Anchored_clause02144 chi hone hbad
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
                exact fin15Anchored_clause02145 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02146 chi hone hbad
                ·
                  exact fin15Anchored_clause02147 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02148 chi hone hbad
                ·
                  exact fin15Anchored_clause02149 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02150 chi hone hbad
                ·
                  exact fin15Anchored_clause02151 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02152 chi hone hbad
                ·
                  exact fin15Anchored_clause02153 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02154 chi hone hbad
                ·
                  exact fin15Anchored_clause02155 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02156 chi hone hbad
                ·
                  exact fin15Anchored_clause02157 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02158 chi hone hbad
                ·
                  exact fin15Anchored_clause02159 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02160 chi hone hbad
                ·
                  exact fin15Anchored_clause02161 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02162 chi hone hbad
                ·
                  exact fin15Anchored_clause02163 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02164 chi hone hbad
                ·
                  exact fin15Anchored_clause02165 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02166 chi hone hbad
                ·
                  exact fin15Anchored_clause02167 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02168 chi hone hbad
                ·
                  exact fin15Anchored_clause02169 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02170 chi hone hbad
                ·
                  exact fin15Anchored_clause02171 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02172 chi hone hbad
                ·
                  exact fin15Anchored_clause02173 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02174 chi hone hbad
                ·
                  exact fin15Anchored_clause02175 chi hone hbad
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
                  exact fin15Anchored_clause02176 chi hone hbad
                ·
                  exact fin15Anchored_clause02177 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02178 chi hone hbad
                ·
                  exact fin15Anchored_clause02179 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02180 chi hone hbad
                ·
                  exact fin15Anchored_clause02181 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02182 chi hone hbad
                ·
                  exact fin15Anchored_clause02183 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02184 chi hone hbad
                ·
                  exact fin15Anchored_clause02185 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02186 chi hone hbad
                ·
                  exact fin15Anchored_clause02187 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02188 chi hone hbad
                ·
                  exact fin15Anchored_clause02189 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02190 chi hone hbad
                ·
                  exact fin15Anchored_clause02191 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02192 chi hone hbad
                ·
                  exact fin15Anchored_clause02193 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02194 chi hone hbad
                ·
                  exact fin15Anchored_clause02195 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02196 chi hone hbad
                ·
                  exact fin15Anchored_clause02197 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02198 chi hone hbad
                ·
                  exact fin15Anchored_clause02199 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02200 chi hone hbad
                ·
                  exact fin15Anchored_clause02201 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02202 chi hone hbad
                ·
                  exact fin15Anchored_clause02203 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02204 chi hone hbad
                ·
                  exact fin15Anchored_clause02205 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02206 chi hone hbad
                ·
                  exact fin15Anchored_clause02207 chi hone hbad
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
                exact fin15Anchored_clause02208 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02209 chi hone hbad
                ·
                  exact fin15Anchored_clause02210 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02211 chi hone hbad
                ·
                  exact fin15Anchored_clause02212 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02213 chi hone hbad
                ·
                  exact fin15Anchored_clause02214 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02215 chi hone hbad
                ·
                  exact fin15Anchored_clause02216 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02217 chi hone hbad
                ·
                  exact fin15Anchored_clause02218 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02219 chi hone hbad
                ·
                  exact fin15Anchored_clause02220 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02221 chi hone hbad
                ·
                  exact fin15Anchored_clause02222 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02223 chi hone hbad
                ·
                  exact fin15Anchored_clause02224 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02225 chi hone hbad
                ·
                  exact fin15Anchored_clause02226 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02227 chi hone hbad
                ·
                  exact fin15Anchored_clause02228 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02229 chi hone hbad
                ·
                  exact fin15Anchored_clause02230 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02231 chi hone hbad
                ·
                  exact fin15Anchored_clause02232 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02233 chi hone hbad
                ·
                  exact fin15Anchored_clause02234 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02235 chi hone hbad
                ·
                  exact fin15Anchored_clause02236 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02237 chi hone hbad
                ·
                  exact fin15Anchored_clause02238 chi hone hbad
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
                  exact fin15Anchored_clause02239 chi hone hbad
                ·
                  exact fin15Anchored_clause02240 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02241 chi hone hbad
                ·
                  exact fin15Anchored_clause02242 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02243 chi hone hbad
                ·
                  exact fin15Anchored_clause02244 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02245 chi hone hbad
                ·
                  exact fin15Anchored_clause02246 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02247 chi hone hbad
                ·
                  exact fin15Anchored_clause02248 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02249 chi hone hbad
                ·
                  exact fin15Anchored_clause02250 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02251 chi hone hbad
                ·
                  exact fin15Anchored_clause02252 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02253 chi hone hbad
                ·
                  exact fin15Anchored_clause02254 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02255 chi hone hbad
                ·
                  exact fin15Anchored_clause02256 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02257 chi hone hbad
                ·
                  exact fin15Anchored_clause02258 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02259 chi hone hbad
                ·
                  exact fin15Anchored_clause02260 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02261 chi hone hbad
                ·
                  exact fin15Anchored_clause02262 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02263 chi hone hbad
                ·
                  exact fin15Anchored_clause02264 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02265 chi hone hbad
                ·
                  exact fin15Anchored_clause02266 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02267 chi hone hbad
                ·
                  exact fin15Anchored_clause02268 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02269 chi hone hbad
                ·
                  exact fin15Anchored_clause02270 chi hone hbad

end ErdosSzekeres

end
