module

public import ErdosSzekeres.Fin15AnchoredClauseChunk023
public import ErdosSzekeres.Fin15AnchoredClauseChunk024
public import ErdosSzekeres.Fin15AnchoredClauseChunk025

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 012. -/

theorem fin15Anchored_rejectSemanticSegment012
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0365 chi) ∨
      ((¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0365 chi) ∨
      (¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0365 chi))) ∨
      (((Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0365 chi) ∨
      (Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0365 chi)) ∨
      ((Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0365 chi) ∨
      (Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0365 chi)))) ∨
      ((((¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0366 chi) ∨
      (¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0366 chi)) ∨
      ((¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0366 chi) ∨
      (Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0366 chi))) ∨
      (((Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0366 chi) ∨
      (¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0367 chi)) ∨
      ((¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0367 chi) ∨
      (¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0367 chi))))) ∨
      (((((Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0367 chi) ∨
      (Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0367 chi)) ∨
      ((Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0367 chi) ∨
      (Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0367 chi))) ∨
      (((¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0368 chi) ∨
      (Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0368 chi)) ∨
      ((Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0368 chi) ∨
      (Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0368 chi)))) ∨
      ((((Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0368 chi) ∨
      (¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0369 chi)) ∨
      ((¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0369 chi) ∨
      (¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0369 chi))) ∨
      (((¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0369 chi) ∨
      (Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0369 chi)) ∨
      ((Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0369 chi) ∨
      (Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0369 chi)))))) ∨
      ((((((Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0369 chi) ∨
      (¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0370 chi)) ∨
      ((¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0370 chi) ∨
      (¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0370 chi))) ∨
      (((¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0370 chi) ∨
      (Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0370 chi)) ∨
      ((Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0370 chi) ∨
      (Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0370 chi)))) ∨
      ((((Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0370 chi) ∨
      (¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0371 chi)) ∨
      ((¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0371 chi) ∨
      (¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0371 chi))) ∨
      (((¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0371 chi) ∨
      (Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0371 chi)) ∨
      ((Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0371 chi) ∨
      (Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0371 chi))))) ∨
      (((((Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0371 chi) ∨
      (¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0372 chi)) ∨
      ((¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0372 chi) ∨
      (¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0372 chi))) ∨
      (((¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0372 chi) ∨
      (Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0372 chi)) ∨
      ((Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0372 chi) ∨
      (Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0372 chi)))) ∨
      ((((¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0373 chi) ∨
      (¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0373 chi)) ∨
      ((¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0373 chi) ∨
      (¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0373 chi))) ∨
      (((Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0373 chi) ∨
      (Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0373 chi)) ∨
      ((Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0373 chi) ∨
      (Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0373 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0374 chi) ∨
      ((¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0374 chi) ∨
      (¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0374 chi))) ∨
      (((¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0374 chi) ∨
      (Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0374 chi)) ∨
      ((Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0374 chi) ∨
      (Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0374 chi)))) ∨
      ((((Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0374 chi) ∨
      (¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0375 chi)) ∨
      ((¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0375 chi) ∨
      (¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0375 chi))) ∨
      (((¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0375 chi) ∨
      (Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0375 chi)) ∨
      ((Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0375 chi) ∨
      (Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0375 chi))))) ∨
      (((((Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0375 chi) ∨
      (¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0376 chi)) ∨
      ((¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0376 chi) ∨
      (¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0376 chi))) ∨
      (((¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0376 chi) ∨
      (Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0376 chi)) ∨
      ((Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0376 chi) ∨
      (Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0376 chi)))) ∨
      ((((Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0376 chi) ∨
      (¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0377 chi)) ∨
      ((¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0377 chi) ∨
      (¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0377 chi))) ∨
      (((¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0377 chi) ∨
      (Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0377 chi)) ∨
      ((Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0377 chi) ∨
      (Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0377 chi)))))) ∨
      ((((((Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0377 chi) ∨
      (¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0378 chi)) ∨
      ((¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0378 chi) ∨
      (¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0378 chi))) ∨
      (((¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0378 chi) ∨
      (Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0378 chi)) ∨
      ((Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0378 chi) ∨
      (Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0378 chi)))) ∨
      ((((Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0378 chi) ∨
      (¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0379 chi)) ∨
      ((¬Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0379 chi) ∨
      (¬Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0379 chi))) ∨
      (((¬Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0379 chi) ∨
      (Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0379 chi)) ∨
      ((Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0379 chi) ∨
      (Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0379 chi))))) ∨
      (((((¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0380 chi) ∨
      (¬Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0380 chi)) ∨
      ((¬Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0380 chi) ∨
      (Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0380 chi))) ∨
      (((Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0380 chi) ∨
      (Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0380 chi)) ∨
      ((Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0380 chi) ∨
      (¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0382 chi)))) ∨
      ((((¬Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0382 chi) ∨
      (¬Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0382 chi)) ∨
      ((¬Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0382 chi) ∨
      (Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0382 chi))) ∨
      (((¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0383 chi) ∨
      (¬Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0383 chi)) ∨
      ((Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0383 chi) ∨
      (¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0385 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0385 chi) ∨
      ((¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0385 chi) ∨
      (¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0385 chi))) ∨
      (((Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0385 chi) ∨
      (Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0385 chi)) ∨
      ((Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0385 chi) ∨
      (Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0385 chi)))) ∨
      ((((¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0386 chi) ∨
      (¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0386 chi)) ∨
      ((¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0386 chi) ∨
      (¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0386 chi))) ∨
      (((Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0386 chi) ∨
      (Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0386 chi)) ∨
      ((Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0386 chi) ∨
      (Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0386 chi))))) ∨
      (((((¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0387 chi) ∨
      (¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0387 chi)) ∨
      ((¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0387 chi) ∨
      (¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0387 chi))) ∨
      (((Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0387 chi) ∨
      (Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0387 chi)) ∨
      ((Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0387 chi) ∨
      (Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0387 chi)))) ∨
      ((((¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0388 chi) ∨
      (¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0388 chi)) ∨
      ((¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0388 chi) ∨
      (¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0388 chi))) ∨
      (((Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0388 chi) ∨
      (Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0388 chi)) ∨
      ((Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0388 chi) ∨
      (Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0388 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0389 chi) ∨
      (¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0389 chi)) ∨
      ((¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0389 chi) ∨
      (¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0389 chi))) ∨
      (((Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0389 chi) ∨
      (Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0389 chi)) ∨
      ((Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0389 chi) ∨
      (Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0389 chi)))) ∨
      ((((¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0390 chi) ∨
      (¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0390 chi)) ∨
      ((¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0390 chi) ∨
      (¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0390 chi))) ∨
      (((Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0390 chi) ∨
      (Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0390 chi)) ∨
      ((Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0390 chi) ∨
      (Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0390 chi))))) ∨
      (((((¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0391 chi) ∨
      (¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0391 chi)) ∨
      ((¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0391 chi) ∨
      (¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0391 chi))) ∨
      (((Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0391 chi) ∨
      (Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0391 chi)) ∨
      ((Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0391 chi) ∨
      (Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0391 chi)))) ∨
      ((((¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0392 chi) ∨
      (¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0392 chi)) ∨
      ((¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0392 chi) ∨
      (¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0392 chi))) ∨
      (((Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0392 chi) ∨
      (Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0392 chi)) ∨
      ((Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0392 chi) ∨
      (Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0392 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0393 chi) ∨
      ((¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0393 chi) ∨
      (¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0393 chi))) ∨
      (((¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0393 chi) ∨
      (Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0393 chi)) ∨
      ((Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0393 chi) ∨
      (Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0393 chi)))) ∨
      ((((Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0393 chi) ∨
      (¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0394 chi)) ∨
      ((¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0394 chi) ∨
      (¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0394 chi))) ∨
      (((¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0394 chi) ∨
      (Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0394 chi)) ∨
      ((Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0394 chi) ∨
      (Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0394 chi))))) ∨
      (((((Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0394 chi) ∨
      (¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0395 chi)) ∨
      ((¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0395 chi) ∨
      (¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0395 chi))) ∨
      (((¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0395 chi) ∨
      (Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0395 chi)) ∨
      ((Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0395 chi) ∨
      (Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0395 chi)))) ∨
      ((((Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0395 chi) ∨
      (¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0396 chi)) ∨
      ((¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0396 chi) ∨
      (¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0396 chi))) ∨
      (((Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0396 chi) ∨
      (Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0396 chi)) ∨
      ((¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0397 chi) ∨
      (¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0397 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0397 chi) ∨
      (¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0397 chi)) ∨
      ((Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0397 chi) ∨
      (Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0397 chi))) ∨
      (((Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0397 chi) ∨
      (Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0397 chi)) ∨
      ((¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0398 chi) ∨
      (¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0398 chi)))) ∨
      ((((¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0398 chi) ∨
      (¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0398 chi)) ∨
      ((Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0398 chi) ∨
      (Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0398 chi))) ∨
      (((Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0398 chi) ∨
      (Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0398 chi)) ∨
      ((¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0399 chi) ∨
      (¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0399 chi))))) ∨
      (((((¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0399 chi) ∨
      (¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0399 chi)) ∨
      ((Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0399 chi) ∨
      (Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0399 chi))) ∨
      (((Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0399 chi) ∨
      (Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0399 chi)) ∨
      ((¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0400 chi) ∨
      (¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0400 chi)))) ∨
      ((((¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0400 chi) ∨
      (Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0400 chi)) ∨
      ((Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0400 chi) ∨
      (Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0400 chi))) ∨
      (((Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0400 chi) ∨
      (¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0401 chi)) ∨
      ((¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0401 chi) ∨
      (¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0401 chi)))))))))) := by
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
                exact fin15Anchored_clause03028 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03029 chi hone hbad
                ·
                  exact fin15Anchored_clause03030 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03031 chi hone hbad
                ·
                  exact fin15Anchored_clause03032 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03033 chi hone hbad
                ·
                  exact fin15Anchored_clause03034 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03035 chi hone hbad
                ·
                  exact fin15Anchored_clause03036 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03037 chi hone hbad
                ·
                  exact fin15Anchored_clause03038 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03039 chi hone hbad
                ·
                  exact fin15Anchored_clause03040 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03041 chi hone hbad
                ·
                  exact fin15Anchored_clause03042 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03043 chi hone hbad
                ·
                  exact fin15Anchored_clause03044 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03045 chi hone hbad
                ·
                  exact fin15Anchored_clause03046 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03047 chi hone hbad
                ·
                  exact fin15Anchored_clause03048 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03049 chi hone hbad
                ·
                  exact fin15Anchored_clause03050 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03051 chi hone hbad
                ·
                  exact fin15Anchored_clause03052 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03053 chi hone hbad
                ·
                  exact fin15Anchored_clause03054 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03055 chi hone hbad
                ·
                  exact fin15Anchored_clause03056 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03057 chi hone hbad
                ·
                  exact fin15Anchored_clause03058 chi hone hbad
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
                  exact fin15Anchored_clause03059 chi hone hbad
                ·
                  exact fin15Anchored_clause03060 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03061 chi hone hbad
                ·
                  exact fin15Anchored_clause03062 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03063 chi hone hbad
                ·
                  exact fin15Anchored_clause03064 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03065 chi hone hbad
                ·
                  exact fin15Anchored_clause03066 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03067 chi hone hbad
                ·
                  exact fin15Anchored_clause03068 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03069 chi hone hbad
                ·
                  exact fin15Anchored_clause03070 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03071 chi hone hbad
                ·
                  exact fin15Anchored_clause03072 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03073 chi hone hbad
                ·
                  exact fin15Anchored_clause03074 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03075 chi hone hbad
                ·
                  exact fin15Anchored_clause03076 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03077 chi hone hbad
                ·
                  exact fin15Anchored_clause03078 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03079 chi hone hbad
                ·
                  exact fin15Anchored_clause03080 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03081 chi hone hbad
                ·
                  exact fin15Anchored_clause03082 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03083 chi hone hbad
                ·
                  exact fin15Anchored_clause03084 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03085 chi hone hbad
                ·
                  exact fin15Anchored_clause03086 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03087 chi hone hbad
                ·
                  exact fin15Anchored_clause03088 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03089 chi hone hbad
                ·
                  exact fin15Anchored_clause03090 chi hone hbad
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
                exact fin15Anchored_clause03091 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03092 chi hone hbad
                ·
                  exact fin15Anchored_clause03093 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03094 chi hone hbad
                ·
                  exact fin15Anchored_clause03095 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03096 chi hone hbad
                ·
                  exact fin15Anchored_clause03097 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03098 chi hone hbad
                ·
                  exact fin15Anchored_clause03099 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03100 chi hone hbad
                ·
                  exact fin15Anchored_clause03101 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03102 chi hone hbad
                ·
                  exact fin15Anchored_clause03103 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03104 chi hone hbad
                ·
                  exact fin15Anchored_clause03105 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03106 chi hone hbad
                ·
                  exact fin15Anchored_clause03107 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03108 chi hone hbad
                ·
                  exact fin15Anchored_clause03109 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03110 chi hone hbad
                ·
                  exact fin15Anchored_clause03111 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03112 chi hone hbad
                ·
                  exact fin15Anchored_clause03113 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03114 chi hone hbad
                ·
                  exact fin15Anchored_clause03115 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03116 chi hone hbad
                ·
                  exact fin15Anchored_clause03117 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03118 chi hone hbad
                ·
                  exact fin15Anchored_clause03119 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03120 chi hone hbad
                ·
                  exact fin15Anchored_clause03121 chi hone hbad
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
                  exact fin15Anchored_clause03122 chi hone hbad
                ·
                  exact fin15Anchored_clause03123 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03124 chi hone hbad
                ·
                  exact fin15Anchored_clause03125 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03126 chi hone hbad
                ·
                  exact fin15Anchored_clause03127 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03128 chi hone hbad
                ·
                  exact fin15Anchored_clause03129 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03130 chi hone hbad
                ·
                  exact fin15Anchored_clause03131 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03132 chi hone hbad
                ·
                  exact fin15Anchored_clause03133 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03134 chi hone hbad
                ·
                  exact fin15Anchored_clause03135 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03136 chi hone hbad
                ·
                  exact fin15Anchored_clause03137 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03138 chi hone hbad
                ·
                  exact fin15Anchored_clause03139 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03140 chi hone hbad
                ·
                  exact fin15Anchored_clause03141 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03142 chi hone hbad
                ·
                  exact fin15Anchored_clause03143 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03144 chi hone hbad
                ·
                  exact fin15Anchored_clause03145 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03146 chi hone hbad
                ·
                  exact fin15Anchored_clause03147 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03148 chi hone hbad
                ·
                  exact fin15Anchored_clause03149 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03150 chi hone hbad
                ·
                  exact fin15Anchored_clause03151 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03152 chi hone hbad
                ·
                  exact fin15Anchored_clause03153 chi hone hbad
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
                exact fin15Anchored_clause03154 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03155 chi hone hbad
                ·
                  exact fin15Anchored_clause03156 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03157 chi hone hbad
                ·
                  exact fin15Anchored_clause03158 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03159 chi hone hbad
                ·
                  exact fin15Anchored_clause03160 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03161 chi hone hbad
                ·
                  exact fin15Anchored_clause03162 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03163 chi hone hbad
                ·
                  exact fin15Anchored_clause03164 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03165 chi hone hbad
                ·
                  exact fin15Anchored_clause03166 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03167 chi hone hbad
                ·
                  exact fin15Anchored_clause03168 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03169 chi hone hbad
                ·
                  exact fin15Anchored_clause03170 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03171 chi hone hbad
                ·
                  exact fin15Anchored_clause03172 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03173 chi hone hbad
                ·
                  exact fin15Anchored_clause03174 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03175 chi hone hbad
                ·
                  exact fin15Anchored_clause03176 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03177 chi hone hbad
                ·
                  exact fin15Anchored_clause03178 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03179 chi hone hbad
                ·
                  exact fin15Anchored_clause03180 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03181 chi hone hbad
                ·
                  exact fin15Anchored_clause03182 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03183 chi hone hbad
                ·
                  exact fin15Anchored_clause03184 chi hone hbad
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
                  exact fin15Anchored_clause03185 chi hone hbad
                ·
                  exact fin15Anchored_clause03186 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03187 chi hone hbad
                ·
                  exact fin15Anchored_clause03188 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03189 chi hone hbad
                ·
                  exact fin15Anchored_clause03190 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03191 chi hone hbad
                ·
                  exact fin15Anchored_clause03192 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03193 chi hone hbad
                ·
                  exact fin15Anchored_clause03194 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03195 chi hone hbad
                ·
                  exact fin15Anchored_clause03196 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03197 chi hone hbad
                ·
                  exact fin15Anchored_clause03198 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03199 chi hone hbad
                ·
                  exact fin15Anchored_clause03200 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03201 chi hone hbad
                ·
                  exact fin15Anchored_clause03202 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03203 chi hone hbad
                ·
                  exact fin15Anchored_clause03204 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03205 chi hone hbad
                ·
                  exact fin15Anchored_clause03206 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03207 chi hone hbad
                ·
                  exact fin15Anchored_clause03208 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03209 chi hone hbad
                ·
                  exact fin15Anchored_clause03210 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03211 chi hone hbad
                ·
                  exact fin15Anchored_clause03212 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03213 chi hone hbad
                ·
                  exact fin15Anchored_clause03214 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03215 chi hone hbad
                ·
                  exact fin15Anchored_clause03216 chi hone hbad
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
                exact fin15Anchored_clause03217 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03218 chi hone hbad
                ·
                  exact fin15Anchored_clause03219 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03220 chi hone hbad
                ·
                  exact fin15Anchored_clause03221 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03222 chi hone hbad
                ·
                  exact fin15Anchored_clause03223 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03224 chi hone hbad
                ·
                  exact fin15Anchored_clause03225 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03226 chi hone hbad
                ·
                  exact fin15Anchored_clause03227 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03228 chi hone hbad
                ·
                  exact fin15Anchored_clause03229 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03230 chi hone hbad
                ·
                  exact fin15Anchored_clause03231 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03232 chi hone hbad
                ·
                  exact fin15Anchored_clause03233 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03234 chi hone hbad
                ·
                  exact fin15Anchored_clause03235 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03236 chi hone hbad
                ·
                  exact fin15Anchored_clause03237 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03238 chi hone hbad
                ·
                  exact fin15Anchored_clause03239 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03240 chi hone hbad
                ·
                  exact fin15Anchored_clause03241 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03242 chi hone hbad
                ·
                  exact fin15Anchored_clause03243 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03244 chi hone hbad
                ·
                  exact fin15Anchored_clause03245 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03246 chi hone hbad
                ·
                  exact fin15Anchored_clause03247 chi hone hbad
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
                  exact fin15Anchored_clause03248 chi hone hbad
                ·
                  exact fin15Anchored_clause03249 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03250 chi hone hbad
                ·
                  exact fin15Anchored_clause03251 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03252 chi hone hbad
                ·
                  exact fin15Anchored_clause03253 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03254 chi hone hbad
                ·
                  exact fin15Anchored_clause03255 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03256 chi hone hbad
                ·
                  exact fin15Anchored_clause03257 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03258 chi hone hbad
                ·
                  exact fin15Anchored_clause03259 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03260 chi hone hbad
                ·
                  exact fin15Anchored_clause03261 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03262 chi hone hbad
                ·
                  exact fin15Anchored_clause03263 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03264 chi hone hbad
                ·
                  exact fin15Anchored_clause03265 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03266 chi hone hbad
                ·
                  exact fin15Anchored_clause03267 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03268 chi hone hbad
                ·
                  exact fin15Anchored_clause03269 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03270 chi hone hbad
                ·
                  exact fin15Anchored_clause03271 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03272 chi hone hbad
                ·
                  exact fin15Anchored_clause03273 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03274 chi hone hbad
                ·
                  exact fin15Anchored_clause03275 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03276 chi hone hbad
                ·
                  exact fin15Anchored_clause03277 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03278 chi hone hbad
                ·
                  exact fin15Anchored_clause03279 chi hone hbad

end ErdosSzekeres

end
