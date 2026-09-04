module

public import ErdosSzekeres.Fin15AnchoredClauseChunk084
public import ErdosSzekeres.Fin15AnchoredClauseChunk085
public import ErdosSzekeres.Fin15AnchoredClauseChunk086

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 043. -/

theorem fin15Anchored_rejectSemanticSegment043
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom1231 chi) ∨
      ((Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom1231 chi) ∨
      (Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom1231 chi))) ∨
      (((¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom1232 chi) ∨
      (¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom1232 chi)) ∨
      ((¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom1232 chi) ∨
      (Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom1232 chi)))) ∨
      ((((Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom1232 chi) ∨
      (Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom1232 chi)) ∨
      ((Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom1232 chi) ∨
      (¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom1233 chi))) ∨
      (((¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom1233 chi) ∨
      (¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom1233 chi)) ∨
      ((¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom1233 chi) ∨
      (Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom1233 chi))))) ∨
      (((((Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom1233 chi) ∨
      (Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom1233 chi)) ∨
      ((Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom1233 chi) ∨
      (¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom1234 chi))) ∨
      (((¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom1234 chi) ∨
      (¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom1234 chi)) ∨
      ((¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom1234 chi) ∨
      (Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom1234 chi)))) ∨
      ((((Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom1234 chi) ∨
      (Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom1234 chi)) ∨
      ((Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom1234 chi) ∨
      (¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom1235 chi))) ∨
      (((¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom1235 chi) ∨
      (¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom1235 chi)) ∨
      ((¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom1235 chi) ∨
      (Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom1235 chi)))))) ∨
      ((((((Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom1235 chi) ∨
      (Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom1235 chi)) ∨
      ((Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom1235 chi) ∨
      (¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom1236 chi))) ∨
      (((¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom1236 chi) ∨
      (Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom1236 chi)) ∨
      ((¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom1237 chi) ∨
      (¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom1237 chi)))) ∨
      ((((Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom1238 chi) ∨
      (¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom1239 chi)) ∨
      ((¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1239 chi) ∨
      (¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom1239 chi))) ∨
      (((¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1239 chi) ∨
      (¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1239 chi)) ∨
      ((Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1239 chi) ∨
      (Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom1239 chi))))) ∨
      (((((Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1239 chi) ∨
      (Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1239 chi)) ∨
      ((Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom1239 chi) ∨
      (¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom1240 chi))) ∨
      (((¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom1240 chi) ∨
      (¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom1240 chi)) ∨
      ((¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom1240 chi) ∨
      (Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom1240 chi)))) ∨
      ((((Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom1240 chi) ∨
      (Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom1240 chi)) ∨
      ((Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom1240 chi) ∨
      (¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom1241 chi))) ∨
      (((¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom1241 chi) ∨
      (¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom1241 chi)) ∨
      ((¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom1241 chi) ∨
      (Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom1241 chi))))))) ∨
      ((((((Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom1241 chi) ∨
      ((Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom1241 chi) ∨
      (Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom1241 chi))) ∨
      (((¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom1242 chi) ∨
      (¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom1242 chi)) ∨
      ((¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom1242 chi) ∨
      (Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom1242 chi)))) ∨
      ((((Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom1242 chi) ∨
      (¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom1243 chi)) ∨
      ((¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1243 chi) ∨
      (¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1243 chi))) ∨
      (((¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom1243 chi) ∨
      (¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1243 chi)) ∨
      ((Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1243 chi) ∨
      (Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom1243 chi))))) ∨
      (((((Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1243 chi) ∨
      (Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom1243 chi)) ∨
      ((¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom1244 chi) ∨
      (¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1244 chi))) ∨
      (((¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom1244 chi) ∨
      (¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1244 chi)) ∨
      ((Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1244 chi) ∨
      (Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom1244 chi)))) ∨
      ((((Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1244 chi) ∨
      (Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom1244 chi)) ∨
      ((¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom1245 chi) ∨
      (¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom1245 chi))) ∨
      (((¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom1245 chi) ∨
      (¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom1245 chi)) ∨
      ((¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom1245 chi) ∨
      (Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom1245 chi)))))) ∨
      ((((((Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom1245 chi) ∨
      (¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom1246 chi)) ∨
      ((¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1246 chi) ∨
      (¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom1246 chi))) ∨
      (((¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1246 chi) ∨
      (¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1246 chi)) ∨
      ((Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1246 chi) ∨
      (Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1246 chi)))) ∨
      ((((Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom1246 chi) ∨
      (Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1246 chi)) ∨
      ((Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom1246 chi) ∨
      (¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom1247 chi))) ∨
      (((¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1247 chi) ∨
      (¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1247 chi)) ∨
      ((¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom1247 chi) ∨
      (¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1247 chi))))) ∨
      (((((¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1247 chi) ∨
      (Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1247 chi)) ∨
      ((Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1247 chi) ∨
      (Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom1247 chi))) ∨
      (((Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1247 chi) ∨
      (Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom1247 chi)) ∨
      ((¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom1248 chi) ∨
      (¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1248 chi)))) ∨
      ((((¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom1248 chi) ∨
      (¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1248 chi)) ∨
      ((Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1248 chi) ∨
      (Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1248 chi))) ∨
      (((Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom1248 chi) ∨
      (Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1248 chi)) ∨
      ((Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom1248 chi) ∨
      (¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom1249 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom1249 chi) ∨
      ((Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1249 chi) ∨
      (Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1249 chi))) ∨
      (((¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom1250 chi) ∨
      (¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1250 chi)) ∨
      ((¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom1250 chi) ∨
      (¬Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1250 chi)))) ∨
      ((((Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1250 chi) ∨
      (Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1250 chi)) ∨
      ((Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom1250 chi) ∨
      (¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom1252 chi))) ∨
      (((Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom1252 chi) ∨
      (Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1253 chi)) ∨
      ((¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom1255 chi) ∨
      (¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1255 chi))))) ∨
      (((((¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom1255 chi) ∨
      (¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1255 chi)) ∨
      ((Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1255 chi) ∨
      (Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1255 chi))) ∨
      (((Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom1255 chi) ∨
      (Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1255 chi)) ∨
      ((Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom1255 chi) ∨
      (¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom1256 chi)))) ∨
      ((((¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom1256 chi) ∨
      (¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom1256 chi)) ∨
      ((¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom1256 chi) ∨
      (Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom1256 chi))) ∨
      (((Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom1256 chi) ∨
      (Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom1256 chi)) ∨
      ((Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom1256 chi) ∨
      (Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom1256 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom1257 chi) ∨
      (¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1257 chi)) ∨
      ((¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1257 chi) ∨
      (¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom1257 chi))) ∨
      (((¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1257 chi) ∨
      (Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1257 chi)) ∨
      ((Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom1257 chi) ∨
      (Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1257 chi)))) ∨
      ((((Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1257 chi) ∨
      (Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom1257 chi)) ∨
      ((¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom1258 chi) ∨
      (¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1258 chi))) ∨
      (((¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1258 chi) ∨
      (¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom1258 chi)) ∨
      ((¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1258 chi) ∨
      (Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1258 chi))))) ∨
      (((((Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom1258 chi) ∨
      (Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1258 chi)) ∨
      ((Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1258 chi) ∨
      (Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom1258 chi))) ∨
      (((¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom1259 chi) ∨
      (¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1259 chi)) ∨
      ((¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom1259 chi) ∨
      (¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1259 chi)))) ∨
      ((((Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1259 chi) ∨
      (Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1259 chi)) ∨
      ((Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom1259 chi) ∨
      (Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1259 chi))) ∨
      (((Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom1259 chi) ∨
      (¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom1260 chi)) ∨
      ((¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1260 chi) ∨
      (¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom1260 chi))))))) ∨
      (((((((¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1260 chi) ∨
      (¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1260 chi)) ∨
      ((¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1260 chi) ∨
      (Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1260 chi))) ∨
      (((Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom1260 chi) ∨
      (Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1260 chi)) ∨
      ((Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1260 chi) ∨
      (Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom1260 chi)))) ∨
      ((((¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom1261 chi) ∨
      (¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1261 chi)) ∨
      ((¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom1261 chi) ∨
      (¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1261 chi))) ∨
      (((Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1261 chi) ∨
      (Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1261 chi)) ∨
      ((Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom1261 chi) ∨
      (Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1261 chi))))) ∨
      (((((Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom1261 chi) ∨
      (¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom1262 chi)) ∨
      ((¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1262 chi) ∨
      (¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom1262 chi))) ∨
      (((¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1262 chi) ∨
      (¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1262 chi)) ∨
      ((Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1262 chi) ∨
      (Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1262 chi)))) ∨
      ((((Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom1262 chi) ∨
      (Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1262 chi)) ∨
      ((Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom1262 chi) ∨
      (¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom1263 chi))) ∨
      (((¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1263 chi) ∨
      (¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom1263 chi)) ∨
      ((¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1263 chi) ∨
      (Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1263 chi)))))) ∨
      ((((((Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom1263 chi) ∨
      (Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1263 chi)) ∨
      ((Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom1263 chi) ∨
      (¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom1264 chi))) ∨
      (((¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom1264 chi) ∨
      (¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom1264 chi)) ∨
      ((¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom1264 chi) ∨
      (Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom1264 chi)))) ∨
      ((((Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom1264 chi) ∨
      (Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom1264 chi)) ∨
      ((Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom1264 chi) ∨
      (¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom1265 chi))) ∨
      (((¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom1265 chi) ∨
      (¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom1266 chi)) ∨
      ((¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom1266 chi) ∨
      (Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom1266 chi))))) ∨
      (((((Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom1266 chi) ∨
      (Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom1266 chi)) ∨
      ((Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom1266 chi) ∨
      (¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom1267 chi))) ∨
      (((¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1267 chi) ∨
      (¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom1267 chi)) ∨
      ((¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1267 chi) ∨
      (¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1267 chi)))) ∨
      ((((Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1267 chi) ∨
      (Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom1267 chi)) ∨
      ((Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1267 chi) ∨
      (Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom1267 chi))) ∨
      (((¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom1268 chi) ∨
      (¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1268 chi)) ∨
      ((¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom1268 chi) ∨
      (¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1268 chi)))))))))) := by
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
                exact fin15Anchored_clause10852 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10853 chi hbad
                ·
                  exact fin15Anchored_clause10854 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10855 chi hbad
                ·
                  exact fin15Anchored_clause10856 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10857 chi hbad
                ·
                  exact fin15Anchored_clause10858 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10859 chi hbad
                ·
                  exact fin15Anchored_clause10860 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10861 chi hbad
                ·
                  exact fin15Anchored_clause10862 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10863 chi hbad
                ·
                  exact fin15Anchored_clause10864 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10865 chi hbad
                ·
                  exact fin15Anchored_clause10866 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10867 chi hbad
                ·
                  exact fin15Anchored_clause10868 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10869 chi hbad
                ·
                  exact fin15Anchored_clause10870 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10871 chi hbad
                ·
                  exact fin15Anchored_clause10872 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10873 chi hbad
                ·
                  exact fin15Anchored_clause10874 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10875 chi hbad
                ·
                  exact fin15Anchored_clause10876 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10877 chi hbad
                ·
                  exact fin15Anchored_clause10878 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10879 chi hbad
                ·
                  exact fin15Anchored_clause10880 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10881 chi hbad
                ·
                  exact fin15Anchored_clause10882 chi hbad
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
                  exact fin15Anchored_clause10883 chi hbad
                ·
                  exact fin15Anchored_clause10884 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10885 chi hbad
                ·
                  exact fin15Anchored_clause10886 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10887 chi hbad
                ·
                  exact fin15Anchored_clause10888 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10889 chi hbad
                ·
                  exact fin15Anchored_clause10890 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10891 chi hbad
                ·
                  exact fin15Anchored_clause10892 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10893 chi hbad
                ·
                  exact fin15Anchored_clause10894 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10895 chi hbad
                ·
                  exact fin15Anchored_clause10896 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10897 chi hbad
                ·
                  exact fin15Anchored_clause10898 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10899 chi hbad
                ·
                  exact fin15Anchored_clause10900 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10901 chi hbad
                ·
                  exact fin15Anchored_clause10902 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10903 chi hbad
                ·
                  exact fin15Anchored_clause10904 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10905 chi hbad
                ·
                  exact fin15Anchored_clause10906 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10907 chi hbad
                ·
                  exact fin15Anchored_clause10908 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10909 chi hbad
                ·
                  exact fin15Anchored_clause10910 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10911 chi hbad
                ·
                  exact fin15Anchored_clause10912 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10913 chi hbad
                ·
                  exact fin15Anchored_clause10914 chi hbad
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
                exact fin15Anchored_clause10915 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10916 chi hbad
                ·
                  exact fin15Anchored_clause10917 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10918 chi hbad
                ·
                  exact fin15Anchored_clause10919 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10920 chi hbad
                ·
                  exact fin15Anchored_clause10921 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10922 chi hbad
                ·
                  exact fin15Anchored_clause10923 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10924 chi hbad
                ·
                  exact fin15Anchored_clause10925 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10926 chi hbad
                ·
                  exact fin15Anchored_clause10927 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10928 chi hbad
                ·
                  exact fin15Anchored_clause10929 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10930 chi hbad
                ·
                  exact fin15Anchored_clause10931 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10932 chi hbad
                ·
                  exact fin15Anchored_clause10933 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10934 chi hbad
                ·
                  exact fin15Anchored_clause10935 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10936 chi hbad
                ·
                  exact fin15Anchored_clause10937 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10938 chi hbad
                ·
                  exact fin15Anchored_clause10939 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10940 chi hbad
                ·
                  exact fin15Anchored_clause10941 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10942 chi hbad
                ·
                  exact fin15Anchored_clause10943 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10944 chi hbad
                ·
                  exact fin15Anchored_clause10945 chi hbad
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
                  exact fin15Anchored_clause10946 chi hbad
                ·
                  exact fin15Anchored_clause10947 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10948 chi hbad
                ·
                  exact fin15Anchored_clause10949 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10950 chi hbad
                ·
                  exact fin15Anchored_clause10951 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10952 chi hbad
                ·
                  exact fin15Anchored_clause10953 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10954 chi hbad
                ·
                  exact fin15Anchored_clause10955 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10956 chi hbad
                ·
                  exact fin15Anchored_clause10957 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10958 chi hbad
                ·
                  exact fin15Anchored_clause10959 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10960 chi hbad
                ·
                  exact fin15Anchored_clause10961 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10962 chi hbad
                ·
                  exact fin15Anchored_clause10963 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10964 chi hbad
                ·
                  exact fin15Anchored_clause10965 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10966 chi hbad
                ·
                  exact fin15Anchored_clause10967 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10968 chi hbad
                ·
                  exact fin15Anchored_clause10969 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10970 chi hbad
                ·
                  exact fin15Anchored_clause10971 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10972 chi hbad
                ·
                  exact fin15Anchored_clause10973 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10974 chi hbad
                ·
                  exact fin15Anchored_clause10975 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10976 chi hbad
                ·
                  exact fin15Anchored_clause10977 chi hbad
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
                exact fin15Anchored_clause10978 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10979 chi hbad
                ·
                  exact fin15Anchored_clause10980 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10981 chi hbad
                ·
                  exact fin15Anchored_clause10982 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10983 chi hbad
                ·
                  exact fin15Anchored_clause10984 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10985 chi hbad
                ·
                  exact fin15Anchored_clause10986 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10987 chi hbad
                ·
                  exact fin15Anchored_clause10988 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10989 chi hbad
                ·
                  exact fin15Anchored_clause10990 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10991 chi hbad
                ·
                  exact fin15Anchored_clause10992 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10993 chi hbad
                ·
                  exact fin15Anchored_clause10994 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10995 chi hbad
                ·
                  exact fin15Anchored_clause10996 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10997 chi hbad
                ·
                  exact fin15Anchored_clause10998 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause10999 chi hbad
                ·
                  exact fin15Anchored_clause11000 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11001 chi hbad
                ·
                  exact fin15Anchored_clause11002 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11003 chi hbad
                ·
                  exact fin15Anchored_clause11004 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11005 chi hbad
                ·
                  exact fin15Anchored_clause11006 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11007 chi hbad
                ·
                  exact fin15Anchored_clause11008 chi hbad
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
                  exact fin15Anchored_clause11009 chi hbad
                ·
                  exact fin15Anchored_clause11010 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11011 chi hbad
                ·
                  exact fin15Anchored_clause11012 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11013 chi hbad
                ·
                  exact fin15Anchored_clause11014 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11015 chi hbad
                ·
                  exact fin15Anchored_clause11016 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11017 chi hbad
                ·
                  exact fin15Anchored_clause11018 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11019 chi hbad
                ·
                  exact fin15Anchored_clause11020 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11021 chi hbad
                ·
                  exact fin15Anchored_clause11022 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11023 chi hbad
                ·
                  exact fin15Anchored_clause11024 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11025 chi hbad
                ·
                  exact fin15Anchored_clause11026 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11027 chi hbad
                ·
                  exact fin15Anchored_clause11028 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11029 chi hbad
                ·
                  exact fin15Anchored_clause11030 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11031 chi hbad
                ·
                  exact fin15Anchored_clause11032 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11033 chi hbad
                ·
                  exact fin15Anchored_clause11034 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11035 chi hbad
                ·
                  exact fin15Anchored_clause11036 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11037 chi hbad
                ·
                  exact fin15Anchored_clause11038 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11039 chi hbad
                ·
                  exact fin15Anchored_clause11040 chi hbad
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
                  exact fin15Anchored_clause11041 chi hbad
                ·
                  exact fin15Anchored_clause11042 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11043 chi hbad
                ·
                  exact fin15Anchored_clause11044 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11045 chi hbad
                ·
                  exact fin15Anchored_clause11046 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11047 chi hbad
                ·
                  exact fin15Anchored_clause11048 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11049 chi hbad
                ·
                  exact fin15Anchored_clause11050 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11051 chi hbad
                ·
                  exact fin15Anchored_clause11052 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11053 chi hbad
                ·
                  exact fin15Anchored_clause11054 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11055 chi hbad
                ·
                  exact fin15Anchored_clause11056 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11057 chi hbad
                ·
                  exact fin15Anchored_clause11058 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11059 chi hbad
                ·
                  exact fin15Anchored_clause11060 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11061 chi hbad
                ·
                  exact fin15Anchored_clause11062 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11063 chi hbad
                ·
                  exact fin15Anchored_clause11064 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11065 chi hbad
                ·
                  exact fin15Anchored_clause11066 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11067 chi hbad
                ·
                  exact fin15Anchored_clause11068 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11069 chi hbad
                ·
                  exact fin15Anchored_clause11070 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11071 chi hbad
                ·
                  exact fin15Anchored_clause11072 chi hbad
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
                  exact fin15Anchored_clause11073 chi hbad
                ·
                  exact fin15Anchored_clause11074 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11075 chi hbad
                ·
                  exact fin15Anchored_clause11076 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11077 chi hbad
                ·
                  exact fin15Anchored_clause11078 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11079 chi hbad
                ·
                  exact fin15Anchored_clause11080 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11081 chi hbad
                ·
                  exact fin15Anchored_clause11082 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11083 chi hbad
                ·
                  exact fin15Anchored_clause11084 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11085 chi hbad
                ·
                  exact fin15Anchored_clause11086 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11087 chi hbad
                ·
                  exact fin15Anchored_clause11088 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11089 chi hbad
                ·
                  exact fin15Anchored_clause11090 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11091 chi hbad
                ·
                  exact fin15Anchored_clause11092 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11093 chi hbad
                ·
                  exact fin15Anchored_clause11094 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11095 chi hbad
                ·
                  exact fin15Anchored_clause11096 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11097 chi hbad
                ·
                  exact fin15Anchored_clause11098 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11099 chi hbad
                ·
                  exact fin15Anchored_clause11100 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11101 chi hbad
                ·
                  exact fin15Anchored_clause11102 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11103 chi hbad
                ·
                  exact fin15Anchored_clause11104 chi hbad

end ErdosSzekeres

end
