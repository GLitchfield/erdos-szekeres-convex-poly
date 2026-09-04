module

public import ErdosSzekeres.Fin15AnchoredClauseChunk029
public import ErdosSzekeres.Fin15AnchoredClauseChunk030
public import ErdosSzekeres.Fin15AnchoredClauseChunk031

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 015. -/

theorem fin15Anchored_rejectSemanticSegment015
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0311 chi) ∨
      ((Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0311 chi) ∨
      (¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0312 chi))) ∨
      (((¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0312 chi) ∨
      (¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0312 chi)) ∨
      ((¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0312 chi) ∨
      (Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0312 chi)))) ∨
      ((((Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0312 chi) ∨
      (Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0312 chi)) ∨
      ((Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0312 chi) ∨
      (¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0313 chi))) ∨
      (((¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0313 chi) ∨
      (¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0313 chi)) ∨
      ((¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0313 chi) ∨
      (Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0313 chi))))) ∨
      (((((Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0313 chi) ∨
      (Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0313 chi)) ∨
      ((Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0313 chi) ∨
      (¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0314 chi))) ∨
      (((¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0314 chi) ∨
      (¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0314 chi)) ∨
      ((¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0314 chi) ∨
      (Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0314 chi)))) ∨
      ((((Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0314 chi) ∨
      (Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0314 chi)) ∨
      ((Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0314 chi) ∨
      (¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0315 chi))) ∨
      (((¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0315 chi) ∨
      (¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0315 chi)) ∨
      ((¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0315 chi) ∨
      (Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0315 chi)))))) ∨
      ((((((Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0315 chi) ∨
      (Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0315 chi)) ∨
      ((Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0315 chi) ∨
      (¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0316 chi))) ∨
      (((¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0316 chi) ∨
      (¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0316 chi)) ∨
      ((¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0316 chi) ∨
      (Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0316 chi)))) ∨
      ((((Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0316 chi) ∨
      (Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0316 chi)) ∨
      ((Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0316 chi) ∨
      (¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0318 chi))) ∨
      (((¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0318 chi) ∨
      (¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0318 chi)) ∨
      ((¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0318 chi) ∨
      (Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0318 chi))))) ∨
      (((((Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0318 chi) ∨
      (Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0318 chi)) ∨
      ((Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0318 chi) ∨
      (¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0319 chi))) ∨
      (((¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0319 chi) ∨
      (¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0319 chi)) ∨
      ((¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0319 chi) ∨
      (Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0319 chi)))) ∨
      ((((Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0319 chi) ∨
      (Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0319 chi)) ∨
      ((Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0319 chi) ∨
      (¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0320 chi))) ∨
      (((¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0320 chi) ∨
      (¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0320 chi)) ∨
      ((¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0320 chi) ∨
      (Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0320 chi))))))) ∨
      ((((((Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0320 chi) ∨
      ((Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0320 chi) ∨
      (Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0320 chi))) ∨
      (((¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0321 chi) ∨
      (¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0321 chi)) ∨
      ((¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0321 chi) ∨
      (¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0321 chi)))) ∨
      ((((Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0321 chi) ∨
      (Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0321 chi)) ∨
      ((Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0321 chi) ∨
      (Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0321 chi))) ∨
      (((¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0322 chi) ∨
      (¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0322 chi)) ∨
      ((¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0322 chi) ∨
      (¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0322 chi))))) ∨
      (((((Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0322 chi) ∨
      (Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0322 chi)) ∨
      ((Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0322 chi) ∨
      (Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0322 chi))) ∨
      (((¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0323 chi) ∨
      (¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0323 chi)) ∨
      ((¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0323 chi) ∨
      (¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0323 chi)))) ∨
      ((((Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0323 chi) ∨
      (Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0323 chi)) ∨
      ((Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0323 chi) ∨
      (Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0323 chi))) ∨
      (((¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0324 chi) ∨
      (¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0324 chi)) ∨
      ((¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0324 chi) ∨
      (¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0324 chi)))))) ∨
      ((((((Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0324 chi) ∨
      (Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0324 chi)) ∨
      ((Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0324 chi) ∨
      (Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0324 chi))) ∨
      (((¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0325 chi) ∨
      (¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0325 chi)) ∨
      ((¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0325 chi) ∨
      (¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0325 chi)))) ∨
      ((((Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0325 chi) ∨
      (Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0325 chi)) ∨
      ((Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0325 chi) ∨
      (Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0325 chi))) ∨
      (((¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0326 chi) ∨
      (¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0326 chi)) ∨
      ((¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0326 chi) ∨
      (Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0326 chi))))) ∨
      (((((Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0326 chi) ∨
      (Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0326 chi)) ∨
      ((Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0326 chi) ∨
      (¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0327 chi))) ∨
      (((¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0327 chi) ∨
      (¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0327 chi)) ∨
      ((¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0327 chi) ∨
      (Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0327 chi)))) ∨
      ((((Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0327 chi) ∨
      (Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0327 chi)) ∨
      ((Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0327 chi) ∨
      (¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0328 chi))) ∨
      (((¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0328 chi) ∨
      (¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0328 chi)) ∨
      ((¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0328 chi) ∨
      (Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0328 chi)))))))) ∨
      (((((((Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0328 chi) ∨
      ((Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0328 chi) ∨
      (Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0328 chi))) ∨
      (((¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0329 chi) ∨
      (¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0329 chi)) ∨
      ((¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0329 chi) ∨
      (¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0329 chi)))) ∨
      ((((Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0329 chi) ∨
      (Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0329 chi)) ∨
      ((Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0329 chi) ∨
      (Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0329 chi))) ∨
      (((¬Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0330 chi) ∨
      (¬Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0330 chi)) ∨
      ((¬Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0330 chi) ∨
      (¬Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0330 chi))))) ∨
      (((((Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0330 chi) ∨
      (Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0330 chi)) ∨
      ((Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0330 chi) ∨
      (Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0330 chi))) ∨
      (((¬Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0331 chi) ∨
      (¬Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0331 chi)) ∨
      ((¬Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0331 chi) ∨
      (¬Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0331 chi)))) ∨
      ((((Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0331 chi) ∨
      (Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0331 chi)) ∨
      ((Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0331 chi) ∨
      (Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0331 chi))) ∨
      (((Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0332 chi) ∨
      (Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0332 chi)) ∨
      ((Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0332 chi) ∨
      (¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0333 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0333 chi) ∨
      (¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0333 chi)) ∨
      ((¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0333 chi) ∨
      (Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0333 chi))) ∨
      (((Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0333 chi) ∨
      (Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0333 chi)) ∨
      ((Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0333 chi) ∨
      (¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0334 chi)))) ∨
      ((((¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0334 chi) ∨
      (¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0334 chi)) ∨
      ((¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0334 chi) ∨
      (Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0334 chi))) ∨
      (((Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0334 chi) ∨
      (Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0334 chi)) ∨
      ((Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0334 chi) ∨
      (¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0335 chi))))) ∨
      (((((¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0335 chi) ∨
      (¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0335 chi)) ∨
      ((¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0335 chi) ∨
      (Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0335 chi))) ∨
      (((Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0335 chi) ∨
      (Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0335 chi)) ∨
      ((Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0335 chi) ∨
      (¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0336 chi)))) ∨
      ((((¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0336 chi) ∨
      (¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0336 chi)) ∨
      ((¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0336 chi) ∨
      (Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0336 chi))) ∨
      (((Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0336 chi) ∨
      (Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0336 chi)) ∨
      ((Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0336 chi) ∨
      (¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0337 chi))))))) ∨
      (((((((¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0337 chi) ∨
      (¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0337 chi)) ∨
      ((¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0337 chi) ∨
      (Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0337 chi))) ∨
      (((Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0337 chi) ∨
      (Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0337 chi)) ∨
      ((Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0337 chi) ∨
      (¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0338 chi)))) ∨
      ((((¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0338 chi) ∨
      (¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0338 chi)) ∨
      ((¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0338 chi) ∨
      (Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0338 chi))) ∨
      (((Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0338 chi) ∨
      (Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0338 chi)) ∨
      ((Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0338 chi) ∨
      (¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0339 chi))))) ∨
      (((((¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0339 chi) ∨
      (¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0339 chi)) ∨
      ((¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0339 chi) ∨
      (Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0339 chi))) ∨
      (((Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0339 chi) ∨
      (Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0339 chi)) ∨
      ((Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0339 chi) ∨
      (¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0340 chi)))) ∨
      ((((¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0340 chi) ∨
      (¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0340 chi)) ∨
      ((¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0340 chi) ∨
      (Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0340 chi))) ∨
      (((Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0340 chi) ∨
      (Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0340 chi)) ∨
      ((Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0340 chi) ∨
      (¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0341 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0341 chi) ∨
      (¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0341 chi)) ∨
      ((¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0341 chi) ∨
      (Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0341 chi))) ∨
      (((Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0341 chi) ∨
      (Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0341 chi)) ∨
      ((Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0341 chi) ∨
      (¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0342 chi)))) ∨
      ((((¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0342 chi) ∨
      (¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0342 chi)) ∨
      ((¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0342 chi) ∨
      (Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0342 chi))) ∨
      (((Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0342 chi) ∨
      (Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0342 chi)) ∨
      ((Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0342 chi) ∨
      (¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0343 chi))))) ∨
      (((((¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0343 chi) ∨
      (¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0343 chi)) ∨
      ((¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0343 chi) ∨
      (Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0343 chi))) ∨
      (((Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0343 chi) ∨
      (Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0343 chi)) ∨
      ((Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0343 chi) ∨
      (¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0344 chi)))) ∨
      ((((¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0344 chi) ∨
      (¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0344 chi)) ∨
      ((¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0344 chi) ∨
      (Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0344 chi))) ∨
      (((Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0344 chi) ∨
      (Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0344 chi)) ∨
      ((Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0344 chi) ∨
      (¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0345 chi)))))))))) := by
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
                exact fin15Anchored_clause03785 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03786 chi hone hbad
                ·
                  exact fin15Anchored_clause03787 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03788 chi hone hbad
                ·
                  exact fin15Anchored_clause03789 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03790 chi hone hbad
                ·
                  exact fin15Anchored_clause03791 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03792 chi hone hbad
                ·
                  exact fin15Anchored_clause03793 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03794 chi hone hbad
                ·
                  exact fin15Anchored_clause03795 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03796 chi hone hbad
                ·
                  exact fin15Anchored_clause03797 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03798 chi hone hbad
                ·
                  exact fin15Anchored_clause03799 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03800 chi hone hbad
                ·
                  exact fin15Anchored_clause03801 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03802 chi hone hbad
                ·
                  exact fin15Anchored_clause03803 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03804 chi hone hbad
                ·
                  exact fin15Anchored_clause03805 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03806 chi hone hbad
                ·
                  exact fin15Anchored_clause03807 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03808 chi hone hbad
                ·
                  exact fin15Anchored_clause03809 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03810 chi hone hbad
                ·
                  exact fin15Anchored_clause03811 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03812 chi hone hbad
                ·
                  exact fin15Anchored_clause03813 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03814 chi hone hbad
                ·
                  exact fin15Anchored_clause03815 chi hone hbad
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
                  exact fin15Anchored_clause03816 chi hone hbad
                ·
                  exact fin15Anchored_clause03817 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03818 chi hone hbad
                ·
                  exact fin15Anchored_clause03819 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03820 chi hone hbad
                ·
                  exact fin15Anchored_clause03821 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03822 chi hone hbad
                ·
                  exact fin15Anchored_clause03823 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03824 chi hone hbad
                ·
                  exact fin15Anchored_clause03825 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03826 chi hone hbad
                ·
                  exact fin15Anchored_clause03827 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03828 chi hone hbad
                ·
                  exact fin15Anchored_clause03829 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03830 chi hone hbad
                ·
                  exact fin15Anchored_clause03831 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03832 chi hone hbad
                ·
                  exact fin15Anchored_clause03833 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03834 chi hone hbad
                ·
                  exact fin15Anchored_clause03835 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03836 chi hone hbad
                ·
                  exact fin15Anchored_clause03837 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03838 chi hone hbad
                ·
                  exact fin15Anchored_clause03839 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03840 chi hone hbad
                ·
                  exact fin15Anchored_clause03841 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03842 chi hone hbad
                ·
                  exact fin15Anchored_clause03843 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03844 chi hone hbad
                ·
                  exact fin15Anchored_clause03845 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03846 chi hone hbad
                ·
                  exact fin15Anchored_clause03847 chi hone hbad
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
                exact fin15Anchored_clause03848 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03849 chi hone hbad
                ·
                  exact fin15Anchored_clause03850 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03851 chi hone hbad
                ·
                  exact fin15Anchored_clause03852 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03853 chi hone hbad
                ·
                  exact fin15Anchored_clause03854 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03855 chi hone hbad
                ·
                  exact fin15Anchored_clause03856 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03857 chi hone hbad
                ·
                  exact fin15Anchored_clause03858 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03859 chi hone hbad
                ·
                  exact fin15Anchored_clause03860 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03861 chi hone hbad
                ·
                  exact fin15Anchored_clause03862 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03863 chi hone hbad
                ·
                  exact fin15Anchored_clause03864 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03865 chi hone hbad
                ·
                  exact fin15Anchored_clause03866 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03867 chi hone hbad
                ·
                  exact fin15Anchored_clause03868 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03869 chi hone hbad
                ·
                  exact fin15Anchored_clause03870 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03871 chi hone hbad
                ·
                  exact fin15Anchored_clause03872 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03873 chi hone hbad
                ·
                  exact fin15Anchored_clause03874 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03875 chi hone hbad
                ·
                  exact fin15Anchored_clause03876 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03877 chi hone hbad
                ·
                  exact fin15Anchored_clause03878 chi hone hbad
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
                  exact fin15Anchored_clause03879 chi hone hbad
                ·
                  exact fin15Anchored_clause03880 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03881 chi hone hbad
                ·
                  exact fin15Anchored_clause03882 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03883 chi hone hbad
                ·
                  exact fin15Anchored_clause03884 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03885 chi hone hbad
                ·
                  exact fin15Anchored_clause03886 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03887 chi hone hbad
                ·
                  exact fin15Anchored_clause03888 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03889 chi hone hbad
                ·
                  exact fin15Anchored_clause03890 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03891 chi hone hbad
                ·
                  exact fin15Anchored_clause03892 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03893 chi hone hbad
                ·
                  exact fin15Anchored_clause03894 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03895 chi hone hbad
                ·
                  exact fin15Anchored_clause03896 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03897 chi hone hbad
                ·
                  exact fin15Anchored_clause03898 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03899 chi hone hbad
                ·
                  exact fin15Anchored_clause03900 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03901 chi hone hbad
                ·
                  exact fin15Anchored_clause03902 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03903 chi hone hbad
                ·
                  exact fin15Anchored_clause03904 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03905 chi hone hbad
                ·
                  exact fin15Anchored_clause03906 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03907 chi hone hbad
                ·
                  exact fin15Anchored_clause03908 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03909 chi hone hbad
                ·
                  exact fin15Anchored_clause03910 chi hone hbad
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
                exact fin15Anchored_clause03911 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03912 chi hone hbad
                ·
                  exact fin15Anchored_clause03913 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03914 chi hone hbad
                ·
                  exact fin15Anchored_clause03915 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03916 chi hone hbad
                ·
                  exact fin15Anchored_clause03917 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03918 chi hone hbad
                ·
                  exact fin15Anchored_clause03919 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03920 chi hone hbad
                ·
                  exact fin15Anchored_clause03921 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03922 chi hone hbad
                ·
                  exact fin15Anchored_clause03923 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03924 chi hone hbad
                ·
                  exact fin15Anchored_clause03925 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03926 chi hone hbad
                ·
                  exact fin15Anchored_clause03927 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03928 chi hone hbad
                ·
                  exact fin15Anchored_clause03929 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03930 chi hone hbad
                ·
                  exact fin15Anchored_clause03931 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03932 chi hone hbad
                ·
                  exact fin15Anchored_clause03933 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03934 chi hone hbad
                ·
                  exact fin15Anchored_clause03935 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03936 chi hone hbad
                ·
                  exact fin15Anchored_clause03937 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03938 chi hone hbad
                ·
                  exact fin15Anchored_clause03939 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03940 chi hone hbad
                ·
                  exact fin15Anchored_clause03941 chi hone hbad
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
                  exact fin15Anchored_clause03942 chi hone hbad
                ·
                  exact fin15Anchored_clause03943 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03944 chi hone hbad
                ·
                  exact fin15Anchored_clause03945 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03946 chi hone hbad
                ·
                  exact fin15Anchored_clause03947 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03948 chi hone hbad
                ·
                  exact fin15Anchored_clause03949 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03950 chi hone hbad
                ·
                  exact fin15Anchored_clause03951 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03952 chi hone hbad
                ·
                  exact fin15Anchored_clause03953 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03954 chi hone hbad
                ·
                  exact fin15Anchored_clause03955 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03956 chi hone hbad
                ·
                  exact fin15Anchored_clause03957 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03958 chi hone hbad
                ·
                  exact fin15Anchored_clause03959 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03960 chi hone hbad
                ·
                  exact fin15Anchored_clause03961 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03962 chi hone hbad
                ·
                  exact fin15Anchored_clause03963 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03964 chi hone hbad
                ·
                  exact fin15Anchored_clause03965 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03966 chi hone hbad
                ·
                  exact fin15Anchored_clause03967 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03968 chi hone hbad
                ·
                  exact fin15Anchored_clause03969 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03970 chi hone hbad
                ·
                  exact fin15Anchored_clause03971 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03972 chi hone hbad
                ·
                  exact fin15Anchored_clause03973 chi hone hbad
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
                  exact fin15Anchored_clause03974 chi hone hbad
                ·
                  exact fin15Anchored_clause03975 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03976 chi hone hbad
                ·
                  exact fin15Anchored_clause03977 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03978 chi hone hbad
                ·
                  exact fin15Anchored_clause03979 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03980 chi hone hbad
                ·
                  exact fin15Anchored_clause03981 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03982 chi hone hbad
                ·
                  exact fin15Anchored_clause03983 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03984 chi hone hbad
                ·
                  exact fin15Anchored_clause03985 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03986 chi hone hbad
                ·
                  exact fin15Anchored_clause03987 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03988 chi hone hbad
                ·
                  exact fin15Anchored_clause03989 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03990 chi hone hbad
                ·
                  exact fin15Anchored_clause03991 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03992 chi hone hbad
                ·
                  exact fin15Anchored_clause03993 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03994 chi hone hbad
                ·
                  exact fin15Anchored_clause03995 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03996 chi hone hbad
                ·
                  exact fin15Anchored_clause03997 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03998 chi hone hbad
                ·
                  exact fin15Anchored_clause03999 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04000 chi hone hbad
                ·
                  exact fin15Anchored_clause04001 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04002 chi hone hbad
                ·
                  exact fin15Anchored_clause04003 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04004 chi hone hbad
                ·
                  exact fin15Anchored_clause04005 chi hone hbad
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
                  exact fin15Anchored_clause04006 chi hone hbad
                ·
                  exact fin15Anchored_clause04007 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04008 chi hone hbad
                ·
                  exact fin15Anchored_clause04009 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04010 chi hone hbad
                ·
                  exact fin15Anchored_clause04011 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04012 chi hone hbad
                ·
                  exact fin15Anchored_clause04013 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04014 chi hone hbad
                ·
                  exact fin15Anchored_clause04015 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04016 chi hone hbad
                ·
                  exact fin15Anchored_clause04017 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04018 chi hone hbad
                ·
                  exact fin15Anchored_clause04019 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04020 chi hone hbad
                ·
                  exact fin15Anchored_clause04021 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04022 chi hone hbad
                ·
                  exact fin15Anchored_clause04023 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04024 chi hone hbad
                ·
                  exact fin15Anchored_clause04025 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04026 chi hone hbad
                ·
                  exact fin15Anchored_clause04027 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04028 chi hone hbad
                ·
                  exact fin15Anchored_clause04029 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04030 chi hone hbad
                ·
                  exact fin15Anchored_clause04031 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04032 chi hone hbad
                ·
                  exact fin15Anchored_clause04033 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04034 chi hone hbad
                ·
                  exact fin15Anchored_clause04035 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04036 chi hone hbad
                ·
                  exact fin15Anchored_clause04037 chi hone hbad

end ErdosSzekeres

end
