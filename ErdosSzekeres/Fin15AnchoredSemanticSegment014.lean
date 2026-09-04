module

public import ErdosSzekeres.Fin15AnchoredClauseChunk027
public import ErdosSzekeres.Fin15AnchoredClauseChunk028
public import ErdosSzekeres.Fin15AnchoredClauseChunk029

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 014. -/

theorem fin15Anchored_rejectSemanticSegment014
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0443 chi) ∨
      ((¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0444 chi) ∨
      (¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0444 chi))) ∨
      (((¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0444 chi) ∨
      (¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0444 chi)) ∨
      ((Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0444 chi) ∨
      (Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0444 chi)))) ∨
      ((((Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0444 chi) ∨
      (Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0444 chi)) ∨
      ((¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0445 chi) ∨
      (¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0445 chi))) ∨
      (((¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0445 chi) ∨
      (¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0445 chi)) ∨
      ((Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0445 chi) ∨
      (Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0445 chi))))) ∨
      (((((Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0445 chi) ∨
      (Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0445 chi)) ∨
      ((¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0446 chi) ∨
      (¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0446 chi))) ∨
      (((¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0446 chi) ∨
      (¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0446 chi)) ∨
      ((Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0446 chi) ∨
      (Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0446 chi)))) ∨
      ((((Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0446 chi) ∨
      (¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0447 chi)) ∨
      ((¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0447 chi) ∨
      (¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0447 chi))) ∨
      (((¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0447 chi) ∨
      (Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0447 chi)) ∨
      ((Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0447 chi) ∨
      (Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0447 chi)))))) ∨
      ((((((Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0447 chi) ∨
      (¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0448 chi)) ∨
      ((¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0448 chi) ∨
      (Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0448 chi))) ∨
      (((¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0449 chi) ∨
      (¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0449 chi)) ∨
      ((¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0449 chi) ∨
      (¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0449 chi)))) ∨
      ((((Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0449 chi) ∨
      (Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0449 chi)) ∨
      ((Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0449 chi) ∨
      (Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0449 chi))) ∨
      (((¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0450 chi) ∨
      (¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0450 chi)) ∨
      ((¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0450 chi) ∨
      (¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0450 chi))))) ∨
      (((((Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0450 chi) ∨
      (Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0450 chi)) ∨
      ((Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0450 chi) ∨
      (Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0450 chi))) ∨
      (((¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0451 chi) ∨
      (¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0451 chi)) ∨
      ((¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0451 chi) ∨
      (¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0451 chi)))) ∨
      ((((Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0451 chi) ∨
      (Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0451 chi)) ∨
      ((Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0451 chi) ∨
      (Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0451 chi))) ∨
      (((¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0452 chi) ∨
      (¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0452 chi)) ∨
      ((¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0452 chi) ∨
      (¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0452 chi))))))) ∨
      ((((((Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0452 chi) ∨
      ((Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0452 chi) ∨
      (Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0452 chi))) ∨
      (((Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0452 chi) ∨
      (¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0453 chi)) ∨
      ((¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0453 chi) ∨
      (¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0453 chi)))) ∨
      ((((¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0453 chi) ∨
      (Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0453 chi)) ∨
      ((Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0453 chi) ∨
      (Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0453 chi))) ∨
      (((Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0453 chi) ∨
      (¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0454 chi)) ∨
      ((Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0454 chi) ∨
      (Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0454 chi))))) ∨
      (((((Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0454 chi) ∨
      (Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0454 chi)) ∨
      ((¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0455 chi) ∨
      (¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0455 chi))) ∨
      (((¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0455 chi) ∨
      (¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0455 chi)) ∨
      ((Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0455 chi) ∨
      (Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0455 chi)))) ∨
      ((((Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0455 chi) ∨
      (Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0455 chi)) ∨
      ((¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0291 chi) ∨
      (¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0291 chi))) ∨
      (((¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0291 chi) ∨
      (¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0291 chi)) ∨
      ((Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0291 chi) ∨
      (Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0291 chi)))))) ∨
      ((((((Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0291 chi) ∨
      (Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0291 chi)) ∨
      ((¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0292 chi) ∨
      (¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0292 chi))) ∨
      (((¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0292 chi) ∨
      (¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0292 chi)) ∨
      ((Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0292 chi) ∨
      (Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0292 chi)))) ∨
      ((((Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0292 chi) ∨
      (Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0292 chi)) ∨
      ((¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0293 chi) ∨
      (¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0293 chi))) ∨
      (((¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0293 chi) ∨
      (¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0293 chi)) ∨
      ((Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0293 chi) ∨
      (Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0293 chi))))) ∨
      (((((Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0293 chi) ∨
      (Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0293 chi)) ∨
      ((¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0294 chi) ∨
      (¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0294 chi))) ∨
      (((¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0294 chi) ∨
      (¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0294 chi)) ∨
      ((Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0294 chi) ∨
      (Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0294 chi)))) ∨
      ((((Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0294 chi) ∨
      (Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0294 chi)) ∨
      ((¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0295 chi) ∨
      (¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0295 chi))) ∨
      (((¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0295 chi) ∨
      (¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0295 chi)) ∨
      ((Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0295 chi) ∨
      (Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0295 chi)))))))) ∨
      (((((((Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0295 chi) ∨
      ((Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0295 chi) ∨
      (¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0296 chi))) ∨
      (((¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0296 chi) ∨
      (¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0296 chi)) ∨
      ((¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0296 chi) ∨
      (Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0296 chi)))) ∨
      ((((Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0296 chi) ∨
      (Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0296 chi)) ∨
      ((¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0297 chi) ∨
      (¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0297 chi))) ∨
      (((¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0297 chi) ∨
      (¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0297 chi)) ∨
      ((Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0297 chi) ∨
      (Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0297 chi))))) ∨
      (((((Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0297 chi) ∨
      (Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0297 chi)) ∨
      ((¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0298 chi) ∨
      (¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0298 chi))) ∨
      (((¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0298 chi) ∨
      (¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0298 chi)) ∨
      ((Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0298 chi) ∨
      (Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0298 chi)))) ∨
      ((((Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0298 chi) ∨
      (Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0298 chi)) ∨
      ((¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0299 chi) ∨
      (¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0299 chi))) ∨
      (((¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0299 chi) ∨
      (¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0299 chi)) ∨
      ((Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0299 chi) ∨
      (Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0299 chi)))))) ∨
      ((((((Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0299 chi) ∨
      (Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0299 chi)) ∨
      ((¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0300 chi) ∨
      (¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0300 chi))) ∨
      (((¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0300 chi) ∨
      (¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0300 chi)) ∨
      ((Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0300 chi) ∨
      (Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0300 chi)))) ∨
      ((((Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0300 chi) ∨
      (Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0300 chi)) ∨
      ((¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0301 chi) ∨
      (¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0301 chi))) ∨
      (((¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0301 chi) ∨
      (¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0301 chi)) ∨
      ((Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0301 chi) ∨
      (Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0301 chi))))) ∨
      (((((Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0301 chi) ∨
      (Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0301 chi)) ∨
      ((¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0302 chi) ∨
      (¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0302 chi))) ∨
      (((¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0302 chi) ∨
      (¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0302 chi)) ∨
      ((Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0302 chi) ∨
      (Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0302 chi)))) ∨
      ((((Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0302 chi) ∨
      (Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0302 chi)) ∨
      ((¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0303 chi) ∨
      (¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0303 chi))) ∨
      (((¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0303 chi) ∨
      (¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0303 chi)) ∨
      ((Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0303 chi) ∨
      (Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0303 chi))))))) ∨
      ((((((Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0303 chi) ∨
      ((Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0303 chi) ∨
      (¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0304 chi))) ∨
      (((¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0304 chi) ∨
      (¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0304 chi)) ∨
      ((¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0304 chi) ∨
      (Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0304 chi)))) ∨
      ((((Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0304 chi) ∨
      (Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0304 chi)) ∨
      ((¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0305 chi) ∨
      (¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0305 chi))) ∨
      (((¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0305 chi) ∨
      (¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0305 chi)) ∨
      ((Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0305 chi) ∨
      (Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0305 chi))))) ∨
      (((((Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0305 chi) ∨
      (Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0305 chi)) ∨
      ((¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0306 chi) ∨
      (¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0306 chi))) ∨
      (((¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0306 chi) ∨
      (¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0306 chi)) ∨
      ((Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0306 chi) ∨
      (Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0306 chi)))) ∨
      ((((Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0306 chi) ∨
      (Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0306 chi)) ∨
      ((¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0307 chi) ∨
      (¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0307 chi))) ∨
      (((¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0307 chi) ∨
      (¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0307 chi)) ∨
      ((Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0307 chi) ∨
      (Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0307 chi)))))) ∨
      ((((((Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0307 chi) ∨
      (Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0307 chi)) ∨
      ((¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0308 chi) ∨
      (¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0308 chi))) ∨
      (((¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0308 chi) ∨
      (¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0308 chi)) ∨
      ((Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0308 chi) ∨
      (Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0308 chi)))) ∨
      ((((Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0308 chi) ∨
      (Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0308 chi)) ∨
      ((¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0309 chi) ∨
      (¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0309 chi))) ∨
      (((¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0309 chi) ∨
      (¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0309 chi)) ∨
      ((Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0309 chi) ∨
      (Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0309 chi))))) ∨
      (((((Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0309 chi) ∨
      (Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0309 chi)) ∨
      ((¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0310 chi) ∨
      (¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0310 chi))) ∨
      (((¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0310 chi) ∨
      (¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0310 chi)) ∨
      ((Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0310 chi) ∨
      (Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0310 chi)))) ∨
      ((((Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0310 chi) ∨
      (Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0310 chi)) ∨
      ((¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0311 chi) ∨
      (¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0311 chi))) ∨
      (((¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0311 chi) ∨
      (¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0311 chi)) ∨
      ((Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0311 chi) ∨
      (Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0311 chi)))))))))) := by
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
                exact fin15Anchored_clause03533 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03534 chi hone hbad
                ·
                  exact fin15Anchored_clause03535 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03536 chi hone hbad
                ·
                  exact fin15Anchored_clause03537 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03538 chi hone hbad
                ·
                  exact fin15Anchored_clause03539 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03540 chi hone hbad
                ·
                  exact fin15Anchored_clause03541 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03542 chi hone hbad
                ·
                  exact fin15Anchored_clause03543 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03544 chi hone hbad
                ·
                  exact fin15Anchored_clause03545 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03546 chi hone hbad
                ·
                  exact fin15Anchored_clause03547 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03548 chi hone hbad
                ·
                  exact fin15Anchored_clause03549 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03550 chi hone hbad
                ·
                  exact fin15Anchored_clause03551 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03552 chi hone hbad
                ·
                  exact fin15Anchored_clause03553 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03554 chi hone hbad
                ·
                  exact fin15Anchored_clause03555 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03556 chi hone hbad
                ·
                  exact fin15Anchored_clause03557 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03558 chi hone hbad
                ·
                  exact fin15Anchored_clause03559 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03560 chi hone hbad
                ·
                  exact fin15Anchored_clause03561 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03562 chi hone hbad
                ·
                  exact fin15Anchored_clause03563 chi hone hbad
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
                  exact fin15Anchored_clause03564 chi hone hbad
                ·
                  exact fin15Anchored_clause03565 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03566 chi hone hbad
                ·
                  exact fin15Anchored_clause03567 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03568 chi hone hbad
                ·
                  exact fin15Anchored_clause03569 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03570 chi hone hbad
                ·
                  exact fin15Anchored_clause03571 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03572 chi hone hbad
                ·
                  exact fin15Anchored_clause03573 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03574 chi hone hbad
                ·
                  exact fin15Anchored_clause03575 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03576 chi hone hbad
                ·
                  exact fin15Anchored_clause03577 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03578 chi hone hbad
                ·
                  exact fin15Anchored_clause03579 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03580 chi hone hbad
                ·
                  exact fin15Anchored_clause03581 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03582 chi hone hbad
                ·
                  exact fin15Anchored_clause03583 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03584 chi hone hbad
                ·
                  exact fin15Anchored_clause03585 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03586 chi hone hbad
                ·
                  exact fin15Anchored_clause03587 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03588 chi hone hbad
                ·
                  exact fin15Anchored_clause03589 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03590 chi hone hbad
                ·
                  exact fin15Anchored_clause03591 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03592 chi hone hbad
                ·
                  exact fin15Anchored_clause03593 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03594 chi hone hbad
                ·
                  exact fin15Anchored_clause03595 chi hone hbad
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
                exact fin15Anchored_clause03596 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03597 chi hone hbad
                ·
                  exact fin15Anchored_clause03598 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03599 chi hone hbad
                ·
                  exact fin15Anchored_clause03600 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03601 chi hone hbad
                ·
                  exact fin15Anchored_clause03602 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03603 chi hone hbad
                ·
                  exact fin15Anchored_clause03604 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03605 chi hone hbad
                ·
                  exact fin15Anchored_clause03606 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03607 chi hone hbad
                ·
                  exact fin15Anchored_clause03608 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03609 chi hone hbad
                ·
                  exact fin15Anchored_clause03610 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03611 chi hone hbad
                ·
                  exact fin15Anchored_clause03612 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03613 chi hone hbad
                ·
                  exact fin15Anchored_clause03614 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03615 chi hone hbad
                ·
                  exact fin15Anchored_clause03616 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03617 chi hone hbad
                ·
                  exact fin15Anchored_clause03618 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03619 chi hone hbad
                ·
                  exact fin15Anchored_clause03620 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03621 chi hone hbad
                ·
                  exact fin15Anchored_clause03622 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03623 chi hone hbad
                ·
                  exact fin15Anchored_clause03624 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03625 chi hone hbad
                ·
                  exact fin15Anchored_clause03626 chi hone hbad
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
                  exact fin15Anchored_clause03627 chi hone hbad
                ·
                  exact fin15Anchored_clause03628 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03629 chi hone hbad
                ·
                  exact fin15Anchored_clause03630 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03631 chi hone hbad
                ·
                  exact fin15Anchored_clause03632 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03633 chi hone hbad
                ·
                  exact fin15Anchored_clause03634 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03635 chi hone hbad
                ·
                  exact fin15Anchored_clause03636 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03637 chi hone hbad
                ·
                  exact fin15Anchored_clause03638 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03639 chi hone hbad
                ·
                  exact fin15Anchored_clause03640 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03641 chi hone hbad
                ·
                  exact fin15Anchored_clause03642 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03643 chi hone hbad
                ·
                  exact fin15Anchored_clause03644 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03645 chi hone hbad
                ·
                  exact fin15Anchored_clause03646 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03647 chi hone hbad
                ·
                  exact fin15Anchored_clause03648 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03649 chi hone hbad
                ·
                  exact fin15Anchored_clause03650 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03651 chi hone hbad
                ·
                  exact fin15Anchored_clause03652 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03653 chi hone hbad
                ·
                  exact fin15Anchored_clause03654 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03655 chi hone hbad
                ·
                  exact fin15Anchored_clause03656 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03657 chi hone hbad
                ·
                  exact fin15Anchored_clause03658 chi hone hbad
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
                exact fin15Anchored_clause03659 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03660 chi hone hbad
                ·
                  exact fin15Anchored_clause03661 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03662 chi hone hbad
                ·
                  exact fin15Anchored_clause03663 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03664 chi hone hbad
                ·
                  exact fin15Anchored_clause03665 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03666 chi hone hbad
                ·
                  exact fin15Anchored_clause03667 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03668 chi hone hbad
                ·
                  exact fin15Anchored_clause03669 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03670 chi hone hbad
                ·
                  exact fin15Anchored_clause03671 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03672 chi hone hbad
                ·
                  exact fin15Anchored_clause03673 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03674 chi hone hbad
                ·
                  exact fin15Anchored_clause03675 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03676 chi hone hbad
                ·
                  exact fin15Anchored_clause03677 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03678 chi hone hbad
                ·
                  exact fin15Anchored_clause03679 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03680 chi hone hbad
                ·
                  exact fin15Anchored_clause03681 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03682 chi hone hbad
                ·
                  exact fin15Anchored_clause03683 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03684 chi hone hbad
                ·
                  exact fin15Anchored_clause03685 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03686 chi hone hbad
                ·
                  exact fin15Anchored_clause03687 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03688 chi hone hbad
                ·
                  exact fin15Anchored_clause03689 chi hone hbad
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
                  exact fin15Anchored_clause03690 chi hone hbad
                ·
                  exact fin15Anchored_clause03691 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03692 chi hone hbad
                ·
                  exact fin15Anchored_clause03693 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03694 chi hone hbad
                ·
                  exact fin15Anchored_clause03695 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03696 chi hone hbad
                ·
                  exact fin15Anchored_clause03697 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03698 chi hone hbad
                ·
                  exact fin15Anchored_clause03699 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03700 chi hone hbad
                ·
                  exact fin15Anchored_clause03701 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03702 chi hone hbad
                ·
                  exact fin15Anchored_clause03703 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03704 chi hone hbad
                ·
                  exact fin15Anchored_clause03705 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03706 chi hone hbad
                ·
                  exact fin15Anchored_clause03707 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03708 chi hone hbad
                ·
                  exact fin15Anchored_clause03709 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03710 chi hone hbad
                ·
                  exact fin15Anchored_clause03711 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03712 chi hone hbad
                ·
                  exact fin15Anchored_clause03713 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03714 chi hone hbad
                ·
                  exact fin15Anchored_clause03715 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03716 chi hone hbad
                ·
                  exact fin15Anchored_clause03717 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03718 chi hone hbad
                ·
                  exact fin15Anchored_clause03719 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03720 chi hone hbad
                ·
                  exact fin15Anchored_clause03721 chi hone hbad
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
                exact fin15Anchored_clause03722 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03723 chi hone hbad
                ·
                  exact fin15Anchored_clause03724 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03725 chi hone hbad
                ·
                  exact fin15Anchored_clause03726 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03727 chi hone hbad
                ·
                  exact fin15Anchored_clause03728 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03729 chi hone hbad
                ·
                  exact fin15Anchored_clause03730 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03731 chi hone hbad
                ·
                  exact fin15Anchored_clause03732 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03733 chi hone hbad
                ·
                  exact fin15Anchored_clause03734 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03735 chi hone hbad
                ·
                  exact fin15Anchored_clause03736 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03737 chi hone hbad
                ·
                  exact fin15Anchored_clause03738 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03739 chi hone hbad
                ·
                  exact fin15Anchored_clause03740 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03741 chi hone hbad
                ·
                  exact fin15Anchored_clause03742 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03743 chi hone hbad
                ·
                  exact fin15Anchored_clause03744 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03745 chi hone hbad
                ·
                  exact fin15Anchored_clause03746 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03747 chi hone hbad
                ·
                  exact fin15Anchored_clause03748 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03749 chi hone hbad
                ·
                  exact fin15Anchored_clause03750 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03751 chi hone hbad
                ·
                  exact fin15Anchored_clause03752 chi hone hbad
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
                  exact fin15Anchored_clause03753 chi hone hbad
                ·
                  exact fin15Anchored_clause03754 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03755 chi hone hbad
                ·
                  exact fin15Anchored_clause03756 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03757 chi hone hbad
                ·
                  exact fin15Anchored_clause03758 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03759 chi hone hbad
                ·
                  exact fin15Anchored_clause03760 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03761 chi hone hbad
                ·
                  exact fin15Anchored_clause03762 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03763 chi hone hbad
                ·
                  exact fin15Anchored_clause03764 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03765 chi hone hbad
                ·
                  exact fin15Anchored_clause03766 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03767 chi hone hbad
                ·
                  exact fin15Anchored_clause03768 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03769 chi hone hbad
                ·
                  exact fin15Anchored_clause03770 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03771 chi hone hbad
                ·
                  exact fin15Anchored_clause03772 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03773 chi hone hbad
                ·
                  exact fin15Anchored_clause03774 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03775 chi hone hbad
                ·
                  exact fin15Anchored_clause03776 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03777 chi hone hbad
                ·
                  exact fin15Anchored_clause03778 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03779 chi hone hbad
                ·
                  exact fin15Anchored_clause03780 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03781 chi hone hbad
                ·
                  exact fin15Anchored_clause03782 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03783 chi hone hbad
                ·
                  exact fin15Anchored_clause03784 chi hone hbad

end ErdosSzekeres

end
