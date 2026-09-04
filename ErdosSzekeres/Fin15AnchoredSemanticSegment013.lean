module

public import ErdosSzekeres.Fin15AnchoredClauseChunk025
public import ErdosSzekeres.Fin15AnchoredClauseChunk026
public import ErdosSzekeres.Fin15AnchoredClauseChunk027

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 013. -/

theorem fin15Anchored_rejectSemanticSegment013
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0401 chi) ∨
      ((Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0401 chi) ∨
      (Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0401 chi))) ∨
      (((Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0401 chi) ∨
      (Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0401 chi)) ∨
      ((¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0403 chi) ∨
      (¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0403 chi)))) ∨
      ((((¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0403 chi) ∨
      (¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0403 chi)) ∨
      ((Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0403 chi) ∨
      (¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0404 chi))) ∨
      (((¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0404 chi) ∨
      (¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0219 chi ∧
      Fin15AnchoredAtom0404 chi)) ∨
      ((¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0404 chi) ∨
      (Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0219 chi ∧
      Fin15AnchoredAtom0404 chi))))) ∨
      (((((Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0404 chi) ∨
      (Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      Fin15AnchoredAtom0404 chi)) ∨
      ((Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0219 chi ∧
      Fin15AnchoredAtom0404 chi) ∨
      (¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0405 chi))) ∨
      (((¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0405 chi) ∨
      (¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0405 chi)) ∨
      ((Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0405 chi) ∨
      (¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0406 chi)))) ∨
      ((((¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0406 chi) ∨
      (¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0406 chi)) ∨
      ((¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0406 chi) ∨
      (Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0406 chi))) ∨
      (((Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0406 chi) ∨
      (Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0406 chi)) ∨
      ((Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0406 chi) ∨
      (¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0407 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0407 chi) ∨
      (¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0407 chi)) ∨
      ((¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0407 chi) ∨
      (Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0407 chi))) ∨
      (((Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0407 chi) ∨
      (Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0407 chi)) ∨
      ((Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0407 chi) ∨
      (¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0408 chi)))) ∨
      ((((¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0408 chi) ∨
      (¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0408 chi)) ∨
      ((¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0408 chi) ∨
      (Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0408 chi))) ∨
      (((Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0408 chi) ∨
      (Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0408 chi)) ∨
      ((Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0408 chi) ∨
      (¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0409 chi))))) ∨
      (((((¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0409 chi) ∨
      (¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0409 chi)) ∨
      ((¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0409 chi) ∨
      (Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0409 chi))) ∨
      (((Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0409 chi) ∨
      (Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0409 chi)) ∨
      ((Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0409 chi) ∨
      (¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0410 chi)))) ∨
      ((((¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0410 chi) ∨
      (¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0410 chi)) ∨
      ((¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0410 chi) ∨
      (Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0410 chi))) ∨
      (((Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0410 chi) ∨
      (Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0410 chi)) ∨
      ((Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0410 chi) ∨
      (¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0411 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0411 chi) ∨
      ((¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0411 chi) ∨
      (¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0411 chi))) ∨
      (((Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0411 chi) ∨
      (Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0411 chi)) ∨
      ((Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0411 chi) ∨
      (Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0411 chi)))) ∨
      ((((¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0412 chi) ∨
      (¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0412 chi)) ∨
      ((¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0412 chi) ∨
      (¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0412 chi))) ∨
      (((Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0412 chi) ∨
      (Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0412 chi)) ∨
      ((Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0412 chi) ∨
      (Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0412 chi))))) ∨
      (((((¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0413 chi) ∨
      (¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0413 chi)) ∨
      ((¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0413 chi) ∨
      (¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0413 chi))) ∨
      (((Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0413 chi) ∨
      (Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0413 chi)) ∨
      ((Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0413 chi) ∨
      (Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0413 chi)))) ∨
      ((((¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0414 chi) ∨
      (¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0414 chi)) ∨
      ((¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0414 chi) ∨
      (¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0414 chi))) ∨
      (((Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0414 chi) ∨
      (Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0414 chi)) ∨
      ((Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0414 chi) ∨
      (Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0414 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0415 chi) ∨
      (¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0415 chi)) ∨
      ((¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0415 chi) ∨
      (¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0415 chi))) ∨
      (((Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0415 chi) ∨
      (Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0415 chi)) ∨
      ((Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0415 chi) ∨
      (Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0415 chi)))) ∨
      ((((¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0416 chi) ∨
      (¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0416 chi)) ∨
      ((¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0416 chi) ∨
      (¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0416 chi))) ∨
      (((Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0416 chi) ∨
      (Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0416 chi)) ∨
      ((¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0417 chi) ∨
      (¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0417 chi))))) ∨
      (((((Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0417 chi) ∨
      (Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0417 chi)) ∨
      ((¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0418 chi) ∨
      (¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0418 chi))) ∨
      (((¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0418 chi) ∨
      (¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0418 chi)) ∨
      ((Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0418 chi) ∨
      (Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0418 chi)))) ∨
      ((((Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0418 chi) ∨
      (Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0418 chi)) ∨
      ((¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0419 chi) ∨
      (¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0419 chi))) ∨
      (((¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0419 chi) ∨
      (¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0419 chi)) ∨
      ((Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0419 chi) ∨
      (Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0419 chi)))))))) ∨
      (((((((Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0419 chi) ∨
      ((Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0419 chi) ∨
      (¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0420 chi))) ∨
      (((¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0420 chi) ∨
      (¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0420 chi)) ∨
      ((¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0420 chi) ∨
      (Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0420 chi)))) ∨
      ((((Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0420 chi) ∨
      (Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0420 chi)) ∨
      ((Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0420 chi) ∨
      (¬Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0421 chi))) ∨
      (((¬Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0421 chi) ∨
      (¬Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0421 chi)) ∨
      ((¬Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0421 chi) ∨
      (Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0421 chi))))) ∨
      (((((Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0421 chi) ∨
      (Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0421 chi)) ∨
      ((Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0421 chi) ∨
      (¬Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0423 chi))) ∨
      (((¬Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0423 chi) ∨
      (¬Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0423 chi)) ∨
      ((¬Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0423 chi) ∨
      (Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0423 chi)))) ∨
      ((((Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0423 chi) ∨
      (Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0423 chi)) ∨
      ((Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0423 chi) ∨
      (¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0427 chi))) ∨
      (((¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0427 chi) ∨
      (¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0427 chi)) ∨
      ((¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0427 chi) ∨
      (Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0427 chi)))))) ∨
      ((((((Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0427 chi) ∨
      (Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0427 chi)) ∨
      ((Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0427 chi) ∨
      (Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0428 chi))) ∨
      (((Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0219 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0428 chi) ∨
      (Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0219 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0428 chi)) ∨
      ((¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0429 chi) ∨
      (¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0429 chi)))) ∨
      ((((Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0429 chi) ∨
      (Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0429 chi)) ∨
      ((Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0429 chi) ∨
      (Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0429 chi))) ∨
      (((¬Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0433 chi) ∨
      (¬Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0433 chi)) ∨
      ((Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0433 chi) ∨
      (Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0219 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0433 chi))))) ∨
      (((((Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0433 chi) ∨
      (¬Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0434 chi)) ∨
      ((¬Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0434 chi) ∨
      (¬Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0434 chi))) ∨
      (((¬Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0434 chi) ∨
      (Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0434 chi)) ∨
      ((Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0434 chi) ∨
      (Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0434 chi)))) ∨
      ((((Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0434 chi) ∨
      (¬Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0435 chi)) ∨
      ((¬Fin15AnchoredAtom0219 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0435 chi) ∨
      (¬Fin15AnchoredAtom0219 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0435 chi))) ∨
      (((¬Fin15AnchoredAtom0219 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0435 chi) ∨
      (Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0435 chi)) ∨
      ((Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0435 chi) ∨
      (Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0435 chi))))))) ∨
      (((((((Fin15AnchoredAtom0219 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0435 chi) ∨
      (¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0436 chi)) ∨
      ((¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0436 chi) ∨
      (¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0436 chi))) ∨
      (((¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0436 chi) ∨
      (Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0436 chi)) ∨
      ((Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0436 chi) ∨
      (Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0436 chi)))) ∨
      ((((Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0436 chi) ∨
      (¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0437 chi)) ∨
      ((¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0437 chi) ∨
      (¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0437 chi))) ∨
      (((¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0437 chi) ∨
      (Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0437 chi)) ∨
      ((Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0437 chi) ∨
      (Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0437 chi))))) ∨
      (((((Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0437 chi) ∨
      (¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0438 chi)) ∨
      ((¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0438 chi) ∨
      (¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0438 chi))) ∨
      (((¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0438 chi) ∨
      (Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0438 chi)) ∨
      ((Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0438 chi) ∨
      (Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0438 chi)))) ∨
      ((((Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0438 chi) ∨
      (¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0439 chi)) ∨
      ((¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0439 chi) ∨
      (¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0439 chi))) ∨
      (((¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0439 chi) ∨
      (Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0439 chi)) ∨
      ((Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0439 chi) ∨
      (Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0439 chi)))))) ∨
      ((((((Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0439 chi) ∨
      (¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0440 chi)) ∨
      ((¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0440 chi) ∨
      (¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0440 chi))) ∨
      (((¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0440 chi) ∨
      (Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0440 chi)) ∨
      ((Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0440 chi) ∨
      (Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0440 chi)))) ∨
      ((((Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0440 chi) ∨
      (¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0441 chi)) ∨
      ((¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0441 chi) ∨
      (¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0441 chi))) ∨
      (((¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0441 chi) ∨
      (Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0441 chi)) ∨
      ((Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0441 chi) ∨
      (Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0441 chi))))) ∨
      (((((Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0441 chi) ∨
      (¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0442 chi)) ∨
      ((¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0442 chi) ∨
      (¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0442 chi))) ∨
      (((¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0442 chi) ∨
      (Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0442 chi)) ∨
      ((Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0442 chi) ∨
      (Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0442 chi)))) ∨
      ((((Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0442 chi) ∨
      (¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0443 chi)) ∨
      ((¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0443 chi) ∨
      (¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0443 chi))) ∨
      (((¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0443 chi) ∨
      (Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0443 chi)) ∨
      ((Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0443 chi) ∨
      (Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0443 chi)))))))))) := by
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
                exact fin15Anchored_clause03280 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03281 chi hone hbad
                ·
                  exact fin15Anchored_clause03282 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03283 chi hone hbad
                ·
                  exact fin15Anchored_clause03284 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03285 chi hone hbad
                ·
                  exact fin15Anchored_clause03286 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03287 chi hone hbad
                ·
                  exact fin15Anchored_clause03288 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03289 chi hone hbad
                ·
                  exact fin15Anchored_clause03290 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03291 chi hone hbad
                ·
                  exact fin15Anchored_clause03292 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03293 chi hone hbad
                ·
                  exact fin15Anchored_clause03294 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03295 chi hone hbad
                ·
                  exact fin15Anchored_clause03296 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03297 chi hone hbad
                ·
                  exact fin15Anchored_clause03298 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03299 chi hone hbad
                ·
                  exact fin15Anchored_clause03300 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03301 chi hone hbad
                ·
                  exact fin15Anchored_clause03302 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03303 chi hone hbad
                ·
                  exact fin15Anchored_clause03304 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03305 chi hone hbad
                ·
                  exact fin15Anchored_clause03306 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03307 chi hone hbad
                ·
                  exact fin15Anchored_clause03308 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03309 chi hone hbad
                ·
                  exact fin15Anchored_clause03310 chi hone hbad
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
                  exact fin15Anchored_clause03311 chi hone hbad
                ·
                  exact fin15Anchored_clause03312 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03313 chi hone hbad
                ·
                  exact fin15Anchored_clause03314 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03315 chi hone hbad
                ·
                  exact fin15Anchored_clause03316 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03317 chi hone hbad
                ·
                  exact fin15Anchored_clause03318 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03319 chi hone hbad
                ·
                  exact fin15Anchored_clause03320 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03321 chi hone hbad
                ·
                  exact fin15Anchored_clause03322 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03323 chi hone hbad
                ·
                  exact fin15Anchored_clause03324 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03325 chi hone hbad
                ·
                  exact fin15Anchored_clause03326 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03327 chi hone hbad
                ·
                  exact fin15Anchored_clause03328 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03329 chi hone hbad
                ·
                  exact fin15Anchored_clause03330 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03331 chi hone hbad
                ·
                  exact fin15Anchored_clause03332 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03333 chi hone hbad
                ·
                  exact fin15Anchored_clause03334 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03335 chi hone hbad
                ·
                  exact fin15Anchored_clause03336 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03337 chi hone hbad
                ·
                  exact fin15Anchored_clause03338 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03339 chi hone hbad
                ·
                  exact fin15Anchored_clause03340 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03341 chi hone hbad
                ·
                  exact fin15Anchored_clause03342 chi hone hbad
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
                exact fin15Anchored_clause03343 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03344 chi hone hbad
                ·
                  exact fin15Anchored_clause03345 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03346 chi hone hbad
                ·
                  exact fin15Anchored_clause03347 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03348 chi hone hbad
                ·
                  exact fin15Anchored_clause03349 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03350 chi hone hbad
                ·
                  exact fin15Anchored_clause03351 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03352 chi hone hbad
                ·
                  exact fin15Anchored_clause03353 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03354 chi hone hbad
                ·
                  exact fin15Anchored_clause03355 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03356 chi hone hbad
                ·
                  exact fin15Anchored_clause03357 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03358 chi hone hbad
                ·
                  exact fin15Anchored_clause03359 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03360 chi hone hbad
                ·
                  exact fin15Anchored_clause03361 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03362 chi hone hbad
                ·
                  exact fin15Anchored_clause03363 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03364 chi hone hbad
                ·
                  exact fin15Anchored_clause03365 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03366 chi hone hbad
                ·
                  exact fin15Anchored_clause03367 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03368 chi hone hbad
                ·
                  exact fin15Anchored_clause03369 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03370 chi hone hbad
                ·
                  exact fin15Anchored_clause03371 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03372 chi hone hbad
                ·
                  exact fin15Anchored_clause03373 chi hone hbad
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
                  exact fin15Anchored_clause03374 chi hone hbad
                ·
                  exact fin15Anchored_clause03375 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03376 chi hone hbad
                ·
                  exact fin15Anchored_clause03377 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03378 chi hone hbad
                ·
                  exact fin15Anchored_clause03379 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03380 chi hone hbad
                ·
                  exact fin15Anchored_clause03381 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03382 chi hone hbad
                ·
                  exact fin15Anchored_clause03383 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03384 chi hone hbad
                ·
                  exact fin15Anchored_clause03385 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03386 chi hone hbad
                ·
                  exact fin15Anchored_clause03387 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03388 chi hone hbad
                ·
                  exact fin15Anchored_clause03389 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03390 chi hone hbad
                ·
                  exact fin15Anchored_clause03391 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03392 chi hone hbad
                ·
                  exact fin15Anchored_clause03393 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03394 chi hone hbad
                ·
                  exact fin15Anchored_clause03395 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03396 chi hone hbad
                ·
                  exact fin15Anchored_clause03397 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03398 chi hone hbad
                ·
                  exact fin15Anchored_clause03399 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03400 chi hone hbad
                ·
                  exact fin15Anchored_clause03401 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03402 chi hone hbad
                ·
                  exact fin15Anchored_clause03403 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03404 chi hone hbad
                ·
                  exact fin15Anchored_clause03405 chi hone hbad
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
                exact fin15Anchored_clause03406 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03407 chi hone hbad
                ·
                  exact fin15Anchored_clause03408 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03409 chi hone hbad
                ·
                  exact fin15Anchored_clause03410 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03411 chi hone hbad
                ·
                  exact fin15Anchored_clause03412 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03413 chi hone hbad
                ·
                  exact fin15Anchored_clause03414 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03415 chi hone hbad
                ·
                  exact fin15Anchored_clause03416 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03417 chi hone hbad
                ·
                  exact fin15Anchored_clause03418 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03419 chi hone hbad
                ·
                  exact fin15Anchored_clause03420 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03421 chi hone hbad
                ·
                  exact fin15Anchored_clause03422 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03423 chi hone hbad
                ·
                  exact fin15Anchored_clause03424 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03425 chi hone hbad
                ·
                  exact fin15Anchored_clause03426 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03427 chi hone hbad
                ·
                  exact fin15Anchored_clause03428 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03429 chi hone hbad
                ·
                  exact fin15Anchored_clause03430 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03431 chi hone hbad
                ·
                  exact fin15Anchored_clause03432 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03433 chi hone hbad
                ·
                  exact fin15Anchored_clause03434 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03435 chi hone hbad
                ·
                  exact fin15Anchored_clause03436 chi hone hbad
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
                  exact fin15Anchored_clause03437 chi hone hbad
                ·
                  exact fin15Anchored_clause03438 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03439 chi hone hbad
                ·
                  exact fin15Anchored_clause03440 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03441 chi hone hbad
                ·
                  exact fin15Anchored_clause03442 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03443 chi hone hbad
                ·
                  exact fin15Anchored_clause03444 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03445 chi hone hbad
                ·
                  exact fin15Anchored_clause03446 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03447 chi hone hbad
                ·
                  exact fin15Anchored_clause03448 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03449 chi hone hbad
                ·
                  exact fin15Anchored_clause03450 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03451 chi hone hbad
                ·
                  exact fin15Anchored_clause03452 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03453 chi hone hbad
                ·
                  exact fin15Anchored_clause03454 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03455 chi hone hbad
                ·
                  exact fin15Anchored_clause03456 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03457 chi hone hbad
                ·
                  exact fin15Anchored_clause03458 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03459 chi hone hbad
                ·
                  exact fin15Anchored_clause03460 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03461 chi hone hbad
                ·
                  exact fin15Anchored_clause03462 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03463 chi hone hbad
                ·
                  exact fin15Anchored_clause03464 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03465 chi hone hbad
                ·
                  exact fin15Anchored_clause03466 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03467 chi hone hbad
                ·
                  exact fin15Anchored_clause03468 chi hone hbad
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
                  exact fin15Anchored_clause03469 chi hone hbad
                ·
                  exact fin15Anchored_clause03470 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03471 chi hone hbad
                ·
                  exact fin15Anchored_clause03472 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03473 chi hone hbad
                ·
                  exact fin15Anchored_clause03474 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03475 chi hone hbad
                ·
                  exact fin15Anchored_clause03476 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03477 chi hone hbad
                ·
                  exact fin15Anchored_clause03478 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03479 chi hone hbad
                ·
                  exact fin15Anchored_clause03480 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03481 chi hone hbad
                ·
                  exact fin15Anchored_clause03482 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03483 chi hone hbad
                ·
                  exact fin15Anchored_clause03484 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03485 chi hone hbad
                ·
                  exact fin15Anchored_clause03486 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03487 chi hone hbad
                ·
                  exact fin15Anchored_clause03488 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03489 chi hone hbad
                ·
                  exact fin15Anchored_clause03490 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03491 chi hone hbad
                ·
                  exact fin15Anchored_clause03492 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03493 chi hone hbad
                ·
                  exact fin15Anchored_clause03494 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03495 chi hone hbad
                ·
                  exact fin15Anchored_clause03496 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03497 chi hone hbad
                ·
                  exact fin15Anchored_clause03498 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03499 chi hone hbad
                ·
                  exact fin15Anchored_clause03500 chi hone hbad
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
                  exact fin15Anchored_clause03501 chi hone hbad
                ·
                  exact fin15Anchored_clause03502 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03503 chi hone hbad
                ·
                  exact fin15Anchored_clause03504 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03505 chi hone hbad
                ·
                  exact fin15Anchored_clause03506 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03507 chi hone hbad
                ·
                  exact fin15Anchored_clause03508 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03509 chi hone hbad
                ·
                  exact fin15Anchored_clause03510 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03511 chi hone hbad
                ·
                  exact fin15Anchored_clause03512 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03513 chi hone hbad
                ·
                  exact fin15Anchored_clause03514 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03515 chi hone hbad
                ·
                  exact fin15Anchored_clause03516 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03517 chi hone hbad
                ·
                  exact fin15Anchored_clause03518 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03519 chi hone hbad
                ·
                  exact fin15Anchored_clause03520 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03521 chi hone hbad
                ·
                  exact fin15Anchored_clause03522 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03523 chi hone hbad
                ·
                  exact fin15Anchored_clause03524 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03525 chi hone hbad
                ·
                  exact fin15Anchored_clause03526 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03527 chi hone hbad
                ·
                  exact fin15Anchored_clause03528 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03529 chi hone hbad
                ·
                  exact fin15Anchored_clause03530 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03531 chi hone hbad
                ·
                  exact fin15Anchored_clause03532 chi hone hbad

end ErdosSzekeres

end
