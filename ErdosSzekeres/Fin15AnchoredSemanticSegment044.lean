module

public import ErdosSzekeres.Fin15AnchoredClauseChunk086
public import ErdosSzekeres.Fin15AnchoredClauseChunk087
public import ErdosSzekeres.Fin15AnchoredClauseChunk088

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 044. -/

theorem fin15Anchored_rejectSemanticSegment044
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1268 chi) ∨
      ((Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1268 chi) ∨
      (Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom1268 chi))) ∨
      (((Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1268 chi) ∨
      (Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1268 chi)) ∨
      ((Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom1268 chi) ∨
      (¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom1269 chi)))) ∨
      ((((¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1269 chi) ∨
      (¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom1269 chi)) ∨
      ((¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1269 chi) ∨
      (Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1269 chi))) ∨
      (((Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1269 chi) ∨
      (Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom1269 chi)) ∨
      ((Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1269 chi) ∨
      (Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1269 chi))))) ∨
      (((((Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom1269 chi) ∨
      (¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1270 chi)) ∨
      ((¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1270 chi) ∨
      (Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1270 chi))) ∨
      (((¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1271 chi) ∨
      (¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1271 chi)) ∨
      ((¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1271 chi) ∨
      (¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1271 chi)))) ∨
      ((((Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1271 chi) ∨
      (Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1271 chi)) ∨
      ((Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1271 chi) ∨
      (¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1273 chi))) ∨
      (((¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom1274 chi) ∨
      (Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1274 chi)) ∨
      ((¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom1275 chi) ∨
      (¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1276 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1276 chi) ∨
      (¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1276 chi)) ∨
      ((¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1276 chi) ∨
      (¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1276 chi))) ∨
      (((Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1276 chi) ∨
      (Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1276 chi)) ∨
      ((Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1276 chi) ∨
      (Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1276 chi)))) ∨
      ((((Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1276 chi) ∨
      (¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom1277 chi)) ∨
      ((¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom1277 chi) ∨
      (Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom1277 chi))) ∨
      (((Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom1277 chi) ∨
      (Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom1277 chi)) ∨
      ((Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom1277 chi) ∨
      (Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom1277 chi))))) ∨
      (((((¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1278 chi) ∨
      (¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1278 chi)) ∨
      ((¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1278 chi) ∨
      (¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1278 chi))) ∨
      (((¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1278 chi) ∨
      (Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1278 chi)) ∨
      ((Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1278 chi) ∨
      (Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1278 chi)))) ∨
      ((((Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1278 chi) ∨
      (¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1279 chi)) ∨
      ((¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1279 chi) ∨
      (¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1279 chi))) ∨
      (((¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1279 chi) ∨
      (¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1279 chi)) ∨
      ((¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1279 chi) ∨
      (Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1279 chi))))))) ∨
      ((((((Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1279 chi) ∨
      ((Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1279 chi) ∨
      (Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1279 chi))) ∨
      (((¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1280 chi) ∨
      (¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1280 chi)) ∨
      ((¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1280 chi) ∨
      (¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1280 chi)))) ∨
      ((((Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1280 chi) ∨
      (Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1280 chi)) ∨
      ((Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1280 chi) ∨
      (Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1280 chi))) ∨
      (((Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1280 chi) ∨
      (¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom1281 chi)) ∨
      ((¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1281 chi) ∨
      (¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom1281 chi))))) ∨
      (((((¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1281 chi) ∨
      (¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1281 chi)) ∨
      ((¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1281 chi) ∨
      (Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1281 chi))) ∨
      (((Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom1281 chi) ∨
      (Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1281 chi)) ∨
      ((Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom1281 chi) ∨
      (¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1282 chi)))) ∨
      ((((¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1282 chi) ∨
      (¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1282 chi)) ∨
      ((¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1282 chi) ∨
      (Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1282 chi))) ∨
      (((Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1282 chi) ∨
      (Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1282 chi)) ∨
      ((Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1282 chi) ∨
      (Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1282 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1283 chi) ∨
      (¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1283 chi)) ∨
      ((¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1283 chi) ∨
      (¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1283 chi))) ∨
      (((¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1283 chi) ∨
      (Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1283 chi)) ∨
      ((Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1283 chi) ∨
      (Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1283 chi)))) ∨
      ((((Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1283 chi) ∨
      (Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1283 chi)) ∨
      ((¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1284 chi) ∨
      (¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1284 chi))) ∨
      (((¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1284 chi) ∨
      (¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1284 chi)) ∨
      ((¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1284 chi) ∨
      (¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1284 chi))))) ∨
      (((((Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1284 chi) ∨
      (Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1284 chi)) ∨
      ((Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1284 chi) ∨
      (Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1284 chi))) ∨
      (((¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom1285 chi) ∨
      (¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom1285 chi)) ∨
      ((¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1285 chi) ∨
      (Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1285 chi)))) ∨
      ((((Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1285 chi) ∨
      (Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom1285 chi)) ∨
      ((Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1285 chi) ∨
      (Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom1285 chi))) ∨
      (((¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom1286 chi) ∨
      (Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom1286 chi)) ∨
      ((¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom1287 chi) ∨
      (¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom1287 chi)))))))) ∨
      (((((((Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom1287 chi) ∨
      ((Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom1287 chi) ∨
      (¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1288 chi))) ∨
      (((¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1288 chi) ∨
      (¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1288 chi)) ∨
      ((¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1288 chi) ∨
      (¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1288 chi)))) ∨
      ((((Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1288 chi) ∨
      (Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1288 chi)) ∨
      ((Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1288 chi) ∨
      (Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1288 chi))) ∨
      (((Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1288 chi) ∨
      (¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1289 chi)) ∨
      ((¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1289 chi) ∨
      (¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1289 chi))))) ∨
      (((((¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1289 chi) ∨
      (Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1289 chi)) ∨
      ((Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1289 chi) ∨
      (Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1289 chi))) ∨
      (((Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1289 chi) ∨
      (¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1290 chi)) ∨
      ((¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1290 chi) ∨
      (¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1290 chi)))) ∨
      ((((¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1290 chi) ∨
      (Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1290 chi)) ∨
      ((Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1290 chi) ∨
      (Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1290 chi))) ∨
      (((Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1290 chi) ∨
      (Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1290 chi)) ∨
      ((Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1290 chi) ∨
      (¬Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1291 chi)))))) ∨
      ((((((Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1291 chi) ∨
      (Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1291 chi)) ∨
      ((Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1291 chi) ∨
      (¬Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1293 chi))) ∨
      (((Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1293 chi) ∨
      (Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1297 chi)) ∨
      ((Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1297 chi) ∨
      (¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0219 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1298 chi)))) ∨
      ((((Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1298 chi) ∨
      (Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1298 chi)) ∨
      ((¬Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1303 chi) ∨
      (Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1303 chi))) ∨
      (((Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1303 chi) ∨
      (¬Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1304 chi)) ∨
      ((¬Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1304 chi) ∨
      (Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1304 chi))))) ∨
      (((((Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1304 chi) ∨
      (¬Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1305 chi)) ∨
      ((¬Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1305 chi) ∨
      (¬Fin15AnchoredAtom0219 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1305 chi))) ∨
      (((Fin15AnchoredAtom0219 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1305 chi) ∨
      (¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1306 chi)) ∨
      ((¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom1306 chi) ∨
      (¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1306 chi)))) ∨
      ((((Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1306 chi) ∨
      (Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1306 chi)) ∨
      ((¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1307 chi) ∨
      (¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1307 chi))) ∨
      (((¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1307 chi) ∨
      (¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1307 chi)) ∨
      ((¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1307 chi) ∨
      (Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1307 chi))))))) ∨
      ((((((Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1307 chi) ∨
      ((Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1307 chi) ∨
      (Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1307 chi))) ∨
      (((¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1308 chi) ∨
      (¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1308 chi)) ∨
      ((¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1308 chi) ∨
      (¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1308 chi)))) ∨
      ((((¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1308 chi) ∨
      (Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1308 chi)) ∨
      ((Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1308 chi) ∨
      (Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1308 chi))) ∨
      (((Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1308 chi) ∨
      (¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1309 chi)) ∨
      ((¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1309 chi) ∨
      (¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1309 chi))))) ∨
      (((((¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1309 chi) ∨
      (¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1309 chi)) ∨
      ((Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1309 chi) ∨
      (Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1309 chi))) ∨
      (((Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1309 chi) ∨
      (Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1309 chi)) ∨
      ((¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1310 chi) ∨
      (¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1310 chi)))) ∨
      ((((¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1310 chi) ∨
      (¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1310 chi)) ∨
      ((Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1310 chi) ∨
      (Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1310 chi))) ∨
      (((Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1310 chi) ∨
      (Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1310 chi)) ∨
      ((Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1310 chi) ∨
      (¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom1311 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom1311 chi) ∨
      (Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom1311 chi)) ∨
      ((¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom1312 chi) ∨
      (¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom1312 chi))) ∨
      (((¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom1312 chi) ∨
      (Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom1312 chi)) ∨
      ((Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom1312 chi) ∨
      (¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1313 chi)))) ∨
      ((((¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1313 chi) ∨
      (¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1313 chi)) ∨
      ((¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1313 chi) ∨
      (¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1313 chi))) ∨
      (((Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1313 chi) ∨
      (Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1313 chi)) ∨
      ((Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1313 chi) ∨
      (Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1313 chi))))) ∨
      (((((Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1313 chi) ∨
      (Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1313 chi)) ∨
      ((¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1314 chi) ∨
      (¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1314 chi))) ∨
      (((¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1314 chi) ∨
      (¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1314 chi)) ∨
      ((Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1314 chi) ∨
      (Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1314 chi)))) ∨
      ((((Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1314 chi) ∨
      (Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1314 chi)) ∨
      ((¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1315 chi) ∨
      (¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1315 chi))) ∨
      (((¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1315 chi) ∨
      (¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1315 chi)) ∨
      ((Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1315 chi) ∨
      (Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1315 chi)))))))))) := by
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
                exact fin15Anchored_clause11105 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11106 chi hbad
                ·
                  exact fin15Anchored_clause11107 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11108 chi hbad
                ·
                  exact fin15Anchored_clause11109 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11110 chi hbad
                ·
                  exact fin15Anchored_clause11111 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11112 chi hbad
                ·
                  exact fin15Anchored_clause11113 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11114 chi hbad
                ·
                  exact fin15Anchored_clause11115 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11116 chi hbad
                ·
                  exact fin15Anchored_clause11117 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11118 chi hbad
                ·
                  exact fin15Anchored_clause11119 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11120 chi hbad
                ·
                  exact fin15Anchored_clause11121 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11122 chi hbad
                ·
                  exact fin15Anchored_clause11123 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11124 chi hbad
                ·
                  exact fin15Anchored_clause11125 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11126 chi hbad
                ·
                  exact fin15Anchored_clause11127 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11128 chi hbad
                ·
                  exact fin15Anchored_clause11129 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11130 chi hbad
                ·
                  exact fin15Anchored_clause11131 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11132 chi hbad
                ·
                  exact fin15Anchored_clause11133 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11134 chi hbad
                ·
                  exact fin15Anchored_clause11135 chi hbad
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
                  exact fin15Anchored_clause11136 chi hbad
                ·
                  exact fin15Anchored_clause11137 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11138 chi hbad
                ·
                  exact fin15Anchored_clause11139 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11140 chi hbad
                ·
                  exact fin15Anchored_clause11141 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11142 chi hbad
                ·
                  exact fin15Anchored_clause11143 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11144 chi hbad
                ·
                  exact fin15Anchored_clause11145 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11146 chi hbad
                ·
                  exact fin15Anchored_clause11147 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11148 chi hbad
                ·
                  exact fin15Anchored_clause11149 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11150 chi hbad
                ·
                  exact fin15Anchored_clause11151 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11152 chi hbad
                ·
                  exact fin15Anchored_clause11153 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11154 chi hbad
                ·
                  exact fin15Anchored_clause11155 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11156 chi hbad
                ·
                  exact fin15Anchored_clause11157 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11158 chi hbad
                ·
                  exact fin15Anchored_clause11159 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11160 chi hbad
                ·
                  exact fin15Anchored_clause11161 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11162 chi hbad
                ·
                  exact fin15Anchored_clause11163 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11164 chi hbad
                ·
                  exact fin15Anchored_clause11165 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11166 chi hbad
                ·
                  exact fin15Anchored_clause11167 chi hbad
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
                exact fin15Anchored_clause11168 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11169 chi hbad
                ·
                  exact fin15Anchored_clause11170 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11171 chi hbad
                ·
                  exact fin15Anchored_clause11172 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11173 chi hbad
                ·
                  exact fin15Anchored_clause11174 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11175 chi hbad
                ·
                  exact fin15Anchored_clause11176 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11177 chi hbad
                ·
                  exact fin15Anchored_clause11178 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11179 chi hbad
                ·
                  exact fin15Anchored_clause11180 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11181 chi hbad
                ·
                  exact fin15Anchored_clause11182 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11183 chi hbad
                ·
                  exact fin15Anchored_clause11184 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11185 chi hbad
                ·
                  exact fin15Anchored_clause11186 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11187 chi hbad
                ·
                  exact fin15Anchored_clause11188 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11189 chi hbad
                ·
                  exact fin15Anchored_clause11190 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11191 chi hbad
                ·
                  exact fin15Anchored_clause11192 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11193 chi hbad
                ·
                  exact fin15Anchored_clause11194 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11195 chi hbad
                ·
                  exact fin15Anchored_clause11196 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11197 chi hbad
                ·
                  exact fin15Anchored_clause11198 chi hbad
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
                  exact fin15Anchored_clause11199 chi hbad
                ·
                  exact fin15Anchored_clause11200 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11201 chi hbad
                ·
                  exact fin15Anchored_clause11202 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11203 chi hbad
                ·
                  exact fin15Anchored_clause11204 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11205 chi hbad
                ·
                  exact fin15Anchored_clause11206 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11207 chi hbad
                ·
                  exact fin15Anchored_clause11208 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11209 chi hbad
                ·
                  exact fin15Anchored_clause11210 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11211 chi hbad
                ·
                  exact fin15Anchored_clause11212 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11213 chi hbad
                ·
                  exact fin15Anchored_clause11214 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11215 chi hbad
                ·
                  exact fin15Anchored_clause11216 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11217 chi hbad
                ·
                  exact fin15Anchored_clause11218 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11219 chi hbad
                ·
                  exact fin15Anchored_clause11220 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11221 chi hbad
                ·
                  exact fin15Anchored_clause11222 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11223 chi hbad
                ·
                  exact fin15Anchored_clause11224 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11225 chi hbad
                ·
                  exact fin15Anchored_clause11226 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11227 chi hbad
                ·
                  exact fin15Anchored_clause11228 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11229 chi hbad
                ·
                  exact fin15Anchored_clause11230 chi hbad
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
                exact fin15Anchored_clause11231 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11232 chi hbad
                ·
                  exact fin15Anchored_clause11233 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11234 chi hbad
                ·
                  exact fin15Anchored_clause11235 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11236 chi hbad
                ·
                  exact fin15Anchored_clause11237 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11238 chi hbad
                ·
                  exact fin15Anchored_clause11239 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11240 chi hbad
                ·
                  exact fin15Anchored_clause11241 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11242 chi hbad
                ·
                  exact fin15Anchored_clause11243 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11244 chi hbad
                ·
                  exact fin15Anchored_clause11245 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11246 chi hbad
                ·
                  exact fin15Anchored_clause11247 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11248 chi hbad
                ·
                  exact fin15Anchored_clause11249 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11250 chi hbad
                ·
                  exact fin15Anchored_clause11251 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11252 chi hbad
                ·
                  exact fin15Anchored_clause11253 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11254 chi hbad
                ·
                  exact fin15Anchored_clause11255 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11256 chi hbad
                ·
                  exact fin15Anchored_clause11257 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11258 chi hbad
                ·
                  exact fin15Anchored_clause11259 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11260 chi hbad
                ·
                  exact fin15Anchored_clause11261 chi hbad
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
                  exact fin15Anchored_clause11262 chi hbad
                ·
                  exact fin15Anchored_clause11263 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11264 chi hbad
                ·
                  exact fin15Anchored_clause11265 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11266 chi hbad
                ·
                  exact fin15Anchored_clause11267 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11268 chi hbad
                ·
                  exact fin15Anchored_clause11269 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11270 chi hbad
                ·
                  exact fin15Anchored_clause11271 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11272 chi hbad
                ·
                  exact fin15Anchored_clause11273 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11274 chi hbad
                ·
                  exact fin15Anchored_clause11275 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11276 chi hbad
                ·
                  exact fin15Anchored_clause11277 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11278 chi hbad
                ·
                  exact fin15Anchored_clause11279 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11280 chi hbad
                ·
                  exact fin15Anchored_clause11281 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11282 chi hbad
                ·
                  exact fin15Anchored_clause11283 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11284 chi hbad
                ·
                  exact fin15Anchored_clause11285 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11286 chi hbad
                ·
                  exact fin15Anchored_clause11287 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11288 chi hbad
                ·
                  exact fin15Anchored_clause11289 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11290 chi hbad
                ·
                  exact fin15Anchored_clause11291 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11292 chi hbad
                ·
                  exact fin15Anchored_clause11293 chi hbad
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
                exact fin15Anchored_clause11294 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11295 chi hbad
                ·
                  exact fin15Anchored_clause11296 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11297 chi hbad
                ·
                  exact fin15Anchored_clause11298 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11299 chi hbad
                ·
                  exact fin15Anchored_clause11300 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11301 chi hbad
                ·
                  exact fin15Anchored_clause11302 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11303 chi hbad
                ·
                  exact fin15Anchored_clause11304 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11305 chi hbad
                ·
                  exact fin15Anchored_clause11306 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11307 chi hbad
                ·
                  exact fin15Anchored_clause11308 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11309 chi hbad
                ·
                  exact fin15Anchored_clause11310 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11311 chi hbad
                ·
                  exact fin15Anchored_clause11312 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11313 chi hbad
                ·
                  exact fin15Anchored_clause11314 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11315 chi hbad
                ·
                  exact fin15Anchored_clause11316 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11317 chi hbad
                ·
                  exact fin15Anchored_clause11318 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11319 chi hbad
                ·
                  exact fin15Anchored_clause11320 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11321 chi hbad
                ·
                  exact fin15Anchored_clause11322 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11323 chi hbad
                ·
                  exact fin15Anchored_clause11324 chi hbad
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
                  exact fin15Anchored_clause11325 chi hbad
                ·
                  exact fin15Anchored_clause11326 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11327 chi hbad
                ·
                  exact fin15Anchored_clause11328 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11329 chi hbad
                ·
                  exact fin15Anchored_clause11330 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11331 chi hbad
                ·
                  exact fin15Anchored_clause11332 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11333 chi hbad
                ·
                  exact fin15Anchored_clause11334 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11335 chi hbad
                ·
                  exact fin15Anchored_clause11336 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11337 chi hbad
                ·
                  exact fin15Anchored_clause11338 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11339 chi hbad
                ·
                  exact fin15Anchored_clause11340 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11341 chi hbad
                ·
                  exact fin15Anchored_clause11342 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11343 chi hbad
                ·
                  exact fin15Anchored_clause11344 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11345 chi hbad
                ·
                  exact fin15Anchored_clause11346 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11347 chi hbad
                ·
                  exact fin15Anchored_clause11348 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11349 chi hbad
                ·
                  exact fin15Anchored_clause11350 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11351 chi hbad
                ·
                  exact fin15Anchored_clause11352 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11353 chi hbad
                ·
                  exact fin15Anchored_clause11354 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause11355 chi hbad
                ·
                  exact fin15Anchored_clause11356 chi hbad

end ErdosSzekeres

end
