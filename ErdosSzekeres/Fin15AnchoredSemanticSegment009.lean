module

public import ErdosSzekeres.Fin15AnchoredClauseChunk017
public import ErdosSzekeres.Fin15AnchoredClauseChunk018
public import ErdosSzekeres.Fin15AnchoredClauseChunk019

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 009. -/

theorem fin15Anchored_rejectSemanticSegment009
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0259 chi) ∨
      ((Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0259 chi) ∨
      (¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0260 chi))) ∨
      (((¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0260 chi) ∨
      (¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0260 chi)) ∨
      ((¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0260 chi) ∨
      (Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0260 chi)))) ∨
      ((((Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0260 chi) ∨
      (Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0260 chi)) ∨
      ((Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0260 chi) ∨
      (¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0261 chi))) ∨
      (((¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0261 chi) ∨
      (¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0261 chi)) ∨
      ((¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0261 chi) ∨
      (Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0261 chi))))) ∨
      (((((Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0261 chi) ∨
      (Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0261 chi)) ∨
      ((Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0261 chi) ∨
      (¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0262 chi))) ∨
      (((¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0262 chi) ∨
      (¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0262 chi)) ∨
      ((¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0262 chi) ∨
      (Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0262 chi)))) ∨
      ((((Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0262 chi) ∨
      (Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0262 chi)) ∨
      ((Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0262 chi) ∨
      (¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0263 chi))) ∨
      (((¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0263 chi) ∨
      (¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0263 chi)) ∨
      ((¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0263 chi) ∨
      (Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0263 chi)))))) ∨
      ((((((Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0263 chi) ∨
      (Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0263 chi)) ∨
      ((Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0263 chi) ∨
      (¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0264 chi))) ∨
      (((¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0264 chi) ∨
      (¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0264 chi)) ∨
      ((¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0264 chi) ∨
      (Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0264 chi)))) ∨
      ((((Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0264 chi) ∨
      (Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0264 chi)) ∨
      ((Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0264 chi) ∨
      (¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0265 chi))) ∨
      (((¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0265 chi) ∨
      (¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0265 chi)) ∨
      ((¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0265 chi) ∨
      (Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0265 chi))))) ∨
      (((((Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0265 chi) ∨
      (Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0265 chi)) ∨
      ((Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0265 chi) ∨
      (¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0266 chi))) ∨
      (((¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0266 chi) ∨
      (¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0266 chi)) ∨
      ((¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0266 chi) ∨
      (Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0266 chi)))) ∨
      ((((Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0266 chi) ∨
      (Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0266 chi)) ∨
      ((Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0266 chi) ∨
      (¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0267 chi))) ∨
      (((¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0267 chi) ∨
      (¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0267 chi)) ∨
      ((¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0267 chi) ∨
      (Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0267 chi))))))) ∨
      ((((((Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0267 chi) ∨
      ((Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0267 chi) ∨
      (Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0267 chi))) ∨
      (((¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0268 chi) ∨
      (¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0268 chi)) ∨
      ((¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0268 chi) ∨
      (¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0268 chi)))) ∨
      ((((Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0268 chi) ∨
      (Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0268 chi)) ∨
      ((Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0268 chi) ∨
      (Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0268 chi))) ∨
      (((¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0269 chi) ∨
      (¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0269 chi)) ∨
      ((¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0269 chi) ∨
      (¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0269 chi))))) ∨
      (((((Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0269 chi) ∨
      (Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0269 chi)) ∨
      ((Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0269 chi) ∨
      (Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0269 chi))) ∨
      (((¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0270 chi) ∨
      (¬Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0270 chi)) ∨
      ((¬Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0270 chi) ∨
      (Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0270 chi)))) ∨
      ((((¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0271 chi) ∨
      (¬Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0271 chi)) ∨
      ((¬Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0271 chi) ∨
      (¬Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0271 chi))) ∨
      (((Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0271 chi) ∨
      (Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0271 chi)) ∨
      ((Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0271 chi) ∨
      (¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0273 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0273 chi) ∨
      (¬Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0273 chi)) ∨
      ((Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0273 chi) ∨
      (Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0273 chi))) ∨
      (((¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0274 chi) ∨
      (¬Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0274 chi)) ∨
      ((Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0274 chi) ∨
      (¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0275 chi)))) ∨
      ((((¬Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0275 chi) ∨
      (¬Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0275 chi)) ∨
      ((Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0275 chi) ∨
      (¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0276 chi))) ∨
      (((¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0276 chi) ∨
      (¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0276 chi)) ∨
      ((¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0276 chi) ∨
      (Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0276 chi))))) ∨
      (((((Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0276 chi) ∨
      (Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0276 chi)) ∨
      ((Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0276 chi) ∨
      (¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0277 chi))) ∨
      (((¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0277 chi) ∨
      (¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0277 chi)) ∨
      ((¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0277 chi) ∨
      (Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0277 chi)))) ∨
      ((((Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0277 chi) ∨
      (Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0277 chi)) ∨
      ((Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0277 chi) ∨
      (¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0278 chi))) ∨
      (((¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0278 chi) ∨
      (¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0278 chi)) ∨
      ((¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0278 chi) ∨
      (Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0278 chi)))))))) ∨
      (((((((Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0278 chi) ∨
      ((Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0278 chi) ∨
      (Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0278 chi))) ∨
      (((¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0279 chi) ∨
      (¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0279 chi)) ∨
      ((¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0279 chi) ∨
      (¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0279 chi)))) ∨
      ((((Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0279 chi) ∨
      (Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0279 chi)) ∨
      ((Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0279 chi) ∨
      (Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0279 chi))) ∨
      (((¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0280 chi) ∨
      (¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0280 chi)) ∨
      ((¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0280 chi) ∨
      (¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0280 chi))))) ∨
      (((((Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0280 chi) ∨
      (Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0280 chi)) ∨
      ((Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0280 chi) ∨
      (Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0280 chi))) ∨
      (((¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0281 chi) ∨
      (¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0281 chi)) ∨
      ((¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0281 chi) ∨
      (¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0281 chi)))) ∨
      ((((Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0281 chi) ∨
      (Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0281 chi)) ∨
      ((Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0281 chi) ∨
      (Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0281 chi))) ∨
      (((¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0282 chi) ∨
      (¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0282 chi)) ∨
      ((¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0282 chi) ∨
      (¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0282 chi)))))) ∨
      ((((((Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0282 chi) ∨
      (Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0282 chi)) ∨
      ((Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0282 chi) ∨
      (Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0282 chi))) ∨
      (((¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0283 chi) ∨
      (¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0283 chi)) ∨
      ((¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0283 chi) ∨
      (¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0283 chi)))) ∨
      ((((Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0283 chi) ∨
      (Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0283 chi)) ∨
      ((Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0283 chi) ∨
      (Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0283 chi))) ∨
      (((¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0284 chi) ∨
      (¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0284 chi)) ∨
      ((¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0284 chi) ∨
      (¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0284 chi))))) ∨
      (((((Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0284 chi) ∨
      (Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0284 chi)) ∨
      ((Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0284 chi) ∨
      (Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0284 chi))) ∨
      (((¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0285 chi) ∨
      (¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0285 chi)) ∨
      ((¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0285 chi) ∨
      (¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0285 chi)))) ∨
      ((((Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0285 chi) ∨
      (Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0285 chi)) ∨
      ((Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0285 chi) ∨
      (¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0286 chi))) ∨
      (((¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0286 chi) ∨
      (¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0286 chi)) ∨
      ((Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0286 chi) ∨
      (Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0286 chi))))))) ∨
      ((((((Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0286 chi) ∨
      ((Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0286 chi) ∨
      (¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0287 chi))) ∨
      (((¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0287 chi) ∨
      (¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0287 chi)) ∨
      ((Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0287 chi) ∨
      (¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0288 chi)))) ∨
      ((((¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0288 chi) ∨
      (¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0288 chi)) ∨
      ((¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0288 chi) ∨
      (Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0288 chi))) ∨
      (((Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0288 chi) ∨
      (Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0288 chi)) ∨
      ((Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0288 chi) ∨
      (¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0289 chi))))) ∨
      (((((¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0289 chi) ∨
      (¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0289 chi)) ∨
      ((¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0289 chi) ∨
      (Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0289 chi))) ∨
      (((Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0289 chi) ∨
      (Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0289 chi)) ∨
      ((Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0289 chi) ∨
      (¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0290 chi)))) ∨
      ((((¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0290 chi) ∨
      (¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0290 chi)) ∨
      ((¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0290 chi) ∨
      (Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0290 chi))) ∨
      (((Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0290 chi) ∨
      (Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0290 chi)) ∨
      ((Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0290 chi) ∨
      (¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0291 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0291 chi) ∨
      (¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0291 chi)) ∨
      ((¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0291 chi) ∨
      (Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0291 chi))) ∨
      (((Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0291 chi) ∨
      (Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0291 chi)) ∨
      ((Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0291 chi) ∨
      (¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0292 chi)))) ∨
      ((((¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0292 chi) ∨
      (¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0292 chi)) ∨
      ((¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0292 chi) ∨
      (Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0292 chi))) ∨
      (((Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0292 chi) ∨
      (Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0292 chi)) ∨
      ((Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0292 chi) ∨
      (¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0293 chi))))) ∨
      (((((¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0293 chi) ∨
      (¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0293 chi)) ∨
      ((¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0293 chi) ∨
      (Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0293 chi))) ∨
      (((Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0293 chi) ∨
      (Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0293 chi)) ∨
      ((Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0293 chi) ∨
      (¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0294 chi)))) ∨
      ((((¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0294 chi) ∨
      (¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0294 chi)) ∨
      ((¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0294 chi) ∨
      (Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0294 chi))) ∨
      (((Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0294 chi) ∨
      (Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0294 chi)) ∨
      ((Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0294 chi) ∨
      (¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0295 chi)))))))))) := by
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
                exact fin15Anchored_clause02271 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02272 chi hone hbad
                ·
                  exact fin15Anchored_clause02273 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02274 chi hone hbad
                ·
                  exact fin15Anchored_clause02275 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02276 chi hone hbad
                ·
                  exact fin15Anchored_clause02277 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02278 chi hone hbad
                ·
                  exact fin15Anchored_clause02279 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02280 chi hone hbad
                ·
                  exact fin15Anchored_clause02281 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02282 chi hone hbad
                ·
                  exact fin15Anchored_clause02283 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02284 chi hone hbad
                ·
                  exact fin15Anchored_clause02285 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02286 chi hone hbad
                ·
                  exact fin15Anchored_clause02287 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02288 chi hone hbad
                ·
                  exact fin15Anchored_clause02289 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02290 chi hone hbad
                ·
                  exact fin15Anchored_clause02291 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02292 chi hone hbad
                ·
                  exact fin15Anchored_clause02293 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02294 chi hone hbad
                ·
                  exact fin15Anchored_clause02295 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02296 chi hone hbad
                ·
                  exact fin15Anchored_clause02297 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02298 chi hone hbad
                ·
                  exact fin15Anchored_clause02299 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02300 chi hone hbad
                ·
                  exact fin15Anchored_clause02301 chi hone hbad
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
                  exact fin15Anchored_clause02302 chi hone hbad
                ·
                  exact fin15Anchored_clause02303 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02304 chi hone hbad
                ·
                  exact fin15Anchored_clause02305 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02306 chi hone hbad
                ·
                  exact fin15Anchored_clause02307 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02308 chi hone hbad
                ·
                  exact fin15Anchored_clause02309 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02310 chi hone hbad
                ·
                  exact fin15Anchored_clause02311 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02312 chi hone hbad
                ·
                  exact fin15Anchored_clause02313 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02314 chi hone hbad
                ·
                  exact fin15Anchored_clause02315 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02316 chi hone hbad
                ·
                  exact fin15Anchored_clause02317 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02318 chi hone hbad
                ·
                  exact fin15Anchored_clause02319 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02320 chi hone hbad
                ·
                  exact fin15Anchored_clause02321 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02322 chi hone hbad
                ·
                  exact fin15Anchored_clause02323 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02324 chi hone hbad
                ·
                  exact fin15Anchored_clause02325 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02326 chi hone hbad
                ·
                  exact fin15Anchored_clause02327 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02328 chi hone hbad
                ·
                  exact fin15Anchored_clause02329 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02330 chi hone hbad
                ·
                  exact fin15Anchored_clause02331 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02332 chi hone hbad
                ·
                  exact fin15Anchored_clause02333 chi hone hbad
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
                exact fin15Anchored_clause02334 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02335 chi hone hbad
                ·
                  exact fin15Anchored_clause02336 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02337 chi hone hbad
                ·
                  exact fin15Anchored_clause02338 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02339 chi hone hbad
                ·
                  exact fin15Anchored_clause02340 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02341 chi hone hbad
                ·
                  exact fin15Anchored_clause02342 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02343 chi hone hbad
                ·
                  exact fin15Anchored_clause02344 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02345 chi hone hbad
                ·
                  exact fin15Anchored_clause02346 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02347 chi hone hbad
                ·
                  exact fin15Anchored_clause02348 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02349 chi hone hbad
                ·
                  exact fin15Anchored_clause02350 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02351 chi hone hbad
                ·
                  exact fin15Anchored_clause02352 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02353 chi hone hbad
                ·
                  exact fin15Anchored_clause02354 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02355 chi hone hbad
                ·
                  exact fin15Anchored_clause02356 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02357 chi hone hbad
                ·
                  exact fin15Anchored_clause02358 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02359 chi hone hbad
                ·
                  exact fin15Anchored_clause02360 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02361 chi hone hbad
                ·
                  exact fin15Anchored_clause02362 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02363 chi hone hbad
                ·
                  exact fin15Anchored_clause02364 chi hone hbad
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
                  exact fin15Anchored_clause02365 chi hone hbad
                ·
                  exact fin15Anchored_clause02366 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02367 chi hone hbad
                ·
                  exact fin15Anchored_clause02368 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02369 chi hone hbad
                ·
                  exact fin15Anchored_clause02370 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02371 chi hone hbad
                ·
                  exact fin15Anchored_clause02372 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02373 chi hone hbad
                ·
                  exact fin15Anchored_clause02374 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02375 chi hone hbad
                ·
                  exact fin15Anchored_clause02376 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02377 chi hone hbad
                ·
                  exact fin15Anchored_clause02378 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02379 chi hone hbad
                ·
                  exact fin15Anchored_clause02380 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02381 chi hone hbad
                ·
                  exact fin15Anchored_clause02382 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02383 chi hone hbad
                ·
                  exact fin15Anchored_clause02384 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02385 chi hone hbad
                ·
                  exact fin15Anchored_clause02386 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02387 chi hone hbad
                ·
                  exact fin15Anchored_clause02388 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02389 chi hone hbad
                ·
                  exact fin15Anchored_clause02390 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02391 chi hone hbad
                ·
                  exact fin15Anchored_clause02392 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02393 chi hone hbad
                ·
                  exact fin15Anchored_clause02394 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02395 chi hone hbad
                ·
                  exact fin15Anchored_clause02396 chi hone hbad
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
                exact fin15Anchored_clause02397 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02398 chi hone hbad
                ·
                  exact fin15Anchored_clause02399 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02400 chi hone hbad
                ·
                  exact fin15Anchored_clause02401 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02402 chi hone hbad
                ·
                  exact fin15Anchored_clause02403 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02404 chi hone hbad
                ·
                  exact fin15Anchored_clause02405 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02406 chi hone hbad
                ·
                  exact fin15Anchored_clause02407 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02408 chi hone hbad
                ·
                  exact fin15Anchored_clause02409 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02410 chi hone hbad
                ·
                  exact fin15Anchored_clause02411 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02412 chi hone hbad
                ·
                  exact fin15Anchored_clause02413 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02414 chi hone hbad
                ·
                  exact fin15Anchored_clause02415 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02416 chi hone hbad
                ·
                  exact fin15Anchored_clause02417 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02418 chi hone hbad
                ·
                  exact fin15Anchored_clause02419 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02420 chi hone hbad
                ·
                  exact fin15Anchored_clause02421 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02422 chi hone hbad
                ·
                  exact fin15Anchored_clause02423 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02424 chi hone hbad
                ·
                  exact fin15Anchored_clause02425 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02426 chi hone hbad
                ·
                  exact fin15Anchored_clause02427 chi hone hbad
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
                  exact fin15Anchored_clause02428 chi hone hbad
                ·
                  exact fin15Anchored_clause02429 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02430 chi hone hbad
                ·
                  exact fin15Anchored_clause02431 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02432 chi hone hbad
                ·
                  exact fin15Anchored_clause02433 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02434 chi hone hbad
                ·
                  exact fin15Anchored_clause02435 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02436 chi hone hbad
                ·
                  exact fin15Anchored_clause02437 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02438 chi hone hbad
                ·
                  exact fin15Anchored_clause02439 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02440 chi hone hbad
                ·
                  exact fin15Anchored_clause02441 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02442 chi hone hbad
                ·
                  exact fin15Anchored_clause02443 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02444 chi hone hbad
                ·
                  exact fin15Anchored_clause02445 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02446 chi hone hbad
                ·
                  exact fin15Anchored_clause02447 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02448 chi hone hbad
                ·
                  exact fin15Anchored_clause02449 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02450 chi hone hbad
                ·
                  exact fin15Anchored_clause02451 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02452 chi hone hbad
                ·
                  exact fin15Anchored_clause02453 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02454 chi hone hbad
                ·
                  exact fin15Anchored_clause02455 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02456 chi hone hbad
                ·
                  exact fin15Anchored_clause02457 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02458 chi hone hbad
                ·
                  exact fin15Anchored_clause02459 chi hone hbad
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
                exact fin15Anchored_clause02460 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02461 chi hone hbad
                ·
                  exact fin15Anchored_clause02462 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02463 chi hone hbad
                ·
                  exact fin15Anchored_clause02464 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02465 chi hone hbad
                ·
                  exact fin15Anchored_clause02466 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02467 chi hone hbad
                ·
                  exact fin15Anchored_clause02468 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02469 chi hone hbad
                ·
                  exact fin15Anchored_clause02470 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02471 chi hone hbad
                ·
                  exact fin15Anchored_clause02472 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02473 chi hone hbad
                ·
                  exact fin15Anchored_clause02474 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02475 chi hone hbad
                ·
                  exact fin15Anchored_clause02476 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02477 chi hone hbad
                ·
                  exact fin15Anchored_clause02478 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02479 chi hone hbad
                ·
                  exact fin15Anchored_clause02480 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02481 chi hone hbad
                ·
                  exact fin15Anchored_clause02482 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02483 chi hone hbad
                ·
                  exact fin15Anchored_clause02484 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02485 chi hone hbad
                ·
                  exact fin15Anchored_clause02486 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02487 chi hone hbad
                ·
                  exact fin15Anchored_clause02488 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02489 chi hone hbad
                ·
                  exact fin15Anchored_clause02490 chi hone hbad
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
                  exact fin15Anchored_clause02491 chi hone hbad
                ·
                  exact fin15Anchored_clause02492 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02493 chi hone hbad
                ·
                  exact fin15Anchored_clause02494 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02495 chi hone hbad
                ·
                  exact fin15Anchored_clause02496 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02497 chi hone hbad
                ·
                  exact fin15Anchored_clause02498 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02499 chi hone hbad
                ·
                  exact fin15Anchored_clause02500 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02501 chi hone hbad
                ·
                  exact fin15Anchored_clause02502 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02503 chi hone hbad
                ·
                  exact fin15Anchored_clause02504 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02505 chi hone hbad
                ·
                  exact fin15Anchored_clause02506 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02507 chi hone hbad
                ·
                  exact fin15Anchored_clause02508 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02509 chi hone hbad
                ·
                  exact fin15Anchored_clause02510 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02511 chi hone hbad
                ·
                  exact fin15Anchored_clause02512 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02513 chi hone hbad
                ·
                  exact fin15Anchored_clause02514 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02515 chi hone hbad
                ·
                  exact fin15Anchored_clause02516 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02517 chi hone hbad
                ·
                  exact fin15Anchored_clause02518 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02519 chi hone hbad
                ·
                  exact fin15Anchored_clause02520 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02521 chi hone hbad
                ·
                  exact fin15Anchored_clause02522 chi hone hbad

end ErdosSzekeres

end
