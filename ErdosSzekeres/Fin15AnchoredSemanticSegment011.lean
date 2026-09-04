module

public import ErdosSzekeres.Fin15AnchoredClauseChunk021
public import ErdosSzekeres.Fin15AnchoredClauseChunk022
public import ErdosSzekeres.Fin15AnchoredClauseChunk023

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 011. -/

theorem fin15Anchored_rejectSemanticSegment011
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0328 chi) ∨
      ((¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0329 chi) ∨
      (¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0329 chi))) ∨
      (((¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0329 chi) ∨
      (¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0329 chi)) ∨
      ((Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0329 chi) ∨
      (Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0329 chi)))) ∨
      ((((Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0329 chi) ∨
      (Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0329 chi)) ∨
      ((¬Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0330 chi) ∨
      (¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0330 chi))) ∨
      (((¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0330 chi) ∨
      (¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0330 chi)) ∨
      ((Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0330 chi) ∨
      (Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0330 chi))))) ∨
      (((((Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0330 chi) ∨
      (¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0331 chi)) ∨
      ((¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0331 chi) ∨
      (¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0331 chi))) ∨
      (((Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0331 chi) ∨
      (Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0331 chi)) ∨
      ((¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0333 chi) ∨
      (¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0333 chi)))) ∨
      ((((¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0333 chi) ∨
      (¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0333 chi)) ∨
      ((Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0333 chi) ∨
      (Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0333 chi))) ∨
      (((Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0333 chi) ∨
      (Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0333 chi)) ∨
      ((¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0334 chi) ∨
      (¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0334 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0334 chi) ∨
      (¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0334 chi)) ∨
      ((Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0334 chi) ∨
      (Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0334 chi))) ∨
      (((Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0334 chi) ∨
      (Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0334 chi)) ∨
      ((¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0335 chi) ∨
      (¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0335 chi)))) ∨
      ((((¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0335 chi) ∨
      (¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0335 chi)) ∨
      ((Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0335 chi) ∨
      (Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0335 chi))) ∨
      (((Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0335 chi) ∨
      (Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0335 chi)) ∨
      ((¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0336 chi) ∨
      (¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0336 chi))))) ∨
      (((((¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0336 chi) ∨
      (¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0336 chi)) ∨
      ((Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0336 chi) ∨
      (Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0336 chi))) ∨
      (((Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0336 chi) ∨
      (Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0336 chi)) ∨
      ((¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0337 chi) ∨
      (¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0337 chi)))) ∨
      ((((¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0337 chi) ∨
      (¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0337 chi)) ∨
      ((Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0337 chi) ∨
      (Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0337 chi))) ∨
      (((¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0338 chi) ∨
      (¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0338 chi)) ∨
      ((¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0338 chi) ∨
      (¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0338 chi))))))) ∨
      ((((((Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0338 chi) ∨
      ((Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0338 chi) ∨
      (Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0338 chi))) ∨
      (((Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0338 chi) ∨
      (¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0339 chi)) ∨
      ((¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0339 chi) ∨
      (¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0339 chi)))) ∨
      ((((¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0339 chi) ∨
      (Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0339 chi)) ∨
      ((Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0339 chi) ∨
      (Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0339 chi))) ∨
      (((Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0339 chi) ∨
      (¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0340 chi)) ∨
      ((¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0340 chi) ∨
      (¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0340 chi))))) ∨
      (((((¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0340 chi) ∨
      (Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0340 chi)) ∨
      ((Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0340 chi) ∨
      (Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0340 chi))) ∨
      (((Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0340 chi) ∨
      (¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0341 chi)) ∨
      ((¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0341 chi) ∨
      (¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0341 chi)))) ∨
      ((((¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0341 chi) ∨
      (Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0341 chi)) ∨
      ((Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0341 chi) ∨
      (Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0341 chi))) ∨
      (((Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0341 chi) ∨
      (¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0342 chi)) ∨
      ((¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0342 chi) ∨
      (¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0342 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0342 chi) ∨
      (Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0342 chi)) ∨
      ((Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0342 chi) ∨
      (Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0342 chi))) ∨
      (((Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0342 chi) ∨
      (¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0343 chi)) ∨
      ((¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0343 chi) ∨
      (¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0343 chi)))) ∨
      ((((¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0343 chi) ∨
      (Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0343 chi)) ∨
      ((Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0343 chi) ∨
      (Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0343 chi))) ∨
      (((Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0343 chi) ∨
      (¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0344 chi)) ∨
      ((¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0344 chi) ∨
      (¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0344 chi))))) ∨
      (((((¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0344 chi) ∨
      (Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0344 chi)) ∨
      ((Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0344 chi) ∨
      (Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0344 chi))) ∨
      (((Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0344 chi) ∨
      (¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0345 chi)) ∨
      ((¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0345 chi) ∨
      (¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0345 chi)))) ∨
      ((((¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0345 chi) ∨
      (Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0345 chi)) ∨
      ((Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0345 chi) ∨
      (Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0345 chi))) ∨
      (((Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0345 chi) ∨
      (¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0346 chi)) ∨
      ((¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0346 chi) ∨
      (¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0346 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0346 chi) ∨
      ((Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0346 chi) ∨
      (Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0346 chi))) ∨
      (((Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0346 chi) ∨
      (Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0346 chi)) ∨
      ((¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0347 chi) ∨
      (¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0347 chi)))) ∨
      ((((¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0347 chi) ∨
      (¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0347 chi)) ∨
      ((Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0347 chi) ∨
      (Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0347 chi))) ∨
      (((Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0347 chi) ∨
      (Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0347 chi)) ∨
      ((¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0348 chi) ∨
      (¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0348 chi))))) ∨
      (((((¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0348 chi) ∨
      (¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0348 chi)) ∨
      ((Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0348 chi) ∨
      (Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0348 chi))) ∨
      (((Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0348 chi) ∨
      (Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0348 chi)) ∨
      ((¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0349 chi) ∨
      (¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0349 chi)))) ∨
      ((((¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0349 chi) ∨
      (¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0349 chi)) ∨
      ((Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0349 chi) ∨
      (Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0349 chi))) ∨
      (((Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0349 chi) ∨
      (Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0349 chi)) ∨
      ((¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0350 chi) ∨
      (¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0350 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0350 chi) ∨
      (¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0350 chi)) ∨
      ((Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0350 chi) ∨
      (Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0350 chi))) ∨
      (((Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0350 chi) ∨
      (Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0350 chi)) ∨
      ((¬Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0351 chi) ∨
      (¬Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0351 chi)))) ∨
      ((((¬Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0351 chi) ∨
      (Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0351 chi)) ∨
      ((Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0351 chi) ∨
      (Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0351 chi))) ∨
      (((¬Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0352 chi) ∨
      (¬Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0352 chi)) ∨
      ((¬Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0352 chi) ∨
      (¬Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0352 chi))))) ∨
      (((((Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0352 chi) ∨
      (Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0352 chi)) ∨
      ((Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0352 chi) ∨
      (Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0352 chi))) ∨
      (((¬Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0355 chi) ∨
      (¬Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0355 chi)) ∨
      ((¬Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0219 chi ∧
      Fin15AnchoredAtom0355 chi) ∨
      (¬Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0355 chi)))) ∨
      ((((Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0355 chi) ∨
      (Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0219 chi ∧
      Fin15AnchoredAtom0355 chi)) ∨
      ((¬Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0356 chi) ∨
      (¬Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0356 chi))) ∨
      (((¬Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      Fin15AnchoredAtom0356 chi) ∨
      (¬Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0356 chi)) ∨
      ((Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0356 chi) ∨
      (¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0357 chi))))))) ∨
      (((((((¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0357 chi) ∨
      (¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0357 chi)) ∨
      ((¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0357 chi) ∨
      (Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0357 chi))) ∨
      (((Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0357 chi) ∨
      (Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0357 chi)) ∨
      ((Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0357 chi) ∨
      (¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0358 chi)))) ∨
      ((((¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0358 chi) ∨
      (¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0358 chi)) ∨
      ((¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0358 chi) ∨
      (Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0358 chi))) ∨
      (((Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0358 chi) ∨
      (Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0358 chi)) ∨
      ((Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0358 chi) ∨
      (¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0359 chi))))) ∨
      (((((¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0359 chi) ∨
      (¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0359 chi)) ∨
      ((¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0359 chi) ∨
      (Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0359 chi))) ∨
      (((Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0359 chi) ∨
      (Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0359 chi)) ∨
      ((Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0359 chi) ∨
      (¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0360 chi)))) ∨
      ((((¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0360 chi) ∨
      (¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0360 chi)) ∨
      ((¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0360 chi) ∨
      (Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0360 chi))) ∨
      (((Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0360 chi) ∨
      (Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0360 chi)) ∨
      ((Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0360 chi) ∨
      (¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0361 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0361 chi) ∨
      (¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0361 chi)) ∨
      ((¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0361 chi) ∨
      (Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0361 chi))) ∨
      (((Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0361 chi) ∨
      (Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0361 chi)) ∨
      ((Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0361 chi) ∨
      (¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0362 chi)))) ∨
      ((((¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0362 chi) ∨
      (¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0362 chi)) ∨
      ((¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0362 chi) ∨
      (Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0362 chi))) ∨
      (((Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0362 chi) ∨
      (Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0362 chi)) ∨
      ((Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0362 chi) ∨
      (¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0363 chi))))) ∨
      (((((¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0363 chi) ∨
      (¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0363 chi)) ∨
      ((¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0363 chi) ∨
      (Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0363 chi))) ∨
      (((Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0363 chi) ∨
      (Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0363 chi)) ∨
      ((Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0363 chi) ∨
      (¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0364 chi)))) ∨
      ((((¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0364 chi) ∨
      (¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0364 chi)) ∨
      ((¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0364 chi) ∨
      (Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0364 chi))) ∨
      (((Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0364 chi) ∨
      (Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0364 chi)) ∨
      ((Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0364 chi) ∨
      (¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0365 chi)))))))))) := by
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
                exact fin15Anchored_clause02775 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02776 chi hone hbad
                ·
                  exact fin15Anchored_clause02777 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02778 chi hone hbad
                ·
                  exact fin15Anchored_clause02779 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02780 chi hone hbad
                ·
                  exact fin15Anchored_clause02781 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02782 chi hone hbad
                ·
                  exact fin15Anchored_clause02783 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02784 chi hone hbad
                ·
                  exact fin15Anchored_clause02785 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02786 chi hone hbad
                ·
                  exact fin15Anchored_clause02787 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02788 chi hone hbad
                ·
                  exact fin15Anchored_clause02789 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02790 chi hone hbad
                ·
                  exact fin15Anchored_clause02791 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02792 chi hone hbad
                ·
                  exact fin15Anchored_clause02793 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02794 chi hone hbad
                ·
                  exact fin15Anchored_clause02795 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02796 chi hone hbad
                ·
                  exact fin15Anchored_clause02797 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02798 chi hone hbad
                ·
                  exact fin15Anchored_clause02799 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02800 chi hone hbad
                ·
                  exact fin15Anchored_clause02801 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02802 chi hone hbad
                ·
                  exact fin15Anchored_clause02803 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02804 chi hone hbad
                ·
                  exact fin15Anchored_clause02805 chi hone hbad
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
                  exact fin15Anchored_clause02806 chi hone hbad
                ·
                  exact fin15Anchored_clause02807 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02808 chi hone hbad
                ·
                  exact fin15Anchored_clause02809 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02810 chi hone hbad
                ·
                  exact fin15Anchored_clause02811 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02812 chi hone hbad
                ·
                  exact fin15Anchored_clause02813 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02814 chi hone hbad
                ·
                  exact fin15Anchored_clause02815 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02816 chi hone hbad
                ·
                  exact fin15Anchored_clause02817 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02818 chi hone hbad
                ·
                  exact fin15Anchored_clause02819 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02820 chi hone hbad
                ·
                  exact fin15Anchored_clause02821 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02822 chi hone hbad
                ·
                  exact fin15Anchored_clause02823 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02824 chi hone hbad
                ·
                  exact fin15Anchored_clause02825 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02826 chi hone hbad
                ·
                  exact fin15Anchored_clause02827 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02828 chi hone hbad
                ·
                  exact fin15Anchored_clause02829 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02830 chi hone hbad
                ·
                  exact fin15Anchored_clause02831 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02832 chi hone hbad
                ·
                  exact fin15Anchored_clause02833 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02834 chi hone hbad
                ·
                  exact fin15Anchored_clause02835 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02836 chi hone hbad
                ·
                  exact fin15Anchored_clause02837 chi hone hbad
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
                exact fin15Anchored_clause02838 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02839 chi hone hbad
                ·
                  exact fin15Anchored_clause02840 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02841 chi hone hbad
                ·
                  exact fin15Anchored_clause02842 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02843 chi hone hbad
                ·
                  exact fin15Anchored_clause02844 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02845 chi hone hbad
                ·
                  exact fin15Anchored_clause02846 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02847 chi hone hbad
                ·
                  exact fin15Anchored_clause02848 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02849 chi hone hbad
                ·
                  exact fin15Anchored_clause02850 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02851 chi hone hbad
                ·
                  exact fin15Anchored_clause02852 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02853 chi hone hbad
                ·
                  exact fin15Anchored_clause02854 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02855 chi hone hbad
                ·
                  exact fin15Anchored_clause02856 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02857 chi hone hbad
                ·
                  exact fin15Anchored_clause02858 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02859 chi hone hbad
                ·
                  exact fin15Anchored_clause02860 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02861 chi hone hbad
                ·
                  exact fin15Anchored_clause02862 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02863 chi hone hbad
                ·
                  exact fin15Anchored_clause02864 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02865 chi hone hbad
                ·
                  exact fin15Anchored_clause02866 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02867 chi hone hbad
                ·
                  exact fin15Anchored_clause02868 chi hone hbad
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
                  exact fin15Anchored_clause02869 chi hone hbad
                ·
                  exact fin15Anchored_clause02870 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02871 chi hone hbad
                ·
                  exact fin15Anchored_clause02872 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02873 chi hone hbad
                ·
                  exact fin15Anchored_clause02874 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02875 chi hone hbad
                ·
                  exact fin15Anchored_clause02876 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02877 chi hone hbad
                ·
                  exact fin15Anchored_clause02878 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02879 chi hone hbad
                ·
                  exact fin15Anchored_clause02880 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02881 chi hone hbad
                ·
                  exact fin15Anchored_clause02882 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02883 chi hone hbad
                ·
                  exact fin15Anchored_clause02884 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02885 chi hone hbad
                ·
                  exact fin15Anchored_clause02886 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02887 chi hone hbad
                ·
                  exact fin15Anchored_clause02888 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02889 chi hone hbad
                ·
                  exact fin15Anchored_clause02890 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02891 chi hone hbad
                ·
                  exact fin15Anchored_clause02892 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02893 chi hone hbad
                ·
                  exact fin15Anchored_clause02894 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02895 chi hone hbad
                ·
                  exact fin15Anchored_clause02896 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02897 chi hone hbad
                ·
                  exact fin15Anchored_clause02898 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02899 chi hone hbad
                ·
                  exact fin15Anchored_clause02900 chi hone hbad
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
                exact fin15Anchored_clause02901 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02902 chi hone hbad
                ·
                  exact fin15Anchored_clause02903 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02904 chi hone hbad
                ·
                  exact fin15Anchored_clause02905 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02906 chi hone hbad
                ·
                  exact fin15Anchored_clause02907 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02908 chi hone hbad
                ·
                  exact fin15Anchored_clause02909 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02910 chi hone hbad
                ·
                  exact fin15Anchored_clause02911 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02912 chi hone hbad
                ·
                  exact fin15Anchored_clause02913 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02914 chi hone hbad
                ·
                  exact fin15Anchored_clause02915 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02916 chi hone hbad
                ·
                  exact fin15Anchored_clause02917 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02918 chi hone hbad
                ·
                  exact fin15Anchored_clause02919 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02920 chi hone hbad
                ·
                  exact fin15Anchored_clause02921 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02922 chi hone hbad
                ·
                  exact fin15Anchored_clause02923 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02924 chi hone hbad
                ·
                  exact fin15Anchored_clause02925 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02926 chi hone hbad
                ·
                  exact fin15Anchored_clause02927 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02928 chi hone hbad
                ·
                  exact fin15Anchored_clause02929 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02930 chi hone hbad
                ·
                  exact fin15Anchored_clause02931 chi hone hbad
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
                  exact fin15Anchored_clause02932 chi hone hbad
                ·
                  exact fin15Anchored_clause02933 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02934 chi hone hbad
                ·
                  exact fin15Anchored_clause02935 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02936 chi hone hbad
                ·
                  exact fin15Anchored_clause02937 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02938 chi hone hbad
                ·
                  exact fin15Anchored_clause02939 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02940 chi hone hbad
                ·
                  exact fin15Anchored_clause02941 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02942 chi hone hbad
                ·
                  exact fin15Anchored_clause02943 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02944 chi hone hbad
                ·
                  exact fin15Anchored_clause02945 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02946 chi hone hbad
                ·
                  exact fin15Anchored_clause02947 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02948 chi hone hbad
                ·
                  exact fin15Anchored_clause02949 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02950 chi hone hbad
                ·
                  exact fin15Anchored_clause02951 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02952 chi hone hbad
                ·
                  exact fin15Anchored_clause02953 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02954 chi hone hbad
                ·
                  exact fin15Anchored_clause02955 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02956 chi hone hbad
                ·
                  exact fin15Anchored_clause02957 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02958 chi hone hbad
                ·
                  exact fin15Anchored_clause02959 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02960 chi hone hbad
                ·
                  exact fin15Anchored_clause02961 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02962 chi hone hbad
                ·
                  exact fin15Anchored_clause02963 chi hone hbad
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
                  exact fin15Anchored_clause02964 chi hone hbad
                ·
                  exact fin15Anchored_clause02965 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02966 chi hone hbad
                ·
                  exact fin15Anchored_clause02967 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02968 chi hone hbad
                ·
                  exact fin15Anchored_clause02969 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02970 chi hone hbad
                ·
                  exact fin15Anchored_clause02971 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02972 chi hone hbad
                ·
                  exact fin15Anchored_clause02973 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02974 chi hone hbad
                ·
                  exact fin15Anchored_clause02975 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02976 chi hone hbad
                ·
                  exact fin15Anchored_clause02977 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02978 chi hone hbad
                ·
                  exact fin15Anchored_clause02979 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02980 chi hone hbad
                ·
                  exact fin15Anchored_clause02981 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02982 chi hone hbad
                ·
                  exact fin15Anchored_clause02983 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02984 chi hone hbad
                ·
                  exact fin15Anchored_clause02985 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02986 chi hone hbad
                ·
                  exact fin15Anchored_clause02987 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02988 chi hone hbad
                ·
                  exact fin15Anchored_clause02989 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02990 chi hone hbad
                ·
                  exact fin15Anchored_clause02991 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02992 chi hone hbad
                ·
                  exact fin15Anchored_clause02993 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02994 chi hone hbad
                ·
                  exact fin15Anchored_clause02995 chi hone hbad
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
                  exact fin15Anchored_clause02996 chi hone hbad
                ·
                  exact fin15Anchored_clause02997 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02998 chi hone hbad
                ·
                  exact fin15Anchored_clause02999 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03000 chi hone hbad
                ·
                  exact fin15Anchored_clause03001 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03002 chi hone hbad
                ·
                  exact fin15Anchored_clause03003 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03004 chi hone hbad
                ·
                  exact fin15Anchored_clause03005 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03006 chi hone hbad
                ·
                  exact fin15Anchored_clause03007 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03008 chi hone hbad
                ·
                  exact fin15Anchored_clause03009 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03010 chi hone hbad
                ·
                  exact fin15Anchored_clause03011 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03012 chi hone hbad
                ·
                  exact fin15Anchored_clause03013 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03014 chi hone hbad
                ·
                  exact fin15Anchored_clause03015 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03016 chi hone hbad
                ·
                  exact fin15Anchored_clause03017 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03018 chi hone hbad
                ·
                  exact fin15Anchored_clause03019 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03020 chi hone hbad
                ·
                  exact fin15Anchored_clause03021 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03022 chi hone hbad
                ·
                  exact fin15Anchored_clause03023 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03024 chi hone hbad
                ·
                  exact fin15Anchored_clause03025 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause03026 chi hone hbad
                ·
                  exact fin15Anchored_clause03027 chi hone hbad

end ErdosSzekeres

end
