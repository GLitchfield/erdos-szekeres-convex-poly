module

public import ErdosSzekeres.Fin15AnchoredClauseChunk019
public import ErdosSzekeres.Fin15AnchoredClauseChunk020
public import ErdosSzekeres.Fin15AnchoredClauseChunk021

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 010. -/

theorem fin15Anchored_rejectSemanticSegment010
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0295 chi) ∨
      ((¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0295 chi) ∨
      (¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0295 chi))) ∨
      (((Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0295 chi) ∨
      (Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0295 chi)) ∨
      ((Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0295 chi) ∨
      (Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0295 chi)))) ∨
      ((((¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0296 chi) ∨
      (¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0296 chi)) ∨
      ((¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0296 chi) ∨
      (¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0296 chi))) ∨
      (((Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0296 chi) ∨
      (Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0296 chi)) ∨
      ((Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0296 chi) ∨
      (Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0296 chi))))) ∨
      (((((¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0297 chi) ∨
      (¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0297 chi)) ∨
      ((¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0297 chi) ∨
      (¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0297 chi))) ∨
      (((Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0297 chi) ∨
      (Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0297 chi)) ∨
      ((Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0297 chi) ∨
      (Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0297 chi)))) ∨
      ((((¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0298 chi) ∨
      (¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0298 chi)) ∨
      ((¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0298 chi) ∨
      (¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0298 chi))) ∨
      (((Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0298 chi) ∨
      (Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0298 chi)) ∨
      ((Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0298 chi) ∨
      (Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0298 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0299 chi) ∨
      (¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0299 chi)) ∨
      ((¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0299 chi) ∨
      (¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0299 chi))) ∨
      (((Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0299 chi) ∨
      (Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0299 chi)) ∨
      ((Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0299 chi) ∨
      (Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0299 chi)))) ∨
      ((((¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0300 chi) ∨
      (¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0300 chi)) ∨
      ((¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0300 chi) ∨
      (¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0300 chi))) ∨
      (((Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0300 chi) ∨
      (Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0300 chi)) ∨
      ((Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0300 chi) ∨
      (Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0300 chi))))) ∨
      (((((¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0301 chi) ∨
      (¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0301 chi)) ∨
      ((¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0301 chi) ∨
      (¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0301 chi))) ∨
      (((Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0301 chi) ∨
      (Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0301 chi)) ∨
      ((Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0301 chi) ∨
      (¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0302 chi)))) ∨
      ((((¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0302 chi) ∨
      (¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0302 chi)) ∨
      ((¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0302 chi) ∨
      (Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0302 chi))) ∨
      (((Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0302 chi) ∨
      (Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0302 chi)) ∨
      ((Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0302 chi) ∨
      (¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0303 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0303 chi) ∨
      ((¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0303 chi) ∨
      (¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0303 chi))) ∨
      (((Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0303 chi) ∨
      (Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0303 chi)) ∨
      ((Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0303 chi) ∨
      (Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0303 chi)))) ∨
      ((((¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0304 chi) ∨
      (¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0304 chi)) ∨
      ((¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0304 chi) ∨
      (¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0304 chi))) ∨
      (((Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0304 chi) ∨
      (Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0304 chi)) ∨
      ((Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0304 chi) ∨
      (Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0304 chi))))) ∨
      (((((¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0305 chi) ∨
      (¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0305 chi)) ∨
      ((¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0305 chi) ∨
      (¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0305 chi))) ∨
      (((Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0305 chi) ∨
      (Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0305 chi)) ∨
      ((Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0305 chi) ∨
      (Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0305 chi)))) ∨
      ((((¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0306 chi) ∨
      (¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0306 chi)) ∨
      ((¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0306 chi) ∨
      (¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0306 chi))) ∨
      (((Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0306 chi) ∨
      (Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0306 chi)) ∨
      ((Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0306 chi) ∨
      (Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0306 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0307 chi) ∨
      (¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0307 chi)) ∨
      ((¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0307 chi) ∨
      (¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0307 chi))) ∨
      (((Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0307 chi) ∨
      (Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0307 chi)) ∨
      ((Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0307 chi) ∨
      (Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0307 chi)))) ∨
      ((((¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0308 chi) ∨
      (¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0308 chi)) ∨
      ((¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0308 chi) ∨
      (¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0308 chi))) ∨
      (((Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0308 chi) ∨
      (Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0308 chi)) ∨
      ((Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0308 chi) ∨
      (Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0308 chi))))) ∨
      (((((¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0309 chi) ∨
      (¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0309 chi)) ∨
      ((¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0309 chi) ∨
      (¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0309 chi))) ∨
      (((Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0309 chi) ∨
      (Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0309 chi)) ∨
      ((Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0309 chi) ∨
      (Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0309 chi)))) ∨
      ((((¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0310 chi) ∨
      (¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0310 chi)) ∨
      ((¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0310 chi) ∨
      (¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0310 chi))) ∨
      (((Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0310 chi) ∨
      (Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0310 chi)) ∨
      ((Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0310 chi) ∨
      (Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0310 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0311 chi) ∨
      ((¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0311 chi) ∨
      (¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0311 chi))) ∨
      (((¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0311 chi) ∨
      (Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0311 chi)) ∨
      ((Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0311 chi) ∨
      (¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0312 chi)))) ∨
      ((((¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0312 chi) ∨
      (¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0312 chi)) ∨
      ((¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0312 chi) ∨
      (Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0312 chi))) ∨
      (((Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0312 chi) ∨
      (Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0312 chi)) ∨
      ((Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0312 chi) ∨
      (¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0313 chi))))) ∨
      (((((¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0313 chi) ∨
      (¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0313 chi)) ∨
      ((¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0313 chi) ∨
      (Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0313 chi))) ∨
      (((Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0313 chi) ∨
      (Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0313 chi)) ∨
      ((Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0313 chi) ∨
      (¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0314 chi)))) ∨
      ((((¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0314 chi) ∨
      (¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0314 chi)) ∨
      ((¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0314 chi) ∨
      (Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0314 chi))) ∨
      (((Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0314 chi) ∨
      (Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0314 chi)) ∨
      ((Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0314 chi) ∨
      (¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0315 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0315 chi) ∨
      (¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0315 chi)) ∨
      ((¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0315 chi) ∨
      (Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0315 chi))) ∨
      (((Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0315 chi) ∨
      (Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0315 chi)) ∨
      ((Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0315 chi) ∨
      (¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0316 chi)))) ∨
      ((((¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0316 chi) ∨
      (¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0316 chi)) ∨
      ((¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0316 chi) ∨
      (Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0316 chi))) ∨
      (((Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0316 chi) ∨
      (Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0316 chi)) ∨
      ((Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0316 chi) ∨
      (¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0318 chi))))) ∨
      (((((¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0318 chi) ∨
      (¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0318 chi)) ∨
      ((¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0318 chi) ∨
      (Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0318 chi))) ∨
      (((Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0318 chi) ∨
      (Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0318 chi)) ∨
      ((Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0318 chi) ∨
      (Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0319 chi)))) ∨
      ((((Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      Fin15AnchoredAtom0319 chi) ∨
      (¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0320 chi)) ∨
      ((¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0320 chi) ∨
      (¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      Fin15AnchoredAtom0320 chi))) ∨
      (((¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0320 chi) ∨
      (Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      Fin15AnchoredAtom0320 chi)) ∨
      ((Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0320 chi) ∨
      (Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      Fin15AnchoredAtom0320 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0321 chi) ∨
      ((¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0321 chi) ∨
      (¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0321 chi))) ∨
      (((¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0321 chi) ∨
      (Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0321 chi)) ∨
      ((Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0321 chi) ∨
      (Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0321 chi)))) ∨
      ((((Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0321 chi) ∨
      (¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0322 chi)) ∨
      ((¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0322 chi) ∨
      (¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0322 chi))) ∨
      (((¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0322 chi) ∨
      (Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0322 chi)) ∨
      ((Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0322 chi) ∨
      (Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0322 chi))))) ∨
      (((((Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0322 chi) ∨
      (¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0323 chi)) ∨
      ((¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0323 chi) ∨
      (¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0323 chi))) ∨
      (((¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0323 chi) ∨
      (Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0323 chi)) ∨
      ((Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0323 chi) ∨
      (Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0323 chi)))) ∨
      ((((Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0323 chi) ∨
      (¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0324 chi)) ∨
      ((¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0324 chi) ∨
      (¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0324 chi))) ∨
      (((¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0324 chi) ∨
      (Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0324 chi)) ∨
      ((Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0324 chi) ∨
      (Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0324 chi)))))) ∨
      ((((((Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0324 chi) ∨
      (¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0325 chi)) ∨
      ((¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0325 chi) ∨
      (¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0325 chi))) ∨
      (((¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0325 chi) ∨
      (Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0325 chi)) ∨
      ((Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0325 chi) ∨
      (Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0325 chi)))) ∨
      ((((Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0325 chi) ∨
      (¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0326 chi)) ∨
      ((¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0326 chi) ∨
      (¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0326 chi))) ∨
      (((¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0326 chi) ∨
      (Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0326 chi)) ∨
      ((Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0326 chi) ∨
      (Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0326 chi))))) ∨
      (((((Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0326 chi) ∨
      (¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0327 chi)) ∨
      ((¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0327 chi) ∨
      (¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0327 chi))) ∨
      (((¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0327 chi) ∨
      (Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0327 chi)) ∨
      ((Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0327 chi) ∨
      (Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0327 chi)))) ∨
      ((((Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0327 chi) ∨
      (¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0328 chi)) ∨
      ((¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0328 chi) ∨
      (¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0328 chi))) ∨
      (((¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0328 chi) ∨
      (Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0328 chi)) ∨
      ((Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0328 chi) ∨
      (Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0328 chi)))))))))) := by
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
                exact fin15Anchored_clause02523 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02524 chi hone hbad
                ·
                  exact fin15Anchored_clause02525 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02526 chi hone hbad
                ·
                  exact fin15Anchored_clause02527 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02528 chi hone hbad
                ·
                  exact fin15Anchored_clause02529 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02530 chi hone hbad
                ·
                  exact fin15Anchored_clause02531 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02532 chi hone hbad
                ·
                  exact fin15Anchored_clause02533 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02534 chi hone hbad
                ·
                  exact fin15Anchored_clause02535 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02536 chi hone hbad
                ·
                  exact fin15Anchored_clause02537 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02538 chi hone hbad
                ·
                  exact fin15Anchored_clause02539 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02540 chi hone hbad
                ·
                  exact fin15Anchored_clause02541 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02542 chi hone hbad
                ·
                  exact fin15Anchored_clause02543 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02544 chi hone hbad
                ·
                  exact fin15Anchored_clause02545 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02546 chi hone hbad
                ·
                  exact fin15Anchored_clause02547 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02548 chi hone hbad
                ·
                  exact fin15Anchored_clause02549 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02550 chi hone hbad
                ·
                  exact fin15Anchored_clause02551 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02552 chi hone hbad
                ·
                  exact fin15Anchored_clause02553 chi hone hbad
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
                  exact fin15Anchored_clause02554 chi hone hbad
                ·
                  exact fin15Anchored_clause02555 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02556 chi hone hbad
                ·
                  exact fin15Anchored_clause02557 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02558 chi hone hbad
                ·
                  exact fin15Anchored_clause02559 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02560 chi hone hbad
                ·
                  exact fin15Anchored_clause02561 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02562 chi hone hbad
                ·
                  exact fin15Anchored_clause02563 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02564 chi hone hbad
                ·
                  exact fin15Anchored_clause02565 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02566 chi hone hbad
                ·
                  exact fin15Anchored_clause02567 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02568 chi hone hbad
                ·
                  exact fin15Anchored_clause02569 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02570 chi hone hbad
                ·
                  exact fin15Anchored_clause02571 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02572 chi hone hbad
                ·
                  exact fin15Anchored_clause02573 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02574 chi hone hbad
                ·
                  exact fin15Anchored_clause02575 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02576 chi hone hbad
                ·
                  exact fin15Anchored_clause02577 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02578 chi hone hbad
                ·
                  exact fin15Anchored_clause02579 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02580 chi hone hbad
                ·
                  exact fin15Anchored_clause02581 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02582 chi hone hbad
                ·
                  exact fin15Anchored_clause02583 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02584 chi hone hbad
                ·
                  exact fin15Anchored_clause02585 chi hone hbad
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
                exact fin15Anchored_clause02586 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02587 chi hone hbad
                ·
                  exact fin15Anchored_clause02588 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02589 chi hone hbad
                ·
                  exact fin15Anchored_clause02590 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02591 chi hone hbad
                ·
                  exact fin15Anchored_clause02592 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02593 chi hone hbad
                ·
                  exact fin15Anchored_clause02594 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02595 chi hone hbad
                ·
                  exact fin15Anchored_clause02596 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02597 chi hone hbad
                ·
                  exact fin15Anchored_clause02598 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02599 chi hone hbad
                ·
                  exact fin15Anchored_clause02600 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02601 chi hone hbad
                ·
                  exact fin15Anchored_clause02602 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02603 chi hone hbad
                ·
                  exact fin15Anchored_clause02604 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02605 chi hone hbad
                ·
                  exact fin15Anchored_clause02606 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02607 chi hone hbad
                ·
                  exact fin15Anchored_clause02608 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02609 chi hone hbad
                ·
                  exact fin15Anchored_clause02610 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02611 chi hone hbad
                ·
                  exact fin15Anchored_clause02612 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02613 chi hone hbad
                ·
                  exact fin15Anchored_clause02614 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02615 chi hone hbad
                ·
                  exact fin15Anchored_clause02616 chi hone hbad
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
                  exact fin15Anchored_clause02617 chi hone hbad
                ·
                  exact fin15Anchored_clause02618 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02619 chi hone hbad
                ·
                  exact fin15Anchored_clause02620 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02621 chi hone hbad
                ·
                  exact fin15Anchored_clause02622 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02623 chi hone hbad
                ·
                  exact fin15Anchored_clause02624 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02625 chi hone hbad
                ·
                  exact fin15Anchored_clause02626 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02627 chi hone hbad
                ·
                  exact fin15Anchored_clause02628 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02629 chi hone hbad
                ·
                  exact fin15Anchored_clause02630 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02631 chi hone hbad
                ·
                  exact fin15Anchored_clause02632 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02633 chi hone hbad
                ·
                  exact fin15Anchored_clause02634 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02635 chi hone hbad
                ·
                  exact fin15Anchored_clause02636 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02637 chi hone hbad
                ·
                  exact fin15Anchored_clause02638 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02639 chi hone hbad
                ·
                  exact fin15Anchored_clause02640 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02641 chi hone hbad
                ·
                  exact fin15Anchored_clause02642 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02643 chi hone hbad
                ·
                  exact fin15Anchored_clause02644 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02645 chi hone hbad
                ·
                  exact fin15Anchored_clause02646 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02647 chi hone hbad
                ·
                  exact fin15Anchored_clause02648 chi hone hbad
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
                exact fin15Anchored_clause02649 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02650 chi hone hbad
                ·
                  exact fin15Anchored_clause02651 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02652 chi hone hbad
                ·
                  exact fin15Anchored_clause02653 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02654 chi hone hbad
                ·
                  exact fin15Anchored_clause02655 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02656 chi hone hbad
                ·
                  exact fin15Anchored_clause02657 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02658 chi hone hbad
                ·
                  exact fin15Anchored_clause02659 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02660 chi hone hbad
                ·
                  exact fin15Anchored_clause02661 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02662 chi hone hbad
                ·
                  exact fin15Anchored_clause02663 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02664 chi hone hbad
                ·
                  exact fin15Anchored_clause02665 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02666 chi hone hbad
                ·
                  exact fin15Anchored_clause02667 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02668 chi hone hbad
                ·
                  exact fin15Anchored_clause02669 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02670 chi hone hbad
                ·
                  exact fin15Anchored_clause02671 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02672 chi hone hbad
                ·
                  exact fin15Anchored_clause02673 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02674 chi hone hbad
                ·
                  exact fin15Anchored_clause02675 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02676 chi hone hbad
                ·
                  exact fin15Anchored_clause02677 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02678 chi hone hbad
                ·
                  exact fin15Anchored_clause02679 chi hone hbad
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
                  exact fin15Anchored_clause02680 chi hone hbad
                ·
                  exact fin15Anchored_clause02681 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02682 chi hone hbad
                ·
                  exact fin15Anchored_clause02683 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02684 chi hone hbad
                ·
                  exact fin15Anchored_clause02685 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02686 chi hone hbad
                ·
                  exact fin15Anchored_clause02687 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02688 chi hone hbad
                ·
                  exact fin15Anchored_clause02689 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02690 chi hone hbad
                ·
                  exact fin15Anchored_clause02691 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02692 chi hone hbad
                ·
                  exact fin15Anchored_clause02693 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02694 chi hone hbad
                ·
                  exact fin15Anchored_clause02695 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02696 chi hone hbad
                ·
                  exact fin15Anchored_clause02697 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02698 chi hone hbad
                ·
                  exact fin15Anchored_clause02699 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02700 chi hone hbad
                ·
                  exact fin15Anchored_clause02701 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02702 chi hone hbad
                ·
                  exact fin15Anchored_clause02703 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02704 chi hone hbad
                ·
                  exact fin15Anchored_clause02705 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02706 chi hone hbad
                ·
                  exact fin15Anchored_clause02707 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02708 chi hone hbad
                ·
                  exact fin15Anchored_clause02709 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02710 chi hone hbad
                ·
                  exact fin15Anchored_clause02711 chi hone hbad
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
                exact fin15Anchored_clause02712 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02713 chi hone hbad
                ·
                  exact fin15Anchored_clause02714 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02715 chi hone hbad
                ·
                  exact fin15Anchored_clause02716 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02717 chi hone hbad
                ·
                  exact fin15Anchored_clause02718 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02719 chi hone hbad
                ·
                  exact fin15Anchored_clause02720 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02721 chi hone hbad
                ·
                  exact fin15Anchored_clause02722 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02723 chi hone hbad
                ·
                  exact fin15Anchored_clause02724 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02725 chi hone hbad
                ·
                  exact fin15Anchored_clause02726 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02727 chi hone hbad
                ·
                  exact fin15Anchored_clause02728 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02729 chi hone hbad
                ·
                  exact fin15Anchored_clause02730 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02731 chi hone hbad
                ·
                  exact fin15Anchored_clause02732 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02733 chi hone hbad
                ·
                  exact fin15Anchored_clause02734 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02735 chi hone hbad
                ·
                  exact fin15Anchored_clause02736 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02737 chi hone hbad
                ·
                  exact fin15Anchored_clause02738 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02739 chi hone hbad
                ·
                  exact fin15Anchored_clause02740 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02741 chi hone hbad
                ·
                  exact fin15Anchored_clause02742 chi hone hbad
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
                  exact fin15Anchored_clause02743 chi hone hbad
                ·
                  exact fin15Anchored_clause02744 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02745 chi hone hbad
                ·
                  exact fin15Anchored_clause02746 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02747 chi hone hbad
                ·
                  exact fin15Anchored_clause02748 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02749 chi hone hbad
                ·
                  exact fin15Anchored_clause02750 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02751 chi hone hbad
                ·
                  exact fin15Anchored_clause02752 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02753 chi hone hbad
                ·
                  exact fin15Anchored_clause02754 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02755 chi hone hbad
                ·
                  exact fin15Anchored_clause02756 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02757 chi hone hbad
                ·
                  exact fin15Anchored_clause02758 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02759 chi hone hbad
                ·
                  exact fin15Anchored_clause02760 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02761 chi hone hbad
                ·
                  exact fin15Anchored_clause02762 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02763 chi hone hbad
                ·
                  exact fin15Anchored_clause02764 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02765 chi hone hbad
                ·
                  exact fin15Anchored_clause02766 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02767 chi hone hbad
                ·
                  exact fin15Anchored_clause02768 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02769 chi hone hbad
                ·
                  exact fin15Anchored_clause02770 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02771 chi hone hbad
                ·
                  exact fin15Anchored_clause02772 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause02773 chi hone hbad
                ·
                  exact fin15Anchored_clause02774 chi hone hbad

end ErdosSzekeres

end
