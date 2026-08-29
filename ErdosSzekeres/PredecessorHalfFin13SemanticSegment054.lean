module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk041
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk042

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 054. -/

theorem predecessorHalfFin13_rejectSemanticSegment054
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0857 chi) ∨
      ((PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0857 chi) ∨
      (PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0857 chi))) ∨
      ((¬PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi) ∨
      ((¬PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi) ∨
      (¬PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0269 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi) ∨
      ((PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0269 chi) ∨
      (PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi))) ∨
      ((PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0269 chi) ∨
      ((PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0269 chi) ∨
      (¬PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0858 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0858 chi) ∨
      ((¬PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0858 chi) ∨
      (¬PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0858 chi))) ∨
      ((¬PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0858 chi) ∨
      ((PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0858 chi) ∨
      (PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0858 chi)))) ∨
      (((PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0858 chi) ∨
      ((PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0858 chi) ∨
      (PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0858 chi))) ∨
      ((¬PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi) ∨
      ((¬PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi) ∨
      (¬PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0270 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi) ∨
      ((PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0270 chi) ∨
      (PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi))) ∨
      ((PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0270 chi) ∨
      ((PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0270 chi) ∨
      (¬PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0859 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0859 chi) ∨
      ((¬PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0859 chi) ∨
      (¬PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0859 chi))) ∨
      ((¬PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0859 chi) ∨
      ((¬PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0859 chi) ∨
      (PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0859 chi))))) ∨
      ((((PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0859 chi) ∨
      ((PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0859 chi) ∨
      (PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0859 chi))) ∨
      ((PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0859 chi) ∨
      ((¬PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi) ∨
      (¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0271 chi) ∨
      ((¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi) ∨
      (PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0271 chi))) ∨
      (((PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi) ∨
      (PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0271 chi)) ∨
      ((PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0271 chi) ∨
      (¬PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0860 chi))))))) ∨
      ((((((¬PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0860 chi) ∨
      ((¬PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0860 chi) ∨
      (¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0860 chi))) ∨
      ((PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0860 chi) ∨
      ((PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0860 chi) ∨
      (PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0860 chi)))) ∨
      (((PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0860 chi) ∨
      ((¬PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi) ∨
      (¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi))) ∨
      ((¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0272 chi) ∨
      ((¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi) ∨
      (PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0272 chi))))) ∨
      ((((PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi) ∨
      ((PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0272 chi) ∨
      (PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0272 chi))) ∨
      ((¬PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0861 chi) ∨
      ((¬PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0861 chi) ∨
      (¬PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0861 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0861 chi) ∨
      ((¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0861 chi) ∨
      (¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0861 chi))) ∨
      ((PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0861 chi) ∨
      ((PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0861 chi) ∨
      (PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0861 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0861 chi) ∨
      ((¬PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi) ∨
      (¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi))) ∨
      ((¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0273 chi) ∨
      ((¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi) ∨
      (PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0273 chi)))) ∨
      (((PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi) ∨
      ((PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0273 chi) ∨
      (PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0273 chi))) ∨
      ((¬PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0862 chi) ∨
      ((¬PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0862 chi) ∨
      (¬PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0862 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0862 chi) ∨
      ((¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0862 chi) ∨
      (PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0862 chi))) ∨
      ((PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0862 chi) ∨
      ((PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0862 chi) ∨
      (PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0862 chi)))) ∨
      (((PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0862 chi) ∨
      ((¬PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi) ∨
      (¬PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi))) ∨
      (((¬PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0274 chi) ∨
      (¬PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi)) ∨
      ((PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0274 chi) ∨
      (PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi))))))))) := by
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
              exact predecessorHalfFin13_clause13702 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13703 chi hbad
              ·
                exact predecessorHalfFin13_clause13704 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13705 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13706 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13707 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13708 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13709 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13710 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13711 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13712 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13713 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13714 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13716 chi hbad
              ·
                exact predecessorHalfFin13_clause13719 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13720 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13721 chi hbad
              ·
                exact predecessorHalfFin13_clause13722 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13725 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13727 chi hbad
              ·
                exact predecessorHalfFin13_clause13728 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13729 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13730 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13731 chi hone hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13732 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13733 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13734 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13735 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13736 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13737 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13738 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13740 chi hbad
              ·
                exact predecessorHalfFin13_clause13742 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13743 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13744 chi hbad
              ·
                exact predecessorHalfFin13_clause13745 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13746 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13749 chi hbad
              ·
                exact predecessorHalfFin13_clause13751 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13752 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13753 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13754 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13755 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13756 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13757 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13758 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13759 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13760 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13761 chi hbad
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
              exact predecessorHalfFin13_clause13762 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13764 chi hbad
              ·
                exact predecessorHalfFin13_clause13768 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13769 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13773 chi hbad
              ·
                exact predecessorHalfFin13_clause13775 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13776 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13777 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13778 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13779 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13780 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13781 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13782 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13783 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13784 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13785 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13786 chi hbad
              ·
                exact predecessorHalfFin13_clause13788 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13789 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13791 chi hbad
              ·
                exact predecessorHalfFin13_clause13792 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13793 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13797 chi hbad
              ·
                exact predecessorHalfFin13_clause13799 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13800 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13801 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13802 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13803 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13804 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13805 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13806 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13807 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13808 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13809 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13810 chi hbad
              ·
                exact predecessorHalfFin13_clause13812 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13814 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13816 chi hbad
              ·
                exact predecessorHalfFin13_clause13817 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13818 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13821 chi hbad
              ·
                exact predecessorHalfFin13_clause13823 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13824 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13825 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13826 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13827 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13828 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13829 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13830 chi hone hbad

end ErdosSzekeres

end
