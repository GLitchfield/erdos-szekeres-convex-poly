module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk036
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk037

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 048. -/

theorem predecessorHalfFin13_rejectSemanticSegment048
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0235 chi) ∨
      ((PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0235 chi) ∨
      (¬PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0824 chi))) ∨
      ((¬PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0824 chi) ∨
      ((¬PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0824 chi) ∨
      (¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0824 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0824 chi) ∨
      ((¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0824 chi) ∨
      (PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0824 chi))) ∨
      ((PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0824 chi) ∨
      ((PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0824 chi) ∨
      (PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0824 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi) ∨
      ((¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi) ∨
      (¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0236 chi))) ∨
      ((¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi) ∨
      ((PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0236 chi) ∨
      (PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi)))) ∨
      (((PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0236 chi) ∨
      ((PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0236 chi) ∨
      (¬PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0825 chi))) ∨
      ((¬PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0825 chi) ∨
      ((¬PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0825 chi) ∨
      (¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0825 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0825 chi) ∨
      ((PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0825 chi) ∨
      (PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0825 chi))) ∨
      ((PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0825 chi) ∨
      ((PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0825 chi) ∨
      (PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0825 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0237 chi) ∨
      ((¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0237 chi) ∨
      (¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0237 chi))) ∨
      ((¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0237 chi) ∨
      ((PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0237 chi) ∨
      (PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0237 chi))))) ∨
      ((((PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0237 chi) ∨
      ((PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0237 chi) ∨
      (¬PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0826 chi))) ∨
      ((¬PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0826 chi) ∨
      ((¬PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0826 chi) ∨
      (¬PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0826 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0826 chi) ∨
      ((¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0826 chi) ∨
      (¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0826 chi))) ∨
      (((PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0826 chi) ∨
      (PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0826 chi)) ∨
      ((PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0826 chi) ∨
      (PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0826 chi))))))) ∨
      ((((((¬PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi) ∨
      ((¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi) ∨
      (¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0238 chi))) ∨
      ((¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi) ∨
      ((PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0238 chi) ∨
      (PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi)))) ∨
      (((PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0238 chi) ∨
      ((PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0238 chi) ∨
      (¬PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      ¬PredecessorHalfFin13Atom0827 chi))) ∨
      ((¬PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0827 chi) ∨
      ((¬PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      ¬PredecessorHalfFin13Atom0827 chi) ∨
      (¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0827 chi))))) ∨
      ((((PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0827 chi) ∨
      ((PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      ¬PredecessorHalfFin13Atom0827 chi) ∨
      (PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0827 chi))) ∨
      ((PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      ¬PredecessorHalfFin13Atom0827 chi) ∨
      ((¬PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi) ∨
      (¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0239 chi) ∨
      ((¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi) ∨
      (PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0239 chi))) ∨
      ((PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi) ∨
      ((PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0239 chi) ∨
      (PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0239 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0828 chi) ∨
      ((¬PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0828 chi) ∨
      (¬PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0828 chi))) ∨
      ((¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0828 chi) ∨
      ((¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0828 chi) ∨
      (PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0828 chi)))) ∨
      (((PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0828 chi) ∨
      ((PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0828 chi) ∨
      (PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0828 chi))) ∨
      ((¬PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0240 chi) ∨
      ((¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0240 chi) ∨
      (¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0240 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0240 chi) ∨
      ((PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0240 chi) ∨
      (PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0240 chi))) ∨
      ((PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0240 chi) ∨
      ((PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0240 chi) ∨
      (¬PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0240 chi ∧
      ¬PredecessorHalfFin13Atom0829 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0240 chi ∧
      PredecessorHalfFin13Atom0829 chi) ∨
      ((¬PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0240 chi ∧
      ¬PredecessorHalfFin13Atom0829 chi) ∨
      (¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0240 chi ∧
      PredecessorHalfFin13Atom0829 chi))) ∨
      (((¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0240 chi ∧
      PredecessorHalfFin13Atom0829 chi) ∨
      (¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0240 chi ∧
      PredecessorHalfFin13Atom0829 chi)) ∨
      ((¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0240 chi ∧
      PredecessorHalfFin13Atom0829 chi) ∨
      (PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0240 chi ∧
      PredecessorHalfFin13Atom0829 chi))))))))) := by
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
              exact predecessorHalfFin13_clause12895 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12896 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12897 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12898 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12900 chi hbad
              ·
                exact predecessorHalfFin13_clause12902 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12903 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12904 chi hbad
              ·
                exact predecessorHalfFin13_clause12905 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12909 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12911 chi hbad
              ·
                exact predecessorHalfFin13_clause12912 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12913 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12914 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12915 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12916 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12917 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12918 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12919 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12920 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12921 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12922 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12924 chi hbad
              ·
                exact predecessorHalfFin13_clause12926 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12928 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12929 chi hbad
              ·
                exact predecessorHalfFin13_clause12930 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12933 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12935 chi hbad
              ·
                exact predecessorHalfFin13_clause12936 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12937 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12938 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12939 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12940 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12941 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12942 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12943 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12944 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12945 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12946 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12947 chi hbad
              ·
                exact predecessorHalfFin13_clause12948 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12949 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12951 chi hbad
              ·
                exact predecessorHalfFin13_clause12952 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12953 chi hbad
              ·
                exact predecessorHalfFin13_clause12957 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12959 chi hbad
              ·
                exact predecessorHalfFin13_clause12960 chi hbad
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
              exact predecessorHalfFin13_clause12961 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12962 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12963 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12964 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12965 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12966 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12967 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12968 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12969 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12970 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12972 chi hbad
              ·
                exact predecessorHalfFin13_clause12976 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12977 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12981 chi hbad
              ·
                exact predecessorHalfFin13_clause12983 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12984 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12985 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12986 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12987 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12988 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12989 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12990 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12991 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12992 chi hone hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12993 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12994 chi hbad
              ·
                exact predecessorHalfFin13_clause12996 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12999 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13000 chi hbad
              ·
                exact predecessorHalfFin13_clause13001 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13005 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13007 chi hbad
              ·
                exact predecessorHalfFin13_clause13008 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13009 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13010 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13011 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13012 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13013 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13014 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13015 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13016 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13017 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13018 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13020 chi hbad
              ·
                exact predecessorHalfFin13_clause13021 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13022 chi hbad
              ·
                exact predecessorHalfFin13_clause13023 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13024 chi hbad
              ·
                exact predecessorHalfFin13_clause13025 chi hbad

end ErdosSzekeres

end
