module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk034
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk035

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 045. -/

theorem predecessorHalfFin13_rejectSemanticSegment045
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0218 chi) ∨
      ((PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0218 chi) ∨
      (¬PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0807 chi))) ∨
      ((¬PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0807 chi) ∨
      ((¬PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0807 chi) ∨
      (¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0807 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0807 chi) ∨
      ((¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0807 chi) ∨
      (PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0807 chi))) ∨
      ((PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0807 chi) ∨
      ((PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0807 chi) ∨
      (PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0807 chi))))) ∨
      ((((PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0807 chi) ∨
      ((¬PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi) ∨
      (¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi))) ∨
      ((¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0219 chi) ∨
      ((¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi) ∨
      (PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0219 chi)))) ∨
      (((PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi) ∨
      ((PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0219 chi) ∨
      (PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0219 chi))) ∨
      ((¬PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0808 chi) ∨
      ((¬PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0808 chi) ∨
      (¬PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0808 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0808 chi) ∨
      ((¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0808 chi) ∨
      (¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0808 chi))) ∨
      ((PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0808 chi) ∨
      ((PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0808 chi) ∨
      (PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0808 chi)))) ∨
      (((PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0808 chi) ∨
      ((¬PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi) ∨
      (¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi))) ∨
      ((¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0220 chi) ∨
      ((¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi) ∨
      (PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0220 chi))))) ∨
      ((((PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi) ∨
      ((PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0220 chi) ∨
      (PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0220 chi))) ∨
      ((¬PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0809 chi) ∨
      ((¬PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0809 chi) ∨
      (¬PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0809 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0809 chi) ∨
      ((PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0809 chi) ∨
      (PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0809 chi))) ∨
      (((PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0809 chi) ∨
      (PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0809 chi)) ∨
      ((¬PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi) ∨
      (¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi))))))) ∨
      ((((((¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0221 chi) ∨
      ((¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi) ∨
      (PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0221 chi))) ∨
      ((PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi) ∨
      ((PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0221 chi) ∨
      (PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0221 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0810 chi) ∨
      ((¬PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0810 chi) ∨
      (¬PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0810 chi))) ∨
      ((¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0810 chi) ∨
      ((PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0810 chi) ∨
      (PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0810 chi))))) ∨
      ((((PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0810 chi) ∨
      ((PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0810 chi) ∨
      (¬PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi))) ∨
      ((¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi) ∨
      ((¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0222 chi) ∨
      (¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi)))) ∨
      (((PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0222 chi) ∨
      ((PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi) ∨
      (PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0222 chi))) ∨
      (((PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0222 chi) ∨
      (¬PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0811 chi)) ∨
      ((¬PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0811 chi) ∨
      (¬PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0811 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0811 chi) ∨
      ((PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0811 chi) ∨
      (PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0811 chi))) ∨
      ((PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0811 chi) ∨
      ((PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0811 chi) ∨
      (¬PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi) ∨
      ((¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0223 chi) ∨
      (¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi))) ∨
      ((PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0223 chi) ∨
      ((PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi) ∨
      (PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0223 chi))))) ∨
      ((((PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0223 chi) ∨
      ((¬PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0812 chi) ∨
      (¬PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0812 chi))) ∨
      ((¬PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0812 chi) ∨
      ((¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0812 chi) ∨
      (PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0812 chi)))) ∨
      (((PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0812 chi) ∨
      ((PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0812 chi) ∨
      (PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0812 chi))) ∨
      (((PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0812 chi) ∨
      (PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0812 chi)) ∨
      ((¬PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi) ∨
      (¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi))))))))) := by
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
              exact predecessorHalfFin13_clause12487 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12488 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12489 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12490 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12492 chi hbad
              ·
                exact predecessorHalfFin13_clause12493 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12495 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12496 chi hbad
              ·
                exact predecessorHalfFin13_clause12497 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12498 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12501 chi hbad
              ·
                exact predecessorHalfFin13_clause12503 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12504 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12505 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12506 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12507 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12508 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12509 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12510 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12511 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12512 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12513 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12514 chi hbad
              ·
                exact predecessorHalfFin13_clause12516 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12517 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12519 chi hbad
              ·
                exact predecessorHalfFin13_clause12520 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12521 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12525 chi hbad
              ·
                exact predecessorHalfFin13_clause12527 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12528 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12529 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12530 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12531 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12532 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12533 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12534 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12535 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12536 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12537 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12538 chi hbad
              ·
                exact predecessorHalfFin13_clause12540 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12544 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12545 chi hbad
              ·
                exact predecessorHalfFin13_clause12549 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12551 chi hbad
              ·
                exact predecessorHalfFin13_clause12552 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12553 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12554 chi hone hbad
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
              exact predecessorHalfFin13_clause12555 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12556 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12557 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12558 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12559 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12560 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12561 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12562 chi hbad
              ·
                exact predecessorHalfFin13_clause12564 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12568 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12569 chi hbad
              ·
                exact predecessorHalfFin13_clause12573 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12575 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12576 chi hbad
              ·
                exact predecessorHalfFin13_clause12577 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12578 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12579 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12580 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12581 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12582 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12583 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12584 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12585 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12586 chi hbad
              ·
                exact predecessorHalfFin13_clause12588 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12592 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12593 chi hbad
              ·
                exact predecessorHalfFin13_clause12597 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12599 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12600 chi hbad
              ·
                exact predecessorHalfFin13_clause12601 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12602 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12603 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12604 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12605 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12606 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12607 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12608 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12609 chi hbad
              ·
                exact predecessorHalfFin13_clause12610 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12612 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12616 chi hbad
              ·
                exact predecessorHalfFin13_clause12617 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12618 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12621 chi hbad
              ·
                exact predecessorHalfFin13_clause12622 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12623 chi hbad
              ·
                exact predecessorHalfFin13_clause12624 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12625 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12626 chi hone hbad

end ErdosSzekeres

end
