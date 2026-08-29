module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk036

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 047. -/

theorem predecessorHalfFin13_rejectSemanticSegment047
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0818 chi) ∨
      ((PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0818 chi) ∨
      (PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0818 chi))) ∨
      ((PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0818 chi) ∨
      ((PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0818 chi) ∨
      (¬PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi) ∨
      ((¬PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0230 chi) ∨
      (¬PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi))) ∨
      ((PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0230 chi) ∨
      ((PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi) ∨
      (PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0230 chi))))) ∨
      ((((PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0230 chi) ∨
      ((¬PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0819 chi) ∨
      (¬PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0819 chi))) ∨
      ((¬PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0819 chi) ∨
      ((¬PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0819 chi) ∨
      (PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0819 chi)))) ∨
      (((PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0819 chi) ∨
      ((PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0819 chi) ∨
      (PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0819 chi))) ∨
      ((PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0819 chi) ∨
      ((¬PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0231 chi) ∨
      (¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0231 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0231 chi) ∨
      ((¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0231 chi) ∨
      (PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0231 chi))) ∨
      ((PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0231 chi) ∨
      ((PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0231 chi) ∨
      (PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0231 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0820 chi) ∨
      ((¬PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0820 chi) ∨
      (¬PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0820 chi))) ∨
      ((¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0820 chi) ∨
      ((PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0820 chi) ∨
      (PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0820 chi))))) ∨
      ((((PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0820 chi) ∨
      ((PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0820 chi) ∨
      (PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0820 chi))) ∨
      ((¬PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0232 chi) ∨
      ((¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0232 chi) ∨
      (¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0232 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0232 chi) ∨
      ((PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0232 chi) ∨
      (PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0232 chi))) ∨
      (((PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0232 chi) ∨
      (PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0232 chi)) ∨
      ((¬PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0821 chi) ∨
      (¬PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0821 chi))))))) ∨
      ((((((¬PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0821 chi) ∨
      ((¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0821 chi) ∨
      (¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0821 chi))) ∨
      ((¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0821 chi) ∨
      ((PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0821 chi) ∨
      (PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0821 chi)))) ∨
      (((PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0821 chi) ∨
      ((PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0821 chi) ∨
      (PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0821 chi))) ∨
      ((¬PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi) ∨
      ((¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi) ∨
      (¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0233 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi) ∨
      ((PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0233 chi) ∨
      (PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi))) ∨
      ((PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0233 chi) ∨
      ((PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0233 chi) ∨
      (¬PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0822 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0822 chi) ∨
      ((¬PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0822 chi) ∨
      (¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0822 chi))) ∨
      (((PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0822 chi) ∨
      (PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0822 chi)) ∨
      ((PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0822 chi) ∨
      (PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0822 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0822 chi) ∨
      ((¬PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi) ∨
      (¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi))) ∨
      ((¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0234 chi) ∨
      ((¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi) ∨
      (PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0234 chi)))) ∨
      (((PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi) ∨
      ((PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0234 chi) ∨
      (PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0234 chi))) ∨
      ((¬PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0823 chi) ∨
      ((¬PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0823 chi) ∨
      (¬PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0823 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0823 chi) ∨
      ((¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0823 chi) ∨
      (¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0823 chi))) ∨
      ((PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0823 chi) ∨
      ((PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0823 chi) ∨
      (PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0823 chi)))) ∨
      (((PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0823 chi) ∨
      ((¬PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi) ∨
      (¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi))) ∨
      (((¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0235 chi) ∨
      (¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi)) ∨
      ((PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0235 chi) ∨
      (PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi))))))))) := by
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
              exact predecessorHalfFin13_clause12761 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12762 chi hbad
              ·
                exact predecessorHalfFin13_clause12765 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12767 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12768 chi hbad
              ·
                exact predecessorHalfFin13_clause12769 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12770 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12771 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12772 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12773 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12774 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12775 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12776 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12777 chi hbad
              ·
                exact predecessorHalfFin13_clause12778 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12780 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12784 chi hbad
              ·
                exact predecessorHalfFin13_clause12785 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12786 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12789 chi hbad
              ·
                exact predecessorHalfFin13_clause12791 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12792 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12793 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12794 chi hone hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12795 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12796 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12797 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12798 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12799 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12800 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12801 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12802 chi hbad
              ·
                exact predecessorHalfFin13_clause12804 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12808 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12809 chi hbad
              ·
                exact predecessorHalfFin13_clause12813 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12814 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12815 chi hbad
              ·
                exact predecessorHalfFin13_clause12816 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12817 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12818 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12819 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12820 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12821 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12822 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12823 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12824 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12825 chi hbad
              ·
                exact predecessorHalfFin13_clause12826 chi hbad
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
              exact predecessorHalfFin13_clause12828 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12830 chi hbad
              ·
                exact predecessorHalfFin13_clause12831 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12832 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12833 chi hbad
              ·
                exact predecessorHalfFin13_clause12837 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12838 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12839 chi hbad
              ·
                exact predecessorHalfFin13_clause12840 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12841 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12842 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12843 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12844 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12845 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12846 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12847 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12848 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12849 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12850 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12852 chi hbad
              ·
                exact predecessorHalfFin13_clause12856 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12857 chi hbad
              ·
                exact predecessorHalfFin13_clause12859 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12861 chi hbad
              ·
                exact predecessorHalfFin13_clause12863 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12864 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12865 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12866 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12867 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12868 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12869 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12870 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12871 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12872 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12873 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12874 chi hbad
              ·
                exact predecessorHalfFin13_clause12876 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12878 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12879 chi hbad
              ·
                exact predecessorHalfFin13_clause12880 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12881 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12885 chi hbad
              ·
                exact predecessorHalfFin13_clause12887 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12888 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12889 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12890 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12891 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12892 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12893 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12894 chi hone hbad

end ErdosSzekeres

end
