module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk060
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk061

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 079. -/

theorem predecessorHalfFin13_rejectSemanticSegment079
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((¬PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0999 chi) ∨
      ((¬PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0999 chi) ∨
      (PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0999 chi))) ∨
      ((PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0999 chi) ∨
      ((PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0999 chi) ∨
      (PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0999 chi)))) ∨
      (((PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0999 chi) ∨
      ((¬PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) ∨
      (¬PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi))) ∨
      ((¬PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0286 chi) ∨
      ((¬PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) ∨
      (PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0286 chi))))) ∨
      ((((PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) ∨
      ((PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0286 chi) ∨
      (PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0286 chi))) ∨
      ((¬PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom1000 chi) ∨
      ((¬PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom1000 chi) ∨
      (¬PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom1000 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom1000 chi) ∨
      ((PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom1000 chi) ∨
      (PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom1000 chi))) ∨
      ((PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom1000 chi) ∨
      ((PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom1000 chi) ∨
      (¬PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) ∨
      ((¬PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0286 chi) ∨
      (¬PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi))) ∨
      ((PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0286 chi) ∨
      ((PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) ∨
      (PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0286 chi)))) ∨
      (((PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0286 chi) ∨
      ((¬PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom1001 chi) ∨
      (¬PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom1001 chi))) ∨
      ((¬PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom1001 chi) ∨
      ((¬PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom1001 chi) ∨
      (¬PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom1001 chi))))) ∨
      ((((PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom1001 chi) ∨
      ((PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom1001 chi) ∨
      (PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom1001 chi))) ∨
      ((PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom1001 chi) ∨
      ((PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom1001 chi) ∨
      (PredecessorHalfFin13Atom1167 chi ∧
      ¬PredecessorHalfFin13Atom0342 chi)))) ∨
      (((PredecessorHalfFin13Atom1167 chi ∧
      ¬PredecessorHalfFin13Atom0343 chi) ∨
      ((PredecessorHalfFin13Atom1167 chi ∧
      ¬PredecessorHalfFin13Atom0351 chi) ∨
      (PredecessorHalfFin13Atom1167 chi ∧
      ¬PredecessorHalfFin13Atom0387 chi))) ∨
      (((PredecessorHalfFin13Atom1167 chi ∧
      ¬PredecessorHalfFin13Atom0672 chi) ∨
      (¬PredecessorHalfFin13Atom1167 chi ∧
      PredecessorHalfFin13Atom0342 chi ∧
      PredecessorHalfFin13Atom0343 chi ∧
      PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0672 chi)) ∨
      ((PredecessorHalfFin13Atom1168 chi ∧
      ¬PredecessorHalfFin13Atom0342 chi) ∨
      (PredecessorHalfFin13Atom1168 chi ∧
      ¬PredecessorHalfFin13Atom0344 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom1168 chi ∧
      ¬PredecessorHalfFin13Atom0352 chi) ∨
      ((PredecessorHalfFin13Atom1168 chi ∧
      ¬PredecessorHalfFin13Atom0388 chi) ∨
      (PredecessorHalfFin13Atom1168 chi ∧
      ¬PredecessorHalfFin13Atom0673 chi))) ∨
      ((¬PredecessorHalfFin13Atom1168 chi ∧
      PredecessorHalfFin13Atom0342 chi ∧
      PredecessorHalfFin13Atom0344 chi ∧
      PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0673 chi) ∨
      ((PredecessorHalfFin13Atom1169 chi ∧
      ¬PredecessorHalfFin13Atom0342 chi) ∨
      (PredecessorHalfFin13Atom1169 chi ∧
      ¬PredecessorHalfFin13Atom0345 chi)))) ∨
      (((PredecessorHalfFin13Atom1169 chi ∧
      ¬PredecessorHalfFin13Atom0353 chi) ∨
      ((PredecessorHalfFin13Atom1169 chi ∧
      ¬PredecessorHalfFin13Atom0389 chi) ∨
      (PredecessorHalfFin13Atom1169 chi ∧
      ¬PredecessorHalfFin13Atom0674 chi))) ∨
      ((¬PredecessorHalfFin13Atom1169 chi ∧
      PredecessorHalfFin13Atom0342 chi ∧
      PredecessorHalfFin13Atom0345 chi ∧
      PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0674 chi) ∨
      ((PredecessorHalfFin13Atom1170 chi ∧
      ¬PredecessorHalfFin13Atom0342 chi) ∨
      (PredecessorHalfFin13Atom1170 chi ∧
      ¬PredecessorHalfFin13Atom0346 chi))))) ∨
      ((((PredecessorHalfFin13Atom1170 chi ∧
      ¬PredecessorHalfFin13Atom0354 chi) ∨
      ((PredecessorHalfFin13Atom1170 chi ∧
      ¬PredecessorHalfFin13Atom0390 chi) ∨
      (PredecessorHalfFin13Atom1170 chi ∧
      ¬PredecessorHalfFin13Atom0675 chi))) ∨
      ((PredecessorHalfFin13Atom1171 chi ∧
      ¬PredecessorHalfFin13Atom0342 chi) ∨
      ((PredecessorHalfFin13Atom1171 chi ∧
      ¬PredecessorHalfFin13Atom0347 chi) ∨
      (PredecessorHalfFin13Atom1171 chi ∧
      ¬PredecessorHalfFin13Atom0355 chi)))) ∨
      (((PredecessorHalfFin13Atom1171 chi ∧
      ¬PredecessorHalfFin13Atom0391 chi) ∨
      ((PredecessorHalfFin13Atom1171 chi ∧
      ¬PredecessorHalfFin13Atom0676 chi) ∨
      (¬PredecessorHalfFin13Atom1171 chi ∧
      PredecessorHalfFin13Atom0342 chi ∧
      PredecessorHalfFin13Atom0347 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0676 chi))) ∨
      (((PredecessorHalfFin13Atom1172 chi ∧
      ¬PredecessorHalfFin13Atom0342 chi) ∨
      (PredecessorHalfFin13Atom1172 chi ∧
      ¬PredecessorHalfFin13Atom0348 chi)) ∨
      ((PredecessorHalfFin13Atom1172 chi ∧
      ¬PredecessorHalfFin13Atom0356 chi) ∨
      (PredecessorHalfFin13Atom1172 chi ∧
      ¬PredecessorHalfFin13Atom0392 chi)))))) ∨
      (((((PredecessorHalfFin13Atom1172 chi ∧
      ¬PredecessorHalfFin13Atom0677 chi) ∨
      ((¬PredecessorHalfFin13Atom1172 chi ∧
      PredecessorHalfFin13Atom0342 chi ∧
      PredecessorHalfFin13Atom0348 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0677 chi) ∨
      (PredecessorHalfFin13Atom1174 chi ∧
      ¬PredecessorHalfFin13Atom0342 chi))) ∨
      ((PredecessorHalfFin13Atom1174 chi ∧
      ¬PredecessorHalfFin13Atom0350 chi) ∨
      ((PredecessorHalfFin13Atom1174 chi ∧
      ¬PredecessorHalfFin13Atom0358 chi) ∨
      (PredecessorHalfFin13Atom1174 chi ∧
      ¬PredecessorHalfFin13Atom0394 chi)))) ∨
      (((PredecessorHalfFin13Atom1174 chi ∧
      ¬PredecessorHalfFin13Atom0679 chi) ∨
      ((¬PredecessorHalfFin13Atom1174 chi ∧
      PredecessorHalfFin13Atom0342 chi ∧
      PredecessorHalfFin13Atom0350 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0679 chi) ∨
      (PredecessorHalfFin13Atom1175 chi ∧
      ¬PredecessorHalfFin13Atom0343 chi))) ∨
      ((PredecessorHalfFin13Atom1175 chi ∧
      ¬PredecessorHalfFin13Atom0344 chi) ∨
      ((PredecessorHalfFin13Atom1175 chi ∧
      ¬PredecessorHalfFin13Atom0359 chi) ∨
      (PredecessorHalfFin13Atom1175 chi ∧
      ¬PredecessorHalfFin13Atom0395 chi))))) ∨
      ((((PredecessorHalfFin13Atom1175 chi ∧
      ¬PredecessorHalfFin13Atom0680 chi) ∨
      ((¬PredecessorHalfFin13Atom1175 chi ∧
      PredecessorHalfFin13Atom0343 chi ∧
      PredecessorHalfFin13Atom0344 chi ∧
      PredecessorHalfFin13Atom0359 chi ∧
      PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0680 chi) ∨
      (PredecessorHalfFin13Atom1176 chi ∧
      ¬PredecessorHalfFin13Atom0343 chi))) ∨
      ((PredecessorHalfFin13Atom1176 chi ∧
      ¬PredecessorHalfFin13Atom0345 chi) ∨
      ((PredecessorHalfFin13Atom1176 chi ∧
      ¬PredecessorHalfFin13Atom0360 chi) ∨
      (PredecessorHalfFin13Atom1176 chi ∧
      ¬PredecessorHalfFin13Atom0396 chi)))) ∨
      (((PredecessorHalfFin13Atom1176 chi ∧
      ¬PredecessorHalfFin13Atom0681 chi) ∨
      ((¬PredecessorHalfFin13Atom1176 chi ∧
      PredecessorHalfFin13Atom0343 chi ∧
      PredecessorHalfFin13Atom0345 chi ∧
      PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0681 chi) ∨
      (PredecessorHalfFin13Atom1177 chi ∧
      ¬PredecessorHalfFin13Atom0343 chi))) ∨
      (((PredecessorHalfFin13Atom1177 chi ∧
      ¬PredecessorHalfFin13Atom0346 chi) ∨
      (PredecessorHalfFin13Atom1177 chi ∧
      ¬PredecessorHalfFin13Atom0361 chi)) ∨
      ((PredecessorHalfFin13Atom1177 chi ∧
      ¬PredecessorHalfFin13Atom0397 chi) ∨
      (PredecessorHalfFin13Atom1177 chi ∧
      ¬PredecessorHalfFin13Atom0682 chi))))))))) := by
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
              exact predecessorHalfFin13_clause17100 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause17104 chi hbad
              ·
                exact predecessorHalfFin13_clause17105 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause17106 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause17109 chi hbad
              ·
                exact predecessorHalfFin13_clause17111 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause17112 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause17113 chi hone hbad
              ·
                exact predecessorHalfFin13_clause17114 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause17115 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause17116 chi hone hbad
              ·
                exact predecessorHalfFin13_clause17117 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause17118 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause17119 chi hone hbad
              ·
                exact predecessorHalfFin13_clause17120 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause17121 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause17122 chi hbad
              ·
                exact predecessorHalfFin13_clause17124 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause17128 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause17129 chi hbad
              ·
                exact predecessorHalfFin13_clause17133 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause17135 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause17136 chi hbad
              ·
                exact predecessorHalfFin13_clause17137 chi hone hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause17138 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause17139 chi hone hbad
              ·
                exact predecessorHalfFin13_clause17140 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause17141 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause17142 chi hone hbad
              ·
                exact predecessorHalfFin13_clause17143 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause17144 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause17145 chi hbad
              ·
                exact predecessorHalfFin13_clause17146 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause17148 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause17149 chi hbad
              ·
                exact predecessorHalfFin13_clause17152 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause17153 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause17156 chi hbad
              ·
                exact predecessorHalfFin13_clause17157 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause17159 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause17160 chi hbad
              ·
                exact predecessorHalfFin13_clause18151 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18152 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18153 chi hbad
              ·
                exact predecessorHalfFin13_clause18154 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18155 chi hbad
              ·
                exact predecessorHalfFin13_clause18156 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18157 chi hbad
              ·
                exact predecessorHalfFin13_clause18158 chi hbad
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
              exact predecessorHalfFin13_clause18159 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18160 chi hbad
              ·
                exact predecessorHalfFin13_clause18161 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18162 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18163 chi hbad
              ·
                exact predecessorHalfFin13_clause18164 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18165 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18166 chi hbad
              ·
                exact predecessorHalfFin13_clause18167 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18168 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18169 chi hbad
              ·
                exact predecessorHalfFin13_clause18170 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18171 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18172 chi hbad
              ·
                exact predecessorHalfFin13_clause18173 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18175 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18176 chi hbad
              ·
                exact predecessorHalfFin13_clause18177 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18178 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18179 chi hbad
              ·
                exact predecessorHalfFin13_clause18180 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18181 chi hbad
              ·
                exact predecessorHalfFin13_clause18182 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18183 chi hbad
              ·
                exact predecessorHalfFin13_clause18184 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18185 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18186 chi hbad
              ·
                exact predecessorHalfFin13_clause18193 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18194 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18195 chi hbad
              ·
                exact predecessorHalfFin13_clause18196 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18197 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18198 chi hbad
              ·
                exact predecessorHalfFin13_clause18199 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18200 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18201 chi hbad
              ·
                exact predecessorHalfFin13_clause18202 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18203 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18204 chi hbad
              ·
                exact predecessorHalfFin13_clause18205 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18206 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18207 chi hbad
              ·
                exact predecessorHalfFin13_clause18208 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18209 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18210 chi hbad
              ·
                exact predecessorHalfFin13_clause18211 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18212 chi hbad
              ·
                exact predecessorHalfFin13_clause18213 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18214 chi hbad
              ·
                exact predecessorHalfFin13_clause18215 chi hbad

end ErdosSzekeres

end
