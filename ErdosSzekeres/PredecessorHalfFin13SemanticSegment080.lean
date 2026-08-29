module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk061
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk062

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 080. -/

theorem predecessorHalfFin13_rejectSemanticSegment080
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((¬PredecessorHalfFin13Atom1177 chi ∧
      PredecessorHalfFin13Atom0343 chi ∧
      PredecessorHalfFin13Atom0346 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0682 chi) ∨
      ((PredecessorHalfFin13Atom1178 chi ∧
      ¬PredecessorHalfFin13Atom0343 chi) ∨
      (PredecessorHalfFin13Atom1178 chi ∧
      ¬PredecessorHalfFin13Atom0347 chi))) ∨
      ((PredecessorHalfFin13Atom1178 chi ∧
      ¬PredecessorHalfFin13Atom0362 chi) ∨
      ((PredecessorHalfFin13Atom1178 chi ∧
      ¬PredecessorHalfFin13Atom0398 chi) ∨
      (PredecessorHalfFin13Atom1178 chi ∧
      ¬PredecessorHalfFin13Atom0683 chi)))) ∨
      (((PredecessorHalfFin13Atom1179 chi ∧
      ¬PredecessorHalfFin13Atom0343 chi) ∨
      ((PredecessorHalfFin13Atom1179 chi ∧
      ¬PredecessorHalfFin13Atom0348 chi) ∨
      (PredecessorHalfFin13Atom1179 chi ∧
      ¬PredecessorHalfFin13Atom0363 chi))) ∨
      ((PredecessorHalfFin13Atom1179 chi ∧
      ¬PredecessorHalfFin13Atom0399 chi) ∨
      ((PredecessorHalfFin13Atom1179 chi ∧
      ¬PredecessorHalfFin13Atom0684 chi) ∨
      (¬PredecessorHalfFin13Atom1179 chi ∧
      PredecessorHalfFin13Atom0343 chi ∧
      PredecessorHalfFin13Atom0348 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0684 chi))))) ∨
      ((((PredecessorHalfFin13Atom1181 chi ∧
      ¬PredecessorHalfFin13Atom0343 chi) ∨
      ((PredecessorHalfFin13Atom1181 chi ∧
      ¬PredecessorHalfFin13Atom0350 chi) ∨
      (PredecessorHalfFin13Atom1181 chi ∧
      ¬PredecessorHalfFin13Atom0365 chi))) ∨
      ((PredecessorHalfFin13Atom1181 chi ∧
      ¬PredecessorHalfFin13Atom0401 chi) ∨
      ((PredecessorHalfFin13Atom1181 chi ∧
      ¬PredecessorHalfFin13Atom0686 chi) ∨
      (¬PredecessorHalfFin13Atom1181 chi ∧
      PredecessorHalfFin13Atom0343 chi ∧
      PredecessorHalfFin13Atom0350 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0401 chi ∧
      PredecessorHalfFin13Atom0686 chi)))) ∨
      (((PredecessorHalfFin13Atom1182 chi ∧
      ¬PredecessorHalfFin13Atom0344 chi) ∨
      ((PredecessorHalfFin13Atom1182 chi ∧
      ¬PredecessorHalfFin13Atom0345 chi) ∨
      (PredecessorHalfFin13Atom1182 chi ∧
      ¬PredecessorHalfFin13Atom0366 chi))) ∨
      ((PredecessorHalfFin13Atom1182 chi ∧
      ¬PredecessorHalfFin13Atom0402 chi) ∨
      ((PredecessorHalfFin13Atom1182 chi ∧
      ¬PredecessorHalfFin13Atom0687 chi) ∨
      (¬PredecessorHalfFin13Atom1182 chi ∧
      PredecessorHalfFin13Atom0344 chi ∧
      PredecessorHalfFin13Atom0345 chi ∧
      PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0687 chi)))))) ∨
      (((((PredecessorHalfFin13Atom1183 chi ∧
      ¬PredecessorHalfFin13Atom0344 chi) ∨
      ((PredecessorHalfFin13Atom1183 chi ∧
      ¬PredecessorHalfFin13Atom0346 chi) ∨
      (PredecessorHalfFin13Atom1183 chi ∧
      ¬PredecessorHalfFin13Atom0367 chi))) ∨
      ((PredecessorHalfFin13Atom1183 chi ∧
      ¬PredecessorHalfFin13Atom0403 chi) ∨
      ((PredecessorHalfFin13Atom1183 chi ∧
      ¬PredecessorHalfFin13Atom0688 chi) ∨
      (¬PredecessorHalfFin13Atom1183 chi ∧
      PredecessorHalfFin13Atom0344 chi ∧
      PredecessorHalfFin13Atom0346 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0688 chi)))) ∨
      (((PredecessorHalfFin13Atom1184 chi ∧
      ¬PredecessorHalfFin13Atom0344 chi) ∨
      ((PredecessorHalfFin13Atom1184 chi ∧
      ¬PredecessorHalfFin13Atom0347 chi) ∨
      (PredecessorHalfFin13Atom1184 chi ∧
      ¬PredecessorHalfFin13Atom0368 chi))) ∨
      ((PredecessorHalfFin13Atom1184 chi ∧
      ¬PredecessorHalfFin13Atom0404 chi) ∨
      ((PredecessorHalfFin13Atom1184 chi ∧
      ¬PredecessorHalfFin13Atom0689 chi) ∨
      (¬PredecessorHalfFin13Atom1184 chi ∧
      PredecessorHalfFin13Atom0344 chi ∧
      PredecessorHalfFin13Atom0347 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0689 chi))))) ∨
      ((((PredecessorHalfFin13Atom1185 chi ∧
      ¬PredecessorHalfFin13Atom0344 chi) ∨
      ((PredecessorHalfFin13Atom1185 chi ∧
      ¬PredecessorHalfFin13Atom0348 chi) ∨
      (PredecessorHalfFin13Atom1185 chi ∧
      ¬PredecessorHalfFin13Atom0369 chi))) ∨
      ((PredecessorHalfFin13Atom1185 chi ∧
      ¬PredecessorHalfFin13Atom0405 chi) ∨
      ((PredecessorHalfFin13Atom1185 chi ∧
      ¬PredecessorHalfFin13Atom0690 chi) ∨
      (¬PredecessorHalfFin13Atom1185 chi ∧
      PredecessorHalfFin13Atom0344 chi ∧
      PredecessorHalfFin13Atom0348 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0690 chi)))) ∨
      (((PredecessorHalfFin13Atom1187 chi ∧
      ¬PredecessorHalfFin13Atom0344 chi) ∨
      ((PredecessorHalfFin13Atom1187 chi ∧
      ¬PredecessorHalfFin13Atom0350 chi) ∨
      (PredecessorHalfFin13Atom1187 chi ∧
      ¬PredecessorHalfFin13Atom0371 chi))) ∨
      (((PredecessorHalfFin13Atom1187 chi ∧
      ¬PredecessorHalfFin13Atom0407 chi) ∨
      (PredecessorHalfFin13Atom1187 chi ∧
      ¬PredecessorHalfFin13Atom0692 chi)) ∨
      ((PredecessorHalfFin13Atom1188 chi ∧
      ¬PredecessorHalfFin13Atom0345 chi) ∨
      (PredecessorHalfFin13Atom1188 chi ∧
      ¬PredecessorHalfFin13Atom0346 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom1188 chi ∧
      ¬PredecessorHalfFin13Atom0372 chi) ∨
      ((PredecessorHalfFin13Atom1188 chi ∧
      ¬PredecessorHalfFin13Atom0408 chi) ∨
      (PredecessorHalfFin13Atom1188 chi ∧
      ¬PredecessorHalfFin13Atom0693 chi))) ∨
      ((¬PredecessorHalfFin13Atom1188 chi ∧
      PredecessorHalfFin13Atom0345 chi ∧
      PredecessorHalfFin13Atom0346 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0693 chi) ∨
      ((PredecessorHalfFin13Atom1189 chi ∧
      ¬PredecessorHalfFin13Atom0345 chi) ∨
      (PredecessorHalfFin13Atom1189 chi ∧
      ¬PredecessorHalfFin13Atom0347 chi)))) ∨
      (((PredecessorHalfFin13Atom1189 chi ∧
      ¬PredecessorHalfFin13Atom0373 chi) ∨
      ((PredecessorHalfFin13Atom1189 chi ∧
      ¬PredecessorHalfFin13Atom0409 chi) ∨
      (PredecessorHalfFin13Atom1189 chi ∧
      ¬PredecessorHalfFin13Atom0694 chi))) ∨
      ((¬PredecessorHalfFin13Atom1189 chi ∧
      PredecessorHalfFin13Atom0345 chi ∧
      PredecessorHalfFin13Atom0347 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0694 chi) ∨
      ((PredecessorHalfFin13Atom1190 chi ∧
      ¬PredecessorHalfFin13Atom0345 chi) ∨
      (PredecessorHalfFin13Atom1190 chi ∧
      ¬PredecessorHalfFin13Atom0348 chi))))) ∨
      ((((PredecessorHalfFin13Atom1190 chi ∧
      ¬PredecessorHalfFin13Atom0374 chi) ∨
      ((PredecessorHalfFin13Atom1190 chi ∧
      ¬PredecessorHalfFin13Atom0410 chi) ∨
      (PredecessorHalfFin13Atom1190 chi ∧
      ¬PredecessorHalfFin13Atom0695 chi))) ∨
      ((¬PredecessorHalfFin13Atom1190 chi ∧
      PredecessorHalfFin13Atom0345 chi ∧
      PredecessorHalfFin13Atom0348 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0695 chi) ∨
      ((PredecessorHalfFin13Atom1192 chi ∧
      ¬PredecessorHalfFin13Atom0345 chi) ∨
      (PredecessorHalfFin13Atom1192 chi ∧
      ¬PredecessorHalfFin13Atom0350 chi)))) ∨
      (((PredecessorHalfFin13Atom1192 chi ∧
      ¬PredecessorHalfFin13Atom0376 chi) ∨
      ((PredecessorHalfFin13Atom1192 chi ∧
      ¬PredecessorHalfFin13Atom0412 chi) ∨
      (PredecessorHalfFin13Atom1192 chi ∧
      ¬PredecessorHalfFin13Atom0697 chi))) ∨
      ((PredecessorHalfFin13Atom1193 chi ∧
      ¬PredecessorHalfFin13Atom0346 chi) ∨
      ((PredecessorHalfFin13Atom1193 chi ∧
      ¬PredecessorHalfFin13Atom0347 chi) ∨
      (PredecessorHalfFin13Atom1193 chi ∧
      ¬PredecessorHalfFin13Atom0377 chi)))))) ∨
      (((((PredecessorHalfFin13Atom1193 chi ∧
      ¬PredecessorHalfFin13Atom0413 chi) ∨
      ((PredecessorHalfFin13Atom1193 chi ∧
      ¬PredecessorHalfFin13Atom0698 chi) ∨
      (¬PredecessorHalfFin13Atom1193 chi ∧
      PredecessorHalfFin13Atom0346 chi ∧
      PredecessorHalfFin13Atom0347 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0698 chi))) ∨
      ((PredecessorHalfFin13Atom1194 chi ∧
      ¬PredecessorHalfFin13Atom0346 chi) ∨
      ((PredecessorHalfFin13Atom1194 chi ∧
      ¬PredecessorHalfFin13Atom0348 chi) ∨
      (PredecessorHalfFin13Atom1194 chi ∧
      ¬PredecessorHalfFin13Atom0378 chi)))) ∨
      (((PredecessorHalfFin13Atom1194 chi ∧
      ¬PredecessorHalfFin13Atom0414 chi) ∨
      ((PredecessorHalfFin13Atom1194 chi ∧
      ¬PredecessorHalfFin13Atom0699 chi) ∨
      (PredecessorHalfFin13Atom1196 chi ∧
      ¬PredecessorHalfFin13Atom0346 chi))) ∨
      ((PredecessorHalfFin13Atom1196 chi ∧
      ¬PredecessorHalfFin13Atom0350 chi) ∨
      ((PredecessorHalfFin13Atom1196 chi ∧
      ¬PredecessorHalfFin13Atom0380 chi) ∨
      (PredecessorHalfFin13Atom1196 chi ∧
      ¬PredecessorHalfFin13Atom0416 chi))))) ∨
      ((((PredecessorHalfFin13Atom1196 chi ∧
      ¬PredecessorHalfFin13Atom0701 chi) ∨
      ((¬PredecessorHalfFin13Atom1196 chi ∧
      PredecessorHalfFin13Atom0346 chi ∧
      PredecessorHalfFin13Atom0350 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0701 chi) ∨
      (PredecessorHalfFin13Atom1197 chi ∧
      ¬PredecessorHalfFin13Atom0347 chi))) ∨
      ((PredecessorHalfFin13Atom1197 chi ∧
      ¬PredecessorHalfFin13Atom0348 chi) ∨
      ((PredecessorHalfFin13Atom1197 chi ∧
      ¬PredecessorHalfFin13Atom0381 chi) ∨
      (PredecessorHalfFin13Atom1197 chi ∧
      ¬PredecessorHalfFin13Atom0417 chi)))) ∨
      (((PredecessorHalfFin13Atom1197 chi ∧
      ¬PredecessorHalfFin13Atom0702 chi) ∨
      ((¬PredecessorHalfFin13Atom1197 chi ∧
      PredecessorHalfFin13Atom0347 chi ∧
      PredecessorHalfFin13Atom0348 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0702 chi) ∨
      (PredecessorHalfFin13Atom1199 chi ∧
      ¬PredecessorHalfFin13Atom0347 chi))) ∨
      (((PredecessorHalfFin13Atom1199 chi ∧
      ¬PredecessorHalfFin13Atom0350 chi) ∨
      (PredecessorHalfFin13Atom1199 chi ∧
      ¬PredecessorHalfFin13Atom0383 chi)) ∨
      ((PredecessorHalfFin13Atom1199 chi ∧
      ¬PredecessorHalfFin13Atom0419 chi) ∨
      (PredecessorHalfFin13Atom1199 chi ∧
      ¬PredecessorHalfFin13Atom0704 chi))))))))) := by
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
              exact predecessorHalfFin13_clause18216 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18217 chi hbad
              ·
                exact predecessorHalfFin13_clause18218 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18219 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18220 chi hbad
              ·
                exact predecessorHalfFin13_clause18221 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18223 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18224 chi hbad
              ·
                exact predecessorHalfFin13_clause18225 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18226 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18227 chi hbad
              ·
                exact predecessorHalfFin13_clause18228 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18235 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18236 chi hbad
              ·
                exact predecessorHalfFin13_clause18237 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18238 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18239 chi hbad
              ·
                exact predecessorHalfFin13_clause18240 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18241 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18242 chi hbad
              ·
                exact predecessorHalfFin13_clause18243 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18244 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18245 chi hbad
              ·
                exact predecessorHalfFin13_clause18246 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18247 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18248 chi hbad
              ·
                exact predecessorHalfFin13_clause18249 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18250 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18251 chi hbad
              ·
                exact predecessorHalfFin13_clause18252 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18253 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18254 chi hbad
              ·
                exact predecessorHalfFin13_clause18255 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18256 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18257 chi hbad
              ·
                exact predecessorHalfFin13_clause18258 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18259 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18260 chi hbad
              ·
                exact predecessorHalfFin13_clause18261 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18262 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18263 chi hbad
              ·
                exact predecessorHalfFin13_clause18264 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18271 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18272 chi hbad
              ·
                exact predecessorHalfFin13_clause18273 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18274 chi hbad
              ·
                exact predecessorHalfFin13_clause18275 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18277 chi hbad
              ·
                exact predecessorHalfFin13_clause18278 chi hbad
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
              exact predecessorHalfFin13_clause18279 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18280 chi hbad
              ·
                exact predecessorHalfFin13_clause18281 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18282 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18283 chi hbad
              ·
                exact predecessorHalfFin13_clause18284 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18285 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18286 chi hbad
              ·
                exact predecessorHalfFin13_clause18287 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18288 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18289 chi hbad
              ·
                exact predecessorHalfFin13_clause18290 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18291 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18292 chi hbad
              ·
                exact predecessorHalfFin13_clause18293 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18294 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18301 chi hbad
              ·
                exact predecessorHalfFin13_clause18302 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18303 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18304 chi hbad
              ·
                exact predecessorHalfFin13_clause18305 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18307 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18308 chi hbad
              ·
                exact predecessorHalfFin13_clause18309 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18310 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18311 chi hbad
              ·
                exact predecessorHalfFin13_clause18312 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18313 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18314 chi hbad
              ·
                exact predecessorHalfFin13_clause18315 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18316 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18317 chi hbad
              ·
                exact predecessorHalfFin13_clause18325 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18326 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18327 chi hbad
              ·
                exact predecessorHalfFin13_clause18328 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18329 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18330 chi hbad
              ·
                exact predecessorHalfFin13_clause18331 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18332 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18333 chi hbad
              ·
                exact predecessorHalfFin13_clause18334 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18335 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18336 chi hbad
              ·
                exact predecessorHalfFin13_clause18343 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18344 chi hbad
              ·
                exact predecessorHalfFin13_clause18345 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18346 chi hbad
              ·
                exact predecessorHalfFin13_clause18347 chi hbad

end ErdosSzekeres

end
