module

public import ErdosSzekeres.Fin15AnchoredClauseChunk067
public import ErdosSzekeres.Fin15AnchoredClauseChunk068
public import ErdosSzekeres.Fin15AnchoredClauseChunk069

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 034. -/

theorem fin15Anchored_rejectSemanticSegment034
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0923 chi) ∨
      ((¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0923 chi) ∨
      (Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0923 chi))) ∨
      (((Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0923 chi) ∨
      (Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0923 chi)) ∨
      ((Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0923 chi) ∨
      (¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0924 chi)))) ∨
      ((((¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0924 chi) ∨
      (¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0924 chi)) ∨
      ((¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0924 chi) ∨
      (Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0924 chi))) ∨
      (((Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0924 chi) ∨
      (Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0924 chi)) ∨
      ((Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0924 chi) ∨
      (Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0924 chi))))) ∨
      (((((¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0925 chi) ∨
      (¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0925 chi)) ∨
      ((¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0925 chi) ∨
      (¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0925 chi))) ∨
      (((Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0925 chi) ∨
      (Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0925 chi)) ∨
      ((Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0925 chi) ∨
      (Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0925 chi)))) ∨
      ((((¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0926 chi) ∨
      (¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0926 chi)) ∨
      ((¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0926 chi) ∨
      (¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0926 chi))) ∨
      (((Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0926 chi) ∨
      (Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0926 chi)) ∨
      ((Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0926 chi) ∨
      (Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0926 chi)))))) ∨
      ((((((Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0926 chi) ∨
      (¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0927 chi)) ∨
      ((¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0927 chi) ∨
      (¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0927 chi))) ∨
      (((Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0927 chi) ∨
      (Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0927 chi)) ∨
      ((Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0927 chi) ∨
      (¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0928 chi)))) ∨
      ((((¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0928 chi) ∨
      (¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0928 chi)) ∨
      ((¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0928 chi) ∨
      (¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0928 chi))) ∨
      (((Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0928 chi) ∨
      (Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0928 chi)) ∨
      ((Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0928 chi) ∨
      (Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0928 chi))))) ∨
      (((((¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0929 chi) ∨
      (¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0929 chi)) ∨
      ((¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0929 chi) ∨
      (¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0929 chi))) ∨
      (((Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0929 chi) ∨
      (Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0929 chi)) ∨
      ((Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0929 chi) ∨
      (Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0929 chi)))) ∨
      ((((¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0930 chi) ∨
      (¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0930 chi)) ∨
      ((¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0930 chi) ∨
      (¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0930 chi))) ∨
      (((Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0930 chi) ∨
      (Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0930 chi)) ∨
      ((Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0930 chi) ∨
      (Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0930 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0931 chi) ∨
      ((¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0932 chi) ∨
      (¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0932 chi))) ∨
      (((¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0932 chi) ∨
      (¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0932 chi)) ∨
      ((Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0932 chi) ∨
      (Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0932 chi)))) ∨
      ((((Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0932 chi) ∨
      (Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0932 chi)) ∨
      ((¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0933 chi) ∨
      (¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0933 chi))) ∨
      (((¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0933 chi) ∨
      (¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0933 chi)) ∨
      ((¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0933 chi) ∨
      (Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0933 chi))))) ∨
      (((((Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0933 chi) ∨
      (Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0933 chi)) ∨
      ((Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0933 chi) ∨
      (Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0933 chi))) ∨
      (((¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0934 chi) ∨
      (¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0934 chi)) ∨
      ((¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0934 chi) ∨
      (¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0934 chi)))) ∨
      ((((Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0934 chi) ∨
      (Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0934 chi)) ∨
      ((Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0934 chi) ∨
      (Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0934 chi))) ∨
      (((¬Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0935 chi) ∨
      (¬Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0935 chi)) ∨
      ((¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0935 chi) ∨
      (¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0935 chi)))))) ∨
      ((((((Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0935 chi) ∨
      (¬Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0936 chi)) ∨
      ((Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0936 chi) ∨
      (Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0936 chi))) ∨
      (((¬Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0937 chi) ∨
      (¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0937 chi)) ∨
      ((¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0937 chi) ∨
      (¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0938 chi)))) ∨
      ((((¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0938 chi) ∨
      (¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0938 chi)) ∨
      ((¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0938 chi) ∨
      (Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0938 chi))) ∨
      (((Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0938 chi) ∨
      (Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0938 chi)) ∨
      ((Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0938 chi) ∨
      (¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0939 chi))))) ∨
      (((((¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0939 chi) ∨
      (¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0939 chi)) ∨
      ((¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0939 chi) ∨
      (¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0939 chi))) ∨
      (((Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0939 chi) ∨
      (Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0939 chi)) ∨
      ((Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0939 chi) ∨
      (Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0939 chi)))) ∨
      ((((¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0940 chi) ∨
      (¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0940 chi)) ∨
      ((¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0940 chi) ∨
      (¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0940 chi))) ∨
      (((¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0940 chi) ∨
      (Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0940 chi)) ∨
      ((Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0940 chi) ∨
      (Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0940 chi)))))))) ∨
      (((((((Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0940 chi) ∨
      ((¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0941 chi) ∨
      (¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0941 chi))) ∨
      (((¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0941 chi) ∨
      (¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0941 chi)) ∨
      ((Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0941 chi) ∨
      (Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0941 chi)))) ∨
      ((((Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0941 chi) ∨
      (Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0941 chi)) ∨
      ((Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0941 chi) ∨
      (¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0942 chi))) ∨
      (((¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0942 chi) ∨
      (¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0942 chi)) ∨
      ((¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0942 chi) ∨
      (Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0942 chi))))) ∨
      (((((Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0942 chi) ∨
      (Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0942 chi)) ∨
      ((Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0942 chi) ∨
      (¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0943 chi))) ∨
      (((¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0943 chi) ∨
      (¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0943 chi)) ∨
      ((¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0943 chi) ∨
      (Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0943 chi)))) ∨
      ((((Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0943 chi) ∨
      (Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0943 chi)) ∨
      ((Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0943 chi) ∨
      (Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0943 chi))) ∨
      (((¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0944 chi) ∨
      (¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0944 chi)) ∨
      ((¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0944 chi) ∨
      (¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0944 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0944 chi) ∨
      (Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0944 chi)) ∨
      ((Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0944 chi) ∨
      (Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0944 chi))) ∨
      (((Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0944 chi) ∨
      (Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0944 chi)) ∨
      ((¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0945 chi) ∨
      (¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0945 chi)))) ∨
      ((((¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0945 chi) ∨
      (¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0945 chi)) ∨
      ((¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0945 chi) ∨
      (¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0945 chi))) ∨
      (((Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0945 chi) ∨
      (Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0945 chi)) ∨
      ((Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0945 chi) ∨
      (Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0945 chi))))) ∨
      (((((Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0945 chi) ∨
      (¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0946 chi)) ∨
      ((Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0946 chi) ∨
      (Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0946 chi))) ∨
      (((¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0947 chi) ∨
      (¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0947 chi)) ∨
      ((¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0947 chi) ∨
      (¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0947 chi)))) ∨
      ((((¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0947 chi) ∨
      (Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0947 chi)) ∨
      ((Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0947 chi) ∨
      (Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0947 chi))) ∨
      (((Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0947 chi) ∨
      (Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0947 chi)) ∨
      ((¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0948 chi) ∨
      (¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0948 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0948 chi) ∨
      ((¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0948 chi) ∨
      (¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0948 chi))) ∨
      (((Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0948 chi) ∨
      (Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0948 chi)) ∨
      ((Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0948 chi) ∨
      (Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0948 chi)))) ∨
      ((((Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0948 chi) ∨
      (¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0949 chi)) ∨
      ((¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0949 chi) ∨
      (¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0949 chi))) ∨
      (((¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0949 chi) ∨
      (¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0949 chi)) ∨
      ((Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0949 chi) ∨
      (Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0949 chi))))) ∨
      (((((Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0949 chi) ∨
      (Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0949 chi)) ∨
      ((Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0949 chi) ∨
      (¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0950 chi))) ∨
      (((¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0950 chi) ∨
      (¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0950 chi)) ∨
      ((¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0950 chi) ∨
      (Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0950 chi)))) ∨
      ((((Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0950 chi) ∨
      (Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0950 chi)) ∨
      ((Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0950 chi) ∨
      (Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0950 chi))) ∨
      (((¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0951 chi) ∨
      (¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0951 chi)) ∨
      ((¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0951 chi) ∨
      (¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0951 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0951 chi) ∨
      (¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0951 chi)) ∨
      ((Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0951 chi) ∨
      (Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0951 chi))) ∨
      (((Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0951 chi) ∨
      (Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0951 chi)) ∨
      ((¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0952 chi) ∨
      (¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0952 chi)))) ∨
      ((((¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0952 chi) ∨
      (¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0952 chi)) ∨
      ((Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0952 chi) ∨
      (Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0952 chi))) ∨
      (((Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0952 chi) ∨
      (Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0952 chi)) ∨
      ((¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0953 chi) ∨
      (¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0953 chi))))) ∨
      (((((¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0953 chi) ∨
      (¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0953 chi)) ∨
      ((¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0953 chi) ∨
      (Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0953 chi))) ∨
      (((Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0953 chi) ∨
      (Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0953 chi)) ∨
      ((Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0953 chi) ∨
      (Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0953 chi)))) ∨
      ((((¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0954 chi) ∨
      (¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0954 chi)) ∨
      ((Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0954 chi) ∨
      (Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0954 chi))) ∨
      (((¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0955 chi) ∨
      (¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0955 chi)) ∨
      ((¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0955 chi) ∨
      (¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0955 chi)))))))))) := by
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
                exact fin15Anchored_clause08581 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08582 chi hbad
                ·
                  exact fin15Anchored_clause08583 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08584 chi hbad
                ·
                  exact fin15Anchored_clause08585 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08586 chi hbad
                ·
                  exact fin15Anchored_clause08587 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08588 chi hbad
                ·
                  exact fin15Anchored_clause08589 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08590 chi hbad
                ·
                  exact fin15Anchored_clause08591 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08592 chi hbad
                ·
                  exact fin15Anchored_clause08593 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08594 chi hbad
                ·
                  exact fin15Anchored_clause08595 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08596 chi hbad
                ·
                  exact fin15Anchored_clause08597 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08598 chi hbad
                ·
                  exact fin15Anchored_clause08599 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08600 chi hbad
                ·
                  exact fin15Anchored_clause08601 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08602 chi hbad
                ·
                  exact fin15Anchored_clause08603 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08604 chi hbad
                ·
                  exact fin15Anchored_clause08605 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08606 chi hbad
                ·
                  exact fin15Anchored_clause08607 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08608 chi hbad
                ·
                  exact fin15Anchored_clause08609 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08610 chi hbad
                ·
                  exact fin15Anchored_clause08611 chi hbad
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
                  exact fin15Anchored_clause08612 chi hbad
                ·
                  exact fin15Anchored_clause08613 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08614 chi hbad
                ·
                  exact fin15Anchored_clause08615 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08616 chi hbad
                ·
                  exact fin15Anchored_clause08617 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08618 chi hbad
                ·
                  exact fin15Anchored_clause08619 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08620 chi hbad
                ·
                  exact fin15Anchored_clause08621 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08622 chi hbad
                ·
                  exact fin15Anchored_clause08623 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08624 chi hbad
                ·
                  exact fin15Anchored_clause08625 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08626 chi hbad
                ·
                  exact fin15Anchored_clause08627 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08628 chi hbad
                ·
                  exact fin15Anchored_clause08629 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08630 chi hbad
                ·
                  exact fin15Anchored_clause08631 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08632 chi hbad
                ·
                  exact fin15Anchored_clause08633 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08634 chi hbad
                ·
                  exact fin15Anchored_clause08635 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08636 chi hbad
                ·
                  exact fin15Anchored_clause08637 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08638 chi hbad
                ·
                  exact fin15Anchored_clause08639 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08640 chi hbad
                ·
                  exact fin15Anchored_clause08641 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08642 chi hbad
                ·
                  exact fin15Anchored_clause08643 chi hbad
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
                exact fin15Anchored_clause08644 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08645 chi hbad
                ·
                  exact fin15Anchored_clause08646 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08647 chi hbad
                ·
                  exact fin15Anchored_clause08648 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08649 chi hbad
                ·
                  exact fin15Anchored_clause08650 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08651 chi hbad
                ·
                  exact fin15Anchored_clause08652 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08653 chi hbad
                ·
                  exact fin15Anchored_clause08654 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08655 chi hbad
                ·
                  exact fin15Anchored_clause08656 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08657 chi hbad
                ·
                  exact fin15Anchored_clause08658 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08659 chi hbad
                ·
                  exact fin15Anchored_clause08660 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08661 chi hbad
                ·
                  exact fin15Anchored_clause08662 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08663 chi hbad
                ·
                  exact fin15Anchored_clause08664 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08665 chi hbad
                ·
                  exact fin15Anchored_clause08666 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08667 chi hbad
                ·
                  exact fin15Anchored_clause08668 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08669 chi hbad
                ·
                  exact fin15Anchored_clause08670 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08671 chi hbad
                ·
                  exact fin15Anchored_clause08672 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08673 chi hbad
                ·
                  exact fin15Anchored_clause08674 chi hbad
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
                  exact fin15Anchored_clause08675 chi hbad
                ·
                  exact fin15Anchored_clause08676 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08677 chi hbad
                ·
                  exact fin15Anchored_clause08678 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08679 chi hbad
                ·
                  exact fin15Anchored_clause08680 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08681 chi hbad
                ·
                  exact fin15Anchored_clause08682 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08683 chi hbad
                ·
                  exact fin15Anchored_clause08684 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08685 chi hbad
                ·
                  exact fin15Anchored_clause08686 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08687 chi hbad
                ·
                  exact fin15Anchored_clause08688 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08689 chi hbad
                ·
                  exact fin15Anchored_clause08690 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08691 chi hbad
                ·
                  exact fin15Anchored_clause08692 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08693 chi hbad
                ·
                  exact fin15Anchored_clause08694 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08695 chi hbad
                ·
                  exact fin15Anchored_clause08696 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08697 chi hbad
                ·
                  exact fin15Anchored_clause08698 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08699 chi hbad
                ·
                  exact fin15Anchored_clause08700 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08701 chi hbad
                ·
                  exact fin15Anchored_clause08702 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08703 chi hbad
                ·
                  exact fin15Anchored_clause08704 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08705 chi hbad
                ·
                  exact fin15Anchored_clause08706 chi hbad
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
                exact fin15Anchored_clause08707 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08708 chi hbad
                ·
                  exact fin15Anchored_clause08709 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08710 chi hbad
                ·
                  exact fin15Anchored_clause08711 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08712 chi hbad
                ·
                  exact fin15Anchored_clause08713 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08714 chi hbad
                ·
                  exact fin15Anchored_clause08715 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08716 chi hbad
                ·
                  exact fin15Anchored_clause08717 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08718 chi hbad
                ·
                  exact fin15Anchored_clause08719 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08720 chi hbad
                ·
                  exact fin15Anchored_clause08721 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08722 chi hbad
                ·
                  exact fin15Anchored_clause08723 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08724 chi hbad
                ·
                  exact fin15Anchored_clause08725 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08726 chi hbad
                ·
                  exact fin15Anchored_clause08727 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08728 chi hbad
                ·
                  exact fin15Anchored_clause08729 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08730 chi hbad
                ·
                  exact fin15Anchored_clause08731 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08732 chi hbad
                ·
                  exact fin15Anchored_clause08733 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08734 chi hbad
                ·
                  exact fin15Anchored_clause08735 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08736 chi hbad
                ·
                  exact fin15Anchored_clause08737 chi hbad
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
                  exact fin15Anchored_clause08738 chi hbad
                ·
                  exact fin15Anchored_clause08739 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08740 chi hbad
                ·
                  exact fin15Anchored_clause08741 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08742 chi hbad
                ·
                  exact fin15Anchored_clause08743 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08744 chi hbad
                ·
                  exact fin15Anchored_clause08745 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08746 chi hbad
                ·
                  exact fin15Anchored_clause08747 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08748 chi hbad
                ·
                  exact fin15Anchored_clause08749 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08750 chi hbad
                ·
                  exact fin15Anchored_clause08751 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08752 chi hbad
                ·
                  exact fin15Anchored_clause08753 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08754 chi hbad
                ·
                  exact fin15Anchored_clause08755 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08756 chi hbad
                ·
                  exact fin15Anchored_clause08757 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08758 chi hbad
                ·
                  exact fin15Anchored_clause08759 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08760 chi hbad
                ·
                  exact fin15Anchored_clause08761 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08762 chi hbad
                ·
                  exact fin15Anchored_clause08763 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08764 chi hbad
                ·
                  exact fin15Anchored_clause08765 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08766 chi hbad
                ·
                  exact fin15Anchored_clause08767 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08768 chi hbad
                ·
                  exact fin15Anchored_clause08769 chi hbad
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
                exact fin15Anchored_clause08770 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08771 chi hbad
                ·
                  exact fin15Anchored_clause08772 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08773 chi hbad
                ·
                  exact fin15Anchored_clause08774 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08775 chi hbad
                ·
                  exact fin15Anchored_clause08776 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08777 chi hbad
                ·
                  exact fin15Anchored_clause08778 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08779 chi hbad
                ·
                  exact fin15Anchored_clause08780 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08781 chi hbad
                ·
                  exact fin15Anchored_clause08782 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08783 chi hbad
                ·
                  exact fin15Anchored_clause08784 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08785 chi hbad
                ·
                  exact fin15Anchored_clause08786 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08787 chi hbad
                ·
                  exact fin15Anchored_clause08788 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08789 chi hbad
                ·
                  exact fin15Anchored_clause08790 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08791 chi hbad
                ·
                  exact fin15Anchored_clause08792 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08793 chi hbad
                ·
                  exact fin15Anchored_clause08794 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08795 chi hbad
                ·
                  exact fin15Anchored_clause08796 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08797 chi hbad
                ·
                  exact fin15Anchored_clause08798 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08799 chi hbad
                ·
                  exact fin15Anchored_clause08800 chi hbad
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
                  exact fin15Anchored_clause08801 chi hbad
                ·
                  exact fin15Anchored_clause08802 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08803 chi hbad
                ·
                  exact fin15Anchored_clause08804 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08805 chi hbad
                ·
                  exact fin15Anchored_clause08806 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08807 chi hbad
                ·
                  exact fin15Anchored_clause08808 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08809 chi hbad
                ·
                  exact fin15Anchored_clause08810 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08811 chi hbad
                ·
                  exact fin15Anchored_clause08812 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08813 chi hbad
                ·
                  exact fin15Anchored_clause08814 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08815 chi hbad
                ·
                  exact fin15Anchored_clause08816 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08817 chi hbad
                ·
                  exact fin15Anchored_clause08818 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08819 chi hbad
                ·
                  exact fin15Anchored_clause08820 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08821 chi hbad
                ·
                  exact fin15Anchored_clause08822 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08823 chi hbad
                ·
                  exact fin15Anchored_clause08824 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08825 chi hbad
                ·
                  exact fin15Anchored_clause08826 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08827 chi hbad
                ·
                  exact fin15Anchored_clause08828 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08829 chi hbad
                ·
                  exact fin15Anchored_clause08830 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08831 chi hbad
                ·
                  exact fin15Anchored_clause08832 chi hbad

end ErdosSzekeres

end
