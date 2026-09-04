module

public import ErdosSzekeres.Fin15AnchoredClauseChunk059
public import ErdosSzekeres.Fin15AnchoredClauseChunk060
public import ErdosSzekeres.Fin15AnchoredClauseChunk061

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 030. -/

theorem fin15Anchored_rejectSemanticSegment030
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((¬Fin15AnchoredAtom0043 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0696 chi) ∨
      ((¬Fin15AnchoredAtom0043 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0696 chi) ∨
      (¬Fin15AnchoredAtom0044 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0697 chi))) ∨
      (((¬Fin15AnchoredAtom0044 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0697 chi) ∨
      (¬Fin15AnchoredAtom0044 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0698 chi)) ∨
      ((¬Fin15AnchoredAtom0044 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0698 chi) ∨
      (¬Fin15AnchoredAtom0045 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0699 chi)))) ∨
      ((((¬Fin15AnchoredAtom0045 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0699 chi) ∨
      (¬Fin15AnchoredAtom0047 chi ∧
      ¬Fin15AnchoredAtom0048 chi ∧
      ¬Fin15AnchoredAtom0056 chi ∧
      ¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0700 chi)) ∨
      ((¬Fin15AnchoredAtom0047 chi ∧
      ¬Fin15AnchoredAtom0048 chi ∧
      ¬Fin15AnchoredAtom0056 chi ∧
      Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0700 chi) ∨
      (¬Fin15AnchoredAtom0047 chi ∧
      ¬Fin15AnchoredAtom0049 chi ∧
      ¬Fin15AnchoredAtom0057 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0701 chi))) ∨
      (((¬Fin15AnchoredAtom0047 chi ∧
      ¬Fin15AnchoredAtom0049 chi ∧
      ¬Fin15AnchoredAtom0057 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0701 chi) ∨
      (¬Fin15AnchoredAtom0047 chi ∧
      ¬Fin15AnchoredAtom0050 chi ∧
      ¬Fin15AnchoredAtom0058 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0702 chi)) ∨
      ((¬Fin15AnchoredAtom0047 chi ∧
      ¬Fin15AnchoredAtom0050 chi ∧
      ¬Fin15AnchoredAtom0058 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0702 chi) ∨
      (¬Fin15AnchoredAtom0047 chi ∧
      ¬Fin15AnchoredAtom0051 chi ∧
      ¬Fin15AnchoredAtom0059 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0703 chi))))) ∨
      (((((¬Fin15AnchoredAtom0047 chi ∧
      ¬Fin15AnchoredAtom0051 chi ∧
      ¬Fin15AnchoredAtom0059 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0703 chi) ∨
      (¬Fin15AnchoredAtom0047 chi ∧
      ¬Fin15AnchoredAtom0052 chi ∧
      ¬Fin15AnchoredAtom0060 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0704 chi)) ∨
      ((¬Fin15AnchoredAtom0047 chi ∧
      ¬Fin15AnchoredAtom0052 chi ∧
      ¬Fin15AnchoredAtom0060 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0704 chi) ∨
      (¬Fin15AnchoredAtom0047 chi ∧
      ¬Fin15AnchoredAtom0053 chi ∧
      ¬Fin15AnchoredAtom0061 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0705 chi))) ∨
      (((¬Fin15AnchoredAtom0047 chi ∧
      ¬Fin15AnchoredAtom0053 chi ∧
      ¬Fin15AnchoredAtom0061 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0705 chi) ∨
      (¬Fin15AnchoredAtom0047 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0706 chi)) ∨
      ((¬Fin15AnchoredAtom0047 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0706 chi) ∨
      (¬Fin15AnchoredAtom0047 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0707 chi)))) ∨
      ((((¬Fin15AnchoredAtom0047 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0707 chi) ∨
      (¬Fin15AnchoredAtom0048 chi ∧
      ¬Fin15AnchoredAtom0049 chi ∧
      ¬Fin15AnchoredAtom0064 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0708 chi)) ∨
      ((¬Fin15AnchoredAtom0048 chi ∧
      ¬Fin15AnchoredAtom0049 chi ∧
      ¬Fin15AnchoredAtom0064 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0708 chi) ∨
      (¬Fin15AnchoredAtom0048 chi ∧
      ¬Fin15AnchoredAtom0050 chi ∧
      ¬Fin15AnchoredAtom0065 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0709 chi))) ∨
      (((¬Fin15AnchoredAtom0048 chi ∧
      ¬Fin15AnchoredAtom0050 chi ∧
      ¬Fin15AnchoredAtom0065 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0709 chi) ∨
      (¬Fin15AnchoredAtom0048 chi ∧
      ¬Fin15AnchoredAtom0051 chi ∧
      ¬Fin15AnchoredAtom0066 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0710 chi)) ∨
      ((¬Fin15AnchoredAtom0048 chi ∧
      ¬Fin15AnchoredAtom0051 chi ∧
      ¬Fin15AnchoredAtom0066 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0710 chi) ∨
      (¬Fin15AnchoredAtom0048 chi ∧
      ¬Fin15AnchoredAtom0052 chi ∧
      ¬Fin15AnchoredAtom0067 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0711 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0048 chi ∧
      ¬Fin15AnchoredAtom0052 chi ∧
      ¬Fin15AnchoredAtom0067 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0711 chi) ∨
      (¬Fin15AnchoredAtom0048 chi ∧
      ¬Fin15AnchoredAtom0053 chi ∧
      ¬Fin15AnchoredAtom0068 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0712 chi)) ∨
      ((¬Fin15AnchoredAtom0048 chi ∧
      ¬Fin15AnchoredAtom0053 chi ∧
      ¬Fin15AnchoredAtom0068 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0712 chi) ∨
      (¬Fin15AnchoredAtom0048 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0713 chi))) ∨
      (((¬Fin15AnchoredAtom0048 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0713 chi) ∨
      (¬Fin15AnchoredAtom0048 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0714 chi)) ∨
      ((¬Fin15AnchoredAtom0048 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0714 chi) ∨
      (¬Fin15AnchoredAtom0049 chi ∧
      ¬Fin15AnchoredAtom0050 chi ∧
      ¬Fin15AnchoredAtom0071 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0715 chi)))) ∨
      ((((¬Fin15AnchoredAtom0049 chi ∧
      ¬Fin15AnchoredAtom0050 chi ∧
      ¬Fin15AnchoredAtom0071 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0715 chi) ∨
      (¬Fin15AnchoredAtom0049 chi ∧
      ¬Fin15AnchoredAtom0051 chi ∧
      ¬Fin15AnchoredAtom0072 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0716 chi)) ∨
      ((¬Fin15AnchoredAtom0049 chi ∧
      ¬Fin15AnchoredAtom0051 chi ∧
      ¬Fin15AnchoredAtom0072 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0716 chi) ∨
      (¬Fin15AnchoredAtom0049 chi ∧
      ¬Fin15AnchoredAtom0053 chi ∧
      ¬Fin15AnchoredAtom0074 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0718 chi))) ∨
      (((¬Fin15AnchoredAtom0049 chi ∧
      ¬Fin15AnchoredAtom0053 chi ∧
      ¬Fin15AnchoredAtom0074 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0718 chi) ∨
      (¬Fin15AnchoredAtom0049 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      ¬Fin15AnchoredAtom0075 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0719 chi)) ∨
      ((¬Fin15AnchoredAtom0049 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      ¬Fin15AnchoredAtom0075 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0719 chi) ∨
      (¬Fin15AnchoredAtom0049 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0720 chi))))) ∨
      (((((¬Fin15AnchoredAtom0049 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0720 chi) ∨
      (¬Fin15AnchoredAtom0050 chi ∧
      ¬Fin15AnchoredAtom0051 chi ∧
      ¬Fin15AnchoredAtom0077 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0721 chi)) ∨
      ((¬Fin15AnchoredAtom0050 chi ∧
      ¬Fin15AnchoredAtom0051 chi ∧
      ¬Fin15AnchoredAtom0077 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0721 chi) ∨
      (¬Fin15AnchoredAtom0050 chi ∧
      ¬Fin15AnchoredAtom0052 chi ∧
      ¬Fin15AnchoredAtom0078 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0722 chi))) ∨
      (((¬Fin15AnchoredAtom0050 chi ∧
      ¬Fin15AnchoredAtom0052 chi ∧
      ¬Fin15AnchoredAtom0078 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0722 chi) ∨
      (¬Fin15AnchoredAtom0050 chi ∧
      ¬Fin15AnchoredAtom0053 chi ∧
      ¬Fin15AnchoredAtom0079 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0723 chi)) ∨
      ((¬Fin15AnchoredAtom0050 chi ∧
      ¬Fin15AnchoredAtom0053 chi ∧
      ¬Fin15AnchoredAtom0079 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0723 chi) ∨
      (¬Fin15AnchoredAtom0050 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0724 chi)))) ∨
      ((((¬Fin15AnchoredAtom0050 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0724 chi) ∨
      (¬Fin15AnchoredAtom0050 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0725 chi)) ∨
      ((¬Fin15AnchoredAtom0050 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0725 chi) ∨
      (¬Fin15AnchoredAtom0051 chi ∧
      ¬Fin15AnchoredAtom0052 chi ∧
      ¬Fin15AnchoredAtom0082 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0726 chi))) ∨
      (((¬Fin15AnchoredAtom0051 chi ∧
      ¬Fin15AnchoredAtom0052 chi ∧
      ¬Fin15AnchoredAtom0082 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0726 chi) ∨
      (¬Fin15AnchoredAtom0051 chi ∧
      ¬Fin15AnchoredAtom0053 chi ∧
      ¬Fin15AnchoredAtom0083 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0727 chi)) ∨
      ((¬Fin15AnchoredAtom0051 chi ∧
      ¬Fin15AnchoredAtom0053 chi ∧
      ¬Fin15AnchoredAtom0083 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0727 chi) ∨
      (¬Fin15AnchoredAtom0051 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0728 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0051 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0728 chi) ∨
      ((¬Fin15AnchoredAtom0051 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0729 chi) ∨
      (¬Fin15AnchoredAtom0051 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0729 chi))) ∨
      (((¬Fin15AnchoredAtom0052 chi ∧
      ¬Fin15AnchoredAtom0053 chi ∧
      ¬Fin15AnchoredAtom0086 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0730 chi) ∨
      (¬Fin15AnchoredAtom0052 chi ∧
      ¬Fin15AnchoredAtom0053 chi ∧
      ¬Fin15AnchoredAtom0086 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0730 chi)) ∨
      ((¬Fin15AnchoredAtom0052 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      ¬Fin15AnchoredAtom0087 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0731 chi) ∨
      (¬Fin15AnchoredAtom0052 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      ¬Fin15AnchoredAtom0087 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0731 chi)))) ∨
      ((((¬Fin15AnchoredAtom0052 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0732 chi) ∨
      (¬Fin15AnchoredAtom0052 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0732 chi)) ∨
      ((¬Fin15AnchoredAtom0053 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0733 chi) ∨
      (¬Fin15AnchoredAtom0053 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0733 chi))) ∨
      (((¬Fin15AnchoredAtom0053 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0734 chi) ∨
      (¬Fin15AnchoredAtom0053 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0734 chi)) ∨
      ((¬Fin15AnchoredAtom0054 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0735 chi) ∨
      (¬Fin15AnchoredAtom0054 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0735 chi))))) ∨
      (((((¬Fin15AnchoredAtom0056 chi ∧
      ¬Fin15AnchoredAtom0057 chi ∧
      ¬Fin15AnchoredAtom0064 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0736 chi) ∨
      (¬Fin15AnchoredAtom0056 chi ∧
      ¬Fin15AnchoredAtom0057 chi ∧
      ¬Fin15AnchoredAtom0064 chi ∧
      Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0736 chi)) ∨
      ((¬Fin15AnchoredAtom0056 chi ∧
      ¬Fin15AnchoredAtom0058 chi ∧
      ¬Fin15AnchoredAtom0065 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0737 chi) ∨
      (¬Fin15AnchoredAtom0056 chi ∧
      ¬Fin15AnchoredAtom0058 chi ∧
      ¬Fin15AnchoredAtom0065 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0737 chi))) ∨
      (((¬Fin15AnchoredAtom0056 chi ∧
      ¬Fin15AnchoredAtom0059 chi ∧
      ¬Fin15AnchoredAtom0066 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0738 chi) ∨
      (¬Fin15AnchoredAtom0056 chi ∧
      ¬Fin15AnchoredAtom0059 chi ∧
      ¬Fin15AnchoredAtom0066 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0738 chi)) ∨
      ((¬Fin15AnchoredAtom0056 chi ∧
      ¬Fin15AnchoredAtom0060 chi ∧
      ¬Fin15AnchoredAtom0067 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0739 chi) ∨
      (¬Fin15AnchoredAtom0056 chi ∧
      ¬Fin15AnchoredAtom0060 chi ∧
      ¬Fin15AnchoredAtom0067 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0739 chi)))) ∨
      ((((¬Fin15AnchoredAtom0056 chi ∧
      ¬Fin15AnchoredAtom0061 chi ∧
      ¬Fin15AnchoredAtom0068 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0740 chi) ∨
      (¬Fin15AnchoredAtom0056 chi ∧
      ¬Fin15AnchoredAtom0061 chi ∧
      ¬Fin15AnchoredAtom0068 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0740 chi)) ∨
      ((¬Fin15AnchoredAtom0056 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0741 chi) ∨
      (¬Fin15AnchoredAtom0056 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0741 chi))) ∨
      (((¬Fin15AnchoredAtom0056 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0742 chi) ∨
      (¬Fin15AnchoredAtom0056 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0742 chi)) ∨
      ((¬Fin15AnchoredAtom0057 chi ∧
      ¬Fin15AnchoredAtom0058 chi ∧
      ¬Fin15AnchoredAtom0071 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0743 chi) ∨
      (¬Fin15AnchoredAtom0057 chi ∧
      ¬Fin15AnchoredAtom0058 chi ∧
      ¬Fin15AnchoredAtom0071 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0743 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0057 chi ∧
      ¬Fin15AnchoredAtom0059 chi ∧
      ¬Fin15AnchoredAtom0072 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0744 chi) ∨
      (¬Fin15AnchoredAtom0057 chi ∧
      ¬Fin15AnchoredAtom0059 chi ∧
      ¬Fin15AnchoredAtom0072 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0744 chi)) ∨
      ((¬Fin15AnchoredAtom0057 chi ∧
      ¬Fin15AnchoredAtom0061 chi ∧
      ¬Fin15AnchoredAtom0074 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0746 chi) ∨
      (¬Fin15AnchoredAtom0057 chi ∧
      ¬Fin15AnchoredAtom0061 chi ∧
      ¬Fin15AnchoredAtom0074 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0746 chi))) ∨
      (((¬Fin15AnchoredAtom0057 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      ¬Fin15AnchoredAtom0075 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0747 chi) ∨
      (¬Fin15AnchoredAtom0057 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      ¬Fin15AnchoredAtom0075 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0747 chi)) ∨
      ((¬Fin15AnchoredAtom0057 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0748 chi) ∨
      (¬Fin15AnchoredAtom0057 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0748 chi)))) ∨
      ((((¬Fin15AnchoredAtom0058 chi ∧
      ¬Fin15AnchoredAtom0059 chi ∧
      ¬Fin15AnchoredAtom0077 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0749 chi) ∨
      (¬Fin15AnchoredAtom0058 chi ∧
      ¬Fin15AnchoredAtom0059 chi ∧
      ¬Fin15AnchoredAtom0077 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0749 chi)) ∨
      ((¬Fin15AnchoredAtom0058 chi ∧
      ¬Fin15AnchoredAtom0060 chi ∧
      ¬Fin15AnchoredAtom0078 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0750 chi) ∨
      (¬Fin15AnchoredAtom0058 chi ∧
      ¬Fin15AnchoredAtom0060 chi ∧
      ¬Fin15AnchoredAtom0078 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0750 chi))) ∨
      (((¬Fin15AnchoredAtom0058 chi ∧
      ¬Fin15AnchoredAtom0061 chi ∧
      ¬Fin15AnchoredAtom0079 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0751 chi) ∨
      (¬Fin15AnchoredAtom0058 chi ∧
      ¬Fin15AnchoredAtom0061 chi ∧
      ¬Fin15AnchoredAtom0079 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0751 chi)) ∨
      ((¬Fin15AnchoredAtom0058 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0752 chi) ∨
      (¬Fin15AnchoredAtom0058 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0752 chi))))) ∨
      (((((¬Fin15AnchoredAtom0058 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0753 chi) ∨
      (¬Fin15AnchoredAtom0058 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0753 chi)) ∨
      ((¬Fin15AnchoredAtom0059 chi ∧
      ¬Fin15AnchoredAtom0060 chi ∧
      ¬Fin15AnchoredAtom0082 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0754 chi) ∨
      (¬Fin15AnchoredAtom0059 chi ∧
      ¬Fin15AnchoredAtom0060 chi ∧
      ¬Fin15AnchoredAtom0082 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0754 chi))) ∨
      (((¬Fin15AnchoredAtom0059 chi ∧
      ¬Fin15AnchoredAtom0061 chi ∧
      ¬Fin15AnchoredAtom0083 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0755 chi) ∨
      (¬Fin15AnchoredAtom0059 chi ∧
      ¬Fin15AnchoredAtom0061 chi ∧
      ¬Fin15AnchoredAtom0083 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0755 chi)) ∨
      ((¬Fin15AnchoredAtom0059 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0756 chi) ∨
      (¬Fin15AnchoredAtom0059 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0756 chi)))) ∨
      ((((¬Fin15AnchoredAtom0059 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0757 chi) ∨
      (¬Fin15AnchoredAtom0059 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0757 chi)) ∨
      ((¬Fin15AnchoredAtom0060 chi ∧
      ¬Fin15AnchoredAtom0061 chi ∧
      ¬Fin15AnchoredAtom0086 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0758 chi) ∨
      (¬Fin15AnchoredAtom0060 chi ∧
      ¬Fin15AnchoredAtom0061 chi ∧
      ¬Fin15AnchoredAtom0086 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0758 chi))) ∨
      (((¬Fin15AnchoredAtom0060 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      ¬Fin15AnchoredAtom0087 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0759 chi) ∨
      (¬Fin15AnchoredAtom0060 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      ¬Fin15AnchoredAtom0087 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0759 chi)) ∨
      ((¬Fin15AnchoredAtom0060 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0760 chi) ∨
      (¬Fin15AnchoredAtom0060 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom0760 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom0061 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0761 chi) ∨
      ((¬Fin15AnchoredAtom0061 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0761 chi) ∨
      (¬Fin15AnchoredAtom0061 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0762 chi))) ∨
      (((¬Fin15AnchoredAtom0061 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0762 chi) ∨
      (¬Fin15AnchoredAtom0062 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0763 chi)) ∨
      ((¬Fin15AnchoredAtom0062 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0763 chi) ∨
      (¬Fin15AnchoredAtom0064 chi ∧
      ¬Fin15AnchoredAtom0065 chi ∧
      ¬Fin15AnchoredAtom0071 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0764 chi)))) ∨
      ((((¬Fin15AnchoredAtom0064 chi ∧
      ¬Fin15AnchoredAtom0065 chi ∧
      ¬Fin15AnchoredAtom0071 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0764 chi) ∨
      (¬Fin15AnchoredAtom0064 chi ∧
      ¬Fin15AnchoredAtom0066 chi ∧
      ¬Fin15AnchoredAtom0072 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0765 chi)) ∨
      ((¬Fin15AnchoredAtom0064 chi ∧
      ¬Fin15AnchoredAtom0066 chi ∧
      ¬Fin15AnchoredAtom0072 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0765 chi) ∨
      (¬Fin15AnchoredAtom0064 chi ∧
      ¬Fin15AnchoredAtom0068 chi ∧
      ¬Fin15AnchoredAtom0074 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0767 chi))) ∨
      (((¬Fin15AnchoredAtom0064 chi ∧
      ¬Fin15AnchoredAtom0068 chi ∧
      ¬Fin15AnchoredAtom0074 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0767 chi) ∨
      (¬Fin15AnchoredAtom0064 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      ¬Fin15AnchoredAtom0075 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0768 chi)) ∨
      ((¬Fin15AnchoredAtom0064 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      ¬Fin15AnchoredAtom0075 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0768 chi) ∨
      (¬Fin15AnchoredAtom0064 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0769 chi))))) ∨
      (((((¬Fin15AnchoredAtom0064 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0769 chi) ∨
      (¬Fin15AnchoredAtom0065 chi ∧
      ¬Fin15AnchoredAtom0066 chi ∧
      ¬Fin15AnchoredAtom0077 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0770 chi)) ∨
      ((¬Fin15AnchoredAtom0065 chi ∧
      ¬Fin15AnchoredAtom0066 chi ∧
      ¬Fin15AnchoredAtom0077 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0770 chi) ∨
      (¬Fin15AnchoredAtom0065 chi ∧
      ¬Fin15AnchoredAtom0067 chi ∧
      ¬Fin15AnchoredAtom0078 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0771 chi))) ∨
      (((¬Fin15AnchoredAtom0065 chi ∧
      ¬Fin15AnchoredAtom0067 chi ∧
      ¬Fin15AnchoredAtom0078 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom0771 chi) ∨
      (¬Fin15AnchoredAtom0065 chi ∧
      ¬Fin15AnchoredAtom0068 chi ∧
      ¬Fin15AnchoredAtom0079 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0772 chi)) ∨
      ((¬Fin15AnchoredAtom0065 chi ∧
      ¬Fin15AnchoredAtom0068 chi ∧
      ¬Fin15AnchoredAtom0079 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0772 chi) ∨
      (¬Fin15AnchoredAtom0065 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0773 chi)))) ∨
      ((((¬Fin15AnchoredAtom0065 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0773 chi) ∨
      (¬Fin15AnchoredAtom0065 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0774 chi)) ∨
      ((¬Fin15AnchoredAtom0065 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0774 chi) ∨
      (¬Fin15AnchoredAtom0066 chi ∧
      ¬Fin15AnchoredAtom0067 chi ∧
      ¬Fin15AnchoredAtom0082 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0775 chi))) ∨
      (((¬Fin15AnchoredAtom0066 chi ∧
      ¬Fin15AnchoredAtom0067 chi ∧
      ¬Fin15AnchoredAtom0082 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0775 chi) ∨
      (¬Fin15AnchoredAtom0066 chi ∧
      ¬Fin15AnchoredAtom0068 chi ∧
      ¬Fin15AnchoredAtom0083 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0776 chi)) ∨
      ((¬Fin15AnchoredAtom0066 chi ∧
      ¬Fin15AnchoredAtom0068 chi ∧
      ¬Fin15AnchoredAtom0083 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0776 chi) ∨
      (¬Fin15AnchoredAtom0066 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0777 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0066 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0777 chi) ∨
      (¬Fin15AnchoredAtom0066 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0778 chi)) ∨
      ((¬Fin15AnchoredAtom0066 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0778 chi) ∨
      (¬Fin15AnchoredAtom0067 chi ∧
      ¬Fin15AnchoredAtom0068 chi ∧
      ¬Fin15AnchoredAtom0086 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0779 chi))) ∨
      (((¬Fin15AnchoredAtom0067 chi ∧
      ¬Fin15AnchoredAtom0068 chi ∧
      ¬Fin15AnchoredAtom0086 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0779 chi) ∨
      (¬Fin15AnchoredAtom0067 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      ¬Fin15AnchoredAtom0087 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0780 chi)) ∨
      ((¬Fin15AnchoredAtom0067 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      ¬Fin15AnchoredAtom0087 chi ∧
      Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom0780 chi) ∨
      (¬Fin15AnchoredAtom0067 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom0781 chi)))) ∨
      ((((¬Fin15AnchoredAtom0067 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom0781 chi) ∨
      (¬Fin15AnchoredAtom0068 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0782 chi)) ∨
      ((¬Fin15AnchoredAtom0068 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0782 chi) ∨
      (¬Fin15AnchoredAtom0068 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0783 chi))) ∨
      (((¬Fin15AnchoredAtom0068 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0783 chi) ∨
      (¬Fin15AnchoredAtom0069 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0784 chi)) ∨
      ((¬Fin15AnchoredAtom0069 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0784 chi) ∨
      (¬Fin15AnchoredAtom0071 chi ∧
      ¬Fin15AnchoredAtom0072 chi ∧
      ¬Fin15AnchoredAtom0077 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0785 chi))))) ∨
      (((((¬Fin15AnchoredAtom0071 chi ∧
      ¬Fin15AnchoredAtom0072 chi ∧
      ¬Fin15AnchoredAtom0077 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0785 chi) ∨
      (¬Fin15AnchoredAtom0071 chi ∧
      ¬Fin15AnchoredAtom0074 chi ∧
      ¬Fin15AnchoredAtom0079 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0787 chi)) ∨
      ((¬Fin15AnchoredAtom0071 chi ∧
      ¬Fin15AnchoredAtom0074 chi ∧
      ¬Fin15AnchoredAtom0079 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0787 chi) ∨
      (¬Fin15AnchoredAtom0071 chi ∧
      ¬Fin15AnchoredAtom0075 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0788 chi))) ∨
      (((¬Fin15AnchoredAtom0071 chi ∧
      ¬Fin15AnchoredAtom0075 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0788 chi) ∨
      (¬Fin15AnchoredAtom0071 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0789 chi)) ∨
      ((¬Fin15AnchoredAtom0071 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0789 chi) ∨
      (¬Fin15AnchoredAtom0072 chi ∧
      ¬Fin15AnchoredAtom0074 chi ∧
      ¬Fin15AnchoredAtom0083 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0791 chi)))) ∨
      ((((¬Fin15AnchoredAtom0072 chi ∧
      ¬Fin15AnchoredAtom0074 chi ∧
      ¬Fin15AnchoredAtom0083 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0791 chi) ∨
      (¬Fin15AnchoredAtom0072 chi ∧
      ¬Fin15AnchoredAtom0075 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0792 chi)) ∨
      ((¬Fin15AnchoredAtom0072 chi ∧
      ¬Fin15AnchoredAtom0075 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0792 chi) ∨
      (¬Fin15AnchoredAtom0072 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0793 chi))) ∨
      (((¬Fin15AnchoredAtom0072 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0793 chi) ∨
      (¬Fin15AnchoredAtom0074 chi ∧
      ¬Fin15AnchoredAtom0075 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0797 chi)) ∨
      ((¬Fin15AnchoredAtom0074 chi ∧
      ¬Fin15AnchoredAtom0075 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0797 chi) ∨
      (¬Fin15AnchoredAtom0074 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0798 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0074 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0798 chi) ∨
      ((¬Fin15AnchoredAtom0075 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0799 chi) ∨
      (¬Fin15AnchoredAtom0075 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0799 chi))) ∨
      (((¬Fin15AnchoredAtom0077 chi ∧
      ¬Fin15AnchoredAtom0078 chi ∧
      ¬Fin15AnchoredAtom0082 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom0800 chi) ∨
      (¬Fin15AnchoredAtom0077 chi ∧
      ¬Fin15AnchoredAtom0078 chi ∧
      ¬Fin15AnchoredAtom0082 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0800 chi)) ∨
      ((¬Fin15AnchoredAtom0077 chi ∧
      ¬Fin15AnchoredAtom0079 chi ∧
      ¬Fin15AnchoredAtom0083 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0801 chi) ∨
      (¬Fin15AnchoredAtom0077 chi ∧
      ¬Fin15AnchoredAtom0079 chi ∧
      ¬Fin15AnchoredAtom0083 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0801 chi)))) ∨
      ((((¬Fin15AnchoredAtom0077 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0802 chi) ∨
      (¬Fin15AnchoredAtom0077 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0802 chi)) ∨
      ((¬Fin15AnchoredAtom0077 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0803 chi) ∨
      (¬Fin15AnchoredAtom0077 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0803 chi))) ∨
      (((¬Fin15AnchoredAtom0078 chi ∧
      ¬Fin15AnchoredAtom0079 chi ∧
      ¬Fin15AnchoredAtom0086 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0804 chi) ∨
      (¬Fin15AnchoredAtom0078 chi ∧
      ¬Fin15AnchoredAtom0079 chi ∧
      ¬Fin15AnchoredAtom0086 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0804 chi)) ∨
      ((¬Fin15AnchoredAtom0078 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      ¬Fin15AnchoredAtom0087 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom0805 chi) ∨
      (¬Fin15AnchoredAtom0078 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      ¬Fin15AnchoredAtom0087 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom0805 chi))))) ∨
      (((((¬Fin15AnchoredAtom0078 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom0806 chi) ∨
      (¬Fin15AnchoredAtom0078 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom0806 chi)) ∨
      ((¬Fin15AnchoredAtom0079 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0807 chi) ∨
      (¬Fin15AnchoredAtom0079 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0807 chi))) ∨
      (((¬Fin15AnchoredAtom0079 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0808 chi) ∨
      (¬Fin15AnchoredAtom0079 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0808 chi)) ∨
      ((¬Fin15AnchoredAtom0080 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0809 chi) ∨
      (¬Fin15AnchoredAtom0080 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0809 chi)))) ∨
      ((((¬Fin15AnchoredAtom0082 chi ∧
      ¬Fin15AnchoredAtom0083 chi ∧
      ¬Fin15AnchoredAtom0086 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom0810 chi) ∨
      (¬Fin15AnchoredAtom0082 chi ∧
      ¬Fin15AnchoredAtom0083 chi ∧
      ¬Fin15AnchoredAtom0086 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom0810 chi)) ∨
      ((¬Fin15AnchoredAtom0082 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      ¬Fin15AnchoredAtom0087 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom0811 chi) ∨
      (¬Fin15AnchoredAtom0082 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      ¬Fin15AnchoredAtom0087 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom0811 chi))) ∨
      (((¬Fin15AnchoredAtom0082 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom0812 chi) ∨
      (¬Fin15AnchoredAtom0082 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom0812 chi)) ∨
      ((¬Fin15AnchoredAtom0083 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom0813 chi) ∨
      (¬Fin15AnchoredAtom0083 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom0813 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0083 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom0814 chi) ∨
      (¬Fin15AnchoredAtom0083 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom0814 chi)) ∨
      ((¬Fin15AnchoredAtom0084 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom0815 chi) ∨
      (¬Fin15AnchoredAtom0084 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom0815 chi))) ∨
      (((¬Fin15AnchoredAtom0086 chi ∧
      ¬Fin15AnchoredAtom0087 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom0816 chi) ∨
      (¬Fin15AnchoredAtom0086 chi ∧
      ¬Fin15AnchoredAtom0087 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom0816 chi)) ∨
      ((¬Fin15AnchoredAtom0086 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom0817 chi) ∨
      (¬Fin15AnchoredAtom0086 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom0817 chi)))) ∨
      ((((¬Fin15AnchoredAtom0087 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom0818 chi) ∨
      (¬Fin15AnchoredAtom0087 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      Fin15AnchoredAtom0454 chi ∧
      Fin15AnchoredAtom0818 chi)) ∨
      ((¬Fin15AnchoredAtom0089 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom0819 chi) ∨
      (¬Fin15AnchoredAtom0089 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom0819 chi))) ∨
      (((¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0820 chi) ∨
      (¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0820 chi)) ∨
      ((¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0820 chi) ∨
      (¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0820 chi))))) ∨
      (((((Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0820 chi) ∨
      (Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0820 chi)) ∨
      ((Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0820 chi) ∨
      (Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0820 chi))) ∨
      (((¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0821 chi) ∨
      (¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0821 chi)) ∨
      ((¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0821 chi) ∨
      (¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0821 chi)))) ∨
      ((((Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0821 chi) ∨
      (Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0821 chi)) ∨
      ((Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0821 chi) ∨
      (Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0821 chi))) ∨
      (((¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0822 chi) ∨
      (¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0822 chi)) ∨
      ((¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0822 chi) ∨
      (¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0822 chi)))))))))) := by
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
                exact fin15Anchored_clause07572 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07573 chi hbad
                ·
                  exact fin15Anchored_clause07574 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07575 chi hbad
                ·
                  exact fin15Anchored_clause07576 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07577 chi hbad
                ·
                  exact fin15Anchored_clause07578 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07579 chi hbad
                ·
                  exact fin15Anchored_clause07580 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07581 chi hbad
                ·
                  exact fin15Anchored_clause07582 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07583 chi hbad
                ·
                  exact fin15Anchored_clause07584 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07585 chi hbad
                ·
                  exact fin15Anchored_clause07586 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07587 chi hbad
                ·
                  exact fin15Anchored_clause07588 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07589 chi hbad
                ·
                  exact fin15Anchored_clause07590 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07591 chi hbad
                ·
                  exact fin15Anchored_clause07592 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07593 chi hbad
                ·
                  exact fin15Anchored_clause07594 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07595 chi hbad
                ·
                  exact fin15Anchored_clause07596 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07597 chi hbad
                ·
                  exact fin15Anchored_clause07598 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07599 chi hbad
                ·
                  exact fin15Anchored_clause07600 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07601 chi hbad
                ·
                  exact fin15Anchored_clause07602 chi hbad
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
                  exact fin15Anchored_clause07603 chi hbad
                ·
                  exact fin15Anchored_clause07604 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07605 chi hbad
                ·
                  exact fin15Anchored_clause07606 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07607 chi hbad
                ·
                  exact fin15Anchored_clause07608 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07609 chi hbad
                ·
                  exact fin15Anchored_clause07610 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07611 chi hbad
                ·
                  exact fin15Anchored_clause07612 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07613 chi hbad
                ·
                  exact fin15Anchored_clause07614 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07615 chi hbad
                ·
                  exact fin15Anchored_clause07616 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07617 chi hbad
                ·
                  exact fin15Anchored_clause07618 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07619 chi hbad
                ·
                  exact fin15Anchored_clause07620 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07621 chi hbad
                ·
                  exact fin15Anchored_clause07622 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07623 chi hbad
                ·
                  exact fin15Anchored_clause07624 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07625 chi hbad
                ·
                  exact fin15Anchored_clause07626 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07627 chi hbad
                ·
                  exact fin15Anchored_clause07628 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07629 chi hbad
                ·
                  exact fin15Anchored_clause07630 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07631 chi hbad
                ·
                  exact fin15Anchored_clause07632 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07633 chi hbad
                ·
                  exact fin15Anchored_clause07634 chi hbad
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
                exact fin15Anchored_clause07635 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07636 chi hbad
                ·
                  exact fin15Anchored_clause07637 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07638 chi hbad
                ·
                  exact fin15Anchored_clause07639 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07640 chi hbad
                ·
                  exact fin15Anchored_clause07641 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07642 chi hbad
                ·
                  exact fin15Anchored_clause07643 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07644 chi hbad
                ·
                  exact fin15Anchored_clause07645 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07646 chi hbad
                ·
                  exact fin15Anchored_clause07647 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07648 chi hbad
                ·
                  exact fin15Anchored_clause07649 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07650 chi hbad
                ·
                  exact fin15Anchored_clause07651 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07652 chi hbad
                ·
                  exact fin15Anchored_clause07653 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07654 chi hbad
                ·
                  exact fin15Anchored_clause07655 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07656 chi hbad
                ·
                  exact fin15Anchored_clause07657 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07658 chi hbad
                ·
                  exact fin15Anchored_clause07659 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07660 chi hbad
                ·
                  exact fin15Anchored_clause07661 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07662 chi hbad
                ·
                  exact fin15Anchored_clause07663 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07664 chi hbad
                ·
                  exact fin15Anchored_clause07665 chi hbad
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
                  exact fin15Anchored_clause07666 chi hbad
                ·
                  exact fin15Anchored_clause07667 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07668 chi hbad
                ·
                  exact fin15Anchored_clause07669 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07670 chi hbad
                ·
                  exact fin15Anchored_clause07671 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07672 chi hbad
                ·
                  exact fin15Anchored_clause07673 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07674 chi hbad
                ·
                  exact fin15Anchored_clause07675 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07676 chi hbad
                ·
                  exact fin15Anchored_clause07677 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07678 chi hbad
                ·
                  exact fin15Anchored_clause07679 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07680 chi hbad
                ·
                  exact fin15Anchored_clause07681 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07682 chi hbad
                ·
                  exact fin15Anchored_clause07683 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07684 chi hbad
                ·
                  exact fin15Anchored_clause07685 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07686 chi hbad
                ·
                  exact fin15Anchored_clause07687 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07688 chi hbad
                ·
                  exact fin15Anchored_clause07689 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07690 chi hbad
                ·
                  exact fin15Anchored_clause07691 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07692 chi hbad
                ·
                  exact fin15Anchored_clause07693 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07694 chi hbad
                ·
                  exact fin15Anchored_clause07695 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07696 chi hbad
                ·
                  exact fin15Anchored_clause07697 chi hbad
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
                exact fin15Anchored_clause07698 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07699 chi hbad
                ·
                  exact fin15Anchored_clause07700 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07701 chi hbad
                ·
                  exact fin15Anchored_clause07702 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07703 chi hbad
                ·
                  exact fin15Anchored_clause07704 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07705 chi hbad
                ·
                  exact fin15Anchored_clause07706 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07707 chi hbad
                ·
                  exact fin15Anchored_clause07708 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07709 chi hbad
                ·
                  exact fin15Anchored_clause07710 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07711 chi hbad
                ·
                  exact fin15Anchored_clause07712 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07713 chi hbad
                ·
                  exact fin15Anchored_clause07714 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07715 chi hbad
                ·
                  exact fin15Anchored_clause07716 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07717 chi hbad
                ·
                  exact fin15Anchored_clause07718 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07719 chi hbad
                ·
                  exact fin15Anchored_clause07720 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07721 chi hbad
                ·
                  exact fin15Anchored_clause07722 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07723 chi hbad
                ·
                  exact fin15Anchored_clause07724 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07725 chi hbad
                ·
                  exact fin15Anchored_clause07726 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07727 chi hbad
                ·
                  exact fin15Anchored_clause07728 chi hbad
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
                  exact fin15Anchored_clause07729 chi hbad
                ·
                  exact fin15Anchored_clause07730 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07731 chi hbad
                ·
                  exact fin15Anchored_clause07732 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07733 chi hbad
                ·
                  exact fin15Anchored_clause07734 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07735 chi hbad
                ·
                  exact fin15Anchored_clause07736 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07737 chi hbad
                ·
                  exact fin15Anchored_clause07738 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07739 chi hbad
                ·
                  exact fin15Anchored_clause07740 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07741 chi hbad
                ·
                  exact fin15Anchored_clause07742 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07743 chi hbad
                ·
                  exact fin15Anchored_clause07744 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07745 chi hbad
                ·
                  exact fin15Anchored_clause07746 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07747 chi hbad
                ·
                  exact fin15Anchored_clause07748 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07749 chi hbad
                ·
                  exact fin15Anchored_clause07750 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07751 chi hbad
                ·
                  exact fin15Anchored_clause07752 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07753 chi hbad
                ·
                  exact fin15Anchored_clause07754 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07755 chi hbad
                ·
                  exact fin15Anchored_clause07756 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07757 chi hbad
                ·
                  exact fin15Anchored_clause07758 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07759 chi hbad
                ·
                  exact fin15Anchored_clause07760 chi hbad
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
                exact fin15Anchored_clause07761 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07762 chi hbad
                ·
                  exact fin15Anchored_clause07763 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07764 chi hbad
                ·
                  exact fin15Anchored_clause07765 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07766 chi hbad
                ·
                  exact fin15Anchored_clause07767 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07768 chi hbad
                ·
                  exact fin15Anchored_clause07769 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07770 chi hbad
                ·
                  exact fin15Anchored_clause07771 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07772 chi hbad
                ·
                  exact fin15Anchored_clause07773 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07774 chi hbad
                ·
                  exact fin15Anchored_clause07775 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07776 chi hbad
                ·
                  exact fin15Anchored_clause07777 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07778 chi hbad
                ·
                  exact fin15Anchored_clause07779 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07780 chi hbad
                ·
                  exact fin15Anchored_clause07781 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07782 chi hbad
                ·
                  exact fin15Anchored_clause07783 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07784 chi hbad
                ·
                  exact fin15Anchored_clause07785 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07786 chi hbad
                ·
                  exact fin15Anchored_clause07787 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07788 chi hbad
                ·
                  exact fin15Anchored_clause07789 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07790 chi hbad
                ·
                  exact fin15Anchored_clause07791 chi hbad
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
                  exact fin15Anchored_clause07792 chi hbad
                ·
                  exact fin15Anchored_clause07793 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07794 chi hbad
                ·
                  exact fin15Anchored_clause07795 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07796 chi hbad
                ·
                  exact fin15Anchored_clause07797 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07798 chi hbad
                ·
                  exact fin15Anchored_clause07799 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07800 chi hbad
                ·
                  exact fin15Anchored_clause07801 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07802 chi hbad
                ·
                  exact fin15Anchored_clause07803 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07804 chi hbad
                ·
                  exact fin15Anchored_clause07805 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07806 chi hbad
                ·
                  exact fin15Anchored_clause07807 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07808 chi hbad
                ·
                  exact fin15Anchored_clause07809 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07810 chi hbad
                ·
                  exact fin15Anchored_clause07811 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07812 chi hbad
                ·
                  exact fin15Anchored_clause07813 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07814 chi hbad
                ·
                  exact fin15Anchored_clause07815 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07816 chi hbad
                ·
                  exact fin15Anchored_clause07817 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07818 chi hbad
                ·
                  exact fin15Anchored_clause07819 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07820 chi hbad
                ·
                  exact fin15Anchored_clause07821 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07822 chi hbad
                ·
                  exact fin15Anchored_clause07823 chi hbad

end ErdosSzekeres

end
