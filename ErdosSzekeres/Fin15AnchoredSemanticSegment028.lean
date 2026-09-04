module

public import ErdosSzekeres.Fin15AnchoredClauseChunk055
public import ErdosSzekeres.Fin15AnchoredClauseChunk056
public import ErdosSzekeres.Fin15AnchoredClauseChunk057

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 028. -/

theorem fin15Anchored_rejectSemanticSegment028
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom0452 chi) ∨
      ((Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom0452 chi) ∨
      (¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom0453 chi))) ∨
      (((¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom0453 chi) ∨
      (¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom0453 chi)) ∨
      ((¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom0453 chi) ∨
      (Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom0453 chi)))) ∨
      ((((Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom0453 chi) ∨
      (Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom0453 chi)) ∨
      ((Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom0453 chi) ∨
      (¬Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom0454 chi))) ∨
      (((¬Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom0454 chi) ∨
      (¬Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom0454 chi)) ∨
      ((¬Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom0454 chi) ∨
      (Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom0454 chi))))) ∨
      (((((Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom0454 chi) ∨
      (Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom0454 chi)) ∨
      ((Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom0454 chi) ∨
      (¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom0455 chi))) ∨
      (((¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom0455 chi) ∨
      (¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom0455 chi)) ∨
      ((¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom0455 chi) ∨
      (Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom0455 chi)))) ∨
      ((((Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom0455 chi) ∨
      (Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom0455 chi)) ∨
      ((Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom0455 chi) ∨
      (¬Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom0455 chi))) ∨
      (((¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom0455 chi) ∨
      (¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      Fin15AnchoredAtom0455 chi)) ∨
      ((¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom0455 chi) ∨
      (Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      Fin15AnchoredAtom0455 chi)))))) ∨
      ((((((Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom0455 chi) ∨
      (Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom0454 chi ∧
      Fin15AnchoredAtom0455 chi)) ∨
      ((Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      Fin15AnchoredAtom0455 chi) ∨
      (¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0456 chi))) ∨
      (((¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0014 chi ∧
      Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0456 chi) ∨
      (¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0457 chi)) ∨
      ((¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0015 chi ∧
      Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0457 chi) ∨
      (¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0458 chi)))) ∨
      ((((¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0016 chi ∧
      Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0458 chi) ∨
      (¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0459 chi)) ∨
      ((¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0017 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0459 chi) ∨
      (¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0460 chi))) ∨
      (((¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0018 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0460 chi) ∨
      (¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0019 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0461 chi)) ∨
      ((¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0019 chi ∧
      Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0461 chi) ∨
      (¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0462 chi))))) ∨
      (((((¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0020 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0462 chi) ∨
      (¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0463 chi)) ∨
      ((¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0021 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0463 chi) ∨
      (¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0022 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0464 chi))) ∨
      (((¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0022 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0464 chi) ∨
      (¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0465 chi)) ∨
      ((¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0023 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0465 chi) ∨
      (¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0466 chi)))) ∨
      ((((¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0024 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0466 chi) ∨
      (¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0467 chi)) ∨
      ((¬Fin15AnchoredAtom0001 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0467 chi) ∨
      (¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0468 chi))) ∨
      (((¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0026 chi ∧
      Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0468 chi) ∨
      (¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0469 chi)) ∨
      ((¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0027 chi ∧
      Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0469 chi) ∨
      (¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0470 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0028 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0470 chi) ∨
      ((¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0471 chi) ∨
      (¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0029 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0471 chi))) ∨
      (((¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0030 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0472 chi) ∨
      (¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0030 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0472 chi)) ∨
      ((¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0473 chi) ∨
      (¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0031 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0473 chi)))) ∨
      ((((¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0474 chi) ∨
      (¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0032 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0474 chi)) ∨
      ((¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0033 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0475 chi) ∨
      (¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0033 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0475 chi))) ∨
      (((¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0476 chi) ∨
      (¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0034 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0476 chi)) ∨
      ((¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0477 chi) ∨
      (¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0477 chi))))) ∨
      (((((¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0478 chi) ∨
      (¬Fin15AnchoredAtom0002 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0478 chi)) ∨
      ((¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0037 chi ∧
      ¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0479 chi) ∨
      (¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0037 chi ∧
      Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0479 chi))) ∨
      (((¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0038 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0480 chi) ∨
      (¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0038 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0480 chi)) ∨
      ((¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0039 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0481 chi) ∨
      (¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0039 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0481 chi)))) ∨
      ((((¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0040 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0482 chi) ∨
      (¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0040 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0482 chi)) ∨
      ((¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0041 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0483 chi) ∨
      (¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0041 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0483 chi))) ∨
      (((¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0042 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0484 chi) ∨
      (¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0042 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0484 chi)) ∨
      ((¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0043 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0485 chi) ∨
      (¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0043 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0485 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0044 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0486 chi) ∨
      (¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0044 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0486 chi)) ∨
      ((¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0487 chi) ∨
      (¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0487 chi))) ∨
      (((¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0488 chi) ∨
      (¬Fin15AnchoredAtom0003 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0488 chi)) ∨
      ((¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0047 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0489 chi) ∨
      (¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0047 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0489 chi)))) ∨
      ((((¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0048 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0490 chi) ∨
      (¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0048 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0490 chi)) ∨
      ((¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0049 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0491 chi) ∨
      (¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0049 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0491 chi))) ∨
      (((¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0050 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0492 chi) ∨
      (¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0050 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0492 chi)) ∨
      ((¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0051 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0493 chi) ∨
      (¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0051 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0493 chi))))) ∨
      (((((¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0052 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0494 chi) ∨
      (¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0052 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0494 chi)) ∨
      ((¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0053 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0495 chi) ∨
      (¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0053 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0495 chi))) ∨
      (((¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0496 chi) ∨
      (¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0496 chi)) ∨
      ((¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0497 chi) ∨
      (¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0497 chi)))) ∨
      ((((¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0056 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0498 chi) ∨
      (¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0056 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0498 chi)) ∨
      ((¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0057 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0499 chi) ∨
      (¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0057 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0499 chi))) ∨
      (((¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0058 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0500 chi) ∨
      (¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0058 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0500 chi)) ∨
      ((¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0059 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0501 chi) ∨
      (¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0059 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0501 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0060 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0502 chi) ∨
      ((¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0060 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0502 chi) ∨
      (¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0061 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0503 chi))) ∨
      (((¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0061 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0503 chi) ∨
      (¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0504 chi)) ∨
      ((¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0504 chi) ∨
      (¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0505 chi)))) ∨
      ((((¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0505 chi) ∨
      (¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0064 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0506 chi)) ∨
      ((¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0064 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0506 chi) ∨
      (¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0065 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0507 chi))) ∨
      (((¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0065 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0507 chi) ∨
      (¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0066 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0508 chi)) ∨
      ((¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0066 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0508 chi) ∨
      (¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0067 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0509 chi))))) ∨
      (((((¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0067 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0509 chi) ∨
      (¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0068 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0510 chi)) ∨
      ((¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0068 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0510 chi) ∨
      (¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0511 chi))) ∨
      (((¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0511 chi) ∨
      (¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0512 chi)) ∨
      ((¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0512 chi) ∨
      (¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0071 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0513 chi)))) ∨
      ((((¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0071 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0513 chi) ∨
      (¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0072 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0514 chi)) ∨
      ((¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0072 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0514 chi) ∨
      (¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0074 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0516 chi))) ∨
      (((¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0074 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0516 chi) ∨
      (¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0075 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0517 chi)) ∨
      ((¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0075 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0517 chi) ∨
      (¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0518 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0518 chi) ∨
      (¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0077 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0519 chi)) ∨
      ((¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0077 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0519 chi) ∨
      (¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0078 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0520 chi))) ∨
      (((¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0078 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0520 chi) ∨
      (¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0079 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0521 chi)) ∨
      ((¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0079 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0521 chi) ∨
      (¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0522 chi)))) ∨
      ((((¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0522 chi) ∨
      (¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0523 chi)) ∨
      ((¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0523 chi) ∨
      (¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0082 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0524 chi))) ∨
      (((¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0082 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0524 chi) ∨
      (¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0083 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0525 chi)) ∨
      ((¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0083 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0525 chi) ∨
      (¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0526 chi))))) ∨
      (((((¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0526 chi) ∨
      (¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0527 chi)) ∨
      ((¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0527 chi) ∨
      (¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0086 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0528 chi))) ∨
      (((¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0086 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0528 chi) ∨
      (¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0087 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0529 chi)) ∨
      ((¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0087 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0529 chi) ∨
      (¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0530 chi)))) ∨
      ((((¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0530 chi) ∨
      (¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0531 chi)) ∨
      ((¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0531 chi) ∨
      (¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0532 chi))) ∨
      (((¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0532 chi) ∨
      (¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0533 chi)) ∨
      ((¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0533 chi) ∨
      (¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0534 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0026 chi ∧
      Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0534 chi) ∨
      ((¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0535 chi) ∨
      (¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0027 chi ∧
      Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0535 chi))) ∨
      (((¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0536 chi) ∨
      (¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0028 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0536 chi)) ∨
      ((¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0537 chi) ∨
      (¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0029 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0537 chi)))) ∨
      ((((¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0019 chi ∧
      ¬Fin15AnchoredAtom0030 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0538 chi) ∨
      (¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0019 chi ∧
      ¬Fin15AnchoredAtom0030 chi ∧
      Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0538 chi)) ∨
      ((¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0539 chi) ∨
      (¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0031 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0539 chi))) ∨
      (((¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0540 chi) ∨
      (¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0032 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0540 chi)) ∨
      ((¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0022 chi ∧
      ¬Fin15AnchoredAtom0033 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0541 chi) ∨
      (¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0022 chi ∧
      ¬Fin15AnchoredAtom0033 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0541 chi))))) ∨
      (((((¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0542 chi) ∨
      (¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0034 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0542 chi)) ∨
      ((¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0543 chi) ∨
      (¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0543 chi))) ∨
      (((¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0544 chi) ∨
      (¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0544 chi)) ∨
      ((¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0037 chi ∧
      ¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0545 chi) ∨
      (¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0037 chi ∧
      Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0545 chi)))) ∨
      ((((¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0038 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0546 chi) ∨
      (¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0038 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0546 chi)) ∨
      ((¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0039 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0547 chi) ∨
      (¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0039 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0547 chi))) ∨
      (((¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0019 chi ∧
      ¬Fin15AnchoredAtom0040 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0548 chi) ∨
      (¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0019 chi ∧
      ¬Fin15AnchoredAtom0040 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0548 chi)) ∨
      ((¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0041 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0549 chi) ∨
      (¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0041 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0549 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0042 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0550 chi) ∨
      (¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0042 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0550 chi)) ∨
      ((¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0022 chi ∧
      ¬Fin15AnchoredAtom0043 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0551 chi) ∨
      (¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0022 chi ∧
      ¬Fin15AnchoredAtom0043 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0551 chi))) ∨
      (((¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0044 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0552 chi) ∨
      (¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0044 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0552 chi)) ∨
      ((¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0553 chi) ∨
      (¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0553 chi)))) ∨
      ((((¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0554 chi) ∨
      (¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0554 chi)) ∨
      ((¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0047 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0555 chi) ∨
      (¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0047 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0555 chi))) ∨
      (((¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0048 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0556 chi) ∨
      (¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0048 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0556 chi)) ∨
      ((¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0019 chi ∧
      ¬Fin15AnchoredAtom0049 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0557 chi) ∨
      (¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0019 chi ∧
      ¬Fin15AnchoredAtom0049 chi ∧
      Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0557 chi))))) ∨
      (((((¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0050 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0558 chi) ∨
      (¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0050 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0558 chi)) ∨
      ((¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0051 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0559 chi) ∨
      (¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0051 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0559 chi))) ∨
      (((¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0022 chi ∧
      ¬Fin15AnchoredAtom0052 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0560 chi) ∨
      (¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0022 chi ∧
      ¬Fin15AnchoredAtom0052 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0560 chi)) ∨
      ((¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0053 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0561 chi) ∨
      (¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0053 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0561 chi)))) ∨
      ((((¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0562 chi) ∨
      (¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0562 chi)) ∨
      ((¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0563 chi) ∨
      (¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0563 chi))) ∨
      (((¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0056 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0564 chi) ∨
      (¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0056 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0564 chi)) ∨
      ((¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0019 chi ∧
      ¬Fin15AnchoredAtom0057 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0565 chi) ∨
      (¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0019 chi ∧
      ¬Fin15AnchoredAtom0057 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0565 chi)))))))))) := by
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
                exact fin15Anchored_clause07067 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07068 chi hone hbad
                ·
                  exact fin15Anchored_clause07069 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07070 chi hone hbad
                ·
                  exact fin15Anchored_clause07071 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07072 chi hone hbad
                ·
                  exact fin15Anchored_clause07073 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07074 chi hone hbad
                ·
                  exact fin15Anchored_clause07075 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07076 chi hone hbad
                ·
                  exact fin15Anchored_clause07077 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07078 chi hone hbad
                ·
                  exact fin15Anchored_clause07079 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07080 chi hone hbad
                ·
                  exact fin15Anchored_clause07081 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07082 chi hone hbad
                ·
                  exact fin15Anchored_clause07083 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07084 chi hone hbad
                ·
                  exact fin15Anchored_clause07085 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07086 chi hone hbad
                ·
                  exact fin15Anchored_clause07087 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07088 chi hone hbad
                ·
                  exact fin15Anchored_clause07089 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07090 chi hone hbad
                ·
                  exact fin15Anchored_clause07091 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07092 chi hone hbad
                ·
                  exact fin15Anchored_clause07093 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07094 chi hone hbad
                ·
                  exact fin15Anchored_clause07095 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07096 chi hone hbad
                ·
                  exact fin15Anchored_clause07097 chi hone hbad
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
                  exact fin15Anchored_clause07098 chi hone hbad
                ·
                  exact fin15Anchored_clause07099 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07100 chi hone hbad
                ·
                  exact fin15Anchored_clause07101 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07102 chi hbad
                ·
                  exact fin15Anchored_clause07103 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07104 chi hbad
                ·
                  exact fin15Anchored_clause07105 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07106 chi hbad
                ·
                  exact fin15Anchored_clause07107 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07108 chi hbad
                ·
                  exact fin15Anchored_clause07109 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07110 chi hbad
                ·
                  exact fin15Anchored_clause07111 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07112 chi hbad
                ·
                  exact fin15Anchored_clause07113 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07114 chi hbad
                ·
                  exact fin15Anchored_clause07115 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07116 chi hbad
                ·
                  exact fin15Anchored_clause07117 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07118 chi hbad
                ·
                  exact fin15Anchored_clause07119 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07120 chi hbad
                ·
                  exact fin15Anchored_clause07121 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07122 chi hbad
                ·
                  exact fin15Anchored_clause07123 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07124 chi hbad
                ·
                  exact fin15Anchored_clause07125 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07126 chi hbad
                ·
                  exact fin15Anchored_clause07127 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07128 chi hbad
                ·
                  exact fin15Anchored_clause07129 chi hbad
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
                exact fin15Anchored_clause07130 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07131 chi hbad
                ·
                  exact fin15Anchored_clause07132 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07133 chi hbad
                ·
                  exact fin15Anchored_clause07134 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07135 chi hbad
                ·
                  exact fin15Anchored_clause07136 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07137 chi hbad
                ·
                  exact fin15Anchored_clause07138 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07139 chi hbad
                ·
                  exact fin15Anchored_clause07140 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07141 chi hbad
                ·
                  exact fin15Anchored_clause07142 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07143 chi hbad
                ·
                  exact fin15Anchored_clause07144 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07145 chi hbad
                ·
                  exact fin15Anchored_clause07146 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07147 chi hbad
                ·
                  exact fin15Anchored_clause07148 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07149 chi hbad
                ·
                  exact fin15Anchored_clause07150 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07151 chi hbad
                ·
                  exact fin15Anchored_clause07152 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07153 chi hbad
                ·
                  exact fin15Anchored_clause07154 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07155 chi hbad
                ·
                  exact fin15Anchored_clause07156 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07157 chi hbad
                ·
                  exact fin15Anchored_clause07158 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07159 chi hbad
                ·
                  exact fin15Anchored_clause07160 chi hbad
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
                  exact fin15Anchored_clause07161 chi hbad
                ·
                  exact fin15Anchored_clause07162 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07163 chi hbad
                ·
                  exact fin15Anchored_clause07164 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07165 chi hbad
                ·
                  exact fin15Anchored_clause07166 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07167 chi hbad
                ·
                  exact fin15Anchored_clause07168 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07169 chi hbad
                ·
                  exact fin15Anchored_clause07170 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07171 chi hbad
                ·
                  exact fin15Anchored_clause07172 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07173 chi hbad
                ·
                  exact fin15Anchored_clause07174 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07175 chi hbad
                ·
                  exact fin15Anchored_clause07176 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07177 chi hbad
                ·
                  exact fin15Anchored_clause07178 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07179 chi hbad
                ·
                  exact fin15Anchored_clause07180 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07181 chi hbad
                ·
                  exact fin15Anchored_clause07182 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07183 chi hbad
                ·
                  exact fin15Anchored_clause07184 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07185 chi hbad
                ·
                  exact fin15Anchored_clause07186 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07187 chi hbad
                ·
                  exact fin15Anchored_clause07188 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07189 chi hbad
                ·
                  exact fin15Anchored_clause07190 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07191 chi hbad
                ·
                  exact fin15Anchored_clause07192 chi hbad
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
                exact fin15Anchored_clause07193 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07194 chi hbad
                ·
                  exact fin15Anchored_clause07195 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07196 chi hbad
                ·
                  exact fin15Anchored_clause07197 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07198 chi hbad
                ·
                  exact fin15Anchored_clause07199 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07200 chi hbad
                ·
                  exact fin15Anchored_clause07201 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07202 chi hbad
                ·
                  exact fin15Anchored_clause07203 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07204 chi hbad
                ·
                  exact fin15Anchored_clause07205 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07206 chi hbad
                ·
                  exact fin15Anchored_clause07207 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07208 chi hbad
                ·
                  exact fin15Anchored_clause07209 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07210 chi hbad
                ·
                  exact fin15Anchored_clause07211 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07212 chi hbad
                ·
                  exact fin15Anchored_clause07213 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07214 chi hbad
                ·
                  exact fin15Anchored_clause07215 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07216 chi hbad
                ·
                  exact fin15Anchored_clause07217 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07218 chi hbad
                ·
                  exact fin15Anchored_clause07219 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07220 chi hbad
                ·
                  exact fin15Anchored_clause07221 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07222 chi hbad
                ·
                  exact fin15Anchored_clause07223 chi hbad
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
                  exact fin15Anchored_clause07224 chi hbad
                ·
                  exact fin15Anchored_clause07225 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07226 chi hbad
                ·
                  exact fin15Anchored_clause07227 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07228 chi hbad
                ·
                  exact fin15Anchored_clause07229 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07230 chi hbad
                ·
                  exact fin15Anchored_clause07231 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07232 chi hbad
                ·
                  exact fin15Anchored_clause07233 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07234 chi hbad
                ·
                  exact fin15Anchored_clause07235 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07236 chi hbad
                ·
                  exact fin15Anchored_clause07237 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07238 chi hbad
                ·
                  exact fin15Anchored_clause07239 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07240 chi hbad
                ·
                  exact fin15Anchored_clause07241 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07242 chi hbad
                ·
                  exact fin15Anchored_clause07243 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07244 chi hbad
                ·
                  exact fin15Anchored_clause07245 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07246 chi hbad
                ·
                  exact fin15Anchored_clause07247 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07248 chi hbad
                ·
                  exact fin15Anchored_clause07249 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07250 chi hbad
                ·
                  exact fin15Anchored_clause07251 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07252 chi hbad
                ·
                  exact fin15Anchored_clause07253 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07254 chi hbad
                ·
                  exact fin15Anchored_clause07255 chi hbad
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
                exact fin15Anchored_clause07256 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07257 chi hbad
                ·
                  exact fin15Anchored_clause07258 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07259 chi hbad
                ·
                  exact fin15Anchored_clause07260 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07261 chi hbad
                ·
                  exact fin15Anchored_clause07262 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07263 chi hbad
                ·
                  exact fin15Anchored_clause07264 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07265 chi hbad
                ·
                  exact fin15Anchored_clause07266 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07267 chi hbad
                ·
                  exact fin15Anchored_clause07268 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07269 chi hbad
                ·
                  exact fin15Anchored_clause07270 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07271 chi hbad
                ·
                  exact fin15Anchored_clause07272 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07273 chi hbad
                ·
                  exact fin15Anchored_clause07274 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07275 chi hbad
                ·
                  exact fin15Anchored_clause07276 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07277 chi hbad
                ·
                  exact fin15Anchored_clause07278 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07279 chi hbad
                ·
                  exact fin15Anchored_clause07280 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07281 chi hbad
                ·
                  exact fin15Anchored_clause07282 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07283 chi hbad
                ·
                  exact fin15Anchored_clause07284 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07285 chi hbad
                ·
                  exact fin15Anchored_clause07286 chi hbad
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
                  exact fin15Anchored_clause07287 chi hbad
                ·
                  exact fin15Anchored_clause07288 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07289 chi hbad
                ·
                  exact fin15Anchored_clause07290 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07291 chi hbad
                ·
                  exact fin15Anchored_clause07292 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07293 chi hbad
                ·
                  exact fin15Anchored_clause07294 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07295 chi hbad
                ·
                  exact fin15Anchored_clause07296 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07297 chi hbad
                ·
                  exact fin15Anchored_clause07298 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07299 chi hbad
                ·
                  exact fin15Anchored_clause07300 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07301 chi hbad
                ·
                  exact fin15Anchored_clause07302 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07303 chi hbad
                ·
                  exact fin15Anchored_clause07304 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07305 chi hbad
                ·
                  exact fin15Anchored_clause07306 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07307 chi hbad
                ·
                  exact fin15Anchored_clause07308 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07309 chi hbad
                ·
                  exact fin15Anchored_clause07310 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07311 chi hbad
                ·
                  exact fin15Anchored_clause07312 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07313 chi hbad
                ·
                  exact fin15Anchored_clause07314 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07315 chi hbad
                ·
                  exact fin15Anchored_clause07316 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07317 chi hbad
                ·
                  exact fin15Anchored_clause07318 chi hbad

end ErdosSzekeres

end
