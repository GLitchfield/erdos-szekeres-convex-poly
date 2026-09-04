module

public import ErdosSzekeres.Fin15AnchoredClauseChunk070
public import ErdosSzekeres.Fin15AnchoredClauseChunk071
public import ErdosSzekeres.Fin15AnchoredClauseChunk072

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 036. -/

theorem fin15Anchored_rejectSemanticSegment036
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0987 chi) ∨
      ((Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0987 chi) ∨
      (Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0987 chi))) ∨
      (((Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0987 chi) ∨
      (Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0987 chi)) ∨
      ((¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0988 chi) ∨
      (¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0988 chi)))) ∨
      ((((¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0988 chi) ∨
      (¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0988 chi)) ∨
      ((Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0988 chi) ∨
      (Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0988 chi))) ∨
      (((Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0988 chi) ∨
      (Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0988 chi)) ∨
      ((Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0988 chi) ∨
      (¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0989 chi))))) ∨
      (((((¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0989 chi) ∨
      (¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0989 chi)) ∨
      ((¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0989 chi) ∨
      (¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0989 chi))) ∨
      (((¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0989 chi) ∨
      (Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0989 chi)) ∨
      ((Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0989 chi) ∨
      (Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0989 chi)))) ∨
      ((((Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0989 chi) ∨
      (Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0989 chi)) ∨
      ((Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0989 chi) ∨
      (Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0989 chi))) ∨
      (((¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0990 chi) ∨
      (¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0990 chi)) ∨
      ((Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0990 chi) ∨
      (Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0990 chi)))))) ∨
      ((((((Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0990 chi) ∨
      (Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0990 chi)) ∨
      ((¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0991 chi) ∨
      (¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0991 chi))) ∨
      (((¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0991 chi) ∨
      (¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0991 chi)) ∨
      ((¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0991 chi) ∨
      (Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0991 chi)))) ∨
      ((((Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0991 chi) ∨
      (Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0991 chi)) ∨
      ((Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0991 chi) ∨
      (Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0991 chi))) ∨
      (((¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0992 chi) ∨
      (¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0992 chi)) ∨
      ((¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0992 chi) ∨
      (¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0992 chi))))) ∨
      (((((¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0992 chi) ∨
      (Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0992 chi)) ∨
      ((Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0992 chi) ∨
      (Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0992 chi))) ∨
      (((Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0992 chi) ∨
      (Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0992 chi)) ∨
      ((¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0993 chi) ∨
      (¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0993 chi)))) ∨
      ((((¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0993 chi) ∨
      (¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0993 chi)) ∨
      ((¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0993 chi) ∨
      (Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0993 chi))) ∨
      (((Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0993 chi) ∨
      (Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0993 chi)) ∨
      ((Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0993 chi) ∨
      (Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0993 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0994 chi) ∨
      ((¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0994 chi) ∨
      (¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0994 chi))) ∨
      (((¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0994 chi) ∨
      (Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0994 chi)) ∨
      ((Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0994 chi) ∨
      (Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0994 chi)))) ∨
      ((((Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0994 chi) ∨
      (¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0995 chi)) ∨
      ((¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0995 chi) ∨
      (¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0995 chi))) ∨
      (((¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0995 chi) ∨
      (¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0995 chi)) ∨
      ((Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0995 chi) ∨
      (Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0995 chi))))) ∨
      (((((Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0995 chi) ∨
      (Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0995 chi)) ∨
      ((Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0995 chi) ∨
      (¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0996 chi))) ∨
      (((¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0996 chi) ∨
      (¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0996 chi)) ∨
      ((¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0996 chi) ∨
      (¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0996 chi)))) ∨
      ((((¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0996 chi) ∨
      (Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0996 chi)) ∨
      ((Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0996 chi) ∨
      (Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0996 chi))) ∨
      (((Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0996 chi) ∨
      (Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0997 chi)) ∨
      ((Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0997 chi) ∨
      (¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0998 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0998 chi) ∨
      (¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0998 chi)) ∨
      ((¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0998 chi) ∨
      (¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0998 chi))) ∨
      (((Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0998 chi) ∨
      (Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0998 chi)) ∨
      ((Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0998 chi) ∨
      (Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0998 chi)))) ∨
      ((((¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0999 chi) ∨
      (¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0999 chi)) ∨
      ((¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0999 chi) ∨
      (¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0999 chi))) ∨
      (((¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0999 chi) ∨
      (¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0999 chi)) ∨
      ((Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0999 chi) ∨
      (Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0999 chi))))) ∨
      (((((Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0999 chi) ∨
      (Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0999 chi)) ∨
      ((Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0999 chi) ∨
      (¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom1000 chi))) ∨
      (((¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1000 chi) ∨
      (¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1000 chi)) ∨
      ((¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom1000 chi) ∨
      (¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1000 chi)))) ∨
      ((((Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1000 chi) ∨
      (Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1000 chi)) ∨
      ((Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom1000 chi) ∨
      (Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1000 chi))) ∨
      (((Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom1000 chi) ∨
      (¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom1001 chi)) ∨
      ((¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom1001 chi) ∨
      (¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom1001 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom1001 chi) ∨
      ((¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom1001 chi) ∨
      (Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom1001 chi))) ∨
      (((Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom1001 chi) ∨
      (Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom1001 chi)) ∨
      ((Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom1001 chi) ∨
      (Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom1001 chi)))) ∨
      ((((Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom1001 chi) ∨
      (¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom1002 chi)) ∨
      ((¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom1002 chi) ∨
      (¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom1002 chi))) ∨
      (((¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom1002 chi) ∨
      (¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom1002 chi)) ∨
      ((Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom1002 chi) ∨
      (Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom1002 chi))))) ∨
      (((((Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom1002 chi) ∨
      (Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom1002 chi)) ∨
      ((¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom1004 chi) ∨
      (¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom1004 chi))) ∨
      (((¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom1004 chi) ∨
      (¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom1004 chi)) ∨
      ((Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom1004 chi) ∨
      (Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom1004 chi)))) ∨
      ((((Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom1004 chi) ∨
      (Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom1004 chi)) ∨
      ((¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom1005 chi) ∨
      (¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom1005 chi))) ∨
      (((¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom1005 chi) ∨
      (¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom1005 chi)) ∨
      ((Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom1005 chi) ∨
      (Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom1005 chi)))))) ∨
      ((((((Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom1005 chi) ∨
      (Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom1005 chi)) ∨
      ((¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom1006 chi) ∨
      (¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom1006 chi))) ∨
      (((¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom1006 chi) ∨
      (¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom1006 chi)) ∨
      ((¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom1006 chi) ∨
      (¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom1006 chi)))) ∨
      ((((Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom1006 chi) ∨
      (Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom1006 chi)) ∨
      ((Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom1006 chi) ∨
      (¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom1007 chi))) ∨
      (((¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1007 chi) ∨
      (¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom1007 chi)) ∨
      ((¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1007 chi) ∨
      (Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1007 chi))))) ∨
      (((((Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1007 chi) ∨
      (Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom1007 chi)) ∨
      ((Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1007 chi) ∨
      (Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1007 chi))) ∨
      (((Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom1007 chi) ∨
      (Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom1008 chi)) ∨
      ((Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom1008 chi) ∨
      (Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom1008 chi)))) ∨
      ((((Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom1008 chi) ∨
      (Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom1008 chi)) ∨
      ((¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom1009 chi) ∨
      (¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1009 chi))) ∨
      (((¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom1009 chi) ∨
      (¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1009 chi)) ∨
      ((Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1009 chi) ∨
      (Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom1009 chi))))))) ∨
      ((((((Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1009 chi) ∨
      ((Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1009 chi) ∨
      (Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom1009 chi))) ∨
      (((¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom1010 chi) ∨
      (¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1010 chi)) ∨
      ((¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom1010 chi) ∨
      (¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1010 chi)))) ∨
      ((((Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1010 chi) ∨
      (Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1010 chi)) ∨
      ((Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom1010 chi) ∨
      (Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1010 chi))) ∨
      (((Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom1010 chi) ∨
      (¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom1011 chi)) ∨
      ((¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom1011 chi) ∨
      (¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom1011 chi))))) ∨
      (((((¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom1011 chi) ∨
      (¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom1011 chi)) ∨
      ((Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom1011 chi) ∨
      (Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom1011 chi))) ∨
      (((Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom1011 chi) ∨
      (Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom1011 chi)) ∨
      ((Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom1011 chi) ∨
      (¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom1012 chi)))) ∨
      ((((¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom1012 chi) ∨
      (¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom1012 chi)) ∨
      ((Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom1012 chi) ∨
      (Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom1012 chi))) ∨
      (((Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom1012 chi) ∨
      (Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom1012 chi)) ∨
      ((Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom1012 chi) ∨
      (¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom1013 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom1013 chi) ∨
      (¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom1013 chi)) ∨
      ((¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom1013 chi) ∨
      (Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom1013 chi))) ∨
      (((Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom1013 chi) ∨
      (Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom1013 chi)) ∨
      ((Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom1013 chi) ∨
      (¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom1014 chi)))) ∨
      ((((¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom1014 chi) ∨
      (¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom1014 chi)) ∨
      ((¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom1014 chi) ∨
      (Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom1014 chi))) ∨
      (((Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom1014 chi) ∨
      (Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom1014 chi)) ∨
      ((Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom1014 chi) ∨
      (Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom1014 chi))))) ∨
      (((((¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom1015 chi) ∨
      (¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom1015 chi)) ∨
      ((¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom1015 chi) ∨
      (¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom1015 chi))) ∨
      (((Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom1015 chi) ∨
      (Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom1015 chi)) ∨
      ((Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom1015 chi) ∨
      (Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom1015 chi)))) ∨
      ((((¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom1016 chi) ∨
      (Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom1016 chi)) ∨
      ((Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom1016 chi) ∨
      (Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom1016 chi))) ∨
      (((Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom1016 chi) ∨
      (¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom1017 chi)) ∨
      ((¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom1019 chi) ∨
      (¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1019 chi)))))))))) := by
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
                exact fin15Anchored_clause09086 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09087 chi hbad
                ·
                  exact fin15Anchored_clause09088 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09089 chi hbad
                ·
                  exact fin15Anchored_clause09090 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09091 chi hbad
                ·
                  exact fin15Anchored_clause09092 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09093 chi hbad
                ·
                  exact fin15Anchored_clause09094 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09095 chi hbad
                ·
                  exact fin15Anchored_clause09096 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09097 chi hbad
                ·
                  exact fin15Anchored_clause09098 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09099 chi hbad
                ·
                  exact fin15Anchored_clause09100 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09101 chi hbad
                ·
                  exact fin15Anchored_clause09102 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09103 chi hbad
                ·
                  exact fin15Anchored_clause09104 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09105 chi hbad
                ·
                  exact fin15Anchored_clause09106 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09107 chi hbad
                ·
                  exact fin15Anchored_clause09108 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09109 chi hbad
                ·
                  exact fin15Anchored_clause09110 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09111 chi hbad
                ·
                  exact fin15Anchored_clause09112 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09113 chi hbad
                ·
                  exact fin15Anchored_clause09114 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09115 chi hbad
                ·
                  exact fin15Anchored_clause09116 chi hbad
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
                  exact fin15Anchored_clause09117 chi hbad
                ·
                  exact fin15Anchored_clause09118 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09119 chi hbad
                ·
                  exact fin15Anchored_clause09120 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09121 chi hbad
                ·
                  exact fin15Anchored_clause09122 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09123 chi hbad
                ·
                  exact fin15Anchored_clause09124 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09125 chi hbad
                ·
                  exact fin15Anchored_clause09126 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09127 chi hbad
                ·
                  exact fin15Anchored_clause09128 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09129 chi hbad
                ·
                  exact fin15Anchored_clause09130 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09131 chi hbad
                ·
                  exact fin15Anchored_clause09132 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09133 chi hbad
                ·
                  exact fin15Anchored_clause09134 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09135 chi hbad
                ·
                  exact fin15Anchored_clause09136 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09137 chi hbad
                ·
                  exact fin15Anchored_clause09138 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09139 chi hbad
                ·
                  exact fin15Anchored_clause09140 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09141 chi hbad
                ·
                  exact fin15Anchored_clause09142 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09143 chi hbad
                ·
                  exact fin15Anchored_clause09144 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09145 chi hbad
                ·
                  exact fin15Anchored_clause09146 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09147 chi hbad
                ·
                  exact fin15Anchored_clause09148 chi hbad
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
                exact fin15Anchored_clause09149 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09150 chi hbad
                ·
                  exact fin15Anchored_clause09151 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09152 chi hbad
                ·
                  exact fin15Anchored_clause09153 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09154 chi hbad
                ·
                  exact fin15Anchored_clause09155 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09156 chi hbad
                ·
                  exact fin15Anchored_clause09157 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09158 chi hbad
                ·
                  exact fin15Anchored_clause09159 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09160 chi hbad
                ·
                  exact fin15Anchored_clause09161 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09162 chi hbad
                ·
                  exact fin15Anchored_clause09163 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09164 chi hbad
                ·
                  exact fin15Anchored_clause09165 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09166 chi hbad
                ·
                  exact fin15Anchored_clause09167 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09168 chi hbad
                ·
                  exact fin15Anchored_clause09169 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09170 chi hbad
                ·
                  exact fin15Anchored_clause09171 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09172 chi hbad
                ·
                  exact fin15Anchored_clause09173 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09174 chi hbad
                ·
                  exact fin15Anchored_clause09175 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09176 chi hbad
                ·
                  exact fin15Anchored_clause09177 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09178 chi hbad
                ·
                  exact fin15Anchored_clause09179 chi hbad
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
                  exact fin15Anchored_clause09180 chi hbad
                ·
                  exact fin15Anchored_clause09181 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09182 chi hbad
                ·
                  exact fin15Anchored_clause09183 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09184 chi hbad
                ·
                  exact fin15Anchored_clause09185 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09186 chi hbad
                ·
                  exact fin15Anchored_clause09187 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09188 chi hbad
                ·
                  exact fin15Anchored_clause09189 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09190 chi hbad
                ·
                  exact fin15Anchored_clause09191 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09192 chi hbad
                ·
                  exact fin15Anchored_clause09193 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09194 chi hbad
                ·
                  exact fin15Anchored_clause09195 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09196 chi hbad
                ·
                  exact fin15Anchored_clause09197 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09198 chi hbad
                ·
                  exact fin15Anchored_clause09199 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09200 chi hbad
                ·
                  exact fin15Anchored_clause09201 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09202 chi hbad
                ·
                  exact fin15Anchored_clause09203 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09204 chi hbad
                ·
                  exact fin15Anchored_clause09205 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09206 chi hbad
                ·
                  exact fin15Anchored_clause09207 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09208 chi hbad
                ·
                  exact fin15Anchored_clause09209 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09210 chi hbad
                ·
                  exact fin15Anchored_clause09211 chi hbad
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
                exact fin15Anchored_clause09212 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09213 chi hbad
                ·
                  exact fin15Anchored_clause09214 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09215 chi hbad
                ·
                  exact fin15Anchored_clause09216 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09217 chi hbad
                ·
                  exact fin15Anchored_clause09218 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09219 chi hbad
                ·
                  exact fin15Anchored_clause09220 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09221 chi hbad
                ·
                  exact fin15Anchored_clause09222 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09223 chi hbad
                ·
                  exact fin15Anchored_clause09224 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09225 chi hbad
                ·
                  exact fin15Anchored_clause09226 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09227 chi hbad
                ·
                  exact fin15Anchored_clause09228 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09229 chi hbad
                ·
                  exact fin15Anchored_clause09230 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09231 chi hbad
                ·
                  exact fin15Anchored_clause09232 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09233 chi hbad
                ·
                  exact fin15Anchored_clause09234 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09235 chi hbad
                ·
                  exact fin15Anchored_clause09236 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09237 chi hbad
                ·
                  exact fin15Anchored_clause09238 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09239 chi hbad
                ·
                  exact fin15Anchored_clause09240 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09241 chi hbad
                ·
                  exact fin15Anchored_clause09242 chi hbad
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
                  exact fin15Anchored_clause09243 chi hbad
                ·
                  exact fin15Anchored_clause09244 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09245 chi hbad
                ·
                  exact fin15Anchored_clause09246 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09247 chi hbad
                ·
                  exact fin15Anchored_clause09248 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09249 chi hbad
                ·
                  exact fin15Anchored_clause09250 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09251 chi hbad
                ·
                  exact fin15Anchored_clause09252 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09253 chi hbad
                ·
                  exact fin15Anchored_clause09254 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09255 chi hbad
                ·
                  exact fin15Anchored_clause09256 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09257 chi hbad
                ·
                  exact fin15Anchored_clause09258 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09259 chi hbad
                ·
                  exact fin15Anchored_clause09260 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09261 chi hbad
                ·
                  exact fin15Anchored_clause09262 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09263 chi hbad
                ·
                  exact fin15Anchored_clause09264 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09265 chi hbad
                ·
                  exact fin15Anchored_clause09266 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09267 chi hbad
                ·
                  exact fin15Anchored_clause09268 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09269 chi hbad
                ·
                  exact fin15Anchored_clause09270 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09271 chi hbad
                ·
                  exact fin15Anchored_clause09272 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09273 chi hbad
                ·
                  exact fin15Anchored_clause09274 chi hbad
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
                exact fin15Anchored_clause09275 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09276 chi hbad
                ·
                  exact fin15Anchored_clause09277 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09278 chi hbad
                ·
                  exact fin15Anchored_clause09279 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09280 chi hbad
                ·
                  exact fin15Anchored_clause09281 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09282 chi hbad
                ·
                  exact fin15Anchored_clause09283 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09284 chi hbad
                ·
                  exact fin15Anchored_clause09285 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09286 chi hbad
                ·
                  exact fin15Anchored_clause09287 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09288 chi hbad
                ·
                  exact fin15Anchored_clause09289 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09290 chi hbad
                ·
                  exact fin15Anchored_clause09291 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09292 chi hbad
                ·
                  exact fin15Anchored_clause09293 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09294 chi hbad
                ·
                  exact fin15Anchored_clause09295 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09296 chi hbad
                ·
                  exact fin15Anchored_clause09297 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09298 chi hbad
                ·
                  exact fin15Anchored_clause09299 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09300 chi hbad
                ·
                  exact fin15Anchored_clause09301 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09302 chi hbad
                ·
                  exact fin15Anchored_clause09303 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09304 chi hbad
                ·
                  exact fin15Anchored_clause09305 chi hbad
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
                  exact fin15Anchored_clause09306 chi hbad
                ·
                  exact fin15Anchored_clause09307 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09308 chi hbad
                ·
                  exact fin15Anchored_clause09309 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09310 chi hbad
                ·
                  exact fin15Anchored_clause09311 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09312 chi hbad
                ·
                  exact fin15Anchored_clause09313 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09314 chi hbad
                ·
                  exact fin15Anchored_clause09315 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09316 chi hbad
                ·
                  exact fin15Anchored_clause09317 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09318 chi hbad
                ·
                  exact fin15Anchored_clause09319 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09320 chi hbad
                ·
                  exact fin15Anchored_clause09321 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09322 chi hbad
                ·
                  exact fin15Anchored_clause09323 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09324 chi hbad
                ·
                  exact fin15Anchored_clause09325 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09326 chi hbad
                ·
                  exact fin15Anchored_clause09327 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09328 chi hbad
                ·
                  exact fin15Anchored_clause09329 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09330 chi hbad
                ·
                  exact fin15Anchored_clause09331 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09332 chi hbad
                ·
                  exact fin15Anchored_clause09333 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09334 chi hbad
                ·
                  exact fin15Anchored_clause09335 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09336 chi hbad
                ·
                  exact fin15Anchored_clause09337 chi hbad

end ErdosSzekeres

end
