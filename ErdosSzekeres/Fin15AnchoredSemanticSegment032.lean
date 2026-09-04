module

public import ErdosSzekeres.Fin15AnchoredClauseChunk063
public import ErdosSzekeres.Fin15AnchoredClauseChunk064
public import ErdosSzekeres.Fin15AnchoredClauseChunk065

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 032. -/

theorem fin15Anchored_rejectSemanticSegment032
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0854 chi) ∨
      ((¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0854 chi) ∨
      (Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0854 chi))) ∨
      (((Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0854 chi) ∨
      (Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0854 chi)) ∨
      ((¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0855 chi) ∨
      (¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0855 chi)))) ∨
      ((((¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0855 chi) ∨
      (¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0855 chi)) ∨
      ((¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0855 chi) ∨
      (Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0855 chi))) ∨
      (((Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0855 chi) ∨
      (Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0855 chi)) ∨
      ((Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0855 chi) ∨
      (¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0856 chi))))) ∨
      (((((¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0856 chi) ∨
      (¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0856 chi)) ∨
      ((¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0856 chi) ∨
      (¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0856 chi))) ∨
      (((Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0856 chi) ∨
      (Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0856 chi)) ∨
      ((Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0856 chi) ∨
      (Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0856 chi)))) ∨
      ((((Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0856 chi) ∨
      (¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0857 chi)) ∨
      ((¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0857 chi) ∨
      (¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0857 chi))) ∨
      (((¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0857 chi) ∨
      (¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0857 chi)) ∨
      ((Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0857 chi) ∨
      (Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0857 chi)))))) ∨
      ((((((Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0857 chi) ∨
      (Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0857 chi)) ∨
      ((Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0857 chi) ∨
      (¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0858 chi))) ∨
      (((¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0859 chi) ∨
      (¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0859 chi)) ∨
      ((¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0859 chi) ∨
      (¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0859 chi)))) ∨
      ((((Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0859 chi) ∨
      (Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0859 chi)) ∨
      ((Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0859 chi) ∨
      (Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0859 chi))) ∨
      (((¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0860 chi) ∨
      (¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0860 chi)) ∨
      ((¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0860 chi) ∨
      (¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0860 chi))))) ∨
      (((((¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0860 chi) ∨
      (Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0860 chi)) ∨
      ((Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0860 chi) ∨
      (Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0860 chi))) ∨
      (((Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0860 chi) ∨
      (Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0860 chi)) ∨
      ((Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0860 chi) ∨
      (Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0861 chi)))) ∨
      ((((Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0861 chi) ∨
      (¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0862 chi)) ∨
      ((¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0862 chi) ∨
      (¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0862 chi))) ∨
      (((¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0862 chi) ∨
      (Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0862 chi)) ∨
      ((Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0862 chi) ∨
      (Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0862 chi))))))) ∨
      ((((((Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0862 chi) ∨
      ((¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0863 chi) ∨
      (¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0863 chi))) ∨
      (((¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0863 chi) ∨
      (¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0863 chi)) ∨
      ((Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0863 chi) ∨
      (Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0863 chi)))) ∨
      ((((Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0863 chi) ∨
      (Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0863 chi)) ∨
      ((Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0863 chi) ∨
      (¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0864 chi))) ∨
      (((¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0864 chi) ∨
      (¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0864 chi)) ∨
      ((¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0864 chi) ∨
      (¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0864 chi))))) ∨
      (((((Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0864 chi) ∨
      (Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0864 chi)) ∨
      ((Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0864 chi) ∨
      (Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0864 chi))) ∨
      (((Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0864 chi) ∨
      (¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0865 chi)) ∨
      ((¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0865 chi) ∨
      (Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0865 chi)))) ∨
      ((((Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0865 chi) ∨
      (¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0866 chi)) ∨
      ((¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0866 chi) ∨
      (Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0866 chi))) ∨
      (((Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0866 chi) ∨
      (Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0866 chi)) ∨
      ((Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0866 chi) ∨
      (¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0868 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0868 chi) ∨
      (Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0868 chi)) ∨
      ((¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0870 chi) ∨
      (¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0870 chi))) ∨
      (((¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0871 chi) ∨
      (¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0871 chi)) ∨
      ((¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0871 chi) ∨
      (¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0871 chi)))) ∨
      ((((Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0871 chi) ∨
      (Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0871 chi)) ∨
      ((Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0871 chi) ∨
      (Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0871 chi))) ∨
      (((Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0871 chi) ∨
      (¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0872 chi)) ∨
      ((¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0872 chi) ∨
      (Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0872 chi))))) ∨
      (((((Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0872 chi) ∨
      (Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0872 chi)) ∨
      ((Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0872 chi) ∨
      (¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0873 chi))) ∨
      (((¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0873 chi) ∨
      (¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0873 chi)) ∨
      ((¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0873 chi) ∨
      (Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0873 chi)))) ∨
      ((((Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0873 chi) ∨
      (Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0873 chi)) ∨
      ((Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0873 chi) ∨
      (¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0874 chi))) ∨
      (((¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0874 chi) ∨
      (¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0874 chi)) ∨
      ((¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0874 chi) ∨
      (Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0874 chi)))))))) ∨
      (((((((Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0874 chi) ∨
      ((Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0874 chi) ∨
      (Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0874 chi))) ∨
      (((¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0875 chi) ∨
      (¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0875 chi)) ∨
      ((¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0875 chi) ∨
      (¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0875 chi)))) ∨
      ((((¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0875 chi) ∨
      (Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0875 chi)) ∨
      ((Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0875 chi) ∨
      (Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0875 chi))) ∨
      (((Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0875 chi) ∨
      (¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0876 chi)) ∨
      ((¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0876 chi) ∨
      (Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0876 chi))))) ∨
      (((((Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0876 chi) ∨
      (¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0877 chi)) ∨
      ((¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0877 chi) ∨
      (¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0877 chi))) ∨
      (((¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0877 chi) ∨
      (¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0877 chi)) ∨
      ((Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0877 chi) ∨
      (Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0877 chi)))) ∨
      ((((Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0877 chi) ∨
      (Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0877 chi)) ∨
      ((¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0878 chi) ∨
      (¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0878 chi))) ∨
      (((¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0878 chi) ∨
      (¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0878 chi)) ∨
      ((Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0878 chi) ∨
      (Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0878 chi)))))) ∨
      ((((((Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0878 chi) ∨
      (Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0878 chi)) ∨
      ((Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0878 chi) ∨
      (¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0879 chi))) ∨
      (((¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0879 chi) ∨
      (¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0879 chi)) ∨
      ((¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0879 chi) ∨
      (Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0879 chi)))) ∨
      ((((Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0879 chi) ∨
      (Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0879 chi)) ∨
      ((Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0879 chi) ∨
      (Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0879 chi))) ∨
      (((¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0880 chi) ∨
      (¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0880 chi)) ∨
      ((Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0880 chi) ∨
      (Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0880 chi))))) ∨
      (((((¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0881 chi) ∨
      (Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0881 chi)) ∨
      ((¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0882 chi) ∨
      (¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0882 chi))) ∨
      (((¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0882 chi) ∨
      (Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0882 chi)) ∨
      ((¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0883 chi) ∨
      (¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0883 chi)))) ∨
      ((((¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0883 chi) ∨
      (¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0883 chi)) ∨
      ((Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0883 chi) ∨
      (Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0883 chi))) ∨
      (((Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0883 chi) ∨
      (Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0883 chi)) ∨
      ((¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0884 chi) ∨
      (¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0884 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0884 chi) ∨
      ((¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0884 chi) ∨
      (Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0884 chi))) ∨
      (((Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0884 chi) ∨
      (Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0884 chi)) ∨
      ((Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0884 chi) ∨
      (¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0885 chi)))) ∨
      ((((¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0885 chi) ∨
      (¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0885 chi)) ∨
      ((¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0885 chi) ∨
      (Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0885 chi))) ∨
      (((Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0885 chi) ∨
      (Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0885 chi)) ∨
      ((Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0885 chi) ∨
      (¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0886 chi))))) ∨
      (((((¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0886 chi) ∨
      (¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0886 chi)) ∨
      ((¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0886 chi) ∨
      (Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0886 chi))) ∨
      (((Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0886 chi) ∨
      (Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0886 chi)) ∨
      ((Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0886 chi) ∨
      (Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0886 chi)))) ∨
      ((((¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0887 chi) ∨
      (¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0887 chi)) ∨
      ((¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0887 chi) ∨
      (¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0887 chi))) ∨
      (((Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0887 chi) ∨
      (Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0887 chi)) ∨
      ((Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0887 chi) ∨
      (Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0887 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0888 chi) ∨
      (¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0888 chi)) ∨
      ((¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0888 chi) ∨
      (¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0888 chi))) ∨
      (((Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0888 chi) ∨
      (Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0888 chi)) ∨
      ((Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0888 chi) ∨
      (Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0888 chi)))) ∨
      ((((¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0889 chi) ∨
      (¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0889 chi)) ∨
      ((¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0889 chi) ∨
      (¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0889 chi))) ∨
      (((Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0889 chi) ∨
      (Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0889 chi)) ∨
      ((Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0889 chi) ∨
      (Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0889 chi))))) ∨
      (((((¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0890 chi) ∨
      (¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0890 chi)) ∨
      ((¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0890 chi) ∨
      (¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0890 chi))) ∨
      (((¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0890 chi) ∨
      (Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0890 chi)) ∨
      ((Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0890 chi) ∨
      (Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0890 chi)))) ∨
      ((((Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0890 chi) ∨
      (¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0891 chi)) ∨
      ((¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0891 chi) ∨
      (¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0891 chi))) ∨
      (((¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0891 chi) ∨
      (Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0891 chi)) ∨
      ((Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0891 chi) ∨
      (Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0891 chi)))))))))) := by
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
                exact fin15Anchored_clause08077 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08078 chi hbad
                ·
                  exact fin15Anchored_clause08079 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08080 chi hbad
                ·
                  exact fin15Anchored_clause08081 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08082 chi hbad
                ·
                  exact fin15Anchored_clause08083 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08084 chi hbad
                ·
                  exact fin15Anchored_clause08085 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08086 chi hbad
                ·
                  exact fin15Anchored_clause08087 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08088 chi hbad
                ·
                  exact fin15Anchored_clause08089 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08090 chi hbad
                ·
                  exact fin15Anchored_clause08091 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08092 chi hbad
                ·
                  exact fin15Anchored_clause08093 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08094 chi hbad
                ·
                  exact fin15Anchored_clause08095 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08096 chi hbad
                ·
                  exact fin15Anchored_clause08097 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08098 chi hbad
                ·
                  exact fin15Anchored_clause08099 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08100 chi hbad
                ·
                  exact fin15Anchored_clause08101 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08102 chi hbad
                ·
                  exact fin15Anchored_clause08103 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08104 chi hbad
                ·
                  exact fin15Anchored_clause08105 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08106 chi hbad
                ·
                  exact fin15Anchored_clause08107 chi hbad
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
                  exact fin15Anchored_clause08108 chi hbad
                ·
                  exact fin15Anchored_clause08109 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08110 chi hbad
                ·
                  exact fin15Anchored_clause08111 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08112 chi hbad
                ·
                  exact fin15Anchored_clause08113 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08114 chi hbad
                ·
                  exact fin15Anchored_clause08115 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08116 chi hbad
                ·
                  exact fin15Anchored_clause08117 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08118 chi hbad
                ·
                  exact fin15Anchored_clause08119 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08120 chi hbad
                ·
                  exact fin15Anchored_clause08121 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08122 chi hbad
                ·
                  exact fin15Anchored_clause08123 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08124 chi hbad
                ·
                  exact fin15Anchored_clause08125 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08126 chi hbad
                ·
                  exact fin15Anchored_clause08127 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08128 chi hbad
                ·
                  exact fin15Anchored_clause08129 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08130 chi hbad
                ·
                  exact fin15Anchored_clause08131 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08132 chi hbad
                ·
                  exact fin15Anchored_clause08133 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08134 chi hbad
                ·
                  exact fin15Anchored_clause08135 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08136 chi hbad
                ·
                  exact fin15Anchored_clause08137 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08138 chi hbad
                ·
                  exact fin15Anchored_clause08139 chi hbad
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
                exact fin15Anchored_clause08140 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08141 chi hbad
                ·
                  exact fin15Anchored_clause08142 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08143 chi hbad
                ·
                  exact fin15Anchored_clause08144 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08145 chi hbad
                ·
                  exact fin15Anchored_clause08146 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08147 chi hbad
                ·
                  exact fin15Anchored_clause08148 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08149 chi hbad
                ·
                  exact fin15Anchored_clause08150 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08151 chi hbad
                ·
                  exact fin15Anchored_clause08152 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08153 chi hbad
                ·
                  exact fin15Anchored_clause08154 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08155 chi hbad
                ·
                  exact fin15Anchored_clause08156 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08157 chi hbad
                ·
                  exact fin15Anchored_clause08158 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08159 chi hbad
                ·
                  exact fin15Anchored_clause08160 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08161 chi hbad
                ·
                  exact fin15Anchored_clause08162 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08163 chi hbad
                ·
                  exact fin15Anchored_clause08164 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08165 chi hbad
                ·
                  exact fin15Anchored_clause08166 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08167 chi hbad
                ·
                  exact fin15Anchored_clause08168 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08169 chi hbad
                ·
                  exact fin15Anchored_clause08170 chi hbad
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
                  exact fin15Anchored_clause08171 chi hbad
                ·
                  exact fin15Anchored_clause08172 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08173 chi hbad
                ·
                  exact fin15Anchored_clause08174 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08175 chi hbad
                ·
                  exact fin15Anchored_clause08176 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08177 chi hbad
                ·
                  exact fin15Anchored_clause08178 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08179 chi hbad
                ·
                  exact fin15Anchored_clause08180 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08181 chi hbad
                ·
                  exact fin15Anchored_clause08182 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08183 chi hbad
                ·
                  exact fin15Anchored_clause08184 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08185 chi hbad
                ·
                  exact fin15Anchored_clause08186 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08187 chi hbad
                ·
                  exact fin15Anchored_clause08188 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08189 chi hbad
                ·
                  exact fin15Anchored_clause08190 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08191 chi hbad
                ·
                  exact fin15Anchored_clause08192 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08193 chi hbad
                ·
                  exact fin15Anchored_clause08194 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08195 chi hbad
                ·
                  exact fin15Anchored_clause08196 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08197 chi hbad
                ·
                  exact fin15Anchored_clause08198 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08199 chi hbad
                ·
                  exact fin15Anchored_clause08200 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08201 chi hbad
                ·
                  exact fin15Anchored_clause08202 chi hbad
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
                exact fin15Anchored_clause08203 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08204 chi hbad
                ·
                  exact fin15Anchored_clause08205 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08206 chi hbad
                ·
                  exact fin15Anchored_clause08207 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08208 chi hbad
                ·
                  exact fin15Anchored_clause08209 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08210 chi hbad
                ·
                  exact fin15Anchored_clause08211 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08212 chi hbad
                ·
                  exact fin15Anchored_clause08213 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08214 chi hbad
                ·
                  exact fin15Anchored_clause08215 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08216 chi hbad
                ·
                  exact fin15Anchored_clause08217 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08218 chi hbad
                ·
                  exact fin15Anchored_clause08219 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08220 chi hbad
                ·
                  exact fin15Anchored_clause08221 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08222 chi hbad
                ·
                  exact fin15Anchored_clause08223 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08224 chi hbad
                ·
                  exact fin15Anchored_clause08225 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08226 chi hbad
                ·
                  exact fin15Anchored_clause08227 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08228 chi hbad
                ·
                  exact fin15Anchored_clause08229 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08230 chi hbad
                ·
                  exact fin15Anchored_clause08231 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08232 chi hbad
                ·
                  exact fin15Anchored_clause08233 chi hbad
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
                  exact fin15Anchored_clause08234 chi hbad
                ·
                  exact fin15Anchored_clause08235 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08236 chi hbad
                ·
                  exact fin15Anchored_clause08237 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08238 chi hbad
                ·
                  exact fin15Anchored_clause08239 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08240 chi hbad
                ·
                  exact fin15Anchored_clause08241 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08242 chi hbad
                ·
                  exact fin15Anchored_clause08243 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08244 chi hbad
                ·
                  exact fin15Anchored_clause08245 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08246 chi hbad
                ·
                  exact fin15Anchored_clause08247 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08248 chi hbad
                ·
                  exact fin15Anchored_clause08249 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08250 chi hbad
                ·
                  exact fin15Anchored_clause08251 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08252 chi hbad
                ·
                  exact fin15Anchored_clause08253 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08254 chi hbad
                ·
                  exact fin15Anchored_clause08255 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08256 chi hbad
                ·
                  exact fin15Anchored_clause08257 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08258 chi hbad
                ·
                  exact fin15Anchored_clause08259 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08260 chi hbad
                ·
                  exact fin15Anchored_clause08261 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08262 chi hbad
                ·
                  exact fin15Anchored_clause08263 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08264 chi hbad
                ·
                  exact fin15Anchored_clause08265 chi hbad
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
                exact fin15Anchored_clause08266 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08267 chi hbad
                ·
                  exact fin15Anchored_clause08268 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08269 chi hbad
                ·
                  exact fin15Anchored_clause08270 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08271 chi hbad
                ·
                  exact fin15Anchored_clause08272 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08273 chi hbad
                ·
                  exact fin15Anchored_clause08274 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08275 chi hbad
                ·
                  exact fin15Anchored_clause08276 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08277 chi hbad
                ·
                  exact fin15Anchored_clause08278 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08279 chi hbad
                ·
                  exact fin15Anchored_clause08280 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08281 chi hbad
                ·
                  exact fin15Anchored_clause08282 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08283 chi hbad
                ·
                  exact fin15Anchored_clause08284 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08285 chi hbad
                ·
                  exact fin15Anchored_clause08286 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08287 chi hbad
                ·
                  exact fin15Anchored_clause08288 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08289 chi hbad
                ·
                  exact fin15Anchored_clause08290 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08291 chi hbad
                ·
                  exact fin15Anchored_clause08292 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08293 chi hbad
                ·
                  exact fin15Anchored_clause08294 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08295 chi hbad
                ·
                  exact fin15Anchored_clause08296 chi hbad
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
                  exact fin15Anchored_clause08297 chi hbad
                ·
                  exact fin15Anchored_clause08298 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08299 chi hbad
                ·
                  exact fin15Anchored_clause08300 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08301 chi hbad
                ·
                  exact fin15Anchored_clause08302 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08303 chi hbad
                ·
                  exact fin15Anchored_clause08304 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08305 chi hbad
                ·
                  exact fin15Anchored_clause08306 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08307 chi hbad
                ·
                  exact fin15Anchored_clause08308 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08309 chi hbad
                ·
                  exact fin15Anchored_clause08310 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08311 chi hbad
                ·
                  exact fin15Anchored_clause08312 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08313 chi hbad
                ·
                  exact fin15Anchored_clause08314 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08315 chi hbad
                ·
                  exact fin15Anchored_clause08316 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08317 chi hbad
                ·
                  exact fin15Anchored_clause08318 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08319 chi hbad
                ·
                  exact fin15Anchored_clause08320 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08321 chi hbad
                ·
                  exact fin15Anchored_clause08322 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08323 chi hbad
                ·
                  exact fin15Anchored_clause08324 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08325 chi hbad
                ·
                  exact fin15Anchored_clause08326 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08327 chi hbad
                ·
                  exact fin15Anchored_clause08328 chi hbad

end ErdosSzekeres

end
