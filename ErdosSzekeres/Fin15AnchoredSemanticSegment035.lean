module

public import ErdosSzekeres.Fin15AnchoredClauseChunk069
public import ErdosSzekeres.Fin15AnchoredClauseChunk070

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 035. -/

theorem fin15Anchored_rejectSemanticSegment035
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0955 chi) ∨
      ((¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0955 chi) ∨
      (Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0955 chi))) ∨
      (((Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0955 chi) ∨
      (Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0955 chi)) ∨
      ((Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0955 chi) ∨
      (¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0956 chi)))) ∨
      ((((¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0956 chi) ∨
      (¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0956 chi)) ∨
      ((¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0956 chi) ∨
      (¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0956 chi))) ∨
      (((Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0956 chi) ∨
      (Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0956 chi)) ∨
      ((Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0956 chi) ∨
      (Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0956 chi))))) ∨
      (((((¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0957 chi) ∨
      (¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0957 chi)) ∨
      ((¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0957 chi) ∨
      (¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0957 chi))) ∨
      (((¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0957 chi) ∨
      (Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0957 chi)) ∨
      ((Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0957 chi) ∨
      (Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0957 chi)))) ∨
      ((((Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0957 chi) ∨
      (¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0958 chi)) ∨
      ((¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0958 chi) ∨
      (¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0958 chi))) ∨
      (((¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0958 chi) ∨
      (Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0958 chi)) ∨
      ((Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0958 chi) ∨
      (Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0958 chi)))))) ∨
      ((((((Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0958 chi) ∨
      (¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0959 chi)) ∨
      ((¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0959 chi) ∨
      (¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0959 chi))) ∨
      (((¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0959 chi) ∨
      (Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0959 chi)) ∨
      ((Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0959 chi) ∨
      (Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0959 chi)))) ∨
      ((((Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0959 chi) ∨
      (Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0959 chi)) ∨
      ((¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0960 chi) ∨
      (¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0960 chi))) ∨
      (((¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0960 chi) ∨
      (¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0960 chi)) ∨
      ((¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0960 chi) ∨
      (¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0960 chi))))) ∨
      (((((Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0960 chi) ∨
      (Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0960 chi)) ∨
      ((Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0960 chi) ∨
      (Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0960 chi))) ∨
      (((¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0961 chi) ∨
      (¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0961 chi)) ∨
      ((¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0961 chi) ∨
      (¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0961 chi)))) ∨
      ((((¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0961 chi) ∨
      (Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0961 chi)) ∨
      ((Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0961 chi) ∨
      (Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0961 chi))) ∨
      (((Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0961 chi) ∨
      (Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0961 chi)) ∨
      ((Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0961 chi) ∨
      (¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0962 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0962 chi) ∨
      ((¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0962 chi) ∨
      (¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0962 chi))) ∨
      (((Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0962 chi) ∨
      (Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0962 chi)) ∨
      ((Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0962 chi) ∨
      (Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0962 chi)))) ∨
      ((((¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0963 chi) ∨
      (¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0963 chi)) ∨
      ((¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0963 chi) ∨
      (¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0963 chi))) ∨
      (((¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0963 chi) ∨
      (Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0963 chi)) ∨
      ((Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0963 chi) ∨
      (Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0963 chi))))) ∨
      (((((Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0963 chi) ∨
      (Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0963 chi)) ∨
      ((¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0964 chi) ∨
      (¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0964 chi))) ∨
      (((¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0964 chi) ∨
      (¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0964 chi)) ∨
      ((¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0964 chi) ∨
      (Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0964 chi)))) ∨
      ((((Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0964 chi) ∨
      (Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0964 chi)) ∨
      ((Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0964 chi) ∨
      (Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0964 chi))) ∨
      (((¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0965 chi) ∨
      (¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0965 chi)) ∨
      ((¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0965 chi) ∨
      (¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0965 chi)))))) ∨
      ((((((Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0965 chi) ∨
      (Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0965 chi)) ∨
      ((Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0965 chi) ∨
      (Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0965 chi))) ∨
      (((¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0966 chi) ∨
      (¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0966 chi)) ∨
      ((¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0966 chi) ∨
      (¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0966 chi)))) ∨
      ((((¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0966 chi) ∨
      (Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0966 chi)) ∨
      ((Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0966 chi) ∨
      (Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0966 chi))) ∨
      (((Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0966 chi) ∨
      (Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0966 chi)) ∨
      ((Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0966 chi) ∨
      (¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0968 chi))))) ∨
      (((((¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0968 chi) ∨
      (¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0968 chi)) ∨
      ((¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0968 chi) ∨
      (Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0968 chi))) ∨
      (((Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0968 chi) ∨
      (Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0968 chi)) ∨
      ((Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0968 chi) ∨
      (Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0968 chi)))) ∨
      ((((¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0969 chi) ∨
      (¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0969 chi)) ∨
      ((¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0969 chi) ∨
      (¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0969 chi))) ∨
      (((Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0969 chi) ∨
      (Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0969 chi)) ∨
      ((Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0969 chi) ∨
      (Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0969 chi)))))))) ∨
      (((((((Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0969 chi) ∨
      ((¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0970 chi) ∨
      (¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0970 chi))) ∨
      (((¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0970 chi) ∨
      (¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0970 chi)) ∨
      ((¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0970 chi) ∨
      (¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0970 chi)))) ∨
      ((((Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0970 chi) ∨
      (Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0970 chi)) ∨
      ((Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0970 chi) ∨
      (¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0971 chi))) ∨
      (((¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0971 chi) ∨
      (¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0971 chi)) ∨
      ((¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0971 chi) ∨
      (Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0971 chi))))) ∨
      (((((Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0971 chi) ∨
      (Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0971 chi)) ∨
      ((Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0971 chi) ∨
      (Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0971 chi))) ∨
      (((¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0972 chi) ∨
      (¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0972 chi)) ∨
      ((¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0972 chi) ∨
      (Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0972 chi)))) ∨
      ((((Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0972 chi) ∨
      (Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0972 chi)) ∨
      ((Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0972 chi) ∨
      (¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0973 chi))) ∨
      (((¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0973 chi) ∨
      (¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0973 chi)) ∨
      ((¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0973 chi) ∨
      (Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0973 chi)))))) ∨
      ((((((Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0973 chi) ∨
      (Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0973 chi)) ∨
      ((Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0973 chi) ∨
      (Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0973 chi))) ∨
      (((¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0974 chi) ∨
      (¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0974 chi)) ∨
      ((¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0974 chi) ∨
      (¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0974 chi)))) ∨
      ((((Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0974 chi) ∨
      (Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0974 chi)) ∨
      ((Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0974 chi) ∨
      (Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0974 chi))) ∨
      (((¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0975 chi) ∨
      (¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0975 chi)) ∨
      ((¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0975 chi) ∨
      (¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0975 chi))))) ∨
      (((((¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0975 chi) ∨
      (Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0975 chi)) ∨
      ((Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0975 chi) ∨
      (Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0975 chi))) ∨
      (((Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0975 chi) ∨
      (Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0975 chi)) ∨
      ((Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0976 chi) ∨
      (¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0977 chi)))) ∨
      ((((¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0977 chi) ∨
      (¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0977 chi)) ∨
      ((¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0977 chi) ∨
      (Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0977 chi))) ∨
      (((Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0977 chi) ∨
      (Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0977 chi)) ∨
      ((Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0977 chi) ∨
      (¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0978 chi))))))) ∨
      (((((((¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0978 chi) ∨
      (¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0978 chi)) ∨
      ((¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0978 chi) ∨
      (Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0978 chi))) ∨
      (((Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0978 chi) ∨
      (Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0978 chi)) ∨
      ((Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0978 chi) ∨
      (¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0979 chi)))) ∨
      ((((¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0979 chi) ∨
      (¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0979 chi)) ∨
      ((¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0979 chi) ∨
      (Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0979 chi))) ∨
      (((Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0979 chi) ∨
      (Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0979 chi)) ∨
      ((Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0979 chi) ∨
      (¬Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0980 chi))))) ∨
      (((((¬Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0980 chi) ∨
      (¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0980 chi)) ∨
      ((¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0980 chi) ∨
      (Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0980 chi))) ∨
      (((Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0980 chi) ∨
      (¬Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0981 chi)) ∨
      ((¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0981 chi) ∨
      (Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0981 chi)))) ∨
      ((((¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0982 chi) ∨
      (¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0983 chi)) ∨
      ((¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0983 chi) ∨
      (¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0983 chi))) ∨
      (((¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0983 chi) ∨
      (Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0983 chi)) ∨
      ((Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0983 chi) ∨
      (Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0983 chi)))))) ∨
      ((((((Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0983 chi) ∨
      (¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0984 chi)) ∨
      ((¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0984 chi) ∨
      (¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0984 chi))) ∨
      (((¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0984 chi) ∨
      (Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0984 chi)) ∨
      ((Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0984 chi) ∨
      (Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0984 chi)))) ∨
      ((((Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0984 chi) ∨
      (Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0984 chi)) ∨
      ((¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0985 chi) ∨
      (¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0985 chi))) ∨
      (((¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0985 chi) ∨
      (¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0985 chi)) ∨
      ((Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0985 chi) ∨
      (Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0985 chi))))) ∨
      (((((Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0985 chi) ∨
      (Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0985 chi)) ∨
      ((¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0986 chi) ∨
      (¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0986 chi))) ∨
      (((¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0986 chi) ∨
      (¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0986 chi)) ∨
      ((Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0986 chi) ∨
      (Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0986 chi)))) ∨
      ((((Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0986 chi) ∨
      (Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0986 chi)) ∨
      ((Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0986 chi) ∨
      (Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0986 chi))) ∨
      (((¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0987 chi) ∨
      (¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0987 chi)) ∨
      ((¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0987 chi) ∨
      (¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0987 chi)))))))))) := by
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
                exact fin15Anchored_clause08833 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08834 chi hbad
                ·
                  exact fin15Anchored_clause08835 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08836 chi hbad
                ·
                  exact fin15Anchored_clause08837 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08838 chi hbad
                ·
                  exact fin15Anchored_clause08839 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08840 chi hbad
                ·
                  exact fin15Anchored_clause08841 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08842 chi hbad
                ·
                  exact fin15Anchored_clause08843 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08844 chi hbad
                ·
                  exact fin15Anchored_clause08845 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08846 chi hbad
                ·
                  exact fin15Anchored_clause08847 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08848 chi hbad
                ·
                  exact fin15Anchored_clause08849 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08850 chi hbad
                ·
                  exact fin15Anchored_clause08851 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08852 chi hbad
                ·
                  exact fin15Anchored_clause08853 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08854 chi hbad
                ·
                  exact fin15Anchored_clause08855 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08856 chi hbad
                ·
                  exact fin15Anchored_clause08857 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08858 chi hbad
                ·
                  exact fin15Anchored_clause08859 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08860 chi hbad
                ·
                  exact fin15Anchored_clause08861 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08862 chi hbad
                ·
                  exact fin15Anchored_clause08863 chi hbad
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
                  exact fin15Anchored_clause08864 chi hbad
                ·
                  exact fin15Anchored_clause08865 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08866 chi hbad
                ·
                  exact fin15Anchored_clause08867 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08868 chi hbad
                ·
                  exact fin15Anchored_clause08869 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08870 chi hbad
                ·
                  exact fin15Anchored_clause08871 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08872 chi hbad
                ·
                  exact fin15Anchored_clause08873 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08874 chi hbad
                ·
                  exact fin15Anchored_clause08875 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08876 chi hbad
                ·
                  exact fin15Anchored_clause08877 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08878 chi hbad
                ·
                  exact fin15Anchored_clause08879 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08880 chi hbad
                ·
                  exact fin15Anchored_clause08881 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08882 chi hbad
                ·
                  exact fin15Anchored_clause08883 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08884 chi hbad
                ·
                  exact fin15Anchored_clause08885 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08886 chi hbad
                ·
                  exact fin15Anchored_clause08887 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08888 chi hbad
                ·
                  exact fin15Anchored_clause08889 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08890 chi hbad
                ·
                  exact fin15Anchored_clause08891 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08892 chi hbad
                ·
                  exact fin15Anchored_clause08893 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08894 chi hbad
                ·
                  exact fin15Anchored_clause08895 chi hbad
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
                exact fin15Anchored_clause08896 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08897 chi hbad
                ·
                  exact fin15Anchored_clause08898 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08899 chi hbad
                ·
                  exact fin15Anchored_clause08900 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08901 chi hbad
                ·
                  exact fin15Anchored_clause08902 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08903 chi hbad
                ·
                  exact fin15Anchored_clause08904 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08905 chi hbad
                ·
                  exact fin15Anchored_clause08906 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08907 chi hbad
                ·
                  exact fin15Anchored_clause08908 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08909 chi hbad
                ·
                  exact fin15Anchored_clause08910 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08911 chi hbad
                ·
                  exact fin15Anchored_clause08912 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08913 chi hbad
                ·
                  exact fin15Anchored_clause08914 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08915 chi hbad
                ·
                  exact fin15Anchored_clause08916 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08917 chi hbad
                ·
                  exact fin15Anchored_clause08918 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08919 chi hbad
                ·
                  exact fin15Anchored_clause08920 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08921 chi hbad
                ·
                  exact fin15Anchored_clause08922 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08923 chi hbad
                ·
                  exact fin15Anchored_clause08924 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08925 chi hbad
                ·
                  exact fin15Anchored_clause08926 chi hbad
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
                  exact fin15Anchored_clause08927 chi hbad
                ·
                  exact fin15Anchored_clause08928 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08929 chi hbad
                ·
                  exact fin15Anchored_clause08930 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08931 chi hbad
                ·
                  exact fin15Anchored_clause08932 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08933 chi hbad
                ·
                  exact fin15Anchored_clause08934 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08935 chi hbad
                ·
                  exact fin15Anchored_clause08936 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08937 chi hbad
                ·
                  exact fin15Anchored_clause08938 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08939 chi hbad
                ·
                  exact fin15Anchored_clause08940 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08941 chi hbad
                ·
                  exact fin15Anchored_clause08942 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08943 chi hbad
                ·
                  exact fin15Anchored_clause08944 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08945 chi hbad
                ·
                  exact fin15Anchored_clause08946 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08947 chi hbad
                ·
                  exact fin15Anchored_clause08948 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08949 chi hbad
                ·
                  exact fin15Anchored_clause08950 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08951 chi hbad
                ·
                  exact fin15Anchored_clause08952 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08953 chi hbad
                ·
                  exact fin15Anchored_clause08954 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08955 chi hbad
                ·
                  exact fin15Anchored_clause08956 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08957 chi hbad
                ·
                  exact fin15Anchored_clause08958 chi hbad
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
                exact fin15Anchored_clause08959 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08960 chi hbad
                ·
                  exact fin15Anchored_clause08961 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08962 chi hbad
                ·
                  exact fin15Anchored_clause08963 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08964 chi hbad
                ·
                  exact fin15Anchored_clause08965 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08966 chi hbad
                ·
                  exact fin15Anchored_clause08967 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08968 chi hbad
                ·
                  exact fin15Anchored_clause08969 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08970 chi hbad
                ·
                  exact fin15Anchored_clause08971 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08972 chi hbad
                ·
                  exact fin15Anchored_clause08973 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08974 chi hbad
                ·
                  exact fin15Anchored_clause08975 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08976 chi hbad
                ·
                  exact fin15Anchored_clause08977 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08978 chi hbad
                ·
                  exact fin15Anchored_clause08979 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08980 chi hbad
                ·
                  exact fin15Anchored_clause08981 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08982 chi hbad
                ·
                  exact fin15Anchored_clause08983 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08984 chi hbad
                ·
                  exact fin15Anchored_clause08985 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08986 chi hbad
                ·
                  exact fin15Anchored_clause08987 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08988 chi hbad
                ·
                  exact fin15Anchored_clause08989 chi hbad
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
                  exact fin15Anchored_clause08990 chi hbad
                ·
                  exact fin15Anchored_clause08991 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08992 chi hbad
                ·
                  exact fin15Anchored_clause08993 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08994 chi hbad
                ·
                  exact fin15Anchored_clause08995 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08996 chi hbad
                ·
                  exact fin15Anchored_clause08997 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08998 chi hbad
                ·
                  exact fin15Anchored_clause08999 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09000 chi hbad
                ·
                  exact fin15Anchored_clause09001 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09002 chi hbad
                ·
                  exact fin15Anchored_clause09003 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09004 chi hbad
                ·
                  exact fin15Anchored_clause09005 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09006 chi hbad
                ·
                  exact fin15Anchored_clause09007 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09008 chi hbad
                ·
                  exact fin15Anchored_clause09009 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09010 chi hbad
                ·
                  exact fin15Anchored_clause09011 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09012 chi hbad
                ·
                  exact fin15Anchored_clause09013 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09014 chi hbad
                ·
                  exact fin15Anchored_clause09015 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09016 chi hbad
                ·
                  exact fin15Anchored_clause09017 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09018 chi hbad
                ·
                  exact fin15Anchored_clause09019 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09020 chi hbad
                ·
                  exact fin15Anchored_clause09021 chi hbad
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
                  exact fin15Anchored_clause09022 chi hbad
                ·
                  exact fin15Anchored_clause09023 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09024 chi hbad
                ·
                  exact fin15Anchored_clause09025 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09026 chi hbad
                ·
                  exact fin15Anchored_clause09027 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09028 chi hbad
                ·
                  exact fin15Anchored_clause09029 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09030 chi hbad
                ·
                  exact fin15Anchored_clause09031 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09032 chi hbad
                ·
                  exact fin15Anchored_clause09033 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09034 chi hbad
                ·
                  exact fin15Anchored_clause09035 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09036 chi hbad
                ·
                  exact fin15Anchored_clause09037 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09038 chi hbad
                ·
                  exact fin15Anchored_clause09039 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09040 chi hbad
                ·
                  exact fin15Anchored_clause09041 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09042 chi hbad
                ·
                  exact fin15Anchored_clause09043 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09044 chi hbad
                ·
                  exact fin15Anchored_clause09045 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09046 chi hbad
                ·
                  exact fin15Anchored_clause09047 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09048 chi hbad
                ·
                  exact fin15Anchored_clause09049 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09050 chi hbad
                ·
                  exact fin15Anchored_clause09051 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09052 chi hbad
                ·
                  exact fin15Anchored_clause09053 chi hbad
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
                  exact fin15Anchored_clause09054 chi hbad
                ·
                  exact fin15Anchored_clause09055 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09056 chi hbad
                ·
                  exact fin15Anchored_clause09057 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09058 chi hbad
                ·
                  exact fin15Anchored_clause09059 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09060 chi hbad
                ·
                  exact fin15Anchored_clause09061 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09062 chi hbad
                ·
                  exact fin15Anchored_clause09063 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09064 chi hbad
                ·
                  exact fin15Anchored_clause09065 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09066 chi hbad
                ·
                  exact fin15Anchored_clause09067 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09068 chi hbad
                ·
                  exact fin15Anchored_clause09069 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09070 chi hbad
                ·
                  exact fin15Anchored_clause09071 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09072 chi hbad
                ·
                  exact fin15Anchored_clause09073 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09074 chi hbad
                ·
                  exact fin15Anchored_clause09075 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09076 chi hbad
                ·
                  exact fin15Anchored_clause09077 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09078 chi hbad
                ·
                  exact fin15Anchored_clause09079 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09080 chi hbad
                ·
                  exact fin15Anchored_clause09081 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09082 chi hbad
                ·
                  exact fin15Anchored_clause09083 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause09084 chi hbad
                ·
                  exact fin15Anchored_clause09085 chi hbad

end ErdosSzekeres

end
