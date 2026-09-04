module

public import ErdosSzekeres.Fin15AnchoredClauseChunk061
public import ErdosSzekeres.Fin15AnchoredClauseChunk062
public import ErdosSzekeres.Fin15AnchoredClauseChunk063

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 031. -/

theorem fin15Anchored_rejectSemanticSegment031
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0822 chi) ∨
      ((Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0822 chi) ∨
      (Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0822 chi))) ∨
      (((Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0822 chi) ∨
      (¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0823 chi)) ∨
      ((¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0823 chi) ∨
      (¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0823 chi)))) ∨
      ((((¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0823 chi) ∨
      (Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0823 chi)) ∨
      ((Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0823 chi) ∨
      (Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0823 chi))) ∨
      (((Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0823 chi) ∨
      (¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0824 chi)) ∨
      ((¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0824 chi) ∨
      (¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0825 chi))))) ∨
      (((((¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0825 chi) ∨
      (¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0825 chi)) ∨
      ((¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0825 chi) ∨
      (Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0825 chi))) ∨
      (((Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0825 chi) ∨
      (Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0825 chi)) ∨
      ((Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0825 chi) ∨
      (¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0826 chi)))) ∨
      ((((¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0826 chi) ∨
      (¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0826 chi)) ∨
      ((¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0826 chi) ∨
      (¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0826 chi))) ∨
      (((¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0826 chi) ∨
      (Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0826 chi)) ∨
      ((Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0826 chi) ∨
      (Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0826 chi)))))) ∨
      ((((((Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0826 chi) ∨
      (Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0826 chi)) ∨
      ((¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0827 chi) ∨
      (¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0827 chi))) ∨
      (((¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0827 chi) ∨
      (¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0828 chi)) ∨
      ((¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0828 chi) ∨
      (¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0828 chi)))) ∨
      ((((¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0828 chi) ∨
      (Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0828 chi)) ∨
      ((Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0828 chi) ∨
      (Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0828 chi))) ∨
      (((Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0828 chi) ∨
      (Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0828 chi)) ∨
      ((¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0829 chi) ∨
      (¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0829 chi))))) ∨
      (((((¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0829 chi) ∨
      (¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0829 chi)) ∨
      ((Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0829 chi) ∨
      (Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0829 chi))) ∨
      (((Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0829 chi) ∨
      (Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0829 chi)) ∨
      ((Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0829 chi) ∨
      (¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0830 chi)))) ∨
      ((((¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0830 chi) ∨
      (¬Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0830 chi)) ∨
      ((¬Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0830 chi) ∨
      (Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0830 chi))) ∨
      (((Fin15AnchoredAtom0092 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0830 chi) ∨
      (Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0830 chi)) ∨
      ((Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0830 chi) ∨
      (Fin15AnchoredAtom0092 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0830 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0831 chi) ∨
      ((¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0831 chi) ∨
      (¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0831 chi))) ∨
      (((¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0831 chi) ∨
      (¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0831 chi)) ∨
      ((Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0831 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0831 chi)))) ∨
      ((((Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0831 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0831 chi)) ∨
      ((Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0831 chi) ∨
      (¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0832 chi))) ∨
      (((¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0832 chi) ∨
      (¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0832 chi)) ∨
      ((¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0832 chi) ∨
      (¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0832 chi))))) ∨
      (((((Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0832 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0832 chi)) ∨
      ((Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0832 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0832 chi))) ∨
      (((Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0832 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0832 chi)) ∨
      ((¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0833 chi) ∨
      (¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0833 chi)))) ∨
      ((((¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0833 chi) ∨
      (¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0833 chi)) ∨
      ((Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0833 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0833 chi))) ∨
      (((Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0833 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0833 chi)) ∨
      ((Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0833 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0833 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0834 chi) ∨
      (¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0834 chi)) ∨
      ((¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0834 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0834 chi))) ∨
      (((Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0834 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0834 chi)) ∨
      ((¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0835 chi) ∨
      (¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0835 chi)))) ∨
      ((((¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0835 chi) ∨
      (¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0835 chi)) ∨
      ((Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0835 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0835 chi))) ∨
      (((Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0835 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0835 chi)) ∨
      ((Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0835 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0835 chi))))) ∨
      (((((¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0836 chi) ∨
      (¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0836 chi)) ∨
      ((¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0836 chi) ∨
      (¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0836 chi))) ∨
      (((Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0836 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0836 chi)) ∨
      ((Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0836 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0836 chi)))) ∨
      ((((Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0836 chi) ∨
      (¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0837 chi)) ∨
      ((¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0837 chi) ∨
      (¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0837 chi))) ∨
      (((¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0837 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0837 chi)) ∨
      ((¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0838 chi) ∨
      (¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0838 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0838 chi) ∨
      ((¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0838 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0838 chi))) ∨
      (((Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0838 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0838 chi)) ∨
      ((Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0838 chi) ∨
      (¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0839 chi)))) ∨
      ((((¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0839 chi) ∨
      (¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0839 chi)) ∨
      ((¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0839 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0839 chi))) ∨
      (((Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0839 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0839 chi)) ∨
      ((Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0839 chi) ∨
      (¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0840 chi))))) ∨
      (((((¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0840 chi) ∨
      (¬Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0840 chi)) ∨
      ((¬Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0840 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0840 chi))) ∨
      (((Fin15AnchoredAtom0093 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0840 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0840 chi)) ∨
      ((Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0840 chi) ∨
      (Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0840 chi)))) ∨
      ((((Fin15AnchoredAtom0093 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0840 chi) ∨
      (¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0841 chi)) ∨
      ((¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0841 chi) ∨
      (¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0841 chi))) ∨
      (((¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0841 chi) ∨
      (Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0841 chi)) ∨
      ((Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0841 chi) ∨
      (Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0841 chi)))))) ∨
      ((((((Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0841 chi) ∨
      (Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0841 chi)) ∨
      ((Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0841 chi) ∨
      (¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0842 chi))) ∨
      (((¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0842 chi) ∨
      (¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0842 chi)) ∨
      ((¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0842 chi) ∨
      (Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0842 chi)))) ∨
      ((((Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0842 chi) ∨
      (Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0842 chi)) ∨
      ((Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0842 chi) ∨
      (Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0842 chi))) ∨
      (((¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0843 chi) ∨
      (¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0844 chi)) ∨
      ((¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0844 chi) ∨
      (¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0844 chi))))) ∨
      (((((¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0844 chi) ∨
      (¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0844 chi)) ∨
      ((Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0844 chi) ∨
      (Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0844 chi))) ∨
      (((Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0844 chi) ∨
      (Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0844 chi)) ∨
      ((¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0845 chi) ∨
      (¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0845 chi)))) ∨
      ((((¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0845 chi) ∨
      (¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0845 chi)) ∨
      ((Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0845 chi) ∨
      (Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0845 chi))) ∨
      (((Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0845 chi) ∨
      (Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0845 chi)) ∨
      ((Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0845 chi) ∨
      (Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0845 chi))))))) ∨
      (((((((¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0846 chi) ∨
      (¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0846 chi)) ∨
      ((¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0846 chi) ∨
      (¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0846 chi))) ∨
      (((Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0846 chi) ∨
      (¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0847 chi)) ∨
      ((¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0847 chi) ∨
      (¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0847 chi)))) ∨
      ((((¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0847 chi) ∨
      (Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0847 chi)) ∨
      ((Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0847 chi) ∨
      (Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0847 chi))) ∨
      (((Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0847 chi) ∨
      (¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0848 chi)) ∨
      ((¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0848 chi) ∨
      (¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0848 chi))))) ∨
      (((((¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0848 chi) ∨
      (Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0848 chi)) ∨
      ((Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0848 chi) ∨
      (Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0848 chi))) ∨
      (((Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0848 chi) ∨
      (¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0849 chi)) ∨
      ((¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0849 chi) ∨
      (¬Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0849 chi)))) ∨
      ((((¬Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0849 chi) ∨
      (Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0849 chi)) ∨
      ((Fin15AnchoredAtom0094 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0849 chi) ∨
      (Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0849 chi))) ∨
      (((Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0849 chi) ∨
      (Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0849 chi)) ∨
      ((Fin15AnchoredAtom0094 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0849 chi) ∨
      (¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0850 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0850 chi) ∨
      (¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0850 chi)) ∨
      ((¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0850 chi) ∨
      (Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0850 chi))) ∨
      (((Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0850 chi) ∨
      (Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0850 chi)) ∨
      ((Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0850 chi) ∨
      (Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0096 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0850 chi)))) ∨
      ((((¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0851 chi) ∨
      (¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0851 chi)) ∨
      ((¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0097 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0851 chi) ∨
      (Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0097 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0851 chi))) ∨
      (((¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0852 chi) ∨
      (¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0852 chi)) ∨
      ((¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0852 chi) ∨
      (¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0852 chi))))) ∨
      (((((Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0852 chi) ∨
      (Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0852 chi)) ∨
      ((Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0852 chi) ∨
      (Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0852 chi))) ∨
      (((Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0852 chi) ∨
      (¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0853 chi)) ∨
      ((¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0853 chi) ∨
      (¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0853 chi)))) ∨
      ((((¬Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0853 chi) ∨
      (Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0853 chi)) ∨
      ((Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0853 chi) ∨
      (Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0853 chi))) ∨
      (((Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0853 chi) ∨
      (Fin15AnchoredAtom0095 chi ∧
      Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0853 chi)) ∨
      ((¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0854 chi) ∨
      (¬Fin15AnchoredAtom0095 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0854 chi)))))))))) := by
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
                exact fin15Anchored_clause07824 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07825 chi hbad
                ·
                  exact fin15Anchored_clause07826 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07827 chi hbad
                ·
                  exact fin15Anchored_clause07828 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07829 chi hbad
                ·
                  exact fin15Anchored_clause07830 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07831 chi hbad
                ·
                  exact fin15Anchored_clause07832 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07833 chi hbad
                ·
                  exact fin15Anchored_clause07834 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07835 chi hbad
                ·
                  exact fin15Anchored_clause07836 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07837 chi hbad
                ·
                  exact fin15Anchored_clause07838 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07839 chi hbad
                ·
                  exact fin15Anchored_clause07840 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07841 chi hbad
                ·
                  exact fin15Anchored_clause07842 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07843 chi hbad
                ·
                  exact fin15Anchored_clause07844 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07845 chi hbad
                ·
                  exact fin15Anchored_clause07846 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07847 chi hbad
                ·
                  exact fin15Anchored_clause07848 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07849 chi hbad
                ·
                  exact fin15Anchored_clause07850 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07851 chi hbad
                ·
                  exact fin15Anchored_clause07852 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07853 chi hbad
                ·
                  exact fin15Anchored_clause07854 chi hbad
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
                  exact fin15Anchored_clause07855 chi hbad
                ·
                  exact fin15Anchored_clause07856 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07857 chi hbad
                ·
                  exact fin15Anchored_clause07858 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07859 chi hbad
                ·
                  exact fin15Anchored_clause07860 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07861 chi hbad
                ·
                  exact fin15Anchored_clause07862 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07863 chi hbad
                ·
                  exact fin15Anchored_clause07864 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07865 chi hbad
                ·
                  exact fin15Anchored_clause07866 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07867 chi hbad
                ·
                  exact fin15Anchored_clause07868 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07869 chi hbad
                ·
                  exact fin15Anchored_clause07870 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07871 chi hbad
                ·
                  exact fin15Anchored_clause07872 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07873 chi hbad
                ·
                  exact fin15Anchored_clause07874 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07875 chi hbad
                ·
                  exact fin15Anchored_clause07876 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07877 chi hbad
                ·
                  exact fin15Anchored_clause07878 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07879 chi hbad
                ·
                  exact fin15Anchored_clause07880 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07881 chi hbad
                ·
                  exact fin15Anchored_clause07882 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07883 chi hbad
                ·
                  exact fin15Anchored_clause07884 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07885 chi hbad
                ·
                  exact fin15Anchored_clause07886 chi hbad
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
                exact fin15Anchored_clause07887 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07888 chi hbad
                ·
                  exact fin15Anchored_clause07889 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07890 chi hbad
                ·
                  exact fin15Anchored_clause07891 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07892 chi hbad
                ·
                  exact fin15Anchored_clause07893 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07894 chi hbad
                ·
                  exact fin15Anchored_clause07895 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07896 chi hbad
                ·
                  exact fin15Anchored_clause07897 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07898 chi hbad
                ·
                  exact fin15Anchored_clause07899 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07900 chi hbad
                ·
                  exact fin15Anchored_clause07901 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07902 chi hbad
                ·
                  exact fin15Anchored_clause07903 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07904 chi hbad
                ·
                  exact fin15Anchored_clause07905 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07906 chi hbad
                ·
                  exact fin15Anchored_clause07907 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07908 chi hbad
                ·
                  exact fin15Anchored_clause07909 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07910 chi hbad
                ·
                  exact fin15Anchored_clause07911 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07912 chi hbad
                ·
                  exact fin15Anchored_clause07913 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07914 chi hbad
                ·
                  exact fin15Anchored_clause07915 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07916 chi hbad
                ·
                  exact fin15Anchored_clause07917 chi hbad
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
                  exact fin15Anchored_clause07918 chi hbad
                ·
                  exact fin15Anchored_clause07919 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07920 chi hbad
                ·
                  exact fin15Anchored_clause07921 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07922 chi hbad
                ·
                  exact fin15Anchored_clause07923 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07924 chi hbad
                ·
                  exact fin15Anchored_clause07925 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07926 chi hbad
                ·
                  exact fin15Anchored_clause07927 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07928 chi hbad
                ·
                  exact fin15Anchored_clause07929 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07930 chi hbad
                ·
                  exact fin15Anchored_clause07931 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07932 chi hbad
                ·
                  exact fin15Anchored_clause07933 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07934 chi hbad
                ·
                  exact fin15Anchored_clause07935 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07936 chi hbad
                ·
                  exact fin15Anchored_clause07937 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07938 chi hbad
                ·
                  exact fin15Anchored_clause07939 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07940 chi hbad
                ·
                  exact fin15Anchored_clause07941 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07942 chi hbad
                ·
                  exact fin15Anchored_clause07943 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07944 chi hbad
                ·
                  exact fin15Anchored_clause07945 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07946 chi hbad
                ·
                  exact fin15Anchored_clause07947 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07948 chi hbad
                ·
                  exact fin15Anchored_clause07949 chi hbad
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
                exact fin15Anchored_clause07950 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07951 chi hbad
                ·
                  exact fin15Anchored_clause07952 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07953 chi hbad
                ·
                  exact fin15Anchored_clause07954 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07955 chi hbad
                ·
                  exact fin15Anchored_clause07956 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07957 chi hbad
                ·
                  exact fin15Anchored_clause07958 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07959 chi hbad
                ·
                  exact fin15Anchored_clause07960 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07961 chi hbad
                ·
                  exact fin15Anchored_clause07962 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07963 chi hbad
                ·
                  exact fin15Anchored_clause07964 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07965 chi hbad
                ·
                  exact fin15Anchored_clause07966 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07967 chi hbad
                ·
                  exact fin15Anchored_clause07968 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07969 chi hbad
                ·
                  exact fin15Anchored_clause07970 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07971 chi hbad
                ·
                  exact fin15Anchored_clause07972 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07973 chi hbad
                ·
                  exact fin15Anchored_clause07974 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07975 chi hbad
                ·
                  exact fin15Anchored_clause07976 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07977 chi hbad
                ·
                  exact fin15Anchored_clause07978 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07979 chi hbad
                ·
                  exact fin15Anchored_clause07980 chi hbad
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
                  exact fin15Anchored_clause07981 chi hbad
                ·
                  exact fin15Anchored_clause07982 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07983 chi hbad
                ·
                  exact fin15Anchored_clause07984 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07985 chi hbad
                ·
                  exact fin15Anchored_clause07986 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07987 chi hbad
                ·
                  exact fin15Anchored_clause07988 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07989 chi hbad
                ·
                  exact fin15Anchored_clause07990 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07991 chi hbad
                ·
                  exact fin15Anchored_clause07992 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07993 chi hbad
                ·
                  exact fin15Anchored_clause07994 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07995 chi hbad
                ·
                  exact fin15Anchored_clause07996 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07997 chi hbad
                ·
                  exact fin15Anchored_clause07998 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07999 chi hbad
                ·
                  exact fin15Anchored_clause08000 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08001 chi hbad
                ·
                  exact fin15Anchored_clause08002 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08003 chi hbad
                ·
                  exact fin15Anchored_clause08004 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08005 chi hbad
                ·
                  exact fin15Anchored_clause08006 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08007 chi hbad
                ·
                  exact fin15Anchored_clause08008 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08009 chi hbad
                ·
                  exact fin15Anchored_clause08010 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08011 chi hbad
                ·
                  exact fin15Anchored_clause08012 chi hbad
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
                  exact fin15Anchored_clause08013 chi hbad
                ·
                  exact fin15Anchored_clause08014 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08015 chi hbad
                ·
                  exact fin15Anchored_clause08016 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08017 chi hbad
                ·
                  exact fin15Anchored_clause08018 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08019 chi hbad
                ·
                  exact fin15Anchored_clause08020 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08021 chi hbad
                ·
                  exact fin15Anchored_clause08022 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08023 chi hbad
                ·
                  exact fin15Anchored_clause08024 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08025 chi hbad
                ·
                  exact fin15Anchored_clause08026 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08027 chi hbad
                ·
                  exact fin15Anchored_clause08028 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08029 chi hbad
                ·
                  exact fin15Anchored_clause08030 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08031 chi hbad
                ·
                  exact fin15Anchored_clause08032 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08033 chi hbad
                ·
                  exact fin15Anchored_clause08034 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08035 chi hbad
                ·
                  exact fin15Anchored_clause08036 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08037 chi hbad
                ·
                  exact fin15Anchored_clause08038 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08039 chi hbad
                ·
                  exact fin15Anchored_clause08040 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08041 chi hbad
                ·
                  exact fin15Anchored_clause08042 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08043 chi hbad
                ·
                  exact fin15Anchored_clause08044 chi hbad
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
                  exact fin15Anchored_clause08045 chi hbad
                ·
                  exact fin15Anchored_clause08046 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08047 chi hbad
                ·
                  exact fin15Anchored_clause08048 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08049 chi hbad
                ·
                  exact fin15Anchored_clause08050 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08051 chi hbad
                ·
                  exact fin15Anchored_clause08052 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08053 chi hbad
                ·
                  exact fin15Anchored_clause08054 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08055 chi hbad
                ·
                  exact fin15Anchored_clause08056 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08057 chi hbad
                ·
                  exact fin15Anchored_clause08058 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08059 chi hbad
                ·
                  exact fin15Anchored_clause08060 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08061 chi hbad
                ·
                  exact fin15Anchored_clause08062 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08063 chi hbad
                ·
                  exact fin15Anchored_clause08064 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08065 chi hbad
                ·
                  exact fin15Anchored_clause08066 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08067 chi hbad
                ·
                  exact fin15Anchored_clause08068 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08069 chi hbad
                ·
                  exact fin15Anchored_clause08070 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08071 chi hbad
                ·
                  exact fin15Anchored_clause08072 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08073 chi hbad
                ·
                  exact fin15Anchored_clause08074 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08075 chi hbad
                ·
                  exact fin15Anchored_clause08076 chi hbad

end ErdosSzekeres

end
