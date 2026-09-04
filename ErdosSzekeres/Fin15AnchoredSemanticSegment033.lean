module

public import ErdosSzekeres.Fin15AnchoredClauseChunk065
public import ErdosSzekeres.Fin15AnchoredClauseChunk066
public import ErdosSzekeres.Fin15AnchoredClauseChunk067

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 033. -/

theorem fin15Anchored_rejectSemanticSegment033
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0891 chi) ∨
      ((Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0891 chi) ∨
      (¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0892 chi))) ∨
      (((¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0892 chi) ∨
      (¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0892 chi)) ∨
      ((Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0892 chi) ∨
      (Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0892 chi)))) ∨
      ((((¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0893 chi) ∨
      (¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0893 chi)) ∨
      ((¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0893 chi) ∨
      (¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0893 chi))) ∨
      (((Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0893 chi) ∨
      (Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0893 chi)) ∨
      ((Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0893 chi) ∨
      (Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0893 chi))))) ∨
      (((((¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0894 chi) ∨
      (¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0894 chi)) ∨
      ((¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0894 chi) ∨
      (¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0894 chi))) ∨
      (((Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0894 chi) ∨
      (Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0894 chi)) ∨
      ((Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0894 chi) ∨
      (Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0894 chi)))) ∨
      ((((¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0895 chi) ∨
      (¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0895 chi)) ∨
      ((¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0895 chi) ∨
      (¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0895 chi))) ∨
      (((Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0895 chi) ∨
      (Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0895 chi)) ∨
      ((Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0895 chi) ∨
      (Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0895 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0896 chi) ∨
      (¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0896 chi)) ∨
      ((¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0896 chi) ∨
      (¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0896 chi))) ∨
      (((Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0896 chi) ∨
      (Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0896 chi)) ∨
      ((Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0896 chi) ∨
      (Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0896 chi)))) ∨
      ((((Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0896 chi) ∨
      (¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0897 chi)) ∨
      ((¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0897 chi) ∨
      (¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0897 chi))) ∨
      (((¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0897 chi) ∨
      (Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0897 chi)) ∨
      ((Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0897 chi) ∨
      (Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0897 chi))))) ∨
      (((((Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0897 chi) ∨
      (Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0897 chi)) ∨
      ((¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0898 chi) ∨
      (¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0898 chi))) ∨
      (((¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0898 chi) ∨
      (¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0898 chi)) ∨
      ((Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0898 chi) ∨
      (Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0898 chi)))) ∨
      ((((Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0898 chi) ∨
      (Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0898 chi)) ∨
      ((Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0898 chi) ∨
      (Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0898 chi))) ∨
      (((¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0899 chi) ∨
      (¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0899 chi)) ∨
      ((¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0899 chi) ∨
      (¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0899 chi))))))) ∨
      ((((((Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0899 chi) ∨
      ((Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0899 chi) ∨
      (Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0899 chi))) ∨
      (((Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0899 chi) ∨
      (Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0899 chi)) ∨
      ((¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0900 chi) ∨
      (¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0900 chi)))) ∨
      ((((¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0900 chi) ∨
      (¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0900 chi)) ∨
      ((Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0900 chi) ∨
      (Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0900 chi))) ∨
      (((Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0900 chi) ∨
      (Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0900 chi)) ∨
      ((Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0900 chi) ∨
      (Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0900 chi))))) ∨
      (((((¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0901 chi) ∨
      (¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0901 chi)) ∨
      ((Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0901 chi) ∨
      (Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0901 chi))) ∨
      (((¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0902 chi) ∨
      (¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0902 chi)) ∨
      ((¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0902 chi) ∨
      (¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0902 chi)))) ∨
      ((((¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0902 chi) ∨
      (Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0902 chi)) ∨
      ((Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0902 chi) ∨
      (Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0902 chi))) ∨
      (((Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0902 chi) ∨
      (¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0903 chi)) ∨
      ((¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0903 chi) ∨
      (¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0903 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0903 chi) ∨
      (Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0903 chi)) ∨
      ((Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0903 chi) ∨
      (Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0903 chi))) ∨
      (((Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0903 chi) ∨
      (¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0904 chi)) ∨
      ((¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0904 chi) ∨
      (¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0904 chi)))) ∨
      ((((¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0904 chi) ∨
      (Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0904 chi)) ∨
      ((Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0904 chi) ∨
      (Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0904 chi))) ∨
      (((Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0904 chi) ∨
      (Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0904 chi)) ∨
      ((¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0905 chi) ∨
      (¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0905 chi))))) ∨
      (((((¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0905 chi) ∨
      (¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0905 chi)) ∨
      ((Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0905 chi) ∨
      (Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0905 chi))) ∨
      (((Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0905 chi) ∨
      (Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0905 chi)) ∨
      ((¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0906 chi) ∨
      (¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0906 chi)))) ∨
      ((((¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0906 chi) ∨
      (¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0906 chi)) ∨
      ((Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0906 chi) ∨
      (Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0906 chi))) ∨
      (((Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0906 chi) ∨
      (Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0906 chi)) ∨
      ((¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0907 chi) ∨
      (¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0907 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0907 chi) ∨
      ((¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0907 chi) ∨
      (Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0907 chi))) ∨
      (((Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0907 chi) ∨
      (Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0907 chi)) ∨
      ((Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0907 chi) ∨
      (¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0908 chi)))) ∨
      ((((¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0908 chi) ∨
      (¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0908 chi)) ∨
      ((¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0908 chi) ∨
      (¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0908 chi))) ∨
      (((¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0908 chi) ∨
      (Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0908 chi)) ∨
      ((Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0908 chi) ∨
      (Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0908 chi))))) ∨
      (((((Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0908 chi) ∨
      (Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0908 chi)) ∨
      ((Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0908 chi) ∨
      (¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0909 chi))) ∨
      (((Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0909 chi) ∨
      (Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0909 chi)) ∨
      ((¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0910 chi) ∨
      (¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0910 chi)))) ∨
      ((((¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0910 chi) ∨
      (¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0910 chi)) ∨
      ((¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0910 chi) ∨
      (Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0910 chi))) ∨
      (((Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0910 chi) ∨
      (Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0910 chi)) ∨
      ((Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0910 chi) ∨
      (Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0910 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0911 chi) ∨
      (¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0911 chi)) ∨
      ((¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0911 chi) ∨
      (¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0911 chi))) ∨
      (((Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0911 chi) ∨
      (Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0911 chi)) ∨
      ((Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0911 chi) ∨
      (Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0911 chi)))) ∨
      ((((Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0911 chi) ∨
      (¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0912 chi)) ∨
      ((¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0912 chi) ∨
      (¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0912 chi))) ∨
      (((¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0912 chi) ∨
      (Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0912 chi)) ∨
      ((Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0912 chi) ∨
      (Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0912 chi))))) ∨
      (((((Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0912 chi) ∨
      (¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0913 chi)) ∨
      ((¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0913 chi) ∨
      (¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0913 chi))) ∨
      (((¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0913 chi) ∨
      (¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0913 chi)) ∨
      ((Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0913 chi) ∨
      (Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0913 chi)))) ∨
      ((((Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0913 chi) ∨
      (Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0913 chi)) ∨
      ((Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0913 chi) ∨
      (¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0914 chi))) ∨
      (((¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0914 chi) ∨
      (¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0914 chi)) ∨
      ((¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0914 chi) ∨
      (Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0914 chi))))))) ∨
      ((((((Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0914 chi) ∨
      ((Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0914 chi) ∨
      (Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0914 chi))) ∨
      (((Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0914 chi) ∨
      (¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0915 chi)) ∨
      ((¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0915 chi) ∨
      (¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0915 chi)))) ∨
      ((((¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0915 chi) ∨
      (¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0915 chi)) ∨
      ((Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0915 chi) ∨
      (Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0915 chi))) ∨
      (((Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0915 chi) ∨
      (Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0915 chi)) ∨
      ((Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0916 chi) ∨
      (Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0916 chi))))) ∨
      (((((¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0917 chi) ∨
      (¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0917 chi)) ∨
      ((¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0917 chi) ∨
      (¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0917 chi))) ∨
      (((¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0917 chi) ∨
      (Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0917 chi)) ∨
      ((Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0917 chi) ∨
      (Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0917 chi)))) ∨
      ((((Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0917 chi) ∨
      (¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0918 chi)) ∨
      ((¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0918 chi) ∨
      (¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0918 chi))) ∨
      (((¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0918 chi) ∨
      (Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0918 chi)) ∨
      ((Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0918 chi) ∨
      (Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0918 chi)))))) ∨
      ((((((Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0918 chi) ∨
      (Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0918 chi)) ∨
      ((Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0918 chi) ∨
      (¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0919 chi))) ∨
      (((¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0919 chi) ∨
      (¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0919 chi)) ∨
      ((¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0919 chi) ∨
      (¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0919 chi)))) ∨
      ((((Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0919 chi) ∨
      (Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0919 chi)) ∨
      ((Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0919 chi) ∨
      (Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0919 chi))) ∨
      (((Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0919 chi) ∨
      (¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0920 chi)) ∨
      ((¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0920 chi) ∨
      (¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0920 chi))))) ∨
      (((((¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0920 chi) ∨
      (Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0920 chi)) ∨
      ((Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0920 chi) ∨
      (Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0920 chi))) ∨
      (((Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0920 chi) ∨
      (Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0920 chi)) ∨
      ((¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0921 chi) ∨
      (¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0921 chi)))) ∨
      ((((¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0921 chi) ∨
      (¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0921 chi)) ∨
      ((¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0921 chi) ∨
      (Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0921 chi))) ∨
      (((Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0921 chi) ∨
      (Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0921 chi)) ∨
      ((Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0921 chi) ∨
      (¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0923 chi)))))))))) := by
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
                exact fin15Anchored_clause08329 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08330 chi hbad
                ·
                  exact fin15Anchored_clause08331 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08332 chi hbad
                ·
                  exact fin15Anchored_clause08333 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08334 chi hbad
                ·
                  exact fin15Anchored_clause08335 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08336 chi hbad
                ·
                  exact fin15Anchored_clause08337 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08338 chi hbad
                ·
                  exact fin15Anchored_clause08339 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08340 chi hbad
                ·
                  exact fin15Anchored_clause08341 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08342 chi hbad
                ·
                  exact fin15Anchored_clause08343 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08344 chi hbad
                ·
                  exact fin15Anchored_clause08345 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08346 chi hbad
                ·
                  exact fin15Anchored_clause08347 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08348 chi hbad
                ·
                  exact fin15Anchored_clause08349 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08350 chi hbad
                ·
                  exact fin15Anchored_clause08351 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08352 chi hbad
                ·
                  exact fin15Anchored_clause08353 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08354 chi hbad
                ·
                  exact fin15Anchored_clause08355 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08356 chi hbad
                ·
                  exact fin15Anchored_clause08357 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08358 chi hbad
                ·
                  exact fin15Anchored_clause08359 chi hbad
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
                  exact fin15Anchored_clause08360 chi hbad
                ·
                  exact fin15Anchored_clause08361 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08362 chi hbad
                ·
                  exact fin15Anchored_clause08363 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08364 chi hbad
                ·
                  exact fin15Anchored_clause08365 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08366 chi hbad
                ·
                  exact fin15Anchored_clause08367 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08368 chi hbad
                ·
                  exact fin15Anchored_clause08369 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08370 chi hbad
                ·
                  exact fin15Anchored_clause08371 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08372 chi hbad
                ·
                  exact fin15Anchored_clause08373 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08374 chi hbad
                ·
                  exact fin15Anchored_clause08375 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08376 chi hbad
                ·
                  exact fin15Anchored_clause08377 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08378 chi hbad
                ·
                  exact fin15Anchored_clause08379 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08380 chi hbad
                ·
                  exact fin15Anchored_clause08381 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08382 chi hbad
                ·
                  exact fin15Anchored_clause08383 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08384 chi hbad
                ·
                  exact fin15Anchored_clause08385 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08386 chi hbad
                ·
                  exact fin15Anchored_clause08387 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08388 chi hbad
                ·
                  exact fin15Anchored_clause08389 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08390 chi hbad
                ·
                  exact fin15Anchored_clause08391 chi hbad
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
                exact fin15Anchored_clause08392 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08393 chi hbad
                ·
                  exact fin15Anchored_clause08394 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08395 chi hbad
                ·
                  exact fin15Anchored_clause08396 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08397 chi hbad
                ·
                  exact fin15Anchored_clause08398 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08399 chi hbad
                ·
                  exact fin15Anchored_clause08400 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08401 chi hbad
                ·
                  exact fin15Anchored_clause08402 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08403 chi hbad
                ·
                  exact fin15Anchored_clause08404 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08405 chi hbad
                ·
                  exact fin15Anchored_clause08406 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08407 chi hbad
                ·
                  exact fin15Anchored_clause08408 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08409 chi hbad
                ·
                  exact fin15Anchored_clause08410 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08411 chi hbad
                ·
                  exact fin15Anchored_clause08412 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08413 chi hbad
                ·
                  exact fin15Anchored_clause08414 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08415 chi hbad
                ·
                  exact fin15Anchored_clause08416 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08417 chi hbad
                ·
                  exact fin15Anchored_clause08418 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08419 chi hbad
                ·
                  exact fin15Anchored_clause08420 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08421 chi hbad
                ·
                  exact fin15Anchored_clause08422 chi hbad
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
                  exact fin15Anchored_clause08423 chi hbad
                ·
                  exact fin15Anchored_clause08424 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08425 chi hbad
                ·
                  exact fin15Anchored_clause08426 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08427 chi hbad
                ·
                  exact fin15Anchored_clause08428 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08429 chi hbad
                ·
                  exact fin15Anchored_clause08430 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08431 chi hbad
                ·
                  exact fin15Anchored_clause08432 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08433 chi hbad
                ·
                  exact fin15Anchored_clause08434 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08435 chi hbad
                ·
                  exact fin15Anchored_clause08436 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08437 chi hbad
                ·
                  exact fin15Anchored_clause08438 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08439 chi hbad
                ·
                  exact fin15Anchored_clause08440 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08441 chi hbad
                ·
                  exact fin15Anchored_clause08442 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08443 chi hbad
                ·
                  exact fin15Anchored_clause08444 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08445 chi hbad
                ·
                  exact fin15Anchored_clause08446 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08447 chi hbad
                ·
                  exact fin15Anchored_clause08448 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08449 chi hbad
                ·
                  exact fin15Anchored_clause08450 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08451 chi hbad
                ·
                  exact fin15Anchored_clause08452 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08453 chi hbad
                ·
                  exact fin15Anchored_clause08454 chi hbad
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
                exact fin15Anchored_clause08455 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08456 chi hbad
                ·
                  exact fin15Anchored_clause08457 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08458 chi hbad
                ·
                  exact fin15Anchored_clause08459 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08460 chi hbad
                ·
                  exact fin15Anchored_clause08461 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08462 chi hbad
                ·
                  exact fin15Anchored_clause08463 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08464 chi hbad
                ·
                  exact fin15Anchored_clause08465 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08466 chi hbad
                ·
                  exact fin15Anchored_clause08467 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08468 chi hbad
                ·
                  exact fin15Anchored_clause08469 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08470 chi hbad
                ·
                  exact fin15Anchored_clause08471 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08472 chi hbad
                ·
                  exact fin15Anchored_clause08473 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08474 chi hbad
                ·
                  exact fin15Anchored_clause08475 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08476 chi hbad
                ·
                  exact fin15Anchored_clause08477 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08478 chi hbad
                ·
                  exact fin15Anchored_clause08479 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08480 chi hbad
                ·
                  exact fin15Anchored_clause08481 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08482 chi hbad
                ·
                  exact fin15Anchored_clause08483 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08484 chi hbad
                ·
                  exact fin15Anchored_clause08485 chi hbad
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
                  exact fin15Anchored_clause08486 chi hbad
                ·
                  exact fin15Anchored_clause08487 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08488 chi hbad
                ·
                  exact fin15Anchored_clause08489 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08490 chi hbad
                ·
                  exact fin15Anchored_clause08491 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08492 chi hbad
                ·
                  exact fin15Anchored_clause08493 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08494 chi hbad
                ·
                  exact fin15Anchored_clause08495 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08496 chi hbad
                ·
                  exact fin15Anchored_clause08497 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08498 chi hbad
                ·
                  exact fin15Anchored_clause08499 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08500 chi hbad
                ·
                  exact fin15Anchored_clause08501 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08502 chi hbad
                ·
                  exact fin15Anchored_clause08503 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08504 chi hbad
                ·
                  exact fin15Anchored_clause08505 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08506 chi hbad
                ·
                  exact fin15Anchored_clause08507 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08508 chi hbad
                ·
                  exact fin15Anchored_clause08509 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08510 chi hbad
                ·
                  exact fin15Anchored_clause08511 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08512 chi hbad
                ·
                  exact fin15Anchored_clause08513 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08514 chi hbad
                ·
                  exact fin15Anchored_clause08515 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08516 chi hbad
                ·
                  exact fin15Anchored_clause08517 chi hbad
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
                exact fin15Anchored_clause08518 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08519 chi hbad
                ·
                  exact fin15Anchored_clause08520 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08521 chi hbad
                ·
                  exact fin15Anchored_clause08522 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08523 chi hbad
                ·
                  exact fin15Anchored_clause08524 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08525 chi hbad
                ·
                  exact fin15Anchored_clause08526 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08527 chi hbad
                ·
                  exact fin15Anchored_clause08528 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08529 chi hbad
                ·
                  exact fin15Anchored_clause08530 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08531 chi hbad
                ·
                  exact fin15Anchored_clause08532 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08533 chi hbad
                ·
                  exact fin15Anchored_clause08534 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08535 chi hbad
                ·
                  exact fin15Anchored_clause08536 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08537 chi hbad
                ·
                  exact fin15Anchored_clause08538 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08539 chi hbad
                ·
                  exact fin15Anchored_clause08540 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08541 chi hbad
                ·
                  exact fin15Anchored_clause08542 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08543 chi hbad
                ·
                  exact fin15Anchored_clause08544 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08545 chi hbad
                ·
                  exact fin15Anchored_clause08546 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08547 chi hbad
                ·
                  exact fin15Anchored_clause08548 chi hbad
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
                  exact fin15Anchored_clause08549 chi hbad
                ·
                  exact fin15Anchored_clause08550 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08551 chi hbad
                ·
                  exact fin15Anchored_clause08552 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08553 chi hbad
                ·
                  exact fin15Anchored_clause08554 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08555 chi hbad
                ·
                  exact fin15Anchored_clause08556 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08557 chi hbad
                ·
                  exact fin15Anchored_clause08558 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08559 chi hbad
                ·
                  exact fin15Anchored_clause08560 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08561 chi hbad
                ·
                  exact fin15Anchored_clause08562 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08563 chi hbad
                ·
                  exact fin15Anchored_clause08564 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08565 chi hbad
                ·
                  exact fin15Anchored_clause08566 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08567 chi hbad
                ·
                  exact fin15Anchored_clause08568 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08569 chi hbad
                ·
                  exact fin15Anchored_clause08570 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08571 chi hbad
                ·
                  exact fin15Anchored_clause08572 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08573 chi hbad
                ·
                  exact fin15Anchored_clause08574 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08575 chi hbad
                ·
                  exact fin15Anchored_clause08576 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08577 chi hbad
                ·
                  exact fin15Anchored_clause08578 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause08579 chi hbad
                ·
                  exact fin15Anchored_clause08580 chi hbad

end ErdosSzekeres

end
