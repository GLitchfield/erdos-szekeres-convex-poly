module

public import ErdosSzekeres.Fin15AnchoredClauseChunk057
public import ErdosSzekeres.Fin15AnchoredClauseChunk058
public import ErdosSzekeres.Fin15AnchoredClauseChunk059

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 029. -/

theorem fin15Anchored_rejectSemanticSegment029
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0058 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0566 chi) ∨
      ((¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0058 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0566 chi) ∨
      (¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0059 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0567 chi))) ∨
      (((¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0059 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0567 chi) ∨
      (¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0022 chi ∧
      ¬Fin15AnchoredAtom0060 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0568 chi)) ∨
      ((¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0022 chi ∧
      ¬Fin15AnchoredAtom0060 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0568 chi) ∨
      (¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0061 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0569 chi)))) ∨
      ((((¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0061 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0569 chi) ∨
      (¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0570 chi)) ∨
      ((¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0570 chi) ∨
      (¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0571 chi))) ∨
      (((¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0571 chi) ∨
      (¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0019 chi ∧
      ¬Fin15AnchoredAtom0064 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0572 chi)) ∨
      ((¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0019 chi ∧
      ¬Fin15AnchoredAtom0064 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0572 chi) ∨
      (¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0065 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0573 chi))))) ∨
      (((((¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0065 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0573 chi) ∨
      (¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0066 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0574 chi)) ∨
      ((¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0066 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0574 chi) ∨
      (¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0022 chi ∧
      ¬Fin15AnchoredAtom0067 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0575 chi))) ∨
      (((¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0022 chi ∧
      ¬Fin15AnchoredAtom0067 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0575 chi) ∨
      (¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0068 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0576 chi)) ∨
      ((¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0068 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0576 chi) ∨
      (¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0577 chi)))) ∨
      ((((¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0577 chi) ∨
      (¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0578 chi)) ∨
      ((¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0578 chi) ∨
      (¬Fin15AnchoredAtom0019 chi ∧
      ¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0071 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0579 chi))) ∨
      (((¬Fin15AnchoredAtom0019 chi ∧
      ¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0071 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0579 chi) ∨
      (¬Fin15AnchoredAtom0019 chi ∧
      ¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0072 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0580 chi)) ∨
      ((¬Fin15AnchoredAtom0019 chi ∧
      ¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0072 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0580 chi) ∨
      (¬Fin15AnchoredAtom0019 chi ∧
      ¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0074 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0582 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0019 chi ∧
      ¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0074 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0582 chi) ∨
      (¬Fin15AnchoredAtom0019 chi ∧
      ¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0075 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      Fin15AnchoredAtom0583 chi)) ∨
      ((¬Fin15AnchoredAtom0019 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0584 chi) ∨
      (¬Fin15AnchoredAtom0019 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      Fin15AnchoredAtom0584 chi))) ∨
      (((¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0077 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0585 chi) ∨
      (¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0077 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0585 chi)) ∨
      ((¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0022 chi ∧
      ¬Fin15AnchoredAtom0078 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0586 chi) ∨
      (¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0022 chi ∧
      ¬Fin15AnchoredAtom0078 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0586 chi)))) ∨
      ((((¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0079 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0587 chi) ∨
      (¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0079 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0587 chi)) ∨
      ((¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0588 chi) ∨
      (¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0588 chi))) ∨
      (((¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0589 chi) ∨
      (¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0589 chi)) ∨
      ((¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0022 chi ∧
      ¬Fin15AnchoredAtom0082 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0590 chi) ∨
      (¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0022 chi ∧
      ¬Fin15AnchoredAtom0082 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0590 chi))))) ∨
      (((((¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0083 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0591 chi) ∨
      (¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0083 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0591 chi)) ∨
      ((¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0592 chi) ∨
      (¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0592 chi))) ∨
      (((¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0593 chi) ∨
      (¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0593 chi)) ∨
      ((¬Fin15AnchoredAtom0022 chi ∧
      ¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0086 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0594 chi) ∨
      (¬Fin15AnchoredAtom0022 chi ∧
      ¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0086 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0594 chi)))) ∨
      ((((¬Fin15AnchoredAtom0022 chi ∧
      ¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0087 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0595 chi) ∨
      (¬Fin15AnchoredAtom0022 chi ∧
      ¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0087 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0595 chi)) ∨
      ((¬Fin15AnchoredAtom0022 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0596 chi) ∨
      (¬Fin15AnchoredAtom0022 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0596 chi))) ∨
      (((¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0597 chi) ∨
      (¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0597 chi)) ∨
      ((¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0598 chi) ∨
      (¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0598 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0599 chi) ∨
      ((¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0599 chi) ∨
      (¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0037 chi ∧
      ¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0600 chi))) ∨
      (((¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0037 chi ∧
      Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0600 chi) ∨
      (¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0038 chi ∧
      ¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0601 chi)) ∨
      ((¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0038 chi ∧
      Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0601 chi) ∨
      (¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0039 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0602 chi)))) ∨
      ((((¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0039 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0602 chi) ∨
      (¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0030 chi ∧
      ¬Fin15AnchoredAtom0040 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0603 chi)) ∨
      ((¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0030 chi ∧
      ¬Fin15AnchoredAtom0040 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0603 chi) ∨
      (¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0041 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0604 chi))) ∨
      (((¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0041 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0604 chi) ∨
      (¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0042 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0605 chi)) ∨
      ((¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0042 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0605 chi) ∨
      (¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0033 chi ∧
      ¬Fin15AnchoredAtom0043 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0606 chi))))) ∨
      (((((¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0033 chi ∧
      ¬Fin15AnchoredAtom0043 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0606 chi) ∨
      (¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0044 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0607 chi)) ∨
      ((¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0044 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0607 chi) ∨
      (¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0608 chi))) ∨
      (((¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0608 chi) ∨
      (¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0609 chi)) ∨
      ((¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0609 chi) ∨
      (¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0047 chi ∧
      ¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0610 chi)))) ∨
      ((((¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0047 chi ∧
      Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0610 chi) ∨
      (¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0048 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0611 chi)) ∨
      ((¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0048 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0611 chi) ∨
      (¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0030 chi ∧
      ¬Fin15AnchoredAtom0049 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0612 chi))) ∨
      (((¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0030 chi ∧
      ¬Fin15AnchoredAtom0049 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0612 chi) ∨
      (¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0050 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0613 chi)) ∨
      ((¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0050 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0613 chi) ∨
      (¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0051 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0614 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0051 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0614 chi) ∨
      (¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0033 chi ∧
      ¬Fin15AnchoredAtom0052 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0615 chi)) ∨
      ((¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0033 chi ∧
      ¬Fin15AnchoredAtom0052 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0615 chi) ∨
      (¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0053 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0616 chi))) ∨
      (((¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0053 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0616 chi) ∨
      (¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0617 chi)) ∨
      ((¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0617 chi) ∨
      (¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0618 chi)))) ∨
      ((((¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0618 chi) ∨
      (¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0056 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0619 chi)) ∨
      ((¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0056 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0619 chi) ∨
      (¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0030 chi ∧
      ¬Fin15AnchoredAtom0057 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0620 chi))) ∨
      (((¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0030 chi ∧
      ¬Fin15AnchoredAtom0057 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0620 chi) ∨
      (¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0058 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0621 chi)) ∨
      ((¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0058 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0621 chi) ∨
      (¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0059 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0622 chi))))) ∨
      (((((¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0059 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0622 chi) ∨
      (¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0033 chi ∧
      ¬Fin15AnchoredAtom0060 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0623 chi)) ∨
      ((¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0033 chi ∧
      ¬Fin15AnchoredAtom0060 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0623 chi) ∨
      (¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0061 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0624 chi))) ∨
      (((¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0061 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0624 chi) ∨
      (¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0625 chi)) ∨
      ((¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0625 chi) ∨
      (¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0626 chi)))) ∨
      ((((¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0626 chi) ∨
      (¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0030 chi ∧
      ¬Fin15AnchoredAtom0064 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0627 chi)) ∨
      ((¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0030 chi ∧
      ¬Fin15AnchoredAtom0064 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0627 chi) ∨
      (¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0065 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0628 chi))) ∨
      (((¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0065 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0628 chi) ∨
      (¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0066 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0629 chi)) ∨
      ((¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0066 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0629 chi) ∨
      (¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0033 chi ∧
      ¬Fin15AnchoredAtom0067 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0630 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0033 chi ∧
      ¬Fin15AnchoredAtom0067 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0630 chi) ∨
      ((¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0068 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0631 chi) ∨
      (¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0068 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0631 chi))) ∨
      (((¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0632 chi) ∨
      (¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0632 chi)) ∨
      ((¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0633 chi) ∨
      (¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0633 chi)))) ∨
      ((((¬Fin15AnchoredAtom0030 chi ∧
      ¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0071 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0634 chi) ∨
      (¬Fin15AnchoredAtom0030 chi ∧
      ¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0071 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0634 chi)) ∨
      ((¬Fin15AnchoredAtom0030 chi ∧
      ¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0072 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0635 chi) ∨
      (¬Fin15AnchoredAtom0030 chi ∧
      ¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0072 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0635 chi))) ∨
      (((¬Fin15AnchoredAtom0030 chi ∧
      ¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0074 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0637 chi) ∨
      (¬Fin15AnchoredAtom0030 chi ∧
      ¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0074 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0637 chi)) ∨
      ((¬Fin15AnchoredAtom0030 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0075 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0638 chi) ∨
      (¬Fin15AnchoredAtom0030 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0075 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0638 chi))))) ∨
      (((((¬Fin15AnchoredAtom0030 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0639 chi) ∨
      (¬Fin15AnchoredAtom0030 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0639 chi)) ∨
      ((¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0077 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0640 chi) ∨
      (¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0077 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0640 chi))) ∨
      (((¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0033 chi ∧
      ¬Fin15AnchoredAtom0078 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0641 chi) ∨
      (¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0033 chi ∧
      ¬Fin15AnchoredAtom0078 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0641 chi)) ∨
      ((¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0079 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0642 chi) ∨
      (¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0079 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0642 chi)))) ∨
      ((((¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0643 chi) ∨
      (¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0643 chi)) ∨
      ((¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0644 chi) ∨
      (¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0644 chi))) ∨
      (((¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0033 chi ∧
      ¬Fin15AnchoredAtom0082 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0645 chi) ∨
      (¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0033 chi ∧
      ¬Fin15AnchoredAtom0082 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0645 chi)) ∨
      ((¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0083 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0646 chi) ∨
      (¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0083 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0646 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0647 chi) ∨
      (¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0647 chi)) ∨
      ((¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0648 chi) ∨
      (¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0648 chi))) ∨
      (((¬Fin15AnchoredAtom0033 chi ∧
      ¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0086 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0649 chi) ∨
      (¬Fin15AnchoredAtom0033 chi ∧
      ¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0086 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0649 chi)) ∨
      ((¬Fin15AnchoredAtom0033 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0087 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0650 chi) ∨
      (¬Fin15AnchoredAtom0033 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0087 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0650 chi)))) ∨
      ((((¬Fin15AnchoredAtom0033 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0651 chi) ∨
      (¬Fin15AnchoredAtom0033 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0651 chi)) ∨
      ((¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0652 chi) ∨
      (¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0652 chi))) ∨
      (((¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0653 chi) ∨
      (¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0653 chi)) ∨
      ((¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0654 chi) ∨
      (¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0654 chi))))) ∨
      (((((¬Fin15AnchoredAtom0037 chi ∧
      ¬Fin15AnchoredAtom0038 chi ∧
      ¬Fin15AnchoredAtom0047 chi ∧
      ¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0655 chi) ∨
      (¬Fin15AnchoredAtom0037 chi ∧
      ¬Fin15AnchoredAtom0038 chi ∧
      ¬Fin15AnchoredAtom0047 chi ∧
      Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0655 chi)) ∨
      ((¬Fin15AnchoredAtom0037 chi ∧
      ¬Fin15AnchoredAtom0039 chi ∧
      ¬Fin15AnchoredAtom0048 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0656 chi) ∨
      (¬Fin15AnchoredAtom0037 chi ∧
      ¬Fin15AnchoredAtom0039 chi ∧
      ¬Fin15AnchoredAtom0048 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0656 chi))) ∨
      (((¬Fin15AnchoredAtom0037 chi ∧
      ¬Fin15AnchoredAtom0040 chi ∧
      ¬Fin15AnchoredAtom0049 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0657 chi) ∨
      (¬Fin15AnchoredAtom0037 chi ∧
      ¬Fin15AnchoredAtom0040 chi ∧
      ¬Fin15AnchoredAtom0049 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0657 chi)) ∨
      ((¬Fin15AnchoredAtom0037 chi ∧
      ¬Fin15AnchoredAtom0041 chi ∧
      ¬Fin15AnchoredAtom0050 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0658 chi) ∨
      (¬Fin15AnchoredAtom0037 chi ∧
      ¬Fin15AnchoredAtom0041 chi ∧
      ¬Fin15AnchoredAtom0050 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0658 chi)))) ∨
      ((((¬Fin15AnchoredAtom0037 chi ∧
      ¬Fin15AnchoredAtom0042 chi ∧
      ¬Fin15AnchoredAtom0051 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0659 chi) ∨
      (¬Fin15AnchoredAtom0037 chi ∧
      ¬Fin15AnchoredAtom0042 chi ∧
      ¬Fin15AnchoredAtom0051 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0659 chi)) ∨
      ((¬Fin15AnchoredAtom0037 chi ∧
      ¬Fin15AnchoredAtom0043 chi ∧
      ¬Fin15AnchoredAtom0052 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0660 chi) ∨
      (¬Fin15AnchoredAtom0037 chi ∧
      ¬Fin15AnchoredAtom0043 chi ∧
      ¬Fin15AnchoredAtom0052 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0660 chi))) ∨
      (((¬Fin15AnchoredAtom0037 chi ∧
      ¬Fin15AnchoredAtom0044 chi ∧
      ¬Fin15AnchoredAtom0053 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0661 chi) ∨
      (¬Fin15AnchoredAtom0037 chi ∧
      ¬Fin15AnchoredAtom0044 chi ∧
      ¬Fin15AnchoredAtom0053 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0661 chi)) ∨
      ((¬Fin15AnchoredAtom0037 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0662 chi) ∨
      (¬Fin15AnchoredAtom0037 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0662 chi))))))) ∨
      (((((((¬Fin15AnchoredAtom0037 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0663 chi) ∨
      (¬Fin15AnchoredAtom0037 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0663 chi)) ∨
      ((¬Fin15AnchoredAtom0038 chi ∧
      ¬Fin15AnchoredAtom0039 chi ∧
      ¬Fin15AnchoredAtom0056 chi ∧
      ¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0664 chi) ∨
      (¬Fin15AnchoredAtom0038 chi ∧
      ¬Fin15AnchoredAtom0039 chi ∧
      ¬Fin15AnchoredAtom0056 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0664 chi))) ∨
      (((¬Fin15AnchoredAtom0038 chi ∧
      ¬Fin15AnchoredAtom0040 chi ∧
      ¬Fin15AnchoredAtom0057 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0665 chi) ∨
      (¬Fin15AnchoredAtom0038 chi ∧
      ¬Fin15AnchoredAtom0040 chi ∧
      ¬Fin15AnchoredAtom0057 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0665 chi)) ∨
      ((¬Fin15AnchoredAtom0038 chi ∧
      ¬Fin15AnchoredAtom0041 chi ∧
      ¬Fin15AnchoredAtom0058 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0666 chi) ∨
      (¬Fin15AnchoredAtom0038 chi ∧
      ¬Fin15AnchoredAtom0041 chi ∧
      ¬Fin15AnchoredAtom0058 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0666 chi)))) ∨
      ((((¬Fin15AnchoredAtom0038 chi ∧
      ¬Fin15AnchoredAtom0042 chi ∧
      ¬Fin15AnchoredAtom0059 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0667 chi) ∨
      (¬Fin15AnchoredAtom0038 chi ∧
      ¬Fin15AnchoredAtom0042 chi ∧
      ¬Fin15AnchoredAtom0059 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0667 chi)) ∨
      ((¬Fin15AnchoredAtom0038 chi ∧
      ¬Fin15AnchoredAtom0043 chi ∧
      ¬Fin15AnchoredAtom0060 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0668 chi) ∨
      (¬Fin15AnchoredAtom0038 chi ∧
      ¬Fin15AnchoredAtom0043 chi ∧
      ¬Fin15AnchoredAtom0060 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0668 chi))) ∨
      (((¬Fin15AnchoredAtom0038 chi ∧
      ¬Fin15AnchoredAtom0044 chi ∧
      ¬Fin15AnchoredAtom0061 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0669 chi) ∨
      (¬Fin15AnchoredAtom0038 chi ∧
      ¬Fin15AnchoredAtom0044 chi ∧
      ¬Fin15AnchoredAtom0061 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0669 chi)) ∨
      ((¬Fin15AnchoredAtom0038 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0670 chi) ∨
      (¬Fin15AnchoredAtom0038 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0670 chi))))) ∨
      (((((¬Fin15AnchoredAtom0038 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0671 chi) ∨
      (¬Fin15AnchoredAtom0038 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0671 chi)) ∨
      ((¬Fin15AnchoredAtom0039 chi ∧
      ¬Fin15AnchoredAtom0040 chi ∧
      ¬Fin15AnchoredAtom0064 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0672 chi) ∨
      (¬Fin15AnchoredAtom0039 chi ∧
      ¬Fin15AnchoredAtom0040 chi ∧
      ¬Fin15AnchoredAtom0064 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0672 chi))) ∨
      (((¬Fin15AnchoredAtom0039 chi ∧
      ¬Fin15AnchoredAtom0041 chi ∧
      ¬Fin15AnchoredAtom0065 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0673 chi) ∨
      (¬Fin15AnchoredAtom0039 chi ∧
      ¬Fin15AnchoredAtom0041 chi ∧
      ¬Fin15AnchoredAtom0065 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0673 chi)) ∨
      ((¬Fin15AnchoredAtom0039 chi ∧
      ¬Fin15AnchoredAtom0042 chi ∧
      ¬Fin15AnchoredAtom0066 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0674 chi) ∨
      (¬Fin15AnchoredAtom0039 chi ∧
      ¬Fin15AnchoredAtom0042 chi ∧
      ¬Fin15AnchoredAtom0066 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0674 chi)))) ∨
      ((((¬Fin15AnchoredAtom0039 chi ∧
      ¬Fin15AnchoredAtom0043 chi ∧
      ¬Fin15AnchoredAtom0067 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0675 chi) ∨
      (¬Fin15AnchoredAtom0039 chi ∧
      ¬Fin15AnchoredAtom0043 chi ∧
      ¬Fin15AnchoredAtom0067 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0675 chi)) ∨
      ((¬Fin15AnchoredAtom0039 chi ∧
      ¬Fin15AnchoredAtom0044 chi ∧
      ¬Fin15AnchoredAtom0068 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0676 chi) ∨
      (¬Fin15AnchoredAtom0039 chi ∧
      ¬Fin15AnchoredAtom0044 chi ∧
      ¬Fin15AnchoredAtom0068 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0676 chi))) ∨
      (((¬Fin15AnchoredAtom0039 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0677 chi) ∨
      (¬Fin15AnchoredAtom0039 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0677 chi)) ∨
      ((¬Fin15AnchoredAtom0039 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0678 chi) ∨
      (¬Fin15AnchoredAtom0039 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0678 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0040 chi ∧
      ¬Fin15AnchoredAtom0041 chi ∧
      ¬Fin15AnchoredAtom0071 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0679 chi) ∨
      (¬Fin15AnchoredAtom0040 chi ∧
      ¬Fin15AnchoredAtom0041 chi ∧
      ¬Fin15AnchoredAtom0071 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0679 chi)) ∨
      ((¬Fin15AnchoredAtom0040 chi ∧
      ¬Fin15AnchoredAtom0042 chi ∧
      ¬Fin15AnchoredAtom0072 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0680 chi) ∨
      (¬Fin15AnchoredAtom0040 chi ∧
      ¬Fin15AnchoredAtom0042 chi ∧
      ¬Fin15AnchoredAtom0072 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0680 chi))) ∨
      (((¬Fin15AnchoredAtom0040 chi ∧
      ¬Fin15AnchoredAtom0044 chi ∧
      ¬Fin15AnchoredAtom0074 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0682 chi) ∨
      (¬Fin15AnchoredAtom0040 chi ∧
      ¬Fin15AnchoredAtom0044 chi ∧
      ¬Fin15AnchoredAtom0074 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0682 chi)) ∨
      ((¬Fin15AnchoredAtom0040 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      ¬Fin15AnchoredAtom0075 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0683 chi) ∨
      (¬Fin15AnchoredAtom0040 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      ¬Fin15AnchoredAtom0075 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0683 chi)))) ∨
      ((((¬Fin15AnchoredAtom0040 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0684 chi) ∨
      (¬Fin15AnchoredAtom0040 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0684 chi)) ∨
      ((¬Fin15AnchoredAtom0041 chi ∧
      ¬Fin15AnchoredAtom0042 chi ∧
      ¬Fin15AnchoredAtom0077 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0685 chi) ∨
      (¬Fin15AnchoredAtom0041 chi ∧
      ¬Fin15AnchoredAtom0042 chi ∧
      ¬Fin15AnchoredAtom0077 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0685 chi))) ∨
      (((¬Fin15AnchoredAtom0041 chi ∧
      ¬Fin15AnchoredAtom0043 chi ∧
      ¬Fin15AnchoredAtom0078 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0686 chi) ∨
      (¬Fin15AnchoredAtom0041 chi ∧
      ¬Fin15AnchoredAtom0043 chi ∧
      ¬Fin15AnchoredAtom0078 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0686 chi)) ∨
      ((¬Fin15AnchoredAtom0041 chi ∧
      ¬Fin15AnchoredAtom0044 chi ∧
      ¬Fin15AnchoredAtom0079 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0687 chi) ∨
      (¬Fin15AnchoredAtom0041 chi ∧
      ¬Fin15AnchoredAtom0044 chi ∧
      ¬Fin15AnchoredAtom0079 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0687 chi))))) ∨
      (((((¬Fin15AnchoredAtom0041 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0688 chi) ∨
      (¬Fin15AnchoredAtom0041 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0688 chi)) ∨
      ((¬Fin15AnchoredAtom0041 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0689 chi) ∨
      (¬Fin15AnchoredAtom0041 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0689 chi))) ∨
      (((¬Fin15AnchoredAtom0042 chi ∧
      ¬Fin15AnchoredAtom0043 chi ∧
      ¬Fin15AnchoredAtom0082 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0690 chi) ∨
      (¬Fin15AnchoredAtom0042 chi ∧
      ¬Fin15AnchoredAtom0043 chi ∧
      ¬Fin15AnchoredAtom0082 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0690 chi)) ∨
      ((¬Fin15AnchoredAtom0042 chi ∧
      ¬Fin15AnchoredAtom0044 chi ∧
      ¬Fin15AnchoredAtom0083 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0691 chi) ∨
      (¬Fin15AnchoredAtom0042 chi ∧
      ¬Fin15AnchoredAtom0044 chi ∧
      ¬Fin15AnchoredAtom0083 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0691 chi)))) ∨
      ((((¬Fin15AnchoredAtom0042 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0692 chi) ∨
      (¬Fin15AnchoredAtom0042 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0692 chi)) ∨
      ((¬Fin15AnchoredAtom0042 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0693 chi) ∨
      (¬Fin15AnchoredAtom0042 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0693 chi))) ∨
      (((¬Fin15AnchoredAtom0043 chi ∧
      ¬Fin15AnchoredAtom0044 chi ∧
      ¬Fin15AnchoredAtom0086 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0694 chi) ∨
      (¬Fin15AnchoredAtom0043 chi ∧
      ¬Fin15AnchoredAtom0044 chi ∧
      ¬Fin15AnchoredAtom0086 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0694 chi)) ∨
      ((¬Fin15AnchoredAtom0043 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      ¬Fin15AnchoredAtom0087 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0695 chi) ∨
      (¬Fin15AnchoredAtom0043 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      ¬Fin15AnchoredAtom0087 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0695 chi)))))))))) := by
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
                exact fin15Anchored_clause07319 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07320 chi hbad
                ·
                  exact fin15Anchored_clause07321 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07322 chi hbad
                ·
                  exact fin15Anchored_clause07323 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07324 chi hbad
                ·
                  exact fin15Anchored_clause07325 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07326 chi hbad
                ·
                  exact fin15Anchored_clause07327 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07328 chi hbad
                ·
                  exact fin15Anchored_clause07329 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07330 chi hbad
                ·
                  exact fin15Anchored_clause07331 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07332 chi hbad
                ·
                  exact fin15Anchored_clause07333 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07334 chi hbad
                ·
                  exact fin15Anchored_clause07335 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07336 chi hbad
                ·
                  exact fin15Anchored_clause07337 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07338 chi hbad
                ·
                  exact fin15Anchored_clause07339 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07340 chi hbad
                ·
                  exact fin15Anchored_clause07341 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07342 chi hbad
                ·
                  exact fin15Anchored_clause07343 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07344 chi hbad
                ·
                  exact fin15Anchored_clause07345 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07346 chi hbad
                ·
                  exact fin15Anchored_clause07347 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07348 chi hbad
                ·
                  exact fin15Anchored_clause07349 chi hbad
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
                  exact fin15Anchored_clause07350 chi hbad
                ·
                  exact fin15Anchored_clause07351 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07352 chi hbad
                ·
                  exact fin15Anchored_clause07353 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07354 chi hbad
                ·
                  exact fin15Anchored_clause07355 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07356 chi hbad
                ·
                  exact fin15Anchored_clause07357 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07358 chi hbad
                ·
                  exact fin15Anchored_clause07359 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07360 chi hbad
                ·
                  exact fin15Anchored_clause07361 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07362 chi hbad
                ·
                  exact fin15Anchored_clause07363 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07364 chi hbad
                ·
                  exact fin15Anchored_clause07365 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07366 chi hbad
                ·
                  exact fin15Anchored_clause07367 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07368 chi hbad
                ·
                  exact fin15Anchored_clause07369 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07370 chi hbad
                ·
                  exact fin15Anchored_clause07371 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07372 chi hbad
                ·
                  exact fin15Anchored_clause07373 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07374 chi hbad
                ·
                  exact fin15Anchored_clause07375 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07376 chi hbad
                ·
                  exact fin15Anchored_clause07377 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07378 chi hbad
                ·
                  exact fin15Anchored_clause07379 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07380 chi hbad
                ·
                  exact fin15Anchored_clause07381 chi hbad
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
                exact fin15Anchored_clause07382 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07383 chi hbad
                ·
                  exact fin15Anchored_clause07384 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07385 chi hbad
                ·
                  exact fin15Anchored_clause07386 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07387 chi hbad
                ·
                  exact fin15Anchored_clause07388 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07389 chi hbad
                ·
                  exact fin15Anchored_clause07390 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07391 chi hbad
                ·
                  exact fin15Anchored_clause07392 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07393 chi hbad
                ·
                  exact fin15Anchored_clause07394 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07395 chi hbad
                ·
                  exact fin15Anchored_clause07396 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07397 chi hbad
                ·
                  exact fin15Anchored_clause07398 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07399 chi hbad
                ·
                  exact fin15Anchored_clause07400 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07401 chi hbad
                ·
                  exact fin15Anchored_clause07402 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07403 chi hbad
                ·
                  exact fin15Anchored_clause07404 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07405 chi hbad
                ·
                  exact fin15Anchored_clause07406 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07407 chi hbad
                ·
                  exact fin15Anchored_clause07408 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07409 chi hbad
                ·
                  exact fin15Anchored_clause07410 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07411 chi hbad
                ·
                  exact fin15Anchored_clause07412 chi hbad
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
                  exact fin15Anchored_clause07413 chi hbad
                ·
                  exact fin15Anchored_clause07414 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07415 chi hbad
                ·
                  exact fin15Anchored_clause07416 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07417 chi hbad
                ·
                  exact fin15Anchored_clause07418 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07419 chi hbad
                ·
                  exact fin15Anchored_clause07420 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07421 chi hbad
                ·
                  exact fin15Anchored_clause07422 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07423 chi hbad
                ·
                  exact fin15Anchored_clause07424 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07425 chi hbad
                ·
                  exact fin15Anchored_clause07426 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07427 chi hbad
                ·
                  exact fin15Anchored_clause07428 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07429 chi hbad
                ·
                  exact fin15Anchored_clause07430 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07431 chi hbad
                ·
                  exact fin15Anchored_clause07432 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07433 chi hbad
                ·
                  exact fin15Anchored_clause07434 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07435 chi hbad
                ·
                  exact fin15Anchored_clause07436 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07437 chi hbad
                ·
                  exact fin15Anchored_clause07438 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07439 chi hbad
                ·
                  exact fin15Anchored_clause07440 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07441 chi hbad
                ·
                  exact fin15Anchored_clause07442 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07443 chi hbad
                ·
                  exact fin15Anchored_clause07444 chi hbad
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
                exact fin15Anchored_clause07445 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07446 chi hbad
                ·
                  exact fin15Anchored_clause07447 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07448 chi hbad
                ·
                  exact fin15Anchored_clause07449 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07450 chi hbad
                ·
                  exact fin15Anchored_clause07451 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07452 chi hbad
                ·
                  exact fin15Anchored_clause07453 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07454 chi hbad
                ·
                  exact fin15Anchored_clause07455 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07456 chi hbad
                ·
                  exact fin15Anchored_clause07457 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07458 chi hbad
                ·
                  exact fin15Anchored_clause07459 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07460 chi hbad
                ·
                  exact fin15Anchored_clause07461 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07462 chi hbad
                ·
                  exact fin15Anchored_clause07463 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07464 chi hbad
                ·
                  exact fin15Anchored_clause07465 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07466 chi hbad
                ·
                  exact fin15Anchored_clause07467 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07468 chi hbad
                ·
                  exact fin15Anchored_clause07469 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07470 chi hbad
                ·
                  exact fin15Anchored_clause07471 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07472 chi hbad
                ·
                  exact fin15Anchored_clause07473 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07474 chi hbad
                ·
                  exact fin15Anchored_clause07475 chi hbad
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
                  exact fin15Anchored_clause07476 chi hbad
                ·
                  exact fin15Anchored_clause07477 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07478 chi hbad
                ·
                  exact fin15Anchored_clause07479 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07480 chi hbad
                ·
                  exact fin15Anchored_clause07481 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07482 chi hbad
                ·
                  exact fin15Anchored_clause07483 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07484 chi hbad
                ·
                  exact fin15Anchored_clause07485 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07486 chi hbad
                ·
                  exact fin15Anchored_clause07487 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07488 chi hbad
                ·
                  exact fin15Anchored_clause07489 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07490 chi hbad
                ·
                  exact fin15Anchored_clause07491 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07492 chi hbad
                ·
                  exact fin15Anchored_clause07493 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07494 chi hbad
                ·
                  exact fin15Anchored_clause07495 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07496 chi hbad
                ·
                  exact fin15Anchored_clause07497 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07498 chi hbad
                ·
                  exact fin15Anchored_clause07499 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07500 chi hbad
                ·
                  exact fin15Anchored_clause07501 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07502 chi hbad
                ·
                  exact fin15Anchored_clause07503 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07504 chi hbad
                ·
                  exact fin15Anchored_clause07505 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07506 chi hbad
                ·
                  exact fin15Anchored_clause07507 chi hbad
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
                  exact fin15Anchored_clause07508 chi hbad
                ·
                  exact fin15Anchored_clause07509 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07510 chi hbad
                ·
                  exact fin15Anchored_clause07511 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07512 chi hbad
                ·
                  exact fin15Anchored_clause07513 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07514 chi hbad
                ·
                  exact fin15Anchored_clause07515 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07516 chi hbad
                ·
                  exact fin15Anchored_clause07517 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07518 chi hbad
                ·
                  exact fin15Anchored_clause07519 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07520 chi hbad
                ·
                  exact fin15Anchored_clause07521 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07522 chi hbad
                ·
                  exact fin15Anchored_clause07523 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07524 chi hbad
                ·
                  exact fin15Anchored_clause07525 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07526 chi hbad
                ·
                  exact fin15Anchored_clause07527 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07528 chi hbad
                ·
                  exact fin15Anchored_clause07529 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07530 chi hbad
                ·
                  exact fin15Anchored_clause07531 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07532 chi hbad
                ·
                  exact fin15Anchored_clause07533 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07534 chi hbad
                ·
                  exact fin15Anchored_clause07535 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07536 chi hbad
                ·
                  exact fin15Anchored_clause07537 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07538 chi hbad
                ·
                  exact fin15Anchored_clause07539 chi hbad
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
                  exact fin15Anchored_clause07540 chi hbad
                ·
                  exact fin15Anchored_clause07541 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07542 chi hbad
                ·
                  exact fin15Anchored_clause07543 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07544 chi hbad
                ·
                  exact fin15Anchored_clause07545 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07546 chi hbad
                ·
                  exact fin15Anchored_clause07547 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07548 chi hbad
                ·
                  exact fin15Anchored_clause07549 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07550 chi hbad
                ·
                  exact fin15Anchored_clause07551 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07552 chi hbad
                ·
                  exact fin15Anchored_clause07553 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07554 chi hbad
                ·
                  exact fin15Anchored_clause07555 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07556 chi hbad
                ·
                  exact fin15Anchored_clause07557 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07558 chi hbad
                ·
                  exact fin15Anchored_clause07559 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07560 chi hbad
                ·
                  exact fin15Anchored_clause07561 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07562 chi hbad
                ·
                  exact fin15Anchored_clause07563 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07564 chi hbad
                ·
                  exact fin15Anchored_clause07565 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07566 chi hbad
                ·
                  exact fin15Anchored_clause07567 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07568 chi hbad
                ·
                  exact fin15Anchored_clause07569 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07570 chi hbad
                ·
                  exact fin15Anchored_clause07571 chi hbad

end ErdosSzekeres

end
