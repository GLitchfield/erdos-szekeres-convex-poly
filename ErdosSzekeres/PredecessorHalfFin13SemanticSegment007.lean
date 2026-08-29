module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk005
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk006

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 007. -/

theorem predecessorHalfFin13_rejectSemanticSegment007
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0390 chi) ∨
      ((PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0390 chi) ∨
      (PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0390 chi))) ∨
      ((PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0390 chi) ∨
      ((PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0034 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0390 chi) ∨
      (¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi) ∨
      ((¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0171 chi) ∨
      (¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi))) ∨
      ((PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0171 chi) ∨
      ((PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi) ∨
      (PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0171 chi))))) ∨
      ((((PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0171 chi) ∨
      ((¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0391 chi) ∨
      (¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0391 chi))) ∨
      ((¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0391 chi) ∨
      ((¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0391 chi) ∨
      (PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0391 chi)))) ∨
      (((PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      ¬PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0391 chi) ∨
      ((PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0391 chi) ∨
      (PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0027 chi ∧
      PredecessorHalfFin13Atom0035 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0391 chi))) ∨
      ((¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi) ∨
      ((¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi) ∨
      (¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0172 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi) ∨
      ((PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0172 chi) ∨
      (PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi))) ∨
      ((PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0172 chi) ∨
      ((PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0172 chi) ∨
      (¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0392 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0392 chi) ∨
      ((¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0392 chi) ∨
      (¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0392 chi))) ∨
      ((PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0392 chi) ∨
      ((PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0392 chi) ∨
      (PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0392 chi))))) ∨
      ((((PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      ¬PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0392 chi) ∨
      ((PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0392 chi) ∨
      (PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0028 chi ∧
      PredecessorHalfFin13Atom0036 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0392 chi))) ∨
      ((¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi) ∨
      ((¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi) ∨
      (¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0174 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi) ∨
      ((PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0174 chi) ∨
      (PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi))) ∨
      (((PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0174 chi) ∨
      (PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0174 chi)) ∨
      ((¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0394 chi) ∨
      (¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0394 chi))))))) ∨
      ((((((¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0394 chi) ∨
      ((¬PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0394 chi) ∨
      (¬PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0394 chi))) ∨
      ((PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0394 chi) ∨
      ((PredecessorHalfFin13Atom0022 chi ∧
      ¬PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0394 chi) ∨
      (PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      ¬PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0394 chi)))) ∨
      (((PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0394 chi) ∨
      ((PredecessorHalfFin13Atom0022 chi ∧
      PredecessorHalfFin13Atom0030 chi ∧
      PredecessorHalfFin13Atom0038 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0394 chi) ∨
      (¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi))) ∨
      ((¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi) ∨
      ((¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0175 chi) ∨
      (¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi))))) ∨
      ((((PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0175 chi) ∨
      ((PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi) ∨
      (PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0175 chi))) ∨
      ((PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0175 chi) ∨
      ((¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0395 chi) ∨
      (¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0395 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0395 chi) ∨
      ((¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0395 chi) ∨
      (¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0395 chi))) ∨
      (((¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0395 chi) ∨
      (¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0395 chi)) ∨
      ((PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0395 chi) ∨
      (PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0395 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0395 chi) ∨
      ((PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      ¬PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0395 chi) ∨
      (PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0039 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0395 chi))) ∨
      ((PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0024 chi ∧
      PredecessorHalfFin13Atom0039 chi ∧
      PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0395 chi) ∨
      ((¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi) ∨
      (¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0176 chi) ∨
      ((¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi) ∨
      (PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0176 chi))) ∨
      ((PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi) ∨
      ((PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0176 chi) ∨
      (PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0176 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0396 chi) ∨
      ((¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0396 chi) ∨
      (¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0396 chi))) ∨
      ((¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0396 chi) ∨
      ((PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0396 chi) ∨
      (PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0396 chi)))) ∨
      (((PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      ¬PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0396 chi) ∨
      ((PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0040 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0396 chi) ∨
      (PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0025 chi ∧
      PredecessorHalfFin13Atom0040 chi ∧
      PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0396 chi))) ∨
      (((¬PredecessorHalfFin13Atom0023 chi ∧
      ¬PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi) ∨
      (¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi)) ∨
      ((¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      ¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0177 chi) ∨
      (¬PredecessorHalfFin13Atom0023 chi ∧
      PredecessorHalfFin13Atom0026 chi ∧
      PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi))))))))) := by
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
              exact predecessorHalfFin13_clause02491 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02492 chi hbad
              ·
                exact predecessorHalfFin13_clause02493 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02495 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02496 chi hbad
              ·
                exact predecessorHalfFin13_clause02497 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02498 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02499 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02500 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02501 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02502 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02503 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02504 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02505 chi hbad
              ·
                exact predecessorHalfFin13_clause02506 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02508 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02512 chi hbad
              ·
                exact predecessorHalfFin13_clause02513 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02517 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02519 chi hbad
              ·
                exact predecessorHalfFin13_clause02520 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02521 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02522 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02523 chi hone hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02524 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02525 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02526 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02527 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02528 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02529 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02530 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02532 chi hbad
              ·
                exact predecessorHalfFin13_clause02536 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02537 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02539 chi hbad
              ·
                exact predecessorHalfFin13_clause02540 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02541 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02543 chi hbad
              ·
                exact predecessorHalfFin13_clause02544 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02569 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02570 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02571 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02572 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02573 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02574 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02575 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02576 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02577 chi hbad
              ·
                exact predecessorHalfFin13_clause02578 chi hbad
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
              exact predecessorHalfFin13_clause02579 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02580 chi hbad
              ·
                exact predecessorHalfFin13_clause02584 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02585 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02588 chi hbad
              ·
                exact predecessorHalfFin13_clause02589 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02591 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02592 chi hbad
              ·
                exact predecessorHalfFin13_clause02593 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02594 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02595 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02596 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02597 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02598 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02599 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02600 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02601 chi hbad
              ·
                exact predecessorHalfFin13_clause02602 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02603 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02604 chi hbad
              ·
                exact predecessorHalfFin13_clause02605 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02607 chi hbad
              ·
                exact predecessorHalfFin13_clause02608 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02609 chi hbad
              ·
                exact predecessorHalfFin13_clause02611 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02613 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02614 chi hbad
              ·
                exact predecessorHalfFin13_clause02615 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02616 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02617 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02618 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02619 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02620 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02621 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02622 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02623 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02624 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02625 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02626 chi hbad
              ·
                exact predecessorHalfFin13_clause02628 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02632 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02633 chi hbad
              ·
                exact predecessorHalfFin13_clause02635 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause02637 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02639 chi hbad
              ·
                exact predecessorHalfFin13_clause02640 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02641 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02642 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause02643 chi hone hbad
              ·
                exact predecessorHalfFin13_clause02644 chi hone hbad

end ErdosSzekeres

end
