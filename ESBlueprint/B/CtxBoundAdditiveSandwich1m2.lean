import ESBlueprint.B.CtxSandwichMiddleBlockContraction
import ESBlueprint.B.CtxBoundAdditiveSandwich112

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- Uniform sandwich additivity with outer block lengths one and two and an arbitrary positive middle length. Both orientations, arbitrary well-formed external context, and every admissible coupling. Follows from the checked four-position (1,1,2) case by exact middle-block contraction.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_bound_additive_sandwich_1m2 (σ : Ctx.Context) (hwf : σ.WellFormed) (b m : ℕ)
  (hpos : σ.childPositions = List.range' b (m + 3)) (hm : 0 < m)
  (d : ℕ) (hd : 1 ≤ d) (hdk : d ≤ σ.k - 2) :
  (σ.part (List.range' b 1 ++ List.range' (b + 1 + m) 2) Ctx.Side.lower d).bound +
      (σ.part (List.range' (b + 1) m) Ctx.Side.upper (σ.k - 1 - d)).bound ≤ σ.bound ∧
  (σ.part (List.range' b 1 ++ List.range' (b + 1 + m) 2) Ctx.Side.upper (σ.k - 1 - d)).bound +
      (σ.part (List.range' (b + 1) m) Ctx.Side.lower d).bound ≤ σ.bound := by
  have hlen : 1 + m + 2 = m + 3 := by omega
  have hpos' : σ.childPositions = List.range' b (1 + m + 2) := by rw [hlen]; exact hpos
  obtain ⟨hW, hCP, hB, hParts⟩ :=
    ctx_sandwich_middle_block_contraction σ hwf b 1 m 2 hpos' (by decide) hm (by decide)
  have hmain := ctx_bound_additive_sandwich_112 _ hW b hCP d hd hdk
  have hL := hParts Ctx.Side.lower d hd hdk
  have hU := hParts Ctx.Side.upper (σ.k - 1 - d) (by omega) (by omega)
  have houter : List.range' b 1 ++ List.range' (b + 1 + 1) 2 = [b, b + 2, b + 3] := by
    simp [List.range'_succ, Nat.add_assoc]
  constructor
  · rw [hB, hL.1, hU.2, houter]
    exact hmain.1
  · rw [hB, hU.1, hL.2, houter]
    exact hmain.2

end ErdosSzekeres
