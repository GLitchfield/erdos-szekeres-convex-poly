import ESBlueprint.B.CtxBoundLeIffAllIntervalCutsLe

set_option maxHeartbeats 20000000
set_option maxRecDepth 10000

namespace ErdosSzekeres

/-- Exact finite R19 k6 middle-child example: SSS1L3L2LS at(5,5,6), maxima111, has full bound8; middle child1 upper3 attains it with remainder6, and every legal singleton choice at any other child has sum at most7. This certifies middle-child uniqueness, including failure of all run ends, rather than only the global first/last. Reuse the closed interval-cut upper certificate to check all72 cuts and avoid full parent reduction. The same literal context is separately certified satisfied; actual external-history realization and uniqueness of side/coupling are outside scope.
@node
@ws B
@kind formalization
@dangling-ok Completes R19 k6 middle-of-run explanation and replaces diagnostic exact maximum/child uniqueness with a kernel-certified finite theorem. -/
theorem ctx_k6_unique_middle_singleton_attainment : let σ : Ctx.Context :=
    ⟨5, 5, 6,
      [Ctx.Letter.child, Ctx.Letter.child, Ctx.Letter.child,
       Ctx.Letter.ext 1 Ctx.Side.lower, Ctx.Letter.ext 3 Ctx.Side.lower,
       Ctx.Letter.ext 2 Ctx.Side.lower, Ctx.Letter.child], [1, 1, 1]⟩
  σ.bound = 8 ∧
  (σ.part [1] Ctx.Side.upper 3).bound +
    (σ.part [0, 2, 6] Ctx.Side.lower 2).bound = σ.bound ∧
  (σ.part [0, 2, 6] Ctx.Side.lower 2).bound = 6 ∧
  (∀ (p : ℕ), p ∈ σ.childPositions → p ≠ 1 → ∀ d : ℕ,
    1 ≤ d → d ≤ σ.k - 2 →
    (σ.part [p] Ctx.Side.lower d).bound +
      (σ.part (σ.childPositions.filter (fun q => q ≠ p))
        Ctx.Side.upper (σ.k - 1 - d)).bound ≤ 7 ∧
    (σ.part [p] Ctx.Side.upper (σ.k - 1 - d)).bound +
      (σ.part (σ.childPositions.filter (fun q => q ≠ p))
        Ctx.Side.lower d).bound ≤ 7) := by
  classical
  let σ : Ctx.Context :=
    ⟨5, 5, 6,
      [Ctx.Letter.child, Ctx.Letter.child, Ctx.Letter.child,
       Ctx.Letter.ext 1 Ctx.Side.lower, Ctx.Letter.ext 3 Ctx.Side.lower,
       Ctx.Letter.ext 2 Ctx.Side.lower, Ctx.Letter.child], [1, 1, 1]⟩
  change σ.bound = 8 ∧ _
  let cuts (block : List ℕ) (d : ℕ) : ℕ × ℕ :=
    ((σ.part block Ctx.Side.lower d).bound +
      (σ.part (σ.childPositions.filter (fun p => p ∉ block))
        Ctx.Side.upper (σ.k - 1 - d)).bound,
     (σ.part block Ctx.Side.upper (σ.k - 1 - d)).bound +
      (σ.part (σ.childPositions.filter (fun p => p ∉ block))
        Ctx.Side.lower d).bound)
  run_tac liftM <| (show IO Unit from do
    let out ← IO.getStdout
    out.putStrLn s!"K6 exact cuts 0/7 certificates; monotonic_ms={← IO.monoMsNow}"
    out.flush)
  have h0 (d : ℕ) (hd1 : 1 ≤ d) (hd4 : d ≤ 4) :
      (cuts [0] d).1 ≤ 7 ∧ (cuts [0] d).2 ≤ 7 := by
    interval_cases d <;> constructor <;> decide +kernel
  run_tac liftM <| (show IO Unit from do
    let out ← IO.getStdout
    out.putStrLn s!"K6 exact cuts 1/7 certificates; monotonic_ms={← IO.monoMsNow}"
    out.flush)
  have h1 (d : ℕ) (hd1 : 1 ≤ d) (hd4 : d ≤ 4) :
      (cuts [1] d).1 ≤ 8 ∧ (cuts [1] d).2 ≤ 8 := by
    interval_cases d <;> constructor <;> decide +kernel
  run_tac liftM <| (show IO Unit from do
    let out ← IO.getStdout
    out.putStrLn s!"K6 exact cuts 2/7 certificates; monotonic_ms={← IO.monoMsNow}"
    out.flush)
  have h2 (d : ℕ) (hd1 : 1 ≤ d) (hd4 : d ≤ 4) :
      (cuts [2] d).1 ≤ 7 ∧ (cuts [2] d).2 ≤ 7 := by
    interval_cases d <;> constructor <;> decide +kernel
  run_tac liftM <| (show IO Unit from do
    let out ← IO.getStdout
    out.putStrLn s!"K6 exact cuts 3/7 certificates; monotonic_ms={← IO.monoMsNow}"
    out.flush)
  have h6 (d : ℕ) (hd1 : 1 ≤ d) (hd4 : d ≤ 4) :
      (cuts [6] d).1 ≤ 7 ∧ (cuts [6] d).2 ≤ 7 := by
    interval_cases d <;> constructor <;> decide +kernel
  run_tac liftM <| (show IO Unit from do
    let out ← IO.getStdout
    out.putStrLn s!"K6 exact cuts 4/7 certificates; monotonic_ms={← IO.monoMsNow}"
    out.flush)
  have h01 (d : ℕ) (hd1 : 1 ≤ d) (hd4 : d ≤ 4) :
      (cuts [0, 1] d).1 ≤ 8 ∧ (cuts [0, 1] d).2 ≤ 8 := by
    interval_cases d <;> constructor <;> decide +kernel
  run_tac liftM <| (show IO Unit from do
    let out ← IO.getStdout
    out.putStrLn s!"K6 exact cuts 5/7 certificates; monotonic_ms={← IO.monoMsNow}"
    out.flush)
  have h12 (d : ℕ) (hd1 : 1 ≤ d) (hd4 : d ≤ 4) :
      (cuts [1, 2] d).1 ≤ 8 ∧ (cuts [1, 2] d).2 ≤ 8 := by
    interval_cases d <;> constructor <;> decide +kernel
  run_tac liftM <| (show IO Unit from do
    let out ← IO.getStdout
    out.putStrLn s!"K6 exact cuts 6/7 certificates; monotonic_ms={← IO.monoMsNow}"
    out.flush)
  have h26 (d : ℕ) (hd1 : 1 ≤ d) (hd4 : d ≤ 4) :
      (cuts [2, 6] d).1 ≤ 8 ∧ (cuts [2, 6] d).2 ≤ 8 := by
    interval_cases d <;> constructor <;> decide +kernel
  run_tac liftM <| (show IO Unit from do
    let out ← IO.getStdout
    out.putStrLn s!"K6 exact cuts 7/7 certificates; monotonic_ms={← IO.monoMsNow}"
    out.flush)
  have hpositions : σ.childPositions = [0, 1, 2, 6] := by decide +kernel
  have hblocks : σ.blocks =
      [[0], [0, 1], [0, 1, 2], [1], [1, 2], [1, 2, 6], [2], [2, 6], [6]] := by
    decide +kernel
  have hruns : 2 ≤ σ.numRuns := by decide +kernel
  have hupper : σ.bound ≤ 8 := by
    apply (ctx_bound_le_iff_all_interval_cuts_le σ hruns 8).2
    intro block hb d hd1 hdk
    have hd4 : d ≤ 4 := hdk
    change (cuts block d).1 ≤ 8 ∧ (cuts block d).2 ≤ 8
    rw [hblocks] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨hl, hu⟩ := h0 d hd1 hd4
      exact ⟨by omega, by omega⟩
    · exact h01 d hd1 hd4
    · obtain ⟨hl, hu⟩ := h6 d hd1 hd4
      change (σ.part [6] Ctx.Side.lower d).bound +
        (σ.part [0, 1, 2] Ctx.Side.upper (σ.k - 1 - d)).bound ≤ 7 at hl
      change (σ.part [6] Ctx.Side.upper (σ.k - 1 - d)).bound +
        (σ.part [0, 1, 2] Ctx.Side.lower d).bound ≤ 7 at hu
      change (σ.part [0, 1, 2] Ctx.Side.lower d).bound +
        (σ.part [6] Ctx.Side.upper (σ.k - 1 - d)).bound ≤ 8 ∧
        (σ.part [0, 1, 2] Ctx.Side.upper (σ.k - 1 - d)).bound +
        (σ.part [6] Ctx.Side.lower d).bound ≤ 8
      constructor <;> omega
    · exact h1 d hd1 hd4
    · exact h12 d hd1 hd4
    · obtain ⟨hl, hu⟩ := h0 d hd1 hd4
      change (σ.part [0] Ctx.Side.lower d).bound +
        (σ.part [1, 2, 6] Ctx.Side.upper (σ.k - 1 - d)).bound ≤ 7 at hl
      change (σ.part [0] Ctx.Side.upper (σ.k - 1 - d)).bound +
        (σ.part [1, 2, 6] Ctx.Side.lower d).bound ≤ 7 at hu
      change (σ.part [1, 2, 6] Ctx.Side.lower d).bound +
        (σ.part [0] Ctx.Side.upper (σ.k - 1 - d)).bound ≤ 8 ∧
        (σ.part [1, 2, 6] Ctx.Side.upper (σ.k - 1 - d)).bound +
        (σ.part [0] Ctx.Side.lower d).bound ≤ 8
      constructor <;> omega
    · obtain ⟨hl, hu⟩ := h2 d hd1 hd4
      exact ⟨by omega, by omega⟩
    · exact h26 d hd1 hd4
    · obtain ⟨hl, hu⟩ := h6 d hd1 hd4
      exact ⟨by omega, by omega⟩
  have hleaf : (σ.part [1] Ctx.Side.upper 3).bound = 2 := by decide +kernel
  have hmiddle : (σ.part [0, 2, 6] Ctx.Side.lower 2).bound = 6 := by
    have hupperMiddle := (h1 2 (by decide) (by decide)).2
    change (σ.part [1] Ctx.Side.upper 3).bound +
      (σ.part [0, 2, 6] Ctx.Side.lower 2).bound ≤ 8 at hupperMiddle
    rw [hleaf] at hupperMiddle
    let γ := σ.part [0, 2, 6] Ctx.Side.lower 2
    let ρ := γ.part (γ.childPositions.filter (fun p => p ∉ [6])) Ctx.Side.upper 2
    have hρ : 2 ≤ ρ.bound := by
      have hle := (ctx_bound_cut_le ρ (by decide +kernel) [0] (by decide +kernel) 1
        (by decide) (by decide)).1
      have hvalue :
          (ρ.part [0] Ctx.Side.lower 1).bound +
            (ρ.part (ρ.childPositions.filter (fun p => p ∉ [0])) Ctx.Side.upper
              (ρ.k - 1 - 1)).bound = 2 := by decide +kernel
      rw [hvalue] at hle
      exact hle
    have hγ : 6 ≤ γ.bound := by
      have hle := (ctx_bound_cut_le γ (by decide +kernel) [6] (by decide +kernel) 3
        (by decide) (by decide)).1
      have hlast : (γ.part [6] Ctx.Side.lower 3).bound = 4 := by decide +kernel
      change (γ.part [6] Ctx.Side.lower 3).bound + ρ.bound ≤ γ.bound at hle
      rw [hlast] at hle
      exact (Nat.add_le_add_left hρ 4).trans hle
    exact Nat.le_antisymm (by omega) hγ
  have hlower : 8 ≤ σ.bound := by
    have hcut := (ctx_bound_cut_le σ hruns [1] (by rw [hblocks]; simp) 2
      (by decide) (by decide)).2
    change (σ.part [1] Ctx.Side.upper 3).bound +
      (σ.part [0, 2, 6] Ctx.Side.lower 2).bound ≤ σ.bound at hcut
    rw [hleaf, hmiddle] at hcut
    exact hcut
  have hexact : σ.bound = 8 := Nat.le_antisymm hupper hlower
  refine ⟨hexact, ?_, hmiddle, ?_⟩
  · rw [hleaf, hmiddle, hexact]
  · intro p hp hp1 d hd1 hdk
    have hd4 : d ≤ 4 := hdk
    rw [hpositions] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact h0 d hd1 hd4
    · exact (hp1 rfl).elim
    · exact h2 d hd1 hd4
    · exact h6 d hd1 hd4

end ErdosSzekeres
