# R21: Theorem 8 for every diagonal a=4 state, (4,k,k) for all k (one Sol trial, gpt-6.1-sol)

**Approval and roles.** Approved by Gavin on 2026-10-02 ("kk go ahead", on the proposal to port Baek's single-set
theorem and assemble the uniform (4,k,k) state).
- Coordinator: `claude-code:22c8132f-fa67-40ab-90d0-f8255f87797f` (Claude).
- Callbacks are not verified, so never wait for replies; keep `PROGRESS.md` here current.
- This is one trial. Never reset the host deadline.

**Worktree and parallel runs.**
- Fresh worktree `runs/worktrees/sol-12h-20261002`, branch `research/r21-etv-port-20261002`, from main `6e4d0e66`.
  Its `.lake/packages` is symlinked to the main checkout.
- `.lake/build` starts empty, so the first check of a module that imports project files materializes them.
  Certificate outputs come from the shared Lake artifact cache (`[build.artifact_cache]`); other modules compile.
  Work Mathlib-only first (phase 1) to keep that cost late and small.
- Running in parallel, do not touch:
  - R19: `runs/worktrees/sol-12h-20260916`, until 2026-10-03T00:25Z;
  - R20: `runs/worktrees/sol-12h-20260913`, until 2026-10-03T04:57Z.
- Two build slots are shared; keep memory caps modest.

## Background

- **The uniform a=4 gate is closed.** R20 closed two theorems on independent branches from `6e4d0e66`:
  - `diagonalCupBlocksForce4kk_of_five_le` (commit `c89df0e8`, branch `node/DiagonalCupBlocksForce4kkOfFiveLe`);
  - `singletonLowerPascalTailGate_four_diagonal_of_five_le : 5 ≤ k → SingletonLowerPascalTailGate 4 k k`
    (commit `82a57072`).

  They are not yet on main; the coordinator integrates them after review. Do NOT cherry-pick them yourself. State
  your assembly theorem with the gate as a HYPOTHESIS; the coordinator instantiates it after integration.
- **The missing single-set input is (S)**: a 4-cap-free set with no strong k-set (k-cups are strong) has at most
  1 + C(k-1,2) = T(4,k,k) points.
  - It is exactly Baek's Theorem 2.7 (J. Baek, *On the Erdős–Tuza–Valtr conjecture*, Eur. J. Combin. 124 (2025)
    104085, arXiv:2206.04260).
  - It holds for arbitrary "configurations" (triple 2-colourings, with cups/caps by consecutive triples), so in
    particular for OneChange colourings.
  - Baek's Apache-2.0 Lean 4 formalization (Lean v4.13.0-rc3, about 2300 lines, Mathlib only) is copied here as
    `baek-erdos-tuza-valtr-a5ad53e/`. Main theorem `main` in `ErdosTuzaValtr/Main/Main.lean`:
    `C(n+2,2)+2 ≤ |S| → HasNCap 4 S ∨ HasNGon (n+3) S`.
  - The project has only finite instances, e.g. `containsCupSeven_of_oneChange_no_capFour_card_ge_twentyTwo`.
- **Assembly template:** `ErdosSzekeres/StructuralChargingResidualWindow488.lean`, i.e. `decomposableStateUpper_488`
  and `criticalRootImpossible_488_of_predecessors`. It uses:
  - the Pascal-tail shell (`criticalRootImpossible_of_predecessors_pascal_tail_gates`, or the 488-specific route);
  - published slices;
  - the classical regime for predecessors (`containsCapSet_or_containsCupSet_of_choose_lt` with
    `IsDecomposable.isSweepRealizable`);
  - (S) in the "upper child is a singleton" case.

  At (4,k,k) the upper Pascal tail has width C(k-3,k-2) = 0, so the upper-tail case is impossible. Handle it
  arithmetically; do not assume an upper gate.

## Work items, in priority order

**1. Port (S) (phase 1, Mathlib only).** Port Baek's development to the project toolchain (Lean 4.29.1 and current
Mathlib).
- Keep Apache-2.0 attribution: put a header comment in every ported file naming J. Baek, the source repository
  `jcpaik/erdos-tuza-valtr` at commit a5ad53e, and the Apache License 2.0.
- Follow project rules: new global statements only via `es node add`. Helper lemmas may live inside node modules,
  or in clearly scoped helper modules if the harness allows. Read AGENTS.md and existing practice (R20 kept its
  helpers local), and ask the harness (`es search`, `es context`) before choosing.
- The registered node (kind formalization) should state (S) in the PROJECT's language: `TripleColoring`,
  `OneChangeOn` (or no hypothesis, since Baek needs none), `ContainsCapSet`, `ContainsStrongPolygonSet`, `Finset`
  card. The suggested form: for k >= 3, no 4-cap and no strong k-set imply card ≤ 1 + C(k-1,2).
- Bridge from Baek's `Config`/`Gon` to `IsStrongPolygonSet`. A cap and a cup sharing both endpoints is strong under
  OneChangeOn; R20 proved a related cup-plus-apex lemma locally, so search first.

**2. Uniform state (phase 2).**

    theorem decomposableStateUpper_four_diagonal_of_gates
      (hgate : ∀ k, 5 ≤ k → SingletonLowerPascalTailGate 4 k k) :
      ∀ k, 5 ≤ k → DecomposableStateUpper 4 k k

Add its colour dual (k,4,k) via `decomposableStateUpper_comm` if cheap.

**Done:** both closed with original-source receipts (standard axioms, no sorry, no certificates and no
`native_decide` beyond what existing imports already contain), or the exact blocking lemma logged.

## Constraints
- `es job run` for anything over a minute; no self-chosen timeouts.
- `es log` every finding and every meaningful compiler failure.
- New statements only via `es node add`; one node per branch; no merge or push.
- Your sandbox cannot write `.git-data`: commit through the guarded es job path, as R17–R20 did.
- Do not modify `/home/gavin/git/erdos-tuza-valtr` (the original clone).
- Write `MATHEMATICAL-HANDOFF.md` here before the deadline.
