R21 (approved by Gavin 2026-10-02; coordinator claude-code:22c8132f-fa67-40ab-90d0-f8255f87797f).

Read and follow runs/r21-sol-20261002/RESEARCH-BRIEF.md, the reviewed instruction file, in full before acting. Also
read AGENTS.md.

Goals, in priority order:

1. Port Baek's Erdős–Tuza–Valtr (n,4,n) theorem (copied in runs/r21-sol-20261002/baek-erdos-tuza-valtr-a5ad53e/,
   Apache-2.0, Lean 4.13) to the project toolchain, with attribution. Register and prove the single-set bound in
   the project's language: a 4-cap-free set with no strong k-set has at most 1 + C(k-1,2) points.
2. Register and prove `decomposableStateUpper_four_diagonal_of_gates`. It takes the (4,k,k) singleton lower
   Pascal-tail gates as a hypothesis (R20 closed them on a branch not yet on main) and concludes
   `DecomposableStateUpper 4 k k` for all k >= 5. Use `StructuralChargingResidualWindow488.lean` as the template.

Keep PROGRESS.md in runs/r21-sol-20261002/ current, and write MATHEMATICAL-HANDOFF.md there before the deadline. Do
not touch R19's or R20's worktrees, branches or nodes.
