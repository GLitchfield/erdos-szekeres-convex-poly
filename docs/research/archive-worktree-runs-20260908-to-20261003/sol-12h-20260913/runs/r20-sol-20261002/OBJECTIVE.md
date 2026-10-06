R20 (approved by Gavin 2026-10-02; coordinator claude-code:22c8132f-fa67-40ab-90d0-f8255f87797f).

Read and follow runs/r20-sol-20261002/RESEARCH-BRIEF.md, the reviewed instruction file, in full before acting. Also
read AGENTS.md, runs/r20-sol-20261002/CUPBLOCK-PROOF.md (the verified hand proof) and
runs/r20-sol-20261002/FORMALIZATION-PLAN.md.

Goals, in priority order:

1. Register and prove `diagonalCupBlocksForce4kk_of_five_le : 5 <= k -> DiagonalCupBlocksForce4kk k`, the uniform
   two-cup-block lemma. Route: a card bound by induction on k, general signotope helpers H1–H3, Claim D, deletion
   of D = {2nd point of the left cup, 2nd-to-last point of the right cup}. Then derive the (4,k,k) singleton
   Pascal-tail gate for all k >= 5.
2. Formalize reusable tools for the open a >= 5 cases: the strong-set shape lemma under no (j+1)-cap, the cup
   layer lemma, and the cup-extension moves. Record any a = 5 proof idea in PROGRESS.md first. No narrowing without
   a stated proof idea.

Keep PROGRESS.md in runs/r20-sol-20261002/ current, and write MATHEMATICAL-HANDOFF.md there before the deadline.
Do not touch R19's worktree, branches or nodes.
