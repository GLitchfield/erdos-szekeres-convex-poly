R22 (approved by Gavin 2026-10-02; coordinator claude-code:f3e0818a-9388-430b-9c32-aeb7dc5d297b (resumed from 22c8132f)).

Read and follow runs/r22-sol-20261002/RESEARCH-BRIEF.md, the reviewed instruction file, in full before acting. Also
read AGENTS.md and runs/r22-sol-20261002/AUDITED-PROOF-5k1k.md and AUDITED-PROOF-5kk.md, the audited paper
proofs.

Goals, in priority order:

1. Register and prove `singletonLowerPascalTailGate_five_pred_of_six_le : 6 <= k -> SingletonLowerPascalTailGate 5 (k-1) k`,
   following the audited proof (Lemmas 1-6 and the 11-case root-split analysis).
2. Register and prove the (5,k,k) gate from AUDITED-PROOF-5kk.md, with the R20 cupblock lemma and R21 Baek bound as
   explicit hypotheses (see the brief).
3. If time allows, derive the colour-dual upper gates.

Keep PROGRESS.md in runs/r22-sol-20261002/ current, and write MATHEMATICAL-HANDOFF.md there before the deadline. Do
not touch R19's worktree, and preserve R21's branches in this worktree.
