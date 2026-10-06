R23 (approved by Gavin 2026-10-02; coordinator claude-code:f3e0818a-9388-430b-9c32-aeb7dc5d297b).

Read and follow runs/r23-sol-20261003/RESEARCH-BRIEF.md, the reviewed instruction file, in full before acting. Also
read AGENTS.md and runs/r23-sol-20261003/AUDITED-PROOF-6k2k.md, the audited paper proof.

Goals, in priority order:

1. Register and prove `singletonLowerPascalTailGate_six_pred_pred_of_seven_le : 7 <= k -> SingletonLowerPascalTailGate 6 (k-2) k`,
   following the audited proof (basic facts, Z-lemmas via one generic peel lemma, marker Lemmas 7-9, R_3 and R2-6,
   then the 13-row root-split analysis). If the gate does not close, close the lemma layer as separate nodes and
   log the exact remaining rows.
2. If time allows, derive the colour-dual upper gate.

Keep PROGRESS.md in runs/r23-sol-20261003/ current, and write MATHEMATICAL-HANDOFF.md there before the deadline.
Preserve R21's and R22's branches in this worktree.
