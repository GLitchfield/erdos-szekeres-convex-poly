Run the single user-authorized Sol trial R11 in worktree
runs/worktrees/sol-12h-20260916. Read and follow
runs/r11-sol-20260930/RESEARCH-BRIEF.md and AGENTS.md. Prove, with standard
axioms only, two registered nodes in order, each on its own branch:
(1) ErdosSzekeres.ctx_bound_additive_single_run_alternating_of_part_contraction_and_deletion
on node/CtxBoundAdditiveSingleRunAlternatingOfPartContractionAndDeletion, then
(2) ErdosSzekeres.ctx_bound_additive_single_run_of_part_contraction_and_alternating
on node/CtxBoundAdditiveSingleRunOfPartContractionAndAlternating. Each is an
existing closed reduction (R9, R6) re-proved with run contraction assumed only
on parts of well-formed single-run contexts (hypothesis hpart): at every use
of the old hcontract, represent the context as such a part. Develop in
guarded scratch compiles (never kill a compile at a self-chosen time; review
progress at checkpoints), close each node with a targeted check, commit each
with es node commit on its branch, and say so in PROGRESS.md (the coordinator
then ends the run early). Use the primary es launcher with --root. Do not
merge, push, touch the primary checkout, edit other statements, run a full
extract, or delegate. Log every finding with evidence. At the end write
MATHEMATICAL-HANDOFF.md and REPORT.sol.md there. Do not start another trial.
