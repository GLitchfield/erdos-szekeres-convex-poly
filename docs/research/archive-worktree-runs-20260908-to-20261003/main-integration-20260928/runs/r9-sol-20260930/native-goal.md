Run the single user-authorized Sol trial R9 in worktree
runs/worktrees/main-integration-20260928 on branch
node/CtxBoundAdditiveSingleRunAlternatingOfRunContractionAndDeletion. Read and
follow runs/r9-sol-20260930/RESEARCH-BRIEF.md and AGENTS.md. Prove, with
standard axioms only, the registered node
ErdosSzekeres.ctx_bound_additive_single_run_alternating_of_run_contraction_and_deletion:
alternating single-run additivity (C3) from the explicit hypotheses C1 (run
contraction under level-one spans) and DelMono (external-letter deletion
monotonicity for isolated children), by induction on the run length with the
closed prefix/suffix (n=2) and singleton-ended sandwich (n=3) bases and the
delete-separator-then-contract step for n>=4. Reuse R6's glue machinery.
Develop in guarded scratch compiles (never kill a compile at a self-chosen
time; review progress at checkpoints), close the node with a targeted check,
and commit with es node commit. Use the primary es launcher with --root. Do
not merge, push, touch the primary checkout, edit other statements, run a
full extract, or delegate. Log every finding with evidence. At the end write
MATHEMATICAL-HANDOFF.md and REPORT.sol.md there. Do not start another trial.
