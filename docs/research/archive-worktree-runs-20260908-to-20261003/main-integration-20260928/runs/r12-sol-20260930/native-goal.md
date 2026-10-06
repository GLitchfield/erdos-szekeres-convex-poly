Run the single user-authorized Sol trial R12 in worktree
runs/worktrees/main-integration-20260928. Read and follow
runs/r12-sol-20260930/RESEARCH-BRIEF.md and AGENTS.md. Replace the sorry of
three existing nodes by proofs from the single-run chain, statements
unchanged, one branch each, in order:
ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end and
ErdosSzekeres.ctx_bound_additive_three_blocks (instances of
ctx_bound_additive_single_run), then
ErdosSzekeres.ctx_bound_uniform_separator_contraction (run contraction on a
part of a single-run context, via the closed bridge applied to the root
conjecture). Each check should show sorry only through that dependency.
Develop in guarded scratch compiles (never kill a compile at a self-chosen
time; review progress at checkpoints), check each node with a targeted
check, commit each with es node commit, and say so in PROGRESS.md (the
coordinator then ends the run early). Use the primary es launcher with
--root. Do not merge, push, touch the primary checkout, edit statements, run
a full extract, or delegate. Log every finding with evidence. At the end
write MATHEMATICAL-HANDOFF.md and REPORT.sol.md there. Do not start another
trial.
