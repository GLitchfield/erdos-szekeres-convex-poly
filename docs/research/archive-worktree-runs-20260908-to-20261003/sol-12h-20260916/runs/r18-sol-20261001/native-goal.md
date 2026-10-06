Run the single user-authorized Sol trial R18 in worktree
runs/worktrees/sol-12h-20260916. Read and follow
runs/r18-sol-20261001/RESEARCH-BRIEF.md and AGENTS.md. Target: C1r
(ErdosSzekeres.ctx_bound_child_run_contraction_one_level_root) through a root
normal form. Part 1: register ROOT-NF (a one-level root's bound equals that of
its normal-form word: same end markers, min(numRuns,2) runs of length 1; data
in the brief) with a falsifier, and a closed node deriving C1r from it; each on
its own branch from main with a targeted check and es node commit. Part 2:
prove ROOT-NF by strong induction on the number of children with ROOT-NF for
smaller roots as hypothesis. Parallel trials R16 (N_root) and R17 (X) work on
C1r's other route: do not touch their nodes; reuse their closed helpers. Time
heavy contexts before probes; never kill at a self-chosen time; review at
checkpoints. Use the primary es launcher with --root. Do not merge, push,
touch the primary checkout, edit existing statements, run a full extract, or
delegate. Log every finding with evidence; say Done/Stuck in PROGRESS.md. At
the end write MATHEMATICAL-HANDOFF.md and REPORT.sol.md there. Do not start
another trial.
