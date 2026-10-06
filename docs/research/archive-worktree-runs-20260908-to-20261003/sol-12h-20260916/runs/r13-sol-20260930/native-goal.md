Run the single user-authorized Sol trial R13 in worktree
runs/worktrees/sol-12h-20260916. Read and follow
runs/r13-sol-20260930/RESEARCH-BRIEF.md and AGENTS.md. Target: the conjecture
ErdosSzekeres.ctx_bound_child_run_contraction_one_level_root (C1r), the only
open dependency of single-run additivity. Prove it with standard axioms, or
narrow it: register (es node add) a strictly narrower, falsifier-tested
exchange lemma X and a closed conditional node deriving C1r from X, and
compose C1r's module from them. The brief lists what is known, what is
refuted, and the P11 rescue data a value argument must reproduce. Develop in
guarded scratch compiles (never kill a compile or probe at a self-chosen
time; review progress at checkpoints), check each node with a targeted check,
commit each with es node commit on its own branch from main, and say so in
PROGRESS.md (the coordinator then ends the run early). Use the primary es
launcher with --root. Do not merge, push, touch the primary checkout, edit
existing statements, run a full extract, or delegate. Log every finding with
evidence. At the end write MATHEMATICAL-HANDOFF.md and REPORT.sol.md there.
Do not start another trial.
