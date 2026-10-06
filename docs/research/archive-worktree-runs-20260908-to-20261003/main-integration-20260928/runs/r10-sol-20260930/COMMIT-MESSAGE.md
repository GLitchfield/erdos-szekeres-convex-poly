Prove single-run part contraction from the one-level root hypothesis

Close ErdosSzekeres.ctx_bound_part_run_contraction_of_one_level_root without
changing its registered statement or docstring. Normalize the part and its
contracted descendant, identify run capacities under deletion of a kept
child, and remove inert exterior letters by equality at every fuel before
applying the explicit root-contraction hypothesis hroot.

Search before proving: es search ctx_single_run_descendant located the
closed descendant bound/limit normalizations; es search ctx_point_limits_eq
located the closed point-limit equality along child intervals. Searches for
boundFuel congr, inert endpoint deletion, point limits child deletion, and
single run word reconstruction found no standalone registered replacement.
Reuse the local coordinate/fold/part transports from R8 and run reconstruction
from R9. es lib search/show workflow.proof and workflow.jobs supplied the
capture and guarded-job workflows; no new workflow code was added.

Validation: full exact-statement scratch compile 20260930-114807-1296db
(rc 0, 19.9 s, 682 MiB). Targeted es check job 20260930-115406-87ab9e
(rc 0, 114.9 s, 2353 MiB) reports status closed, sorry false, and only
propext, Classical.choice, Quot.sound. Receipt:
1de650ee0589affa54d452e27dea92de8232cb6e90707dc829ef09e76276b046.
git diff --check is clean. No full extraction was run.

R10 artifacts and mathematical account:
runs/r10-sol-20260930/MATHEMATICAL-HANDOFF.md
runs/r10-sol-20260930/REPORT.sol.md

hroot remains an explicit premise; this commit proves the bridge only.
