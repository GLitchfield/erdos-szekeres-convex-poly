# R16 Sol self-review: neither-marked opposite-three selector

Review window window-f8cf11c6d0c34b4b; research window window-bd8228675abb4748 ended with one
accepted checked result. Host permits only Sol/xhigh; this is Sol self-review,
not independent Astra review. No delegation.

Accepted scope: k>=3, marker global G>=3<=k, opposite global exactly3,
old maximum m in1..k-2, uniform word with actual old marker, child at both ends,
at least2runs, either marker side. First global child cut opposite maximum k-2,
selected complement maximum1. Registered type3b3e5de88d9d3684 is unchanged.
Full N_ends/N_root, larger opposite globals and global-two cases remain open.

Construction reviewed:
- Reused accepted14 exact geometry, Pascal, both-marked lower and unrestricted
  exposed-first lower as local proofs on approved5847 independent branch.
- Genericized exposed lower over legal H/M and rootWF over legal M.
  Reflection uses closed ctx_bound_reverse only after establishing WellFormed;
  H=min(G,k-m)=2 never invokes reflection of a possibly illegal m+1 root.
- Actual old-marker position replaces last-marker witness for the exposed
  first point and singleton. All old markers are after first position0.
- Complementary prefix merge retains G and changes maximum to m+1.
  Last child survives because a nonempty remaining child list forces lastposition>0;
  original lastchild belongs to ps and is unchanged by part/merge.
- Reused accepted16 raw absorbed-marker upper as a local proof. Source<=H-1,
  first leaf=1, complement>=H-2 when H>=3; H2 uses nonnegativity only.
- Original raw singleton threshold and non-p filter restored explicitly.
  Accepted3b3e5de88d9d3684 statement is byte-preserved in all versions.

Guarded check20261001-082439-9c20aa:
62.739049434661865s,2984MiB,4G; receipt
a6e6966856ae4c4a800935d860ad849bffeffc3953b0d207f8e617cb81c63514.
Closed, lock_oktrue, sorryfalse, blocked_by[], nonstandard_axioms[],
uncovered_axioms[]; axioms propext/Classical.choice/Quot.sound.
393 actual dependencies, no open N_ends/N_root/X constants.
Proof fixture3b68a98b3c9c39e32978060bc656f8813b2b2697601fee4e70d2e3f7018b943f.
Frozen accepted source Neither-opposite-three.closed.lean SHA
a44c8f8825617089ac3b578b5136ee1a6e720f32953a34b5e663193c2d355535.

Failures preserved and logged before each repair:
- v1/check082032-922bec missing namespace open;8.176701s696MiB.
- v2/check082132-759619 redundantrfl, generated dependent side matcher,
  finalcons-filter/kprojection rewrites;71.666802s2633MiB.
- v3 changes only these local repairs. No mathematical target refutation.
Frozen failed sources/CHECK/BUILD files retained.

Code/maintenance review: new/changed tracked code is one registered Lean proof
and generated node registry/import/lock/status files. No Python/C/workflow
algorithm or shared harness script changed for this theorem. Inline journal
commands are primary es launcher, guarded node registration/branch/check/commit,
short source freeze/hash and metadata inspection; no guard bypass. Existing
neither-marked diagnostic caller remains source-pinned and separately reviewed.
Reuse accepted helpers; defer cross-branch helper export/integration because
user forbids merge/cherry-pick/primary edits and requires independent node branches.
No generic algorithm promotion is warranted by this proof-only work.
