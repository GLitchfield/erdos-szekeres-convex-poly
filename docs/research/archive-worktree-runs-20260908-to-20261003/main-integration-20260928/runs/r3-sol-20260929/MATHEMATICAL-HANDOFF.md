# R3 mathematical handoff

Mathematical result consolidated 2026-09-30T06:09Z. Reflection is registered
and Lean-certified closed; the requested commit is blocked by read-only Git
metadata. The fixed native-goal deadline remains in force.
Agent `codex:agent-run-05b62a652ed044f8`, native thread
`01a0ef82-4628-70e3-b639-20c97e4857b6`, host `20260929-193122-598d60`.
Worktree `runs/worktrees/main-integration-20260928`, branch
`node/CtxBoundReverse`, base `5d58845b64c80c52f843290e31fa573398ebdd9f`.
One Sol/xhigh trial, no delegation. Deadline 2026-09-30T09:31:28.094139Z;
consolidation begins 09:01:28Z. Do not reset either deadline.

## Part A: park the endpoint chain

Verdict **Fail**, claim released `blocked`. The mathematical account, exact
source admissions, predicate definitions, witness cuts, domain restrictions and
next-action recommendation are in [K6-GATE.md](K6-GATE.md).
The target source and both admissions at lines 3605/4024 are unchanged.
There is no new accepted gate theorem and no universal noninheritance result.

The useful distinction is that final legal witnesses have actual source bound
3 and independent charge 4, but equality-charge cuts `2+2` have no piece
recognized by the proposed invariant. The final cuts use k6 lower2/upper3 and
k7 upper4/lower2. The preceding largest-maximum cuts were repaired by the
added terminal class; do not conflate the two versions. Exact final-cut Lean
runtime replay `20260929-204540-701aaf` verifies actual piece sums `2+1` and
`1+2`. This is diagnostic computation, not a node receipt.

Last candidate probes: `20260929-203912-3616cf`,
`20260929-203912-c2a968`, 3000 sampled legal histories each, both done.
Their witness JSON preserves the full ancestor and sequence of legal cuts.
All recursive cuts of matching sources were checked. Source enumeration is
sampled. Larger clean-family probes `20260929-201129-daac04` and
`20260929-201129-479064` ended at 30-minute budgets, complete only through
five children at k6 and four at k7. No six-child completion was obtained.

Reusable observations: physical child multiplicity must remain explicit;
original-history pruning supplies independent charges; exact-saving relaxation
passes many small sources but is not a geometric predicate; active capacity-one
pieces can contain the missing unit. The dense mixed-both-axes class has finite
positive audits, but does not establish the remaining middle endpoint exclusion.
Read the failed predicates and their stated domains before proposing a new trial.

## Part B: registered, closed reflection theorem

Requested statement, without added hypotheses:

```lean
theorem ctx_bound_reverse (σ : Ctx.Context) (hwf : σ.WellFormed) :
    ({ σ with word := σ.word.reverse } : Ctx.Context).bound = σ.bound
```

Current complete source [ReflectionAudit.reused.lean](ReflectionAudit.reused.lean)
compiles as guarded job `20260929-201544-f6a775` (4GiB cap, 522MiB peak).
Its axiom print is exactly `propext`, `Classical.choice`, `Quot.sound`.
It has no admission, `native_decide`, or added axiom. The registered source is
`ESBlueprint/B/CtxBoundReverse.lean`; type hash `4125616738b08f1d` matches its
statement lock. Original-module check `20260930-020436-781047` is done, with
`sorry=false`, `status=closed`, `lock_ok=true`, no uncovered/nonstandard axioms,
and only the three standard axioms above. This is accepted theorem credit.

Exact proof body [ctx_bound_reverse.body.lean](ctx_bound_reverse.body.lean),
19,179 bytes, SHA256
`45513fcc29fe22ac1ab32ff4aeb950e43f9f5e0d530d39758355df18a93448a0`.
It needs imports `ESBlueprint.B.CtxReverseExtensionTransport` and
`ESBlueprint.B.CtxPointLimitsEqOfChildInterval`, and the scratch's heartbeat and
recursion settings. No additional top-level lemma is needed.

Already accepted reusable nodes:

- `ctx_reverse_extension_transport`, type hash `4d6c2aaed124fffe`, closed with
  standard axioms. Receipt artifact
  `e91800c5e079104907eb46ddfc665d36a1cf1baaab5c88b757a9bf2be92f466f`.
- `ctx_point_limits_eq_of_child_interval`, type hash `817ec12effbc65aa`, closed
  with standard axioms. It replaces the initially duplicated constant-fold
  argument. Exact search found it after a prose search missed it.

Proof route: bounded position involution transports child letters and child
positions, proper nonempty block infixes, complements and `part`. At most one
run is equivalent to physical convexity of child positions; reflection preserves
that property. Point capacities are constant across that run by the checked
interval theorem, so the new first child's base equals the old first child's
base. Fuel induction compares each legal cut with its reversed cut, using
`WellFormed.part` at both admissible maxima. Involutivity gives equality for all
fuels; equal child counts supply the full `bound` equality. Empty-child cases
are handled explicitly. Unrestricted multirun `base` equality is never assumed.

Local Lean failures were elaboration/tactic repairs, preserved in the journal;
there is no repeated unsolved mathematical obligation in the completed proof.
The original longer source/body are archived separately; use the reused version.
Search evidence: `search-reflection.final-before-registration.json` has no hit
for `ctx_bound_reverse`. The PR draft must cite the earlier transport/interval
searches and reuse them.

## Receipts and exact recovery

Registration job `20260929-200349-567bbc` was initially cancelled before
execution because its20GiB reservation could not fit and the worker's aging
rule blocked younger jobs. After N27 ended and R6's registration completed,
the same job was requeued at05:54Z and completed. No other job was changed.
Registration and checking used targeted/incremental extraction; no full
extraction was run. `es node finish` was avoided because it includes one.

Frozen fixture `a33d21a46c266e2daa79ecea06e6b05b7f63b5b03030b9b2b22dab3e48bfc792`;
isolated operation `op-b9d9edf4b84a4654`, job `20260930-015957-47d5b7`, receipt
`2a5679692abe8beb64bdd4555af34ac754ed7940d762716fda8902507a6bc36c` explicitly
accepted the proof. Its audit has the locked type and only standard axioms.
Shared `es.finalize.preflight` and `es.proofs.assembled` inserted that exact
source, SHA256 `b7cedc2e2bd969ee0b96f5af992fbb59b43e8c29927c65f62dfbac7f171f59b9`.
See `reflection.insertion-receipt.json` and `reflection.proof-check-result.json`.

Targeted original-module check receipt
`492f82808b20c3216db2349a8bbf5fca32262d1b5788e4579dc8cf0855ec0dab`, saved
as `reflection.targeted-check-receipt.json`, reports closure and unchanged type.
Its module build took3.838s at670MiB peak; the whole guarded job included the
incremental index update. The declared dependency tag names transport; actual
dependencies also include the checked point-interval node and generated local
auxiliaries. This diagnostic mismatch does not introduce an axiom or open node.

The authorized three-file `git add` failed exit128: `.git-data/index.lock`
cannot be created on the read-only metadata filesystem. Nothing was staged or
committed; HEAD remains `5d58845b64c80c52f843290e31fa573398ebdd9f`. The host
denies approvals, so no approval request or mount bypass was attempted.
Exact deliverable `ctx-bound-reverse.patch` contains only the theorem module,
one root import and one new statement-lock entry (422 inserted lines).
Patch SHA256 `1a51d350487e567157b49dcff2786067cf001a6f9c1476dd1b1bf5ae4ac947d0`.
Generated `harness/nodes.json` and `harness/status.md` remain unstaged because
they also capture another agent's live claim. Preserve them as the current
automatic cache; do not commit that unrelated snapshot.

Safest next action: a coordinator with writable Git metadata reviews the exact
three-file change and receipts, stages those files and commits on this branch.
`delivery.sha256` pins the module, root import, lock, patch and validation
evidence. From this worktree on `node/CtxBoundReverse`, the intended commands
on such a host are:

```sh
git -c gc.auto=0 -c maintenance.auto=false --git-dir=.git-data --work-tree=. add -- ESBlueprint/B/CtxBoundReverse.lean ESBlueprint.lean harness/statements.lock
git -c gc.auto=0 -c maintenance.auto=false --git-dir=.git-data --work-tree=. commit -m 'Prove ctx_bound_reverse'
```

No new mathematical trial is needed. No merge, push, unrelated statement edit
or second trial is authorized. The endpoint gate remains parked independently.

## Review, accounting and artifacts

[CODE-REVIEW.md](CODE-REVIEW.md) records the Sol source/mathematical self-review
in separate observational window `window-de1a257b85a04dac`, ended accepted=0.
Independent Astra/coordinator review is pending because this run fixes Sol and
forbids delegation. Shared promotion is deferred by the allowed write scope.
The evaluator adaptation and source-domain limits are explicit in that review.

`code-manifest.final-gate.sha256` records executed sources and archived variants.
`review.pre-registration.json` references immutable code/usage inventory
`6c9a50b1346eca8b0351ea12bb56ece2c28e8dd7be3846e17b490afc534f34bc`.
Refresh `es run review runs/r3-sol-20260929/host --artifact-root runs/r3-sol-20260929`
after final validation. Inventory or process exit alone earns no theorem credit.
Canonical usage window is `window-2749aebd7bed480b`; sync there only, avoiding
double import into review/setup windows. The accidental overlapping setup
window `window-50546f2a00d04aa4` ended accepted=0 and receives no usage import.
All gate, registration, isolated proof and targeted-check jobs are terminal.
Reflection claim is released closed with this handoff; gate claim was already
released blocked. No active own claims remain. The commit is the only remaining
implementation step and requires a writable host. Refresh usage/review at the fixed deadline; do not
mark the native goal achieved while that required commit remains missing.
