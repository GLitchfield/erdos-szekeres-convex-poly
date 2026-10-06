# R21 code and library review

Review window: `window-7373e4889c364aa7`.
Reviewer: the configured gpt-6.1-sol at xhigh, with no delegation or model
override, as required by the native-goal contract. An independent Astra review
is not claimed.

The first phase's only ad hoc script is `prepare_baek_port.py`. It performs source-specific
import traversal, identifier/API text preparation, section isolation, and
provenance hashing. It runs no Lean, budgets, job orchestration, falsifiers,
or mathematical evaluator. Its output was subsequently repaired explicitly
and checked as original Lean source. All 18 original source bodies still
match their recorded hashes, verified with shared
`es.artifact_cache.sha256_file`; receipt `baek-port/source-manifest-verified.json`.

The preparation script intentionally remains a one-off artifact. Its textual
renaming and scope counting are not a generic Lean parser, and rerunning it
would replace repaired diagnostics. This limit is documented in the script,
the port README, and the mathematical handoff. No recurring mathematical
algorithm was introduced, so there is no algorithm to promote to
`harness/research/` and no new catalog fixture or example to maintain.

Execution reused the existing node-add, proof capture/check, node-finish,
guarded build, job, resource reconciliation, usage, and commit workflows.
The inline job commands invoke those APIs or pinned Lean diagnostics; the
parallel restoration budget derives from the user's fixed deadline. Storage
cleanup used the supported PID/start-identity and cgroup checks, with a
receipt reporting no uncertain execution and no external effects retried.
No lock bypass, direct unguarded compiler, separate execution framework,
or changed tracked workflow script was introduced.

Two reusable operational observations are preserved in the shared journal:
full extraction in a fresh worktree needs the ESCore root in addition to
the blueprint target, and cached core restoration is much faster via the
existing no-serial native-cache path than repeated serial Lake starts.
The exact full target succeeded in 12 seconds, job `20261002-155725-92b804`.
The ten-minute stopped serial coverage and initial storage refusal remain
documented. A harness source change is deferred because the supported
commands resolve this run and this trial's tracked change is one mathematical
node; this is not an unresolved mathematical obstruction.

Final source/audit review for the first node found only the new node, root
import, and harness records changed. Full extraction reported no problems;
allowlist audit and layer audit reported no failures or violations in
`20261002-161845-f1fb21`. The target's unchanged type hash is
`17d2458e770c2e45`, with only the three standard axioms. There is no sorry,
new axiom, native_decide, or generated certificate source in the new module.
The original-source receipt, not script exit or inventory counts, establishes
the mathematical result.

One provenance invocation used a nonexistent worktree virtualenv and did not
run. Its premature log was explicitly corrected before a successful system
Python recheck. That failed invocation is not accepted evidence.

## Exact diagonal source review

Separate window `window-dc0da6abc7784922`, with the same configured Sol model
and no independent Astra review claimed. Research window
`window-1f56fe4fe55046ba` ended with the original-source receipt before this
review began. Audit job `20261002-170811-d4a30d` reports no failures or layer
violations. The committed single-set source remains byte-for-byte unchanged.

The new diagonal source contains only the registered declaration and its proof.
It obtains whole-set OneChangeOn from decomposability, applies the certified
single-set bound, and evaluates the three-entry binomial window by symmetry
and Pascal. The exact gate binder is deliberately unused. Source hash
`383673715f23c362195b19aaeffbfe4acaaa3064c5f965b1e6f756ec41bd0d09` agrees
between isolated acceptance and full original-source closure. Shared assembly
reconstructs exactly the captured prefix, accepted body, and suffix;
`diagonal-finalization/accepted-body.diff` and `review.json` preserve that review.
Receipt artifact `3282828854a31abf87f12abdb7ec9e64388a3c0b9b221484a8b8cee8ddee1982`
is explicitly a manual full-source-route review, not a node-finish operation.

The archived `INSERTION-RECIPE.py.txt` uses existing fixture, dependency,
claim/branch/lock preflight, and byte assembly APIs. It checks the accepted
body and candidate-source hashes before replacing the source. It cannot be
rerun against the now-proved source because the fixture source check would
fail. The short review command checks original-source closure, type hash,
axioms, audits, source assembly, branch, and unchanged base commit; it runs
no Lean and creates no execution framework. Full source checking is the
supported fallback because the gate interface's 28.4 GiB object closure
exceeds the configured targeted ceiling. No limits or locks were bypassed.

`parity-witness/check_parity_witness.py` evaluates one fixed coloring with ten
triples and five quartets. It reuses `one_change` and `strong_sizes`; its cap
test uses all triples, as required for the project semantics without a
one-change assumption. Consecutive chain profiles would be unsuitable here.
The cap/cup gon printed in its result is justified by the exact triple table;
its union's RRLR quartet fails strongness. No sweep, search algorithm, or
general evaluator was added. This one-off mathematical witness remains an
artifact; its diagnostic status is explicit. There is nothing recurring to
promote to the library, and no tracked workflow script has changed.

## Optional dual review

Separate window `window-aaf19fdf62ef405c`, configured Sol self-review only.
Original-source check `20261002-172932-0a1eb5` closes unchanged type hash
`9fbc31b5eb51b848` with only standard axioms. Audit job
`20261002-174759-82d42d` has no failures or layer violations. The first two
theorem files still match their committed accepted hashes.

The new dual module has one registered statement and a direct application
of existing `decomposableStateUpper_comm`; the three arithmetic premises follow
from k at least five. There is no new combinatorial lemma or new certificate.
The archived insertion recipe repeats calls to existing fixture/preflight/assembly
APIs with this node's pinned data. It implements no new workflow primitive.
The short receipt review again checks exact assembly, closure, axioms, lock,
branch/base, and audits. Full checking respects the known targeted closure
ceiling. No tracked workflow script or configuration has changed.

Manual full-source-route review artifact
`e0a9967bbec97ce9df4d5b3bb65e44c85c7f8a2e71e1b52c9131e95a01d71657`
pins source SHA-256
`1575ca2c4b3b9c0f5c8321eae172606e092fdaf15fa8f365b88c41bc0d69699d`.
The authoritative source check and audit receipts establish acceptance;
the review inventory itself grants no theorem credit. Generic full-source
node-finish support remains a documented maintenance opportunity, deferred
because the existing shared APIs and supported full check already complete
both large-interface nodes without another execution framework.

## Approved early-finish finalization

Window `window-9b7d5d80cdae43c1` inspects existing proof receipts, terminal
job records, audit/layer outputs, source SHA-256s and read-only Git history.
All three sources match their accepted and committed bytes. Only run
documentation and accounting snapshots were updated after the early deadline;
no theorem source, tracked workflow script, compiler job or new algorithm
was added. No further promotion or library maintenance is warranted.
Monitoring window `window-57469c43b8994b9c` used 5,070 recorded output tokens
as of its ending snapshot, within its observational 10,000-token target.
Direct usage sync includes setup, failed work and monitoring; later reporting
may lag. The known umbrella/phase reassignment conflict remains documented,
with no reassignment or zero-cost/savings claim.
