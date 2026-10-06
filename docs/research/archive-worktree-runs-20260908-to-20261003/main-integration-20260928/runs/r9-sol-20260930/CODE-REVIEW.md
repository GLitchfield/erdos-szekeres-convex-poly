# R9 final mathematical and code review

Reviewed after research window `window-1729ff967c6d4641` ended, in separate
review window `window-b4b387cfb8814e08`. Review uses the user-required configured
Sol/xhigh model. No delegation or different-model review was invoked.

Accepted: commit `4cf96422ce0f5b6d99ad03d3eaa703c6333470f4`, exactly one
registered node, targeted receipt `CHECK-RECEIPT.json`. The unchanged type hash
is `2f0a94ddbcb29ccf`; `sorry=false`, `uncovered_axioms=[]`, standard axioms only.
The original docstring and theorem header compare byte-for-byte with the commit
baseline (`DECLARATION.original.txt` / `DECLARATION.final.txt`). All new proof
body lines fit 100 columns; the inherited locked header/docstring are preserved.

The proof review checked both Boolean starts, the surviving same-level separator
in the minimal n=4 case, isolated children before DelMono, WellFormed of the
intermediate shortened parent and its part, C1's complete strict-span condition,
word/field/maxima equality after each operation, admissibility of `k-1-d`, both
closed bases and reversed orientations, induction decrease by two, equal parent
base, and exact registered parity/complement lists. C1 and DelMono are explicit
hypotheses, so no unconditional result is inferred.

The intended consumer was also checked: job `20260930-093734-c64ab7` compiles
`ConsumptionInline.lean`, which imports committed R9, includes the unchanged R6
source, and supplies R9 directly as R6's alternating hypothesis. The resulting
anonymous example proves arbitrary-keep single-run additivity from C1+DelMono.
It grants no additional registered theorem credit.

All Lean artifacts in R9 were inspected, including failed snapshots and logs.
Failures are labelled in the mathematical handoff; their error-recovery axiom
prints are not accepted receipts. Original R6's existing unnecessary-simpa
warning is retained without changing its source. No Python or solver algorithm,
new workflow script, generated certificate, or other statement was introduced.

Inline job commands use existing guarded `es job run`, `es check`, and
`es node commit` interfaces. Lean output is captured with `set -euo pipefail`
and `tee`; timings are observations, with no custom kill deadline. The sole
cancelled job was an unstarted 20G queue reservation, replaced by the identical
targeted check under 6G. No compile was killed. The failed partial LEAN_PATH
overlay attempt is retained as a diagnostic and is not the accepted workflow.
Its replacement uses only source inclusion under the same guarded compiler.

Reused: R6 local Lean glue and the catalogued proof/jobs/node-commit workflows.
Promotion: none. This is a one-node mathematical proof; generalizing its local
helpers or one-off source-inclusion verification would be outside the approved
write scope. No recurring Python/workflow algorithm needs a library entry.

Automated inventory artifact
`b2ca652a16b324b07c32f65349c8462ed83f2ffedc343829973ed40861e7cec9`
hashes the R9 Lean files and changed tracked module. Its jobs/receipts fields
are empty because the host's inherited researcher id differs from the explicit
thread-based `ES_AGENT` used for R9 records. Manual review therefore uses every
exact job named in `MATHEMATICAL-HANDOFF.md`, the targeted immutable receipt,
and commit job `20260930-092916-755d72`; no zero-resource or savings claim is made.

Scope checked against baseline `b706beec9cebb538179cd5ef8994d94c8a1d25a7`:
only the target module and its derived `harness/nodes.json` / `harness/status.md`
are committed. Working tree is clean. No merge, push, full extract, another
trial, primary-source edit, or other statement edit occurred.
