# R16 proof and code review — 2026-10-01 07:04Z

Additional bookkeeping review: repair_usage_window_boundary.py uses the existing
load_config/Store APIs. It only corrects this agent's already closed research
window end to the recorded start of its own review window, preserving the prior
timestamp and reason in metadata and the journal. It changes no usage values or
host-owned window. Job030618-05dcd8 is queued; no correction result yet. Catalog
workflow.usage has no retrospective-boundary API, so this one-off correction is
retained as an audited artifact rather than promoted. Direct-job window resource
totals omit jobs without operation links; zero is not a measured compute cost.

Performed by configured gpt-6.1-sol only; the task forbids delegation or another
model, so no separate Astra reviewer was used. Usage windowwindow-3f3a2be329af4056.

Certified helper source Boundary-exact.closed.lean, SHA256
f0cb79aef9c6bc2377e047325d3613545bdc5e6de6f30b03688e9e8d53967eb2.
Targeted accepted check030155-fd7bff,CHECK.boundary-exact-v7.json,fileSHA256
56ede496302f1bcd63a4bbe643af9853cb1af7fe98167b4bcce114e6616c20a3;
closed fixture64f6fe0aa17c4aa95b8129cccc7ab0f0441781f526712d82283841d6d1ef3397.
Typehash81fb6b0b14b6f62a,lock_ok,true,sorry=false,only standard axioms.
Proof reviewed: sole marker gives one extension in the boundary direction;
positive selected maximum absorbs the pure-chain term in the selected join.
Order-preserving surviving-level bijection retains opposite-side extensions
and maxima. Normalization commutes with all parts; sole marker, selected
maximum, positive labels, boundary and terminal-axis conditions propagate.
Fuel induction preserves complete cut lists, including empty-child/base cases.
No existing statements changed. Search before proof: boundary singleton marker
erase normalize exact equality returned no result; one-way helpers reused.

Ad hoc code reviewed: boundary_candidates.py,probe_boundary_normalization.py,
N-ends.falsifier.py snapshot, N-ends.falsifier.cache-size.py,CACHE-SIZE.patch.
Candidates are small and separate from execution. Shared part, sole-opposite
normalization, compiled evaluator, singleton cuts and threshold/limit routines
are reused; no new evaluator/recurrence/workflow infrastructure.
The boundary runner closes all evaluator pools, records source hashes, reports
progress and preserves failures. Opposite-global1 instances are explicitly
skipped and remain outside that diagnostic. Same-axis merged maxima may exceed
legal root range; a future induction must handle that case. Frozen selector
import tested030011-f68350,6equalities,no failures; generator semantics retained.
Cache parameter change keeps default2M; insufficient speed benefit was measured
and original tracked source restored. No optimization claimed.

Job journal commands reviewed: registrations/checks/branch creation use primary
es --root and guarded jobs. No manual compiler,full extract,deadline-kill,merge,
push,primary source edit or delegation. Nested4G→20G extraction refusals are
documented and terminal candidates rerun with20G enclosing allowance.

Promotion decision: no new generic algorithm or workflow helper to promote.
Shared contracts already cover execution. One-off p0 normalization candidates
remain in durable run artifacts until the exact root normalization/application
is proved; do not generalize them solely to enlarge the library. New certified
Lean helper is registered in ESBlueprint and its closed import/lock/index entry.
