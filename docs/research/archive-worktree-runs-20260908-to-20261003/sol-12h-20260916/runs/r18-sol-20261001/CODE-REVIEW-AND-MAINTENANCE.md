# R18 Sol self-review and library maintenance — completed 02:29 UTC

Configured gpt-6.1-sol/xhigh only, no delegation. The instruction to use Astra
for review is overridden by this run's explicit Sol-only contract. Same Sol
performed the review; this is recorded separately from research, not an
independent model review. Maintenance window-a4873af9906b446d ended with one
new public accepted helper; final mathematical review is window-c85462127fc74aca.

Research window-bff1ef2d0f4547b3 ended with12 accepted public nodes, excludes
OPEN NFpartial. Overall13 CLOSED public nodes have original-source receipts;
the accepted partial and private carriers receive no extra theorem credit.

Native review inventory222224-38d26c/artifact
dc3613391f3091bf559c1969f6d6ab72e9c0112852dabbc45b5ef0e4c9036414 was read
in four bounded pages, then parsed completely. It covered25 artifact scripts,
38 baseline-to-current tracked scripts and two inline Python commands.
Its169 jobs/26 explicit proof receipts/17645 workerseconds/8687MiB max peak
are a snapshot, not a final total or theorem count. Pending2 at that instant
were helperaudit and the review job itself; both subsequently terminal.
Failed oversized artifactpage request and its corrected bounded fetch are logged.

Ownership: baseline-to-current38 tracked scripts include inherited R15/coordinator
Lean/harness changes. They are not new R18 changes. Own source changes are the
13 node branches, OPEN NFpartial, and its registered one-line falsifier fix.
Current helper branch0edc has onlymodule/root/lock in its commit; source-only
comparison proves all378 inherited lockrecords unchanged. No primary tracked
source, sharedworkflow implementation or other trial node was changed by R18.

All21 Python artifacts were reviewed as base sources plus retained-version
diffs. Four early ROOT-NF .lean draft mirrors were reviewed through v2->v5
diffs/full v5, including projection/parser/dsimp and empty-child repairs.
They are historical proof text; only the original ESBlueprint target audit
grants checkpoint credit. Later .lean.txt body/fragments have their explicit
compiler failure or acceptance receipts; the accepted v21 statement/FULLP
byte invariants and exactly3holes were rechecked. Public same-side body61lines
received fresh complete-parent and original-source audits, noholes/stdonly.

Reused research APIs: compiled context-bound evaluator, rank primitives
part/extension, singleton cut values, existing threshold/context-limit code.
Shared APIs own execution, cache/worker semantics and part construction.
Candidate transforms remained small in artifacts; Python/C diagnostic-to-Lean
equivalence is unproved. None of their finite passes grants theorem credit.

Reviewed candidate semantics:
- Component bridge compares BOTH components, even permitting a swap; failures
  survive that relaxation. Its actual(4,22)/NF26 witness has FOUR children,
  correcting earlier five-child prose. Explicit root families append right ends.
- Interior/relabel/delete cut variants retain paired-sum checks and separate
  actual/candidate sums. Both scalar transports failed; their fixed domains,
  clipping rules and cache-only changes remain archived, not promoted.
- End visibility, NF2 formula, reachable complement and raw unilateral probes
  construct their words explicitly; frozen-words bug does not affect those.
- Axis-two broad grid did import defective frozen words; old right/both-marked
  coverage is withdrawn. Corrected NF grids do not silently certify its Boolean
  formula's missing k7/right-end cases; that diagnostic coverage remains open.
- Corrected sharding adds only a disjoint legal global-a selector and exact
  count. All7 disjoint shards/correct scopes/PASS157680/terminal statuses checked.
- New five-child family explicitly dedups frozen bases and appends right ends,
  guards128 parameter/word records with actual5children, and saves all inputs.
  First cardinality assertion failure and corrected source are preserved.

The two inline job commands were reviewed verbatim from the inventory:
213908-9ae026 audits input enumeration only; 222141-8ee9c9 compares complete
inherited JSON lockrecords against exactmain8c8 only. Both are read-only toward
sources/locks; their JSON output semantics are explicit. They perform no Lean
or evaluator call and no process signalling, reconciliation or approval.

Maintained registered falsifier: append the omitted right markers, source
a2ea44c0477f4c803f7e4470c18079dcb11a81f84a8e04066fa183b18760be40,
committed with fresh officialPASS29520 receipt on NFbranch09395.
Old frozen source and old diagnostic receipts preserved; old endpoint coverage
withdrawn. Corrected187200 grids plus128 boundedfivechild cases PASSdiagnostic.

Regression: stdlib fixture validates10 n1..5/Side cases and preserved-bug negative
control. Initial pytest attempt failed beforetests; v2 passed on NFbranch.
Maintenance v3 pins preserved corrected/frozen source copies so replay works on
any R18 branch; job222733-b9d7d2 PASS0.2s12MiB, current source
75d036fc53b452c80aa60f60f5fe19311a80934f3bc7f4939294866918c56a9e.
Prior fixture sources/receipts preserved. No evaluator is called by regression.

Promotion/reuse decisions: reusable mathematics is published as13 typed Lean
nodes (latestsame-side bridge0edc), indexed by es, with original-source receipts.
No new procedural algorithm or generic workflow helper was promoted: stable
evaluator/part/cut/proof/node/job/accounting APIs already exist; failed scalar/
component transforms and one-off formula candidates have no accepted generic
contract. A general endpoint-word API/catalog addition is deferred until it has
a repeated independent consumer and stable contract; this run fixes the actual
registered falsifier directly. No wrapper was written to grow the library.
Since there is no procedural promotion, no new librarycatalog/example entry
is claimed. Regression and explicit semantics remain durable artifacts.

Infrastructure lessons retained: closure-size memory estimator misses11k-line
proof elaboration; matched12G floor+outer reservation worked. Temporary config
was restored byteexact20 before every commit/capture. Concurrent falsifier/
check worktree reservation refusal was recorded and stages sequenced; noforce.
Missing declared stdout outputs are explicit; full joblog JSONs are authoritative.
No chosen timeout/cancellation, merge/push/newtrial or delegation occurred.

Usage: explicit own-session sync is reconciled and includes failed work/setup.
Host review's0/unavailable usage reflects a different window association, not
zero consumption. Preserve own sync/window reports and late reconciliation.
No matched all-in savings claim is made.
