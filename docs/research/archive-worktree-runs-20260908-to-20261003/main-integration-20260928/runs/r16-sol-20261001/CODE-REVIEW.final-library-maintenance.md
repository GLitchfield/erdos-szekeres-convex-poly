# R16 final ad hoc-code/library review — 2026-10-01 16:52Z

Separate Sol self-review window window-3d695eaa14e04241 follows mathematical
receipt/parent/proof review window-b734f927e1874a91, ended accepted0.
Host permits only configured gpt-6.1-sol/xhigh and forbids delegation, so this
is not an independent Astra review. No source integration or shared library edit.

New final audit helper audit-committed-proof-spans.py was read in full.
It uses shared es.proofs.whole_span (lexical byte-span parser), never runs
Lean, C, lake, extraction or a solver, and never opens/writes the shared DB.
Git show is read-only with gc/maintenance disabled and the required .git-data
flags. It reads the frozen thirty-result inventory and closed/commit local Lean
artifacts, computes SHA256, compares exact stripped proof bodies separately from
full-module bytes, prints pernode progress to stderr and JSON only to stdout.
The guarded shell redirects that stdout to the declared new Runs artifact.
Every subprocess argument is a list, so no statement/candidate shell interpolation.

Semantic limits: files that lack that exact registered declaration are skipped
using the shared parser. A match is documentary consistency, not compilation.
A missing match would make all_match false even though the metadata process
could exit0; the actual output was inspected rather than trusting exit alone.
The first3 sample took1.650285s; full30 estimate16.5s, actual17.269732 internal/
17.5guarded seconds,20MiB/1GiB. Job20261001-124906-638eb3 completed with all
outputs present, no OOM/refusal/budgethit and termination acknowledged.
All30 match;28 full modules byteequal. Both remaining diffs remove exactly one
blank line after the final namespace end; imports, signature and body unchanged.
Exact artifacts AUDIT.committed-proof-spans-1649.json and
AUDIT.committed-proof-nonbody-diffs-1649.json. Do not overwrite frozen outputs.

The final JS orchestration used sequential es job status/artifact show calls;
legacy missing-ok/enclosing-command normalization failures were logged before
repair. It required each actual node's closed/locked/hole-free/standard-axiom
fields and each enclosing output receipt, not successful exit alone.
Independent Git metadata batches used Promise.allSettled and all five-path
commits contain exactly the own module plus four node/import metadata files.
All shell metadata commands finish below one second; only full proof-span
comparison was conservatively submitted as a guarded job. No chosen deadline,
configuration override, approval, worker mutation or other-job control.

Library search/show workflow.proof/node-commit/jobs and corresponding source
inspection preceded the helper. Shared proof parsing and job/artifact workflows
were reused; no duplicate parser/evaluator/workflow engine was implemented.
No promotion now: the short caller documents this one frozen thirty-node
inventory, not a recurring new research algorithm. If future runs repeatedly
need committed-proof comparisons, add a reviewed shared audit command with
regression fixtures/catalog/example under separately authorized maintenance.
Generic readonly-admission CLI, evaluator-domain catalog clarification,
unit-global C shortcut and duplicated Lean transport factoring remain deferred
for the explicit reasons in earlier review records; primary/shared-source edits
and integration are forbidden in this trial.

All thirty accepted commits change no tracked Python/C/harness scripts.
Earlier run Python callers, candidates, inline jobs and failures remain reviewed
in their individual CODE-REVIEW.* files, including the offline infrastructure
review's v4/SQLite query. Original evidence was not rewritten. The final reports
add documentary summaries and receipt links; no existing Lean statement changed.

This review grants no new theorem credit and does not close N_ends or N_root.
Whole-thread usage is reconciled with ES_WINDOW_ID unset so historic explicit
window assignments are never overwritten; overlapping/offline/late and direct-
job attribution gaps remain. No matched savings claim.
