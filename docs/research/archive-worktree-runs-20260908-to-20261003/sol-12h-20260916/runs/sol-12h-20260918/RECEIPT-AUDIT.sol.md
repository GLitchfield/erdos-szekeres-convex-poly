# Sol receipt audit

Status: **receipt reconciliation and final full extraction complete**.

The immutable native-run review bundle is
`dccec1c0752457e849675ce7e0a8893ecb97735c821262682095e648804056a5`
(768,453 bytes, SHA-256 rechecked). This audit used receipt-review usage window
`window-fff8b28d0c4e4c59`, closed with zero new accepted theorem results.
Its recorded snapshot contains 72 responses through
`2026-09-19T14:12:34.940000+00:00`, sourced from
`/home/gavin/.codex/sessions/2026/09/18/rollout-2026-09-18T16-19-12-01a0b62c-4ff2-7c20-b4d8-616a192610be.jsonl`;
the active final response and later reporting require late reconciliation.
The machine-readable ledger is
`verified-results-reviewed.json`.

## Verified proof boundary

From baseline `70c20c037f9ec031346e81508a0eb6f5ef223fc8` through reviewed HEAD
`eb421ac30725bf7b2b1155ac21dc745e2f9d994b`, there are 22 theorem commits,
22 new Lean modules, and exactly 22 public theorem declarations. Every theorem
has a successful `es check`, a content-addressed proof fixture, and a commit
receipt. All 22 proof fixtures were opened and reconciled against the current
committed source: source hash, type hash, and standard-axiom list match in all
22 cases. Every node has `sorry = false`, no nonstandard axioms, and exactly
`propext`, `Classical.choice`, and `Quot.sound`. The new modules contain
no `sorry`, `native_decide`, or axiom declaration, and the baseline-to-HEAD
diff passes `git diff --check`.

Historical full extractions succeeded at 17 boundaries, including four
successful 28 GiB `es check` jobs that performed full extraction internally.
The last completed
historical extraction is job `20260918-224646-bba7cf`, exit 0, tree
`8e59cdbfd4e380fb`, 317 nodes, covering all new declarations through commit
`100d186b`. The final theorem at `eb421ac3` has successful targeted check
job `20260918-225944-4b703d` and receipt
`7cb963a5c9c850325264e95f378b6a594b921550c58d2acaedefb46d490b3b39`.
It was the only theorem missing from the full index. Final guarded extraction
job `20260919-095926-c9ccdd` finished with exit 0 in 638.8 seconds at the
30 GiB peak, with no OOM, budget overrun, or refusal. Its full JSON receipt is
`runs/sol-12h-20260918/review/final-extract.json`. The resulting tree is
`9d83d6f89554e35b`: 318 nodes, 17 destinations, no extraction problems, no
stale node, and status counts 305 closed / 12 open / 1 refuted. The final node
is closed, lock-valid, `sorry = false`, has no nonstandard axioms, and retains
type hash `eb0b005237aa44a7`.

## Mathematical scope

The 22 compiled results form a conditional chain:

- exterior one-sided actual companion bound 9;
- low/high capacity pruning bounds 5 and 6, plus separated and active-separated
  transports to 11;
- actual-marker residual classifications through active low straddles,
  small pair overlap, two collision witnesses, intersection cardinality at
  least three, and oriented high support;
- exact high-support and mixed low/high pair-cardinality transport; and
- a final actual-companion wrapper from the explicit hypothesis
  `(pairs 0).card + (pairs 1).card <= 11` to every-fuel/full bound 11.

The final wrapper assumes `hPairCard`; no new theorem proves that inequality
for every residual configuration. The union-nine result does not supply the
needed sum bound in the remaining large-intersection case. Thus the full
coupled branch and `ctx_bound_additive_sandwich_one_singleton_end` remain
open. Several early first/max-one wrappers retain `n = 1` syntactically and
derive `maximumAt 1 = 1` only into an unused local fact; the generic coupled
recursion does not exploit maximum one. The classification theorems and final
wrapper do return the marker/max-one facts, but this does not close the missing
pair-cardinality argument.

## Native-run resource accounting

The immutable review bundle contains 160 jobs: 117 done and 43 failed. Of the
failures, 41 exited 3 and two exited 128. They are retained as failed attempts
and grant no proof credit.

Twelve successful early `es check` jobs were enclosed by 20 GiB job scopes
while the configured full-extraction stage requested 28 GiB. Their logs
explicitly report that the nested full extraction was refused, after which
`es check` succeeded through a targeted module extraction. These are checks
`164923-515fed`, `171109-86e664`, `172605-b9e2b0`,
`173842-d8b94e`, `175403-dfb118`, `181221-795416`,
`185049-87b682`, `190354-57933b`, `191727-87dbc8`,
`193154-722718`, `200726-3f5066`, and `202123-fa8935`.
Separate successful 28 GiB full extractions subsequently supplied full-index
receipts for those sources. This historical reservation mismatch cannot be
rewritten as a full check; the final reconciliation job uses a 30 GiB
enclosing cap and is the current full-environment boundary.

All 22 new nodes have explicit historical releases with outcome `closed`.
The only expired claim is the umbrella consumer after the native run reached
`usageLimited`. Its history was preserved, and an audit log under
`codex:01a0b62c-4ff2-7c20-b4d8-616a192610be` records the reviewed outcome as
`partial`: the supporting nodes are compiled, while the consumer is open.

## Metadata boundary

Before the final extraction, generated metadata reflected
`100d186b`/tree `8e59cdbfd4e380fb` and therefore reported the final theorem
stale. It now reflects `eb421ac3`/tree `9d83d6f89554e35b`, with no stale
nodes or problems. After Astra reviewed the exact generated diff, the only
tracked changes, `harness/nodes.json` and `harness/status.md`, were committed
as metadata-only commit `668e390e22c6d7ce769e19c2913ee15cb8a65d13`.
The reviewed proof HEAD remains `eb421ac30725bf7b2b1155ac21dc745e2f9d994b`;
the metadata commit adds no proof source.
