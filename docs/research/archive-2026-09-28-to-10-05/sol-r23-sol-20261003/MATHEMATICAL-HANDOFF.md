# R23 mathematical handoff — research stopped, gate OPEN

Research ended at **2026-10-03T13:51:14.586618Z** by coordinator direction:
Gavin redirected all resources to generalization, and the single `(6,k-2,k)`
gate is no longer a target. This supersedes the original twelve-hour schedule.
Finalization hard stop: **2026-10-03T14:21:14.586618Z**. No new proof work,
candidate checks, captures, falsifiers or research jobs were admitted after
the cutoff. Finalization inspected existing evidence and safely followed
the registration job already submitted before the cutoff.

Agent `codex:agent-run-6b3abc23e58d4be6`, thread
`01a101a8-9b71-74e0-82bf-1da12b0c8ee7`, configured Sol/xhigh only, no
delegation. Baseline `6ae26b5d2543198ddd1b7bed7574827f72c02595`.
R21/R22 branches were preserved; nothing was merged or pushed.

## Exact open obligation and proof understanding

`singletonLowerPascalTailGate_six_pred_pred_of_seven_le` asks, for every
`k >= 7`, for `SingletonLowerPascalTailGate 6 (k-2) k`. It stays **OPEN**,
lock `135fffe38adb53ba`, scaffold commit
`9db1872a8a1dedd11a24ea740af48eaed5ef0dc6`. Its authorized ESBlueprint
`sorry` remains. Neither the gate, any of its thirteen root rows, nor the
optional upper colour dual has an accepted proof receipt. Completing this
run's report does not close that theorem.

The accepted mechanism is cap-start peeling: a cup ending where a cap starts
extends one of them. First points of c-caps therefore form a smaller-cup-free
family, while their complement is c-cap-free. This explains Pascal induction
and why gap-side exclusions localize starts into an earlier region. It is a
reusable structural argument, not a numerical fit.

The audited gate route combines this with marker endpoint exclusions and
root coupling, converting upper cap rank into a lower cup deficit. Its
remaining obstacle is uncompiled asymmetric marker counting, R3/R26 local
hypotheses and arithmetic, and the exhaustive root split. No counterexample
was established. The route is preserved for provenance; the next authorized
effort is generalization using the accepted mechanism.

## Requested accepted general results

All five original-source check jobs below are **DONE, exit code 0**. The
compiled receipts report CLOSED, exact locked types, `lock_ok=true`,
`sorry=false`, no nonstandard axioms, and only `propext`, `Classical.choice`,
`Quot.sound`. Finalization inspected these receipts and commits without
rerunning Lean. These are targeted original-source checks; no final
whole-project rebuild is claimed.

| Result / declaration | Lock | Source check job | Commit | Receipt stem |
|---|---|---|---|---|
| Generic peel: `exists_capStartPeel_of_oneChange_no_capSucc_no_cup` | `7a3d81dee5638d0b` | `20261003-082029-56f844` | `e9d72dc51b48feb3e18189b2582af988c5eb920a` | peel |
| Classical: `card_le_choose_of_oneChange_no_cap_no_cup` | `6e4f3d0cdd9013a5` | `20261003-085553-e4194e` | `bad5a94efe907f9d19352826904be0df34d8cdb9` | classical |
| Z6: `card_le_choose_add_choose_of_oneChange_gap_no_capSix_no_cup` | `253769f86d20a5ab` | `20261003-090056-567700` | `60bae7a83376f216b4baca5edcd7819b9270bbe5` | z6 |
| ZR/cup-prefix: `card_le_choose_add_choose_of_oneChange_asymmetric_gap_no_capSix_no_cup` | `3b86d68cec1b72c3` | `20261003-090944-96c6e4` | `531f795cbb90671fcfa4751a1e1e32ef3c0c1b93` | zr |
| Threshold: `decomposableThreshold_six_pred_pred_of_seven_le` | `761c42a05a5c1f69` | `20261003-082944-f198ab` | `1cb1c58802cab020dc335eba4ace60d27007af1b` | threshold |

Receipts are `<stem>-original-source-receipt.json` in this directory. Peel's
compact receipt points to immutable artifact
`2775be05943472870c7e2dae1e33f2b16ba32943231f07747487fb2acc848610`;
[peel-original-source-receipt-full.json](peel-original-source-receipt-full.json)
contains the authoritative compiled node record. Fixtures, accepted candidate
receipts, assembly records and audits remain beside the source receipts.
`SEARCHES.md` records the required theorem searches. No PR was created.

Here `C(a,b)` denotes `Nat.choose a b`; locked receipt types are authoritative.

* **Peel:** `c,v >= 2`, one-change, no `(c+1)`-cap and no v-cup imply an
  exact family `Z ⊆ s` of first points of c-caps, a c-cap-free complement
  `s \ Z`, and no `(v-1)`-cup in Z. The cap witness iff is exported.
* **Classical:** `c,v >= 2`, one-change, no c-cap and no v-cup imply
  `s.card <= C(c+v-4,c-2)`. Pascal induction uses the peel; parameter-two
  bases force at most one point.
* **Z6:** `v >= 2`, `q ∉ s`, one-change, both sides of q five-cap-free,
  whole set six-cap-free, no v-cup imply
  `s.card <= C(v+1,3)+C(v,3)`. Five-cap starts localize left.
* **ZR/cup-prefix:** the same hypotheses with left four-cap-free/right
  five-cap-free give `C(v+1,3)+C(v-1,2)`. The paired conclusion replaces
  the second term by `v-2` when the left side is a cup. Both admit `v=2`.
* **Threshold:** `k >= 7` gives
  `decomposableThreshold 6 (k-2) k = C(k-3,4)+C(k-1,3)+C(k-3,3)`.
  The reservoir yielding `G+1`, for `G=C(k-1,3)+C(k-3,3)`, is a
  mathematical consequence. Its exact gate-wrapper use is uncompiled;
  no separate accepted reservoir Lean theorem is claimed.

## Other already-accepted results

These pre-cutoff source receipts have the same CLOSED/locked/no-sorry/standard
axiom properties. They are auxiliary results, not gate credit.

| Declaration | Lock | Source check job | Commit | Receipt stem |
|---|---|---|---|---|
| `card_le_theta_of_oneChange_three_blocks_no_capFive_no_cup` | `6ec945469926b7b6` | `20261003-091838-2bb74e` | `08ab08f0b1dbce4072299f26822237c0b58317e6` | theta |
| `containsCupSet_succ_or_containsCapSet_succ_of_oneChange_common_endpoint` | `e6dfd0cd7e387aa5` | `20261003-092251-cd6887` | `7806d5c4f63648e9f6c18e6c9f12e88dc5f53c87` | cup-cap-extension |
| `card_le_choose_add_two_choose_of_oneChange_three_blocks_no_capSix_no_cup` | `5ac6eb3a799efa21` | `20261003-092800-15e367` | `7fffcb47aea740a7c876ce67f37553284d8a30b1` | l3 |
| `marker_straddle_turn_core` | `c147047e303865c` | `20261003-093339-329e33` | `b8c7a30194cb2ef0aabc1548d2698a8eceaba70a` | marker-core |
| `markerCupEndpoints_no_endpoint_cap_on_one_side` | `8a2844f6ddc77431` | `20261003-094007-b7d3ec` | `a6d600a9465670daac6d205772c1159bf61371aa` | marker-endpoint |
| `card_le_two_choose_cubic_of_oneChange_gap_no_capSix_straddled_cups` | `24241293e3c69ea4` | `20261003-094815-4f05d4` | `6008c8327606ea3a4d55b96fb5160a2a1ab84fd8` | marker-six |

Theta assumes three ordered four-cap-free blocks, five-cap-free union, no
v-cup and `v >= 3`; bound `C(v,2)+C(v-1,2)+C(v-2,2)`, with last term
`v-3` if the first block is a cup. L3 assumes the same block exclusions,
five-cap-free adjacent unions, six-cap-free total, no v-cup and `v >= 3`;
bound `C(v,2)+2*C(v-1,2)`, or `C(v,2)+C(v-1,2)+(v-2)` with cup first
block. L3 combines two start families into one smaller-cup-free piece by
the common-endpoint extension dichotomy.

That extension theorem assumes a cup P and cap C, each of size at least two,
with shared endpoint z=max P=min C and OneChangeOn on their union; it gives
a cup of size P.card+1 or cap of size C.card+1 in the union.

The marker core is an eight-point contradiction under explicit saturation,
bridge and blocked-extension turns. The endpoint theorem derives these from
actual witnesses: `a,b,m >= 3`, missing q, one-change, left a-cap-free/right
b-cap-free, no `(m+1)`-cup and all m-cups straddling h imply that either no
`(a-1)`-cap ends at a witnessed first m-cup endpoint or no `(b-1)`-cap starts
at a witnessed last endpoint. No global six-cap exclusion is needed here.
Marker6 **does** retain global six-cap exclusion, both sides five-cap-free,
`m >= 3`, no `(m+1)`-cup and all m-cups straddling h; bound `2*C(m+1,3)`.
Marker core's isolated audit omitted Classical.choice; its source receipt
includes it and is authoritative.

## Preserved unfinished work — no proof credit

Current branch `node/CardLeChooseCubicOfOneChangeAsymmetricGapStraddledCups`,
HEAD `6008c8327606ea3a4d55b96fb5160a2a1ab84fd8`. Registration
`20261003-095112-7e4316` was submitted at 13:51:12Z before the cutoff and
finished during finalization: DONE rc0, about 106 seconds/2312 MiB. It creates
only the **OPEN** asymmetric marker scaffold, lock `9e3423b55839fa99`.
No candidate check followed. The untracked module, ESBlueprint import and
generated registry/lock/status edits remain uncommitted.

`marker-asymmetric-body.lean`, `r3-body.lean`, `r26-body.lean`,
`root-six-body.lean`, `gate-six-body.lean`, `upper-six-body.lean` are
uncompiled drafts. All thirteen root rows remain open: empty side;
NN1 beta<=2; NN2 beta=3; NN3 beta=4/A all-left; NN4 beta=4/maxA right;
N1a beta=3; N1b beta<=2; N2a beta<=2; N2b beta=3; N2c beta=4/A5cf;
N2d beta=4/A5cap; N2e beta=5/A5cap (k>=8, k=7 empty); N2f beta=5/A5cf.
BN and the other N2f orientation require unchecked reflection in the root
draft. R3/R26 each retain eight unaccepted rows.

The provisional R26 beta=5 straddle route applies L3-cup around lower extrema,
suggesting `C(k-2,2)+C(k-3,2)+(k-4)`; its local hypotheses and arithmetic are
unchecked. N2e preserves the audited triangular-prefix/square-suffix route;
the alternative Theta6 bound was not established. These remain questions.
The exact gate and all dropped coverage stay OPEN.

## Failures and operational limits

Meaningful compiler failures were logged before retry and were not refutations:

* Classical `succ` versus `+1` choose atoms: normalized. Diagnostic
  `0bbd758da1ab9702a4f07fc358e900026f0a66c54bf445d426de2d8b9c5661d2`.
* ZR nonexistent `Nat.reduceChoose`: replaced by `Nat.choose_self`.
  Diagnostic `401a315385ab277da8d3bc216450a9416763b4be25cfe569ce316811ffbb0179`.
* Theta carrier alias versus union card atoms: explicit partition identity.
  Diagnostic `1e54547a9313056e0db98947dfcf296a1f04170a4e9aa056dbb374168cd82bcf`.
* Marker6 choose index `2+1` versus `3`: typed Pascal/index normalization.
  Diagnostic `aaeecf157dda5ca01ca62d917f4d8dab868150a7eec94175fbbc46dd8cf3215a`.

Initial cancellation released the peel claim; assembly refused before writing,
and reclaim/requeue passed. A premature 4G check could not reserve the 20G
blueprint root build; its guarded replacement passed. Full gate registration
`20261003-083304-4ef76b` took about 16 minutes/5810 MiB under 28G. No new
falsifier, enumeration or mathematical probe was run. No full-gate proof or
whole-project final rebuild is evidenced.

## Final review, usage and next action

Research window `window-a94d596de85d45f0` is administratively closed; its
effective cutoff remains 13:51:14.586618Z. Separate finalization/review window:
`window-058a20a897e74372`. Accepted-result counts are bookkeeping.

Read-only review `20261003-095508-d25408` is DONE rc0, inventory
`c7cb92d6c849439ad1da4e42bff7f8f8155a329e89d2e42897e7af15b2bf6fe3`.
`final-run-review.json` and three `final-review-page-*.json` preserve it.
The review covers 17 artifact Lean bodies, 13 changed tracked Lean files and
48 inline job commands; untracked asymmetric registration is additionally
covered by its receipt and OPEN record. No changed tracked Python/execution
script was found. Inline assembly glue reused cataloged fixture/preflight/
assembled APIs, checking receipt/body/type identities; source checks supply
proof acceptance. No new library algorithm was introduced or promoted.
Repeated glue is retained for provenance; future authorized work should use
existing proof/node automation. Uncompiled drafts warrant no promotion.
This was same-agent review under Sol-only/no-delegation instructions; no
separate Astra or independent reviewer run is claimed.

The observer inventory has unavailable usage coverage and zero response
records; this is not zero-cost evidence. Session import
`20261003-095824-10c84e` is DONE rc0: `final-usage-sync-explicit.json`
reconciles 324 records through 13:58:23.677Z, including setup/failed work.
Input 44,880,395; cached input 43,937,792; output 273,005; reasoning output
88,495. Active/later reporting can lag. Prior import `20261003-095803-c50eba`
failed for missing inherited CODEX_THREAD_ID; explicit-env retry fixed it.
Default paging and a refused oversized artifact page caused read-only decode
failures; supported pages resolved access without changing evidence.
Final reconciliation and factual harness handoffs are recorded in PROGRESS.md.

Final accounting job `20261003-100442-929080` is DONE rc0. Both imports are
reconciled snapshots through **14:04:41.755Z**, with 341 recorded requests:
input 46,169,245; cached input 45,171,072; output 293,588; reasoning output
92,598. See `research-usage-final.json`, `finalization-usage-final.json`,
`research-factual-handoff.json`, `finalization-factual-handoff.json` and
`finalization-window-end.json`. Both administrative windows are complete;
finalization accepted zero new results. Administrative research closure at
13:54:16Z includes some initial finalization after the effective cutoff,
so these records do not give an exact research/review cost split. Active or
later reporting can still lag, and window resource reports exclude unlinked
jobs. No all-in savings or zero-cost claim is made.

`final-gate-release.json` confirms PARTIAL release. `final-status.json` reports
the gate OPEN with `sorry=true`, no live claim, `stale=[]`, `problems=[]`.
Node-show's cached claimed label is preserved in
`final-gate-state-after-release.json`; the current status/live-claim record
is authoritative. The release preserved this handoff as immutable artifact
`a41a6e70895cd3d470816b1ea245e11b4181a1a5e30b2b9e31f8fa4477105890`
because the same relative path in the primary checkout had different content.
That older primary copy was not overwritten. The authoritative final document
is this file in the `sol-12h-20261002` worktree; the shared journal names its
absolute path. Finalization changes only reporting/accounting records.

Safe next action: the coordinator-authorized **generalization effort**, reusing
the generic peel and all-parameter classical binomial theorem, with the exact
Z6/ZR hypotheses retained. Do not automatically resume this retired gate
trial. Future authorized work must first read `es status`, relevant multi-day
or node-filtered journal, and this handoff. Preserve prior branches/receipts.
The gate remains OPEN regardless of native run lifecycle status.

Native lifecycle was marked COMPLETE at 14:06:11Z only for the coordinator's
revised supported handoff/report scope. The mathematical gate remains OPEN;
its claim outcome is PARTIAL. `final-status-verified.json` confirms that state
and no own live job or claim, with no stale index or reported problems. Native
usage counter: 948,479 tokens and 6,284 seconds; session/window accounting has
the distinct snapshot and coverage limits documented above.
