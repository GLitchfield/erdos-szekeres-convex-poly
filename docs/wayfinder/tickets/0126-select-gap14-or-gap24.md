---
title: Select placement 14 or placement 24
type: research
mode: HITL
status: closed
claim: common-anchor-gap24-selected-over-gap14-2026-09-01
blocked_by: none
---

# Ticket 0126: select placement 14 or placement 24

## Question

After placement `13` elaborates, should the next common-anchor source lane
close final contradiction `14` or attempt qualified dual transport `24`?

## Decision criteria

1. Compare both against one authenticated current source snapshot.
2. Require all five theorem-entry fields and a strict source measure decrease.
3. Distinguish mathematical obligation reduction from code compression.
4. Preserve correlation: both are leaves of one `FP-01` mechanism, not
   independent proof routes.
5. Select at most one bounded information-gathering source lane, or stop
   honestly if neither remains qualified.

## Evidence

- Frozen snapshot SHA-256:
  `1d3324768993c95d42e5c35e3a77283e2083a3deb980150b0116f55fbfbec311`.
- Placement-`14` report SHA-256:
  `51279f0ac0dc843ad3d935fdcc80f1a682ccc2ded58796b7d092102c9680594d`.
- Placement-`24` report SHA-256:
  `42dca4253bb8724e61f8cbfd198fdb17f76637123cd0408f6e47f76a226dffeb`.
- Independent adversarial report SHA-256:
  `4a4bf574a6b6237346243cea26c629e3c5e6a3643ec12bc144013d0e4fc8218c`.
- Root selection report SHA-256:
  `d5461d12103a46ab7af31c282cf296736ecc5a18cc48d555159e5d7d3871a832`.
- Frozen placement-`24` execution-plan SHA-256:
  `afe6d3648b2559d4d97074ea1ff130a620863fd09f9be0f0bd2a81e72832b2f9`.

## Resolution

Both candidates remain theorem-entry complete.  Placement `14` is cheaper,
uses no `OneChangeOn`, and would close contradiction-source deficit `1 -> 0`.
Placement `24` has the larger proof surface but tests the first remaining
actual-order dual mechanism: two literal one-change words, a proposition-only
matching reversal, and the color-terminal extraction.  The independent audit
selects `24` because this is new mathematical information, while `14` would be
the fourth source instance of the already stable active-clique producer.

Root therefore selects only `C015-DHALF-GAP24-SOURCE-V1` as one information-
gathering source-incubation lane and retains `14` as the theorem-ready reserve.
Fable's proposed equality-head helper is independently judged valid but only
code packaging; it removes no obligation and is excluded.  The complete plan
is `gap24-execution-plan.md` under the run directory and awaits explicit user
approval before Lean execution.

## Proof-distance accounting

- **Net proof movement:** `neutral`.
- **Evidence:** three authenticated read-only proposals; no Lean edit or
  checked computation.
- **Damage scope:** `candidate-local` proposal ceiling only; no admitted
  mathematical negative.
- **Difficulty displaced:** none; four actual source leaves and every admitted
  downstream dependency remain.
- **Counterfactual test:** the review changes allocation toward a genuinely
  different dual mechanism rather than another active-clique instance, but
  does not shorten admitted proof depth.
- **Planning consequence:** retain `FP-01` and `FP-03` as `gated`; select only
  placement `24`, retain `14`, exclude the helper, and await execution
  approval.
- **Load-bearing ledger edge changed:** none.

No failure genome is created.  The three audits used 3:06, 1:59, and 2:25 wall
time; CPU and peak RSS were not instrumented.
