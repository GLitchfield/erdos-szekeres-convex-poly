---
title: Select placement 14 or a corrected placement 24 mutation
type: research
mode: HITL
status: closed
claim: common-anchor-corrected-gap24-selected-2026-09-01
blocked_by: none
---

# Ticket 0128: select placement 14 or a corrected placement 24 mutation

## Question

After exact identity `C015-DHALF-GAP24-SOURCE-V1` stops candidate-locally at
its frozen `OneChangeOn` call, should the next one-lane slate execute the
already theorem-ready contradiction leaf `14`, admit a genuinely new
implementation identity for placement `24`, or stop with neither selected?

## Decision criteria

1. Authenticate the reconciled post-Ticket-0127 source and failure evidence.
2. Do not promote either candidate merely because the other failed.
3. Require a corrected `24` mutation to pass source, novelty, premise,
   target-equivalence, model-tier, producer, return-bridge, and immutable-gate
   review under a new identity.
4. Verify that correcting the `OneChangeOn` binder preserves the original
   mathematical words and theorem statement rather than changing a premise.
5. Treat the downstream heartbeat diagnostic separately: require a bounded
   exact relabel/case plan without increasing heartbeats or adding an
   obligation-displacing helper.
6. Reauthenticate all five theorem-entry fields for `14`; its selection must
   rest on present leverage, not automatic reserve substitution.
7. Select at most one information-gathering Lean lane, or stop honestly.

## Evidence

Three hash-frozen read-only reviews completed from
`runs/agents/20260901-ticket0128-next-leaf-selection/`:

- corrected placement-`24` entry, terminal
  `GAP24-MUTATION-ENTRY-COMPLETE`, SHA-256
  `a214239b9ba635a18075ee2e6fe37920df18289118109d97233577823be03918`;
- current placement-`14` reserve, terminal
  `GAP14-CURRENT-ENTRY-COMPLETE`, SHA-256
  `efb29f5008a9ab49c8eba208fdf432ce5a50a7fbe86d47c4f0c4b9d015f03e72`;
- independent allocation challenge, terminal `SELECT-GAP24-MUTATION`,
  SHA-256
  `9e8bdc36ee4cf8385a2515f5e17d049f5e920aa2500238fbedfe2b85e8c83026`.

Root selection report SHA-256 is
`bc73a2c58c229fe9a756b2de691ca75b5df961f101e925871e0ee71e28d6ac65`.
The frozen execution-plan SHA-256 is
`c7ebe04a16a393fda7f90b5fc09a26481cdc5c9b1d8b754e524f300dc74ee69e`.

## Resolution

Select only new identity `C016-DHALF-GAP24-WORD-FIX-V1` as a proposed one-lane
information-gathering slate.  Retain placement `14` as theorem-entry-complete
reserve without demotion or automatic substitution.

The selected mutation is not a blind retry.  Its exact `OneChangeOn` calls are
`hone h1o ho2 h2p` and `hone h1o ho3 h3p`, which preserve the original sorted
quadruples and words.  The downstream broad proposition-reversal `simp` is
removed rather than retried or granted more heartbeats: a frozen inline
three-matching case split returns `M0`, with both other matchings contradicting
negative edge `01`.  This changes no theorem statement, premise, model tier,
producer, or return bridge and introduces no helper.

- **Net proof movement:** `neutral`.
- **Evidence:** three authenticated read-only proposals; no Lean diagnostic,
  source edit, checked computation, or compiling theorem.
- **Damage scope:** `candidate-local` proposal ceiling only.
- **Difficulty displaced:** none.  All four source leaves and every downstream
  common-anchor obligation remain open until a later execution gate.
- **Counterfactual test:** the reviews distinguish an API-only repair from the
  still-untested matching/color mechanism and prevent both a blind retry and
  automatic reserve substitution; admitted proof depth is unchanged.
- **Planning consequence:** retain `FP-01` as `gated`, freeze only the
  corrected `24` plan, retain `14`, and await explicit user approval before
  executing the one declaration-scoped pass.

The temporary slate has zero proof-producing and one information-gathering
slot.  No load-bearing ledger edge or failure genome changes.  Review wall
times were 5:08, 2:09, and 2:53; CPU and peak RSS were not instrumented.
This ticket authorizes no Lean execution, Make/Lake command, repository test,
service action, commit, or push.
