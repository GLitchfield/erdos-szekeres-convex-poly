---
title: Adopt a four-plus-one research generation
type: research
mode: HITL
status: closed
claim: codex-four-plus-one-research-generation-2026-08-19
blocked_by: none
---

# Ticket 0045: adopt a four-plus-one research generation

## Question

How should bounded investigations, accumulated factory ideas, and refreshed
Sol ideation be coupled so that every new batch sees the latest evidence and
the project continues testing ideas rather than merely accumulating them?

## Decision criteria

The process must respect the four-active-agent limit, preserve the Wayfinder as
the sole strategic tracker, give Sol the admitted outcomes of the immediately
preceding investigations, retain negative results for duplicate avoidance,
and prevent untested factory proposals from being counted as proof movement or
automatically promoted into the frontier portfolio.

## Resolution

Adopt a **four-plus-one research generation**:

1. target four bounded investigation threads, while selecting fewer whenever
   the validated portfolio has fewer than four mathematically distinct
   executable gates;
2. admit and integrate every terminal result, updating the map, affected
   portfolio entries, this generation's ticket, idea statuses, negative
   knowledge, and timing records;
3. rebuild the deterministic whole-project Sol packet from that reconciled
   state;
4. run one max-effort factory batch requesting exactly five semantically new
   ideas from distinct mechanism families; and
5. route-review the factory backlog and result-generated follow-ups, reconcile
   admitted mechanisms into the canonical frontier portfolio, validate it,
   and choose the next slate from that portfolio alone.

A full four-thread slate consumes the concurrency budget as three delegated
workers plus one root-owned investigation.  Four is a capacity target rather
than a quota: never pad a slate with unadmitted, undefined, correlated, or
strategically inert work.  If fewer valid gates are ready, run the smaller
honest slate or pause for route grounding.  The factory is a serial refresh
after integration, not a fifth simultaneous slot and not one of the
investigations.  This guarantees that its prompt includes the newest results.
A provider or packet stop is recorded as an operational factory outcome and
does not undo the completed investigation slate.

Factory ideas remain proposal-level search information.  Scheduling one first
requires an explicit route decision that merges it into an existing `FP-NN`
entry or admits a stable new portfolio family with a destination consumer,
scope ceiling, bridge, obstruction, and bounded gate.  Its intake also records
a model tier, defined objects or an explicit grounding objective, cheapest
discriminating probe, predeclared outcomes, and prior-negative/duplicate check.
It does not require knowing in advance that the idea is true or useful.  The
idea ledger never schedules work directly.  By default no more than two
investigation slots may share one correlated mechanism family.  At least one
slot should be proof-producing when a credible theorem gate is executable; an
all-information slate must be identified and approved as exploration.

## Proof-distance accounting

- **Net proof movement:** neutral.
- **Evidence:** process decision informed by the terminal four-slot Ticket 0044
  slate and the successfully refreshed Batch 004 context.
- **Difficulty displaced:** none; no mathematical dependency is closed by a
  scheduling rule.
- **Counterfactual test:** applying this cadence before Ticket 0044 would not
  have shortened the proof, but it would have made the post-run packet refresh
  and next-slate selection explicit and repeatable.
- **Planning consequence:** use four-plus-one as the default capacity target,
  never as a padding requirement; retain flexibility to run a smaller slate or
  pause when readiness, measured throughput, provider limits, or the mix of
  proof-producing work supplies contrary evidence.
- **Load-bearing ledger:** no edge changed.

## Evidence

Ticket 0044 terminates all four selected investigations and reconciles their
outcomes.  The subsequent packet at
`runs/agents/20260819-sol-idea-loop/context-post-batch-004/` commits 7,520
artifacts plus this process decision, 50,341 Lean declarations, the updated
Wayfinder documents, the append-only idea ledger, prior batches, and admitted
run summaries/results.  Because this ticket is itself an indexed input, the
authoritative final counts and hashes live in that packet's
`packet-summary.json` and `manifest.json` rather than being copied back into
this ticket.
