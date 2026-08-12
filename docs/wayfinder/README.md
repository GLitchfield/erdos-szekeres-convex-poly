# Wayfinder for open-ended mathematics

This directory adapts Matt Pocock's Wayfinder framework into a durable
decision layer for long-horizon mathematical research. The upstream framework
charts decisions rather than an implementation backlog. This adaptation keeps
that principle while allowing a decision ticket to execute a bounded
computation when computation is the only honest way to resolve the question.

The layers have different jobs:

1. `map.md` is the low-resolution destination, decision index, fog, and scope
   boundary.
2. `frontier-portfolio.md` is the canonical inclusive registry of every
   currently credible progress thread, including gated, parked, suspended, and
   merged work. It is not an execution backlog.
3. `tickets/` stores one sharp decision or investigation per file.
4. `docs/experiments/`, `data/derived/`, proofs, and source code store evidence.
5. A project roadmap may narrate milestones, but the Wayfinder map and
   frontier portfolio are authoritative for strategic state.

## Frontier portfolio versus execution slate

The [frontier portfolio](frontier-portfolio.md) answers which threads remain
potentially valuable and what evidence would advance or expire them. It aims
for coverage: a credible thread stays recorded even when it is not selected
for immediate work.

An execution slate answers which small subset should consume the available
worker slots in a particular approved block. It aims for leverage under current
dependencies and resource constraints. Formally, the slate is a temporary
subset of the executable portfolio entries. Agent assignments, slot counts,
task packets, and wall-time estimates belong to the slate, not to the
portfolio. Selection does not promote a route, and omission does not demote
one.

The portfolio's required fields, state transitions, update rules, and
selection criteria are defined in its own file. Run
`python3 scripts/check_frontier_portfolio.py` after editing it.

## Ticket schema

```text
---
title: A human-readable decision name
type: research
mode: AFK
status: open
claim: unclaimed
blocked_by: none
---

## Question

...

## Decision criteria

...

## Resolution

Open.

## Evidence

...
```

Allowed types are `research`, `prototype`, `grilling`, and `task`. Allowed
modes are `AFK` and `HITL`. Status is `open` or `closed`. `blocked_by` is
`none` or a comma-separated list of ticket filenames.

The extra criteria and evidence sections are deliberate mathematical
adaptations. They make expensive or ambiguous investigations falsifiable
without turning tickets into ordinary to-do lists.

## Session protocol

1. Read `map.md` and `frontier-portfolio.md`, then run
   `python3 scripts/wayfinder_status.py` and
   `python3 scripts/check_frontier_portfolio.py`.
2. Select the first unclaimed frontier ticket unless the user names another.
   When planning a multi-thread work block, separately select an execution
   slate from the portfolio and cite the stable `FP-NN` identifiers.
   Claim it before substantive work.
3. Resolve one strategic ticket in the session, except explicitly parallel
   research tickets.
4. Before a strategic selection, redirection, closure, or frontier promotion,
   run a bounded Sol/Fable review of the proposed decision and selected
   evidence.
5. Address material review objections with mathematics, computation, or a
   sharper scope. Model agreement is never itself a resolution.
6. Put detailed reasoning in the ticket, close it, and add one linked gist to
   `Decisions so far`.
7. Create newly sharp tickets and wire blockers. Keep indistinct future work in
   the fog.
8. Run `make test`, commit, and push the decision state with its evidence.

## Planning and execution

Wayfinder plans by default. A mathematical project may carry execution inside
the map because an experiment often resolves the decision. Such a ticket must
state:

- the uncertainty being resolved;
- deterministic inputs and conventions;
- the resource and search bound;
- success and advancement criteria;
- redirection criteria;
- precision- or verification-limited criteria;
- closure criteria and the scope of a negative result; and
- the independent certificate that will support the conclusion.

A long run with no declared decision payoff does not belong on the frontier.
Routine implementation required by an already-made decision does not need a
new strategic ticket.

## Integrated Sol/Fable boundary

`scripts/adversarial_review.py` gives two models the same explicit, read-only
evidence packet. Use it at the point where the map could otherwise become
self-confirming: route selection, route closure, redirection, and promotion of
a new frontier.

The review packet should contain the sharp question, ticket criteria, compact
evidence, and proposed consequence. Inspect blind reviews before reciprocal
critiques. Record the packet hash and the disposition of material concerns in
the ticket.

Sol/Fable output is advisory planning evidence. It cannot prove a theorem,
certify a numerical computation, replace a primary source, establish
exhaustiveness, or authorize external actions. The mathematical evidence layer
remains independent.

## Fog and scope

Ticket a question when it is already sharp, even if blocked. Keep it in `Not
yet specified` when it cannot yet be phrased precisely. Work beyond the
destination belongs in `Out of scope`; if an existing ticket is revealed as
mis-scoped, close it and link it there rather than recording it as a decision
on the route.

## Attribution

Adapted from Matt Pocock's Wayfinder skill under the MIT License. See `NOTICE`.
