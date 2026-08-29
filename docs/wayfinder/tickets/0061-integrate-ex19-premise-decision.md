---
title: Integrate the EX19 complete-premise decision
type: research
mode: HITL
status: closed
claim: codex-ex19-premise-unsat-integration-2026-08-21
blocked_by: none
---

# Ticket 0061: integrate the EX19 complete-premise decision

## Question

What does the approved Ticket 0060 execution establish after full formula
reconstruction and proof replay, and how should `FP-06`, `FP-09`, and
`FP-09.A` be reconciled without treating finite premise emptiness as a
successor theorem?

## Authorization and classification

The user approved Ticket 0060's complete plan, including its five-hour wall,
two-core generation/solver phases, conditional serial LRAT replays, and
conditional post-result provider review. The slate contained **zero
proof-producing and one information-gathering lane** and was exploration.

No tracked Lean theorem, external repository, dependency, system package,
network-fetched artifact, coordinate search, second solver seed, altered
formula, `k=11` instance, or certificate sequel was part of the run.

## Decision criteria

- `EX19-PREMISE-SAT`: at least one separately frozen formula has a complete
  model accepted by both semantic checkers.
- `EX19-PREMISE-UNSAT`: both formulas are independently reconstructed and
  their complete LRAT proofs replay to the empty clause.
- `EX19-ORIENTATION-SPLIT`: exactly one orientation is authenticated SAT and
  the other authenticated UNSAT.
- `EX19-INCONCLUSIVE`: at least one orientation remains undecided or lacks its
  predeclared evidence gate.
- `EX19-SEMANTIC-STOP` or `EX19-OPERATIONAL`: the Lean interpretation,
  producer/auditor agreement, controls, tool identity, or resources fail.

Every branch is neutral on the load-bearing proof ledger.

## Resolution

Outcome: `EX19-PREMISE-UNSAT`.

The two exact abstract Fin19 existential premise presentations are empty at
checked-computation level. They were not combined by reflection: each received
its own primary CNF, independent full semantic reconstruction, CaDiCaL run,
and serial LRAT replay.

| orientation | CNF SHA-256 | bytes | solver | LRAT evidence |
| --- | --- | ---: | --- | --- |
| `9+10` | `027dfc32ef5020b0a8089b5424f4de1c9120953ab0ee9b95e2bebe36da23fe82` | 300,443,017 | exit 20; 2.83 s; 413,920 KiB RSS | 308,001,582 bytes; 89,131 additions; 87,497 deletion lines; empty clause |
| `10+9` | `55eb805cbbfcb2d527a8cbc0cd7d9417678b73a30b506fa270e7c3585d380c4f` | 300,443,008 | exit 20; 2.59 s; 235,260 KiB RSS | 307,815,514 bytes; 88,526 additions; 87,414 deletion lines; empty clause |

Each formula has 8,721 variables, 141,678 clauses, and 50,116,884 literal
occurrences. The independent auditor computes triple and equality identifiers
by closed-form lexicographic ranks, imports no primary-encoder code, parses the
whole DIMACS file, and reconstructs every clause family. Both audits accept
the exact prospective counts, bytes, and hashes.

The LRAT traces have SHA-256 values
`e13a69fc07be21cddcb15d4ca092cd9085389391899c187a6325fdc0a04a00f4`
and
`3e0f015c9d02c4606b9b5b55cf159d35424cfcbb8aaa27f4b954d4fc34fb006f`.
The freshly built independent checker reaches the empty clause in 3.82 and
4.02 seconds respectively, using about 319 MiB peak RSS each.

This says only that no arbitrary `TripleColoring 19` satisfies either exact
complete-premise conjunction. It proves no exchange conclusion, realizability
claim, Lean emptiness theorem, induction base, uniform successor, or bound.

## Admission chain and trust boundary

The immutable task has base revision
`e1751075e5632c93a7b406136ed5d93b6fbe919e` and tracked admission fingerprint
`d28ecf8784903b3ce92772d257848dd60f30f9d22e5823281168a1fc7088891d`.
All ten declared input hashes and the base revision matched both before and
after execution. The solver banner is 1.7.3 and its observed binary SHA-256 is
`7b73df0a6d9cf3c751a1948300e5baff8e82c4d39bcd88f0c063b5f5cfb8b33e`.

Before formula generation:

- the run-local Lean file compiled the exact four exchange-cup absence
  consequences with only `propext`, `Classical.choice`, and `Quot.sound`;
- four model-checker control runs rejected incomplete assignments and forced
  cup-sign flips;
- the LRAT checker accepted a valid tiny contradiction and rejected a
  corrupted hint; and
- the independent formula auditor rejected a deleted cup unit and an altered
  literal in a 660-literal strong-set clause.

The producer and auditor authenticate the frozen prose-to-CNF semantics as
checked computation. There is no general Lean theorem proving this encoder
equivalent to the project predicates. Because the formulas were UNSAT, the
SAT checkers' complete-model branches did not run; the prospectively declared
UNSAT gate was instead independent full-formula reconstruction followed by
full proof replay. These are explicit trust and evidence ceilings, not hidden
proof claims.

The schema-valid terminal result and one-thread slate pass:

```text
python3 scripts/check_agent_orchestration.py \
  --task-packet runs/agents/20260821-ex19-premise-decision/task.json \
  --result runs/agents/20260821-ex19-premise-decision/result.json
python3 scripts/check_agent_slate.py \
  --slate runs/agents/20260821-ex19-premise-decision/slate.json
```

## Conditional route review and root adjudication

The exact result rules out a formula-defined finite subfamily, so Ticket
0060's conditional route review fired. The first Claude call returned a
transient HTTP 529 overload with zero output tokens. Root made one bounded
same-packet resume; the cached Sol result was not recomputed as mathematical
evidence. The complete reciprocal report uses evidence-packet SHA-256
`79c87ab18bd51aac127fa453409152160da3b6d7487f1ed0ae3dbd9bd0dd4398`
and report SHA-256
`8d931093906f6678928f12c2c3e056afd341caf9b40f5e95e7fb6bbd0d585a6e`.

All four advisory outputs require completion of the post-result artifact
chain before integration; root did so. They agree on the finite scope,
neutral ledger accounting, and no automatic descendant. They disagree on
whether `FP-09` should remain gated, become parked, or become suspended.

Root records `suspended`, for this explicit exhaustion argument:

1. Ticket 0050 showed the combined COM endpoint/target consumer is
   target-equivalent;
2. Ticket 0057 consumed the sole authorized rational family without one
   complete-premise case; and
3. this run checks that the exact complete abstract Fin19 premise itself is
   empty in both separately encoded presentations.

Thus the ordinary current continuations are consumed or invalid. Suspension
does not claim mechanism-wide refutation. A materially different premise or
successor mechanism can revive the entry only after it is stated exactly,
shown independently nonvacuous, connected to a noncollapsed consumer, and
given a bounded falsifier.

The review also proposed an order-reversal equivalence, single-block ablation,
and a Fin17 nonvacuity test. None was in the frozen packet; none was executed,
proved, or admitted. The two orientation results remain separate checked runs
but are not counted as independent mechanism-family evidence.

## Portfolio reconciliation

- `FP-06` remains `merged`. Its compiling finite `k=9` theorem is unchanged.
  EX19 does not establish or refute the Fin17 premise's nonvacuity, which must
  be explicit if a future consumer makes it load-bearing.
- `FP-09` changes from `gated` to `suspended`. Its scope ceiling now records
  compiling finite `k=9` theorems and checked finite `k=10` premise emptiness,
  not a symbolic successor. The current next gate is none; the revival package
  above is mandatory.
- `FP-09.A` remains an expired combined-extraction child. EX19 now rules out
  revival by another coordinate family satisfying the unchanged complete
  premise. A genuinely weaker nonvacuous premise and noncollapsed consumer are
  required.

No entry is promoted, no new child is admitted, and no failure is charged
beyond the formula-exact fixed Fin19 complete-premise subfamily.

## Proof-distance accounting

- **Net proof movement:** neutral.
- **Evidence:** compiling run-local semantic interface and independently
  reconstructed/replayed checked finite computation.
- **Damage scope:** `subfamily`, defined exactly as the two frozen complete
  Fin19 premise presentations. No one-block, ambient-premise,
  architecture-level, or mechanism-wide damage is claimed.
- **Difficulty displaced:** the finite complete-premise witness route is
  eliminated, but the missing uniform weaker extraction producer is unchanged
  and not demonstrably smaller.
- **Counterfactual test:** knowing this result earlier would prevent a second
  coordinate family, seed, or witness search under the same premise and would
  improve resource allocation. It would not reduce the estimated uniform
  proof work or probability by producing a closing mechanism.
- **Planning consequence:** suspend the exhausted current architecture and
  return to the serial post-integration factory boundary. Do not promote a
  refined descendant merely because this outcome supplied negative search
  information.
- **Load-bearing dependency changed:** none. `D-DECOMP` and every other open
  destination edge retain their prior status.

## Actual resources and timing

- Lean semantic smoke: 33.50 seconds, 5,299,396 KiB peak RSS.
- Two concurrent primary encoders: about 12.7 seconds wall, below 20 MiB RSS
  each.
- Two concurrent independent audits: about 68.4 seconds wall, below 19 MiB RSS
  each.
- Two concurrent solvers: 2.83 seconds critical-path wall, below 414 MiB RSS
  each.
- Two serial proof replays: 7.84 seconds total, below 319 MiB RSS each.
- Task-owned output: about 1.2 GiB.
- Whole execution and integration wall: recorded in
  `docs/agents/time-estimates.csv`; below the 90-minute low forecast and far
  below the five-hour hard wall.

Every phase remained under the approved CPU, memory, time, and output caps.

## Next boundary

The four-plus-one cadence now reaches its serial post-integration factory
boundary. Rebuilding the whole-project packet and running the next five-idea
factory batch were explicitly outside Ticket 0060 and are not performed here.
No execution slate is selected in this ticket.

## Evidence

- `runs/agents/20260821-ex19-premise-decision/`
- `runs/reviews/20260821-ex19-premise-integration-opus/REPORT.md`
- `docs/wayfinder/tickets/0060-plan-ex19-premise-decision.md`
- `docs/wayfinder/tickets/0059-select-post-batch008-slate.md`
