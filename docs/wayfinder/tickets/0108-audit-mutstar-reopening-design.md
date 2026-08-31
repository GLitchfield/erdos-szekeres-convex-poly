---
title: Audit the FP-01.D mutation-star reopening design
type: research
mode: HITL
status: closed
claim: mutstar-reopening-value-audit-2026-08-30
blocked_by: none
---

# Ticket 0108: audit the FP-01.D mutation-star reopening design

## Question

After Ticket 0107 selected an empty snapshot-specific slate, does the existing
`FP-01.D` mutation-star support chain have enough mathematical decision value
to justify a fresh author replay, non-author audit, semantic-readiness receipt,
and eventual real acquisition? If not, what stale lifecycle state must be
reconciled without executing the chain?

## Decision criteria

1. Reconstruct the exact package repair and independent-audit contracts without
   executing either one.
2. Distinguish technical packet readiness from a mathematically justified
   allocation under Tickets 0103 and 0107.
3. Apply the counterfactual test to every eventual acquisition branch, including
   the complete consumer ladder through the still-unapproved panel.
4. Reconcile spent identities and Ticket 0077's stale open status without
   treating historical approval as current authority.
5. Preserve `FP-01.D`'s candidate-local ceilings, the empty-slate decision, the
   service holds, and the load-bearing ledger unless authenticated evidence
   actually changes them.

## Evidence

### Baseline and frozen review

The user approved a design-only reopening audit on 2026-08-30. The baseline is
commit `cee3b9f9a0db199c9465179ee3e41656275134b1` on
`codex/state-578-tree-reservoir`. At launch,
`python3 -B scripts/wayfinder_status.py` reported no frontier or blocked
ticket, and `python3 -B scripts/check_frontier_portfolio.py` validated nineteen
entries: two completed, six gated, two merged, one parked, two retired, and six
suspended. No entry was `advancing`.

The four briefs are frozen under
`runs/agents/20260830-ticket0108-mutstar-reopening-design/ready/`. The context
container SHA-256 is
`9fe0c7e980254225848bfd26e0ec648ca78234fd72e21f8a604add471bb9215c`,
with embedded aggregate
`1ca65b6559e7d9274dfdd40e74be7813c80dd7c9bce5f4f4c5801322a8722aae`;
the manifest SHA-256 is
`91baf211b1a66ea94da39f5553df13bc6ab87d5ff6064544fb8fb7b681c578b4`.
The wave contains four parallel static audits and **zero proof-producing and
zero information-gathering mathematical investigations**. It authorized no
package, test, hostile replay, fixture, solver, Lean command, service action,
provider call, real mutation row, or canonical worker edit.

## Authenticated lane results

| Lane | Literal terminal | Result SHA-256 | Root disposition |
| --- | --- | --- | --- |
| package reconstruction | `PACKAGE-REPLAY-DESIGN-READY` | `e5dae3882d0831b837603cbc47f7885a3c8fa0222c6c3f48903c8c6f05eafe3d` | The five substantive sources are byte-identical to the admitted repair, and `test_synthetic.py` differs only by the two intended durable filenames. A fresh identity and non-lossy two-receipt design are technically possible; no replay is authorized. |
| independent audit design | `INDEPENDENT-AUDIT-DESIGN-READY` | `5dbaaad40cf6f8ab24823c0b58f6ab31017a4395c6a6706dbb4a399e5ba1bd80` | A later audit can snapshot-bind the successful fresh package, protected predecessor, and corrected marker and require two hostile replays. It is conditional on an author `READY` terminal and authorizes no real row. |
| mathematical decision value | `ACQUISITION-VALUE-INSUFFICIENT` | `8977cf0b2ded4b6e3fd84afc90681fbd1b81bf08e5a34e3035990d024711da40` | The support chain is a prerequisite to acquiring a prerequisite for a separately reviewed finite panel. Its branches do not shorten a proof obligation or change a load-bearing allocation. This terminal controls scheduling. |
| lifecycle and approval | `LIFECYCLE-RECONCILIATION-REQUIRED` | `78cc93b9e8fe31fc5a9122e40c874abb6115c376aa77ffe7fd6b0f928cb44a39` | Ticket 0077's machine-open state is stale; all of its authorities are consumed and later records control. Close it, retain the child gated, and stop before packet freeze. |

Root reproduced all four hashes and sole result paths, verified the context
capsule against its eight live baseline sources, reauthenticated the accepted
contract, excluded path, protected predecessor, latest author task/result, and
prior audit task/result, and independently compared the v1/v2 package bytes.
The exact test delta is the insertion of `implementation-report.md` and
`result.json` into test 99's sorted allowed-file list. Agent prose remains
proposal evidence.

The reports total 61,303 bytes. The interval from capsule creation to the last
result was about 9 minutes 34 seconds. CPU and RSS were not instrumented, so no
peak claim is made.

## Adjudication

The operational designs are coherent but are not selected. Their complete
consumer ladder is

```text
fresh author replay
  -> fresh non-author source/synthetic audit
  -> separate semantic-readiness receipt
  -> fixed 286-row acquisition
  -> authenticated off-path fixture, only on MUTSTAR-WINNER
  -> new panel review and user decision
  -> finite panel result
  -> still-missing uniform alternating-layer freeness producer
  -> PredecessorHalfSubsetAt
  -> D-HALF / D-UPPER
```

The first three arrows are operational prerequisites. The acquisition and
panel are search-information gates, not theorem producers. A
`MUTSTAR-WINNER` would make a new panel review eligible but would not test the
alternating support or reduce its uniform producer. `MUTSTAR-NONE` would expire
only the fixed-label, fixed-`x`, radius-one star. A mismatch or resource stop
would change no mathematical allocation. Thus even perfect foreknowledge of
the acquisition result would at most enable one more probe or prevent reuse of
one local acquisition candidate; it would not make the remaining proof work
demonstrably smaller.

Ticket 0103 permits at most one separately approved cheap falsifier when it can
change allocation. Here that falsifier is the later panel. The author, audit,
readiness, and acquisition stages merely determine whether the panel can be
formed. Ticket 0107 already resolved this distinction: its literal reopening
condition is an authenticated off-path fixture followed by panel review, and
it declined immediate package support as process work without a theorem-first
workload. No new mathematical observation, source theorem, producer memo, or
fixture has appeared since then.

The technically ready designs are retained as duplicate-avoidance information,
not as an execution slate. No task packet is frozen, no approval is requested,
and no bounded Sol/Fable route review is repeated because this ticket neither
selects nor redirects a main route. A future author chain would require new
evidence that changes this decision-value account or an explicit later policy
decision, followed by fresh immutable identities and approvals at every serial
boundary. Historical identities cannot be retried.

Ticket 0077 is closed in place. Its admitted implementation terminal and all
hashes remain historical evidence, but Tickets 0081/0082 and the later
`MUTSTAR-PACKAGE-V2-AUTHOR-REVISE` terminal supersede its scheduling authority.
This lifecycle correction removes one stale Wayfinder claim and changes no
mathematical evidence.

## Resolution and slate

`MUTSTAR-REOPENING-DESIGN-STOP__ACQUISITION-VALUE-INSUFFICIENT`.

The temporary execution slate remains:

- **proof-producing investigations:** 0;
- **information-gathering investigations:** 0.

`FP-01.D` remains `gated`. No advancing high-leverage entry is deferred, no
portfolio state or membership changes, and no load-bearing destination edge
changes. The scheduler remains intentionally stopped and the continuous idea
generator remains failed/stopped; neither was inspected, modified, or
restarted.

## Proof-distance accounting

- **Net proof movement:** `neutral`.
- **Evidence:** four authenticated proposal-level static audits and root byte/
  hash reconstruction; no theorem or new mathematical computation.
- **Damage scope:** `operational-only` for the package/lifecycle disposition.
  No new mathematical negative is admitted.
- **Difficulty displaced:** none. The authenticated off-path fixture, uniform
  alternating-support freeness theorem, `D-HALF`, and `D-UPPER` are unchanged
  and not demonstrably smaller.
- **Counterfactual test:** a real star result could stop this exact acquisition
  candidate or permit a panel review, but the support chain would not reduce
  the remaining formal proof work or close a named dependency.
- **Planning consequence:** retain the Ticket-0107 empty slate, close stale
  Ticket 0077, freeze no successor, and reconsider only after a literal
  reopening condition or a new decision-value premise is authenticated.
- **Load-bearing ledger edge changed:** none.

No mathematical negative is admitted, so no failure genome is created.
