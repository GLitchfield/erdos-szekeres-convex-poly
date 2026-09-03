---
title: Execute the rolling common-anchor leaf wave
type: research
mode: HITL
status: closed
claim: common-anchor-rolling-leaf-wave-closed-2026-09-01
blocked_by: none
---

# Ticket 0129: execute the rolling common-anchor leaf wave

## Question

Can the source-clean common-anchor actual-placement inventory be reduced by
executing corrected placement `24` and then placement `14`, while parallel
read-only lanes freeze the remaining dual leaves and router boundary far enough
ahead to avoid item-by-item planning?

The user approved this rolling wave after reviewing its contingent horizon.
This approval covers only the exact root execution stages and read-only lanes
below.  It does not authorize a provider call, scheduler or idea-generator
action, external mutation, commit, push, or a Lean implementation whose exact
contract was not frozen before this ticket was claimed.

## Decision criteria

1. Preserve the exact corrected-`24` contract and its single diagnostic gate.
2. Serialize every canonical Lean write at root while delegated lanes remain
   read-only and hash-frozen.
3. Continue to placement `14` only after an exact packet authenticates against
   the post-`24` source and no shared-source stop occurred.
4. Treat `23`, `34`, and the router as planning outputs until their exact
   theorem contracts and source baselines are frozen.
5. Admit no source candidate as a theorem before the guarded Makefile path.

## Evidence

### Frozen snapshot

- `AGENTS.md`: `83bb11d556180c2fd9bab8a29ba928667a7ae69da029d370ad32dbcc28bcbb40`
- canonical Lean source:
  `17ebe8718f977b2c0d69640e3c8d5bb6fa3edb55c06b957bd26bd768797a971d`
- Wayfinder map:
  `c7a1ad7f3333f56314af1c3852c525dc4a9965ee412bcd57f143f76f02669346`
- frontier portfolio:
  `868f7640006992e7fa58baf0e56a09679b88fa4b93c519f5bdb39d7ffce68f5f`
- Ticket 0128:
  `36c8521f501a1b68ff1aef31e96cea6f585dae707e816ec1fd88aec4caeb9cb7`
- corrected-`24` execution plan:
  `c7ebe04a16a393fda7f90b5fc09a26481cdc5c9b1d8b754e524f300dc74ee69e`
- current-`14` theorem-entry review:
  `efb29f5008a9ab49c8eba208fdf432ce5a50a7fbe86d47c4f0c4b9d015f03e72`
- current-`04` theorem-entry review:
  `b7be1995b1f841223ca5ed2fffb9eb54ba89e6951500a94cc0b04fd9baa3d0e3`

The run snapshot and delegated briefs live under
`runs/agents/20260901-ticket0129-rolling-common-anchor-wave/`.

The completed evidence is:

- C016 result `GAP24-LSP-CLEAN-SOURCE-CANDIDATE`, SHA-256
  `04038b862f7b7c572fb674e285e9061012e1d11eda3b2ce4c43ca6cfbf1e2a82`;
- C017 result `GAP14-LSP-ELABORATED-WITH-WARNINGS`;
- placement-`14` executable-packet review, SHA-256
  `0d46307562d52a09b04827177a01eb1bc5b47cb4ebc8f6bf59f9521b76580f9a`;
- placement-`23`/`34` theorem-entry review, SHA-256
  `d7f31dc63eec9d05880fac9e681fa8e4e900201883bd9ef7363b351e7c818e82`;
- router preflight, SHA-256
  `008455e2dca9fea6f06b49fe83737b84036f980ad56f7b63f7bc169552186726`;
- final canonical Lean source SHA-256
  `15b4988978224288cc84c7313e38d1381acbf63c6b6434016ec15ea2dcab520b`.

## Temporary execution slate

The four active slots are one root-owned proof pass and three delegated
read-only audits:

| Lane | Label | Exact boundary |
| --- | --- | --- |
| root `C016` | information-gathering | execute the frozen corrected placement-`24` plan with one declaration-scoped diagnostic |
| placement `14` | information-gathering | freeze an exact execution packet; root may execute it serially only after that packet authenticates and no shared-source stop occurred |
| placements `23`/`34` | information-gathering | freeze five-field theorem-entry packets or exact blockers; no Lean edit |
| all-placement router | information-gathering | inventory producers and freeze the consumer boundary; no Lean edit |

This is an exploration slate with zero admitted `proof-producing` slots and
four `information-gathering` slots.  It deliberately exceeds the default
same-family concentration because all four lanes discharge distinct immediate
producer questions for one finite all-placement router; the shared Lean writer
is serialized at root, and no result is treated as failure-independent merely
because it ran in another lane.

## Resolution

The approved slate and contingent horizon completed without a source,
dependency, or mathematical stop.

### Dependency-ordered horizon

1. Execute `C016-DHALF-GAP24-WORD-FIX-V1` exactly as frozen.  A clean source
   diagnostic retains the candidate; an error follows the packet's exact
   rollback and terminal.  No repair or second Lean call occurs inside C016.
2. In parallel, complete the three read-only packets above.
3. If and only if the placement-`14` packet is theorem-entry complete, its
   source baseline matches the post-C016 source, and C016 exposed no shared
   source/dependency defect, root may freeze and run placement `14` as a new
   identity with its own single declaration-scoped diagnostic.  This is a
   serial next stage, not an in-packet fallback for C016.
4. Placement `23`, placement `34`, and the router remain planning outputs in
   this wave.  They may not receive Lean edits until their exact contracts,
   proof plans, and source baselines are frozen in a later approved execution
   slate.
5. Only after all selected leaf candidates are source-clean may a later slate
   assemble the router and run one guarded Makefile admission gate for the
   package.  No repetitive project testing is authorized here.

## Stops and accounting

Stop automatic continuation on theorem-contract drift, a premise or model-tier
change, a shared mathematical obstruction, an architecture-level failure, a
request for broader resources or authority, source-hash drift not caused by
the serialized root declaration, or the absence of a qualified exact packet.

At reconciliation, report net proof movement, evidence level, damage scope,
difficulty displaced, counterfactual test, planning consequence, actual wall
time, and the exact load-bearing ledger edge changed or unchanged.  No source
proposal counts as a completed theorem before the guarded Makefile build path
admits it.

### Final reconciliation

C016 and C017 each passed their sole declaration-scoped diagnostic with no
errors, timeout, partial result, or failed dependency.  C016 reported five and
C017 six unused-`or_assoc` warnings; neither received a cleanup pass.  The
proposal-level actual-placement deficit changes `4 -> 2`, leaving only `23`
and `34`; the contradiction deficit changes `1 -> 0`, and the dual deficit
changes `3 -> 2`.

Both remaining dual leaves are theorem-entry complete at proposal level, with
`23` the smaller two-word equality-head continuation and `34` the larger
six-word, three-branch reversal.  The router preflight confirms that the leaf
inventory is not its only blocker: exact tag/swap, `AnchorSelectsTag`,
uniqueness, and pair-classifier producers are also absent.  The router is not
executable in the current bytes.

- **Net proof movement:** `neutral`.
- **Evidence:** two LSP-clean source proposals and three authenticated static
  reviews; no guarded project build or completed theorem.
- **Damage scope:** `candidate-local` evidence ceiling only; no negative
  mathematical damage is admitted.
- **Difficulty displaced:** source implementation work is smaller by two
  literal leaves and the contradiction-source subfamily is complete, but the
  two dual leaves, router helpers, router, closure, adaptive consumer,
  full-context successor, uniform tail, and guarded admission remain.
- **Counterfactual test:** the wave removes two exact source implementations
  and exposes the router-helper boundary, improving the next allocation, but
  it does not reduce admitted dependency depth before the guarded build.
- **Planning consequence:** retain `FP-01` and `FP-03` as gated; freeze the
  next serial execution wave in order `23`, then `34`, while separately
  designing the router-helper producers.  Do not attempt the router after the
  leaves alone.
- **Load-bearing ledger:** no edge changed.
- **Failure genome:** none.

Measured lane walls were 40 seconds for C016, 19 seconds for C017, 2 minutes
54 seconds for the post-C016 `14` packet, 8 minutes 5 seconds for the `23`/`34`
entry audit, and 2 minutes 10 seconds for router preflight.  CPU time and peak
RSS were not instrumented and are not estimated.
