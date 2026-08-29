# Continuous idea generator

Ticket 0083 supersedes Ticket 0079's one-reserve protocol. The evidence-first
campaign's seed stage now runs as a bounded, self-refilling, chat-independent
service. Its single mathematical job is to maintain an immutable inbox of
proposal-level seed batches for later root review. It is not an autonomous
research director.

## Authority boundary

One standing authorization binds the daemon entrypoint, packet builder,
campaign validator, seed schema, Codex CLI version, provider, generation modes,
resource ceilings, rate limits, inbox
high-water marks, circuit breakers, and total invocation cap. Within that
closed envelope the service may repeatedly:

1. rebuild a fresh whole-project snapshot from current repository bytes;
2. freeze a new campaign identity, prompt, task, output schema, and packet;
3. authenticate those receipts and launch exactly one read-only Sol call;
4. validate the returned seed batch, remove only deterministic literal
   semantic-core duplicates, and preserve immutable receipts; and
5. continue after the cooldown while inbox and standing-budget capacity remain.

It may inspect the repository read-only and use live primary-source web search.
It may not run a seed's first test, edit Lean or canonical documentation, admit
or schedule a route, assign proof movement, consume or reconcile its own inbox,
spawn subagents, mutate Git, or retry an attempted packet. Root alone performs
semantic duplicate review, evidence admission, failure-genome reconciliation,
portfolio changes, and execution selection.

Each attempt writes `attempt.json` before provider process creation. That exact
packet can never be invoked again, including after a daemon or WSL restart. A
later cycle always has a new campaign identity and snapshot. Two consecutive
provider stops or two consecutive zero-seed novelty stops open a circuit rather
than silently spending through a repeated failure.

## Version-two standing envelope

- provider: `gpt-5.6-sol` at `max` reasoning effort;
- concurrency: one provider job and no subagents;
- per-call ceiling: 90 minutes, 2 local CPU cores, 4 GiB local process-tree
  RSS, and 0.05 GiB captured output;
- provider sandbox: read-only, noninteractive, ephemeral, with live web search;
- cadence: at most six calls in any rolling 24 hours and at least 30 minutes
  between completed calls;
- standing ceiling: 100 provider invocations;
- inbox high water: ten unreconciled batches or fifty seeds, whichever arrives
  first;
- circuit breakers: two consecutive provider stops or two consecutive
  zero-seed batches;
- generation rotation: `context_rich`, `failure_dual`, then `recombination`;
- output: the canonical research-seed schema plus immutable provider,
  deterministic-dedup, packet, and admission receipts; and
- retry: never for an attempted packet.

The high-water and rate limits make “continuous” event-driven rather than a
blind infinite loop. Consuming a root-reconciled batch automatically releases
capacity; no new chat action is needed. Configured ceilings may be tightened
but never weakened. Changing the implementation, model,
effort, modes, ceilings, or authority invalidates the standing receipt and
requires a new explicit authorization.

## Duplicate and failure memory

Every new coordinator snapshot includes all earlier validated continuous seed
batches, including unreconciled ones, in `prior-idea-registry.json`. Those
entries are duplicate-avoidance memory only and never positive evidence. After
the provider returns, the service computes a normalized fingerprint from each
seed's target, model, mechanism, and first-test question. Exact repeats are
removed and recorded in `dedup-report.json`; the batch becomes a novelty stop
when fewer than five remain. Target equivalence and failure-genome scope are
mathematical judgments and remain root-only.

## Operator commands

Freeze one standing authorization after its limits receive user approval:

```text
python3 scripts/continuous_idea_generator.py configure \
  --approval-ref <literal-approval-reference>
```

Start the persistent service with that exact receipt:

```text
python3 scripts/continuous_idea_generator.py start \
  --authorization <versioned-authorization-path-from-configure> \
  --authorization-sha256 <sha256>
```

The service immediately freezes and queues its own first cycle. Inspect it
without changing state:

```text
python3 scripts/continuous_idea_generator.py status
```

After root has checked and reconciled a batch, release only that inbox item:

```text
python3 scripts/continuous_idea_generator.py consume \
  --campaign-id <campaign> \
  --seed-batch-sha256 <sha256> \
  --reconciliation-ref <canonical-ticket-or-ledger-reference>
```

Graceful stop disables the persistent unit and terminates only its own provider
control group:

```text
python3 scripts/continuous_idea_generator.py stop --reason <reason>
```

The stable state lives under `runs/agents/continuous-idea-generator/`. A linked
and enabled user-systemd unit owns the daemon, restarts it after process
failure, and starts it again with the user service manager after WSL restart.
The unit enforces a 5 GiB cgroup memory ceiling, two-core CPU quota, bounded
task count, and control-group shutdown. The standing authorization's exact
implementation-set hashes prevent old or modified daemon, builder, validator,
or schema code from consuming its authority. Authorizations are immutable,
versioned files; a separate active pointer may be rotated only while the daemon
is stopped, so earlier packet receipts remain replayable.

Provider recovery authenticates the Linux boot identifier, process start
ticks, PID, and process group before attaching to a still-live child. A reused
PID is never followed or killed. Recovered children remain subject to the
original wall, RSS, output, and stop ceilings; a recorded attempt is finalized
without retry when its exact child no longer exists.

## Admission boundary

Every `seed-batch.json` is proposal-level search information. Root must run

```text
python3 scripts/check_research_campaign.py --seed-batch <path>
```

and then perform the ordinary stale-snapshot, semantic-duplicate, model-tier,
source, failure-memory, and route review. Daemon uptime, batch count, provider
agreement, or deterministic literal deduplication changes no load-bearing
dependency or portfolio state.
