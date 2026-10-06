# Complete the small-history internal chosen-kept cut at k=6

This is a fresh authorized Sol/xhigh research run. It is not a resume of the
September 22 native thread, which is frozen `paused_by_user` and must never be
resumed. Root must fill the launch clock after its final package review and
submit exactly one new host.

- Overall start: `2026-09-23T01:26:15Z` (goal selection and launch setup)
- Overall hard stop: `2026-09-23T14:40:00Z` (includes bounded finalization and review)
- Native research cutoff: no later than `2026-09-23T13:40:00Z`; the host freezes its exact earlier deadline at pickup
- Native finalization hard stop: no later than `2026-09-23T14:10:00Z`; the host freezes its exact earlier deadline at pickup
- Host hours: `12` native research hours, followed by the existing bounded
  finalization policy; recovery never extends either deadline
- Model and effort: `gpt-5.6-sol`, `xhigh`
- Root coordinator thread: `01a0b62b-4802-7872-9bb7-709aa9951ac2`
- New native thread/job/window: record after the single submission

## Frozen baseline and scope

Work only in
`/home/gavin/git/erdos-szekeres-convex-poly/runs/worktrees/sol-12h-20260916`.
The reviewed clean baseline is
`21b999f5f6041f69c0d359ed421be789688d17b6`, currently on
`node/CtxTwoActualMarkerOppositeBetweenCompanionElevenBound`. Preserve all
September 22 receipts and the shared Lean cache. Do not touch the unrelated
primary checkout changes.

Read before changing mathematics:

- `/home/gavin/git/erdos-szekeres-convex-poly/AGENTS.md`;
- primary `runs/straddling-companion-20260922/TERMINAL-REVIEW.sol.md`;
- primary `runs/straddling-companion-20260922/REPORT.md`;
- primary `runs/sol-12h-20260923/GOAL-OPTIONS.md`;
- this checkout's
  `runs/straddling-companion-20260922/FINAL-HANDOFF.md` and
  `ConsumerInterfaceSmoke.lean`.

The only primary outcome is a compiling theorem for the complete
small-history, internally bracketed, chosen-kept actual cut at `k=6`, proving
both the independently fueled and full sum are at most twelve. The
older-exterior placement is the central mathematical obstruction. A theorem
that merely repackages the compiled between-marker case, assumes the missing
numerical inequality, or reproves the opposite-kept orientation does not
satisfy the goal.

## Exact target interface

Use the repository's explicit side-selected `match` expressions in the actual
Lean declaration. The intended theorem is equivalent to:

```lean
theorem ctx_two_actual_marker_small_history_internal_chosen_kept_cut_six_bound
    (σ : Ctx.Context)
    (hpositive : ∀ p j v,
      σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
    (s t : Ctx.Side) (hne : s ≠ t)
    (N M x y : ℕ)
    (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M)
    (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s)
    (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M)
    (hchosenGlobal :
      (match s with | .lower => σ.u | .upper => σ.a) ≤ 5)
    (hoppositeLower :
      2 ≤ (match t with | .lower => σ.u | .upper => σ.a))
    (hopposite :
      (match t with | .lower => σ.u | .upper => σ.a) ≤ 5)
    (hchosen : ∀ j ∈ σ.levelsOn s 0,
      ∀ z ∈ σ.extPositions j, z = x ∨ z = y)
    (hmax : ∀ j ∈ σ.levelsOn s 0, σ.maximumAt j ≤ 1)
    (keep : List ℕ) (q₀ l r m n : ℕ)
    (hq₀ : q₀ ∈ keep)
    (hkeep : ∀ p ∈ keep, p ∈ σ.childPositions)
    (hl : l ∈ σ.childPositions) (hr : r ∈ σ.childPositions)
    (hlnot : l ∉ keep) (hrnot : r ∉ keep)
    (hinside : ∀ p ∈ keep, l < p ∧ p < r)
    (hconvex : ∀ p ∈ keep, ∀ q ∈ keep,
      ∀ z ∈ σ.childPositions, p ≤ z → z ≤ q → z ∈ keep)
    (hm : m + 2 = σ.k) (hk : σ.k = 6)
    (hn : 1 ≤ n) (hcoupling : m + n = σ.k - 1) :
  let rest := σ.childPositions.filter (· ∉ keep)
  (∀ f g,
      Ctx.Context.boundFuel f (σ.part keep s m) +
      Ctx.Context.boundFuel g (σ.part rest t n) ≤ 12) ∧
    (σ.part keep s m).bound + (σ.part rest t n).bound ≤ 12
```

Minor hypothesis changes are allowed only when source inspection proves the
consumer supplies them or a counterexample proves this exact statement false.
Log the reason before restating. Preserve independent fuel, the actual `part`
contexts, arbitrary opposite indexed history, inactive children, and the
legal coupling. Do not strengthen the result to `B ≤ 11` unless it follows;
the coupled sum may use a charge shared between the two parts.

With

```text
A    := σ.part keep s m
rest := σ.childPositions.filter (· ∉ keep)
B    := σ.part rest t n,
```

the equations give `m=4`, `n=1`, and the compiled sibling-maximum theorem
gives `A≤1`. The small-history classifier gives either the whole cut at most
eleven or an active chosen-capacity-three `high`, an active
capacity-at-most-two `low`, and the oriented relation `low<y<high` or its
reverse. The target should consume that classifier internally so its public
interface does not expose `high`, `low`, placement, or pair supports.

## Compiled boundary to reuse

Search and inspect the exact declarations before proof work:

- `ctx_extreme_cut_six_small_history_mixed_capacity_residual_classification`;
- `ctx_extreme_cut_six_twelve_of_large_chosen_history_maximum`;
- `ctx_bound_le_one_of_large_sibling_maximum`;
- `ctx_two_actual_marker_opposite_between_companion_eleven_bound`, type hash
  `921f91ce0bd5254e`, for a retained child strictly between `x,y`;
- `CtxTwoActualMarkerOppositeBoundaryCompanionNineBound` for endpoint blocks;
- `ctx_two_marker_older_exterior_internal_interval_cut_potential_bound` and
  `ctx_two_marker_internal_interval_cut_potential_bound`, which give only
  `P(4)=13` in the chosen-kept orientation;
- `ctx_two_actual_marker_saturated_nonunit_bracketed_cut_bound`, useful only
  in its stated clear-history/top-band nonunit regime;
- `ctx_two_marker_opposite_kept_block_cut_six_bound`, type hash
  `9d6e22634a9072a4`, and
  `ctx_two_marker_internal_complement_cut_six_bound`, which completely solve
  the reverse recurrence orientation
  `part rest s m + part keep t n` and are not the target.

The September 22 theorem is compiled, sorry-free, replayed, and extracted at
this baseline. Its proof actually uses the physical between placement and
actual companion construction; `hchosen`, `high`, and its capacity premises
remain unused. Reuse it rather than rebuilding its rank-pair proof.

## Placement map and central obstruction

For an internal convex retained block bracketed by complementary children:

1. If some retained child lies strictly between `x,y`, call the compiled
   between-companion theorem and combine `B≤11` with `A≤1`.
2. If no retained child is between the markers but a retained child lies in
   the younger exterior, the compiled run split has spatial regions of
   cardinalities `3+8` or `8+3`; this yields `B≤11`. This proof is derived but
   not yet compiled.
3. If every retained child lies beyond the older marker,
   `(x<y ∧ ∀p∈keep, y<p) ∨ (y<x ∧ ∀p∈keep, p<y)`, the known independent
   companion split gives only `8+6=14` or `6+8`, while the general coupled
   potential gives 13. This is the real gap. There is no known counterexample
   to the desired coupled sum or to `B≤11`; the failed number is an upper bound
   from naive independent accounting, not a refutation.

Investigate whether the residual classifier's oriented `low<y<high` witness,
convexity and the bracketing children force a rank-pair collision, end
reservation, or recurrence charge shared with `A`. A valid coupled proof can
show `A+B≤12` directly and need not force `B≤11`.

## Phased priorities

### Phase 0: admission and exact statement

Run `es status`, `es ready`, and `es search` again. If the index is stale, use
`es extract` before choosing work. Claim
`ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end` before research.
Create one fresh branch
`node/CtxTwoActualMarkerSmallHistoryInternalChosenKeptCutSixBound`. Add the new
statement only with `es node add`, then claim that node. Never edit a statement
by hand; use `es node restate` only after a logged mathematical reason. A PR
closes exactly this node.

### Phase 1: older-exterior proof-or-refutation audit

Spend the first serious block on the older-exterior residual before writing
mechanical placement wrappers. Unfold the exact `boundFuel` recurrence and
compare the existing 13-bound proof, the compiled opposite-kept
older-exterior proof, and the residual classifier witnesses. State on paper
the exact charge saving. If a faithful small witness refutes the proposed
theorem, preserve it, log the method change, and restate the smallest true
consumer-supplied hypothesis rather than assuming the desired inequality.

### Phase 2: formalize the hard lemma

Formalize the smallest reusable coupled lemma for the older-exterior residual.
Search before every new lemma. Keep candidate proof bodies in the run
directory and use `es proof capture/check/prove` when applicable. Compile only
through `es build`, `es check`, or `es node finish`; never use bare
`lake build`. Do not add axioms, `native_decide`, `unsafe`, or unallowlisted
`sorry`.

### Phase 3: assemble the complete target

Case the retained block relative to `x,y`. Reuse the compiled between theorem.
For younger exterior, reuse its run split and change only the spatial
inclusions to the `3+8` regions. Assemble every placement into the exact
target and check both independent fuel and full bound. A wrapper is useful
only after the older branch is genuinely discharged.

### Phase 4: receipt and finalization

Run a targeted `es check` for the new node, then `es node finish --policy
review --extract-memory 28G` or the current equivalent to validate, insert,
fully extract, audit, and prepare review. Capture the accepted body, source and
dependency identities, exact axioms, type hash, job IDs, commit IDs, and clean
tree. A successful process exit, fixture, smoke file, or run inventory alone
does not earn theorem credit. Make a consumer smoke only if it tests a real
interface risk.

Stop research once a compiled checked theorem is obtained. Reserve the final
clock segment for source/receipt review, `es run handoff`, usage sync, code and
library review, clean committed-tree replay where needed, and a precise
`FINAL-HANDOFF.md`. When the primary theorem and all required review are
actually complete, mark the native goal complete and end the native turn; do
not poll the run watcher or wait out unused research time. Do not leave an
active claim or live child job at terminal handoff.

## Meaningful fallback

If the older-exterior audit reaches a documented impasse within the bounded
exploration, make one logged method change and prove

```text
ctx_two_actual_marker_opposite_younger_exterior_companion_eleven_bound
```

with the exact public interface of the compiled between theorem, replacing
`hbetween` by

```text
(p < x ∧ x < y) ∨ (y < x ∧ x < p).
```

The proof uses the same actual run decomposition and the explicit pair regions
`Q([1,2])` of cardinality 3 and
`Q([1,2]) ∪ Q([2,4])` of cardinality 8. This fallback must compile and receive
the same proof checks. Report it as partial: it leaves the older-exterior
coupled obstruction and the parent open. Do not use the fallback merely to
avoid auditing the selected primary obstruction, and do not spend the run on
a between-marker consumer wrapper alone.

## Finite probes and shared library

The setup `es search` found no existing declaration matching the complete
target. `es lib search` found and `es lib show` inspected:

- `research.recursive-bounds`;
- `workflow.recursive-cut-probe`;
- `decomposable.context-limits`.

Prefer `es probe run/replay` and these catalogued implementations. Do not write
new Python or workflow glue before another exact `es lib search/show` and a
source search. Every finite result must record its domain, semantics, source
hash, arguments, cap, and output. The registered recursive evaluators are
exploratory: `context-bound-zero-children-v1` is not certified equivalent to
Lean, and the registered two-marker domain explicitly grants neither Lean
refutation nor proof credit. A bounded negative search cannot establish the
theorem. Preserve a concrete positive counterexample candidate for replay and
Lean checking before treating it as a refutation.

At run end Astra must review any run-local code or inline commands and decide
whether to reuse, promote, or defer. Do not generalize one-off mathematics to
grow the library.

## Resource and execution discipline

The shared live-job budget is 30G. The native host reserves 2G, ordinary builds
reserve 20G, full extraction/finalization may reserve 28G, and the configured
retry/final cap is 30G. Do not start a 30G stage while the 2G host is live.
The 28G final stage exactly fills the shared budget with the host, so ensure no
other live reservation and use the harness's explicit outer guard. If a true
30G stage is required, stop or finish the host first. Never silently lower a
cap to force admission.

Every command expected to exceed one minute must use `es job run` with a
purpose, exact output under this run directory, node when available, memory
cap, CPU cap if useful, and wall budget. Keep the reporting turn open through
terminal status and inspect outputs. Preserve failed jobs and commands.

The root coordinator submits exactly once from this mathematical checkout:

```text
ES_AGENT=codex:01a0b62b-4802-7872-9bb7-709aa9951ac2 tools/es/bin/es run agent \
  --out runs/sol-12h-20260923/host \
  --prompt runs/sol-12h-20260923/native-goal.md \
  --model gpt-5.6-sol --effort xhigh \
  --hours 12
```

Do not retry an uncertain submission. Record its JSON, confirm worker pickup,
register the monitor window, and verify the exact root thread with
`es delivery verify --thread "$CODEX_THREAD_ID"`; callback readiness requires
the returned challenge through that client. On terminal state, use
`es run review runs/sol-12h-20260923/host --artifact-root
runs/sol-12h-20260923`, then independently inspect proof receipts and changed
code before granting credit.

## Setup evidence

At package creation the index was fresh: 306 closed, 12 open, one refuted,
zero stale entries and zero problems. The parent was ready/open. There were no
queued, starting, or running jobs and no active claims. The checkout was clean
at the frozen HEAD. Physical storage had 437,620,895,744 bytes and 64,999,625
inodes free. The shared `.lake` tree was approximately 130.6 GB and is already
backed by the reviewed hard-linked cache; do not copy or clean it.

Direct user-bus access from setup was unavailable. Guarded queued probe
`20260922-212729-d7d672` completed in 0.2 seconds at 92 MiB under a 128M cap and
confirmed ordinary worker PID 492743, active/running since September 18,
working in the primary checkout with Codex 0.155.1 and Node 24.14.0. No host,
claim, checkout, branch, build, extraction, or tracked source edit was made in
preparation.
