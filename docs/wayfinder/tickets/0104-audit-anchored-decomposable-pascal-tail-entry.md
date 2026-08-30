---
title: Audit an anchored decomposable Pascal-tail theorem entry
type: research
mode: HITL
status: closed
claim: anchored-decomposable-pascal-entry-audit-2026-08-30
blocked_by: none
---

# Ticket 0104: audit an anchored decomposable Pascal-tail theorem entry

## Question

Does the first post-Ticket-0103 `D-DECOMP` design block expose a natural
boundary-aware theorem with an independently smaller producer and the existing
Pascal-tail consumer, so that a proof-producing Lean packet can honestly be
frozen?

## Decision criteria

1. Reconstruct the exact existing arithmetic reduction and named downstream
   consumer before proposing another theorem.
2. State the candidate producer at its honest model tier and reject any
   interface whose conclusion merely renames the open cardinal bound.
3. Exhibit a strict recursive measure decrease or independently smaller
   obligation before labeling the item proof-producing.
4. Test the proposed information against every relevant admitted collision and
   the expired state-567 proof-mining controls.
5. Freeze a Lean packet only if all five Ticket 0103 theorem-entry fields pass;
   otherwise close at a bounded route-design stop and reconcile `FP-03`.

## Approved boundary and baseline

The user approved one bounded 60--90 minute theorem-entry design block after
the Ticket 0102/0103 checkpoint.  The checkpoint is commit
`d8662215c6a4d45bd0428226b40b6bebc995752d` on
`codex/state-578-tree-reservoir`; its guarded `make test` completed all 11,753
Lean jobs and 348 workflow tests before this audit.  This ticket authorizes no
Lean implementation, finite search, provider call, service action, or later
execution slate.

The audit reads the current theorem interfaces and admitted controls in
`Decomposable.lean`, `StructuralChargingPascalTails.lean`,
`StructuralChargingPascalTailGates.lean`, `RankProfileCollision.lean`,
`TurnLanguageCollision.lean`, `IncomingStarPrefixCollision.lean`, and
`IncomingStarTransitionCollision.lean`.  Repository theorems and previously
admitted evidence are the source of truth; no new computational or source
claim is introduced here.

## Evidence

The evidence admitted by this ticket is the checked repository state at the
baseline above: compiling theorem signatures and proofs, the current
load-bearing dependency ledger, and hostile controls already reconciled in
`FP-03`.  The candidate theorem below and its proposed address mechanism remain
proposal-level analysis; they are not new Lean declarations or mathematical
results.

## Structural position reconstructed

The all-parameter arithmetic reduction is already present.  Strict predecessor
states plus lower and upper singleton Pascal-tail gates close every active
critical root, and `criticalRootImpossible_of_predecessors_pascal_twoSide_bounds`
provides a uniform consumer for ordered two-side bounds.  The first open
specialization is not an arithmetic recurrence: by
`pascalTailTwoSideBound_567_iff`, `PascalTailTwoSideBound 5 6 7` is exactly the
open `TwoCapFreeSidesBound567` cardinal bound.

The current consumer discards useful structure at one precise point.  Its
singleton-root input already contains `IsDecomposableOn χ upper`, but after
partitioning `upper` at the anchor `q` into `left` and `right`, it invokes
`PascalTailTwoSideBound`, whose model tier is an arbitrary `OneChangeOn`
coloring.  Since the proof also establishes `left ∪ right = upper`, the
decomposability premise is available and need not be forgotten.

## Five-field theorem-entry memo

### 1. Exact producer theorem and model tier

The narrow bridge that can be stated without invention is the following
decomposable-only weakening of the current two-side interface:

```lean
def DecomposablePascalTailTwoSideBound (a u k : ℕ) : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n}
      {left right : Finset (Fin n)},
    Disjoint left right →
    (∀ x ∈ left, ∀ y ∈ right, x < y) →
    IsDecomposableOn χ (left ∪ right) →
    ¬ContainsCapSet χ left (a - 1) →
    ¬ContainsCapSet χ right (a - 1) →
    ¬ContainsCapSet χ (left ∪ right) a →
    ¬ContainsCupSet χ (left ∪ right) u →
    ¬ContainsStrongPolygonSet χ (left ∪ right) k →
    left.card + right.card < lowerPascalTailReservoir a u k
```

`OneChangeOn` need not be a separate premise because decomposability already
produces its four-point turn law.  This is an exact useful bridge, but it is not
yet an independently produced structural theorem: its conclusion is still the
entire missing cardinal bound.

The genuinely smaller producer would have to define a canonical
context-sensitive address for each vertex of `left ∪ right`, map those
addresses into a family with strictly fewer than
`lowerPascalTailReservoir a u k` members, and prove injectivity from the
target-free hypotheses.  Neither that address type nor its map is presently
defined.  Therefore field 1 fails for a theorem-entry producer even though the
bridge statement itself is exact.

### 2. Existing named downstream consumer

The consumer ladder is short and already kernel-checked:

```text
DecomposablePascalTailTwoSideBound
  -> SingletonLowerPascalTailGate
  -> LowerPascalTailCriticalGate
  -> DecomposableCriticalRootImpossible
```

The first arrow is an elementary adaptation of
`singletonLowerPascalTailGate_of_twoSideBound`: transport the supplied
`IsDecomposableOn χ upper` across `left ∪ right = upper`.  The remaining arrows
are the existing `lowerPascalTailCriticalGate_of_singleton` and
`criticalRootImpossible_of_predecessors_interior_pascal_tail_gates`, with
`singletonUpperPascalTailGate_iff_lower_dual` supplying the upper side.  Field
2 passes; no new consumer mechanism is needed.

### 3. Strict difficulty separation or measure decrease

The proposed bridge strictly narrows the model from arbitrary `OneChangeOn`
two-side systems to recursively decomposable systems, and every non-singleton
input exposes a smaller-cardinality decomposition split.  That is a plausible
source of induction, but no current statement proves that splitting preserves
an anchored two-side obligation, decreases a target parameter, or assigns a
bounded set of child obligations.  The numerical cut at `q` can cross a
decomposition split, so the mixed inner/outer triple colors are exactly the
context that a naive recursive summary loses.

Consequently no predeclared measure is known to decrease from the open
cardinality bound to independently closable child theorems.  Field 3 is not
established.

### 4. Small hostile neighboring worlds

Any proposed address or summary must survive all of the following already
admitted controls before Lean implementation:

- `published_induction_boundary_regression`, which proves the scalar
  off-diagonal boundary failure rather than merely observing it;
- `exists_realizable_pairRankState_collision`, where sweep-realizable,
  decomposable singleton-root systems have identical complete clipped child
  pair-rank states but different parent states;
- the turn-language and incoming-star prefix/transition collisions, including
  the decomposable closed-transition collision, which show that existing
  separated child spectra and root-relevant prefixes do not determine the
  required parent context; and
- the admitted 567/657 same-middle-profile two-extension countermodel recorded
  in `FP-03`, which defeats ambient multiplicity without supplying a Lean
  counterexample theorem.

The accepted state-567 proof traces are not additional producers: their
semantic-mining gate is expired because one advertised terminal is unused and
the other stable boundary is instance-wide.  Field 4 passes as a hostile-test
inventory.

### 5. Fact expected to produce the theorem

The missing fact would be a **contextual decomposition address law**.  Relative
to the singleton anchor and both ordered endpoints, a root-to-leaf path would
have to retain enough mixed-triple crossing data that:

1. restriction to a decomposition child has a well-defined transition;
2. two vertices with the same address force a cap, cup, or strong polygon;
3. the legal addresses obey a Pascal recurrence with the required strict
   reservoir count; and
4. color duality transports the construction without adding an independent
   producer.

No repository theorem or authenticated source object presently supplies this
law.  In particular, the recorded source audit found marked endpoint downsets
but no joint synchronization of the other endpoint, and the existing collision
theorems rule out constructing the law solely from clipped pair ranks,
separated incoming-star spectra, or their recorded prefixes.  Field 5 is
missing.

## Resolution

`DDECOMP-THEOREM-ENTRY-NOT-QUALIFIED__CONTEXT-ADDRESS-PRODUCER-MISSING`.

The decomposable-only bridge is a legitimate narrowing and should remain
available as route-design memory, but it does not pass the Ticket 0103 entry
gate.  Do not create the definition, its routine conditional adapter, a Lean
builder, a state-567 certificate packet, or a proof-producing label until a
prospective memo defines the context address and proves a genuine recursive
measure decrease.  Merely naming an injection into an unspecified address set
would restate the cardinal bound and is not a producer.

This approved block therefore contains **zero proof-producing slots and one
information-gathering route-design slot**.  It ends at its predeclared honest
stop.  No execution slate is frozen or authorized.

## Proof-distance accounting

- **Net proof movement:** neutral.
- **Evidence:** proposal-level theorem-interface audit against compiling Lean
  consumers and previously admitted hostile controls.
- **Damage scope:** `candidate-local`; only this incomplete context-address
  entry design is withheld, not the decomposable-Pascal mechanism family.
- **Difficulty displaced:** none.  The exact cross-endpoint/context producer,
  `TwoCapFreeSidesBound567`, the all-parameter Pascal-tail transition, and
  `D-DECOMP` all remain open.  The hard obligation is named more precisely but
  is not demonstrably smaller.
- **Counterfactual test:** knowing this before a builder run prevents a
  conditional interface and certificate work that would leave the same
  cardinal bound as a premise, but it does not reduce the estimated remaining
  proof work or raise the route's admitted success probability.
- **Planning consequence:** retain `FP-03` as `gated`, schedule no immediate
  descendant, and return to current-frontier selection.  Under Ticket 0103's
  rolling weights, the next bounded design allocation should move to a
  structurally distinct `D-HALF` producer audit rather than spend another
  consecutive block on the same missing cross-endpoint mechanism.
- **Load-bearing ledger edge changed:** none.

This is not a newly admitted mathematical refutation, so it receives no
failure genome.  The compiling collision theorems remain anchored where they
are already recorded.
