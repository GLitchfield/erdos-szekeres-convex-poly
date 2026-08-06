# Actual child-ray event-pair gate

## Question

Experiment 0031 formally refuted block expansion after retaining only the
endpoint interval incident to the actual child ray.  The predeclared fallback
was a skew-Bollobas set-pair inequality built from the ray witnesses
themselves.  Laplace proposed the first concrete event key:

    (normalized ray direction, complete child witness chain, marked chain vertex).

For an exact parent rank `r`, one selected witness chain supplies a `present`
set of `r-1` marked events.  An `absent` set has `k-r-1` actual events that are
not incident to the same span.  Every earlier present set must meet every later
absent set.  Together with self-disjointness, the skew-Bollobas inequality
would give exactly

    choose ((r - 1) + (k - r - 1)) (r - 1)
      = choose (k - 2) (r - 1).

This gate asks whether that exact event identity and cardinality contract even
exists on the already committed frozen `n = 12`, `k = 7` frontier.

## Fixed semantics

The frontier is the cap/rank-three family

    (0,4), (2,5), (4,6), (5,7), (6,10), (8,11).

Its active child is the six-vertex upper set `{0,3,5,6,9,11}`.  Exact child
rank is two, so every active witness chain has exactly two vertices.  A
lower-left/upper-right parent uses a left ray; an upper-left/lower-right parent
uses a right ray.  Each incident chain contributes its two marked event keys.
The complete chain and direction are part of the key exactly as proposed; the
gate does not coarsen either field after observing the answer.

## Adjacent-pair gate

The first necessary test passes.  Span `(2,5)` has the left-ray witness chain
`(3,5)`, giving marked events

    (left, (3,5), 3), (left, (3,5), 5).

Neither event is incident to `(4,6)`, whose unique left-ray chain is `(5,6)`.
Thus the support difference is nonempty.  The active-interval collision from
Experiment 0031 does not by itself refute actual witness events.

## Full-frontier refutation

The exact event key nevertheless fails on the same frozen frontier.  The first
four unique present sets come from

    right (0,3), left (3,5), left (5,6), right (5,6).

Because direction and the complete chain belong to the key, these four
two-event sets are pairwise disjoint.  At the fifth span `(6,10)`, every one of
those events is nonincident and hence eligible for its absent set.  But meeting
all four disjoint present sets requires at least four events, while

    k - rank - 1 = 7 - 3 - 1 = 3.

Therefore no exact-size skew set pair can be assigned at the fifth span.  This
is a direct capacity certificate, not failure of a heuristic selection
algorithm.

## Independent replay

The producer reconstructs the decomposable coloring with the cell-mask
enumeration code, enumerates child chains, and records direction/chain/mark
events.  The checker imports no producer code.  It reconstructs the tree with
the independent replay engine, represents events as four-tuples, and verifies
the unique active supports, adjacent support difference, four pairwise
disjoint earlier present sets, nonincidence at the fifth span, and the
`4 > 3` obstruction.

The compact manifest SHA-256 is
`6d3f1f4dba35eb653d9fc5eaffebe6cf89264f937f78058f921a8d64aab2ee40`.

## Claim boundary and next decision

This is bounded computational evidence refuting the exact marked-chain event
contract.  It is not a Lean theorem and does not refute all actual-ray
set-pair arguments.  In particular, a coarser event identity might let
overlapping chains share events, but it must preserve the semantic distinction
between incident and nonincident events and cannot be chosen merely to make
the skew intersections true.

Before another contract is promoted, the Innovation Scout must compare:

1. a semantic quotient of actual events;
2. exact incidence-matrix or exterior-algebra accounting; and
3. a proof using both reflected endpoint intervals without selecting one
   active endpoint.

No option may enlarge the untagged Pascal carrier or restate Hall expansion as
an event premise.

Experiment 0033 tests the preferred semantic quotient.  It is also refuted:
the adjacent spans `(2,5)` and `(4,6)` have identical directed role/depth
incidence keys, so fiberwise absence at the later span cannot meet the earlier
present set under any tie-breaking rule.

## Reproduction

    python3 scripts/check_actual_ray_event_pairs.py \
      --output data/derived/e3-actual-ray-event-pair-frozen-n12-k7.json
    python3 scripts/replay_actual_ray_event_pairs.py \
      data/derived/e3-actual-ray-event-pair-frozen-n12-k7.json
