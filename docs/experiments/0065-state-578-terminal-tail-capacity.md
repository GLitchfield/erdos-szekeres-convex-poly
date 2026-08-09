# Experiment 0065: terminal-tail capacity and private cap witnesses

## Question

Can the `32/23` cap density in the unresolved singleton-lower `(5,7,8)`
branch turn the terminal cap's nine outer tails and their first-exit addresses
into an additive capacity contradiction?

Only the declarations proved in Lean are completed mathematical results.
Bounded searches selected and rejected candidate lemmas; both negative
claims described below were reconstructed as separate Lean theorems.

## Lower-sibling buckets

Following the terminal cap down a decomposition-tree path gives an ordered
list of lower-sibling supports.  Lean proves that these supports are pairwise
disjoint and that every false first-exit vertex belongs to its unique support.
For vertices in three distinct ordered buckets, the shallow endpoint triples
have color `left` while a shallow middle triple has color `right`.

The first numerical consumer now compiles:

```text
IsCapSet.card_le_three_of_lowerSiblingBucket_fibers
```

A cap whose vertices are all covered by the path buckets and whose bucket
fibers have size at most one has at most three vertices.  Equivalently, every
four-cap either has an uncovered vertex or places two distinct vertices in a
single lower-sibling bucket.  This is a genuine capacity law, but the current
state routes only selected tail vertices rather than every vertex of a
secondary cap.

## Global residual-cap transversal

Fix a terminal four-cap.  Every disjoint residual four-cap meets the genuine
outer-tail set; otherwise it would lie strictly inside the terminal cap's
sweep interval.  The `32/23` density also shows that any such cap transversal
has at least six vertices: deleting the fixed cap and at most five transversal
vertices leaves a 23-set and hence another disjoint four-cap.

Lean chooses a minimum transversal `T` inside the tail set.  Minimality makes
every selected `x` essential: deleting `x` exposes a private residual cap
`C_x` disjoint from `T.erase x`.  Consequently

```text
T ∩ C_x = {x}.
```

Choosing one witness per selected vertex is injective, so the terminal
residual has at least six distinct private four-caps.  Every selected tail is
also routed either inside the terminal cap's lowest node or through a
certified lower-directed first exit.  Pigeonhole gives three private internal
owners or three private external owners.  The theorem

```text
exists_terminalFourCap_sixPrivateRoutedTailTransversal_at_578
```

threads the complete package back into the actual state-578 obstruction.

## Two refuted shortcuts

The first candidate said that every disjoint secondary cap must consume two
of the nine terminal tails.  Deterministic search with seed `57832` produced
a 17-vertex recursive tree whose terminal cap is `{7,8,13,14}`, whose outer
tail set has nine vertices, and whose secondary cap `{5,9,10,11}` meets the
tails only at `5`.  It has no five-cap, seven-cup, or strong eight-set.  The
counterexample module proves

```text
not_terminalNineTailSecondaryMultiplicityGate578.
```

The second shortcut treated six distinct private caps as six nearly disjoint
charges.  A nine-vertex recursively decomposable target-free coloring has
owners `{0,1,2,3,4,5}` and caps

```text
{x,6,7,8}  for every selected owner x.
```

All six caps are distinct and private relative to the owner set, but share the
same three-vertex core.  Lean checks decomposability and absence of every
target in

```text
six_distinct_privateCaps_can_share_three_vertex_core.
```

This smaller obstruction does not satisfy the terminal-cap or `32/23`
density package.  It therefore rejects only the inference from distinctness
and target avoidance to disjoint petals or bounded shared-core multiplicity.

## Deep-split word law

The positive structural response is independent of the counterexample.  For
any four-cap at a deep split, if the cap is not wholly in the lower child,
both of its middle sweep vertices lie in the upper child.  Any lower-child cap
vertices are confined to the two sweep endpoints.  This strengthens the old
cardinality-specific `2+2` word theorem and constrains all node-contained
private caps:

```text
capFour_deepSplit_lower_subset_endpoints.
```

It still does not bound how many private caps can reuse one upper middle pair.
The live missing bridge is therefore whole-cap information: terminality and
global density must either route the other three vertices of one private cap,
bound a same-bucket/shared-core collision, or force a finite path-staircase
configuration that yields a forbidden target.

## Route review and selected next interface

This section records the selection made at the end of experiment 0065. The
bounded trace milestone has since been completed and formally expired as a
standalone closure route; see experiment 0066.

A bounded post-result review used evidence packet SHA-256
`9b98a3e1aa0151eb04dd5684d6fae7872c4b9b58bb4c795e8c81bf3a9c01be52`.
Codex Sol returned `supported` at high confidence and Claude Fable 5 returned
`partially_supported` at medium confidence.  Both ranked the whole-cap path
trace first, retained a density-aware shared-core gate as the only reserve,
and found the packet insufficient to prefer the separate `41+1` branch.
This agreement is advisory rather than mathematical evidence.

The review's exact first interface now compiles.  If a private cap's owner has
a lower-directed first exit, then either two cap vertices collide in one
lower-sibling bucket or the generic uncovered vertex can be chosen different
from the owner:

```text
IsPrivateFourCapAssignment.privateCap_nonowner_uncovered_or_bucketCollision.
```

The next and only selected trace milestone is a finite classification of this
uncovered non-owner using the deep-split endpoint law.  The route expires to
infrastructure if a full-hypothesis bounded model realizes only harmless
uncovered/collision traces, or if that one trace layer cannot extract a new
color or capacity constraint without an additional global assumption.  On
expiry, the density-aware shared-core test receives one bounded attempt before
the project switches branches.

## Resource incident and safe replay

The first attempt to certify the 17-vertex example evaluated a raw nested
powerset proposition during Lean elaboration.  It reached approximately
28.4 GiB resident memory in about four minutes and likely caused the WSL
failure.  That checker is gone.  The replacement enumerates only fixed-size
subsets with compact executable checks; its targeted build used roughly
3.3 GiB combined peak memory and completed under an 8 GiB per-process limit.

Safe reproduction:

```bash
prlimit --as=8589934592 -- lake build ErdosSzekeres.StructuralChargingNextState578Capacity
prlimit --as=8589934592 -- lake build ErdosSzekeres.StructuralChargingNextState578CapacityCounterexample
prlimit --as=8589934592 -- lake build ErdosSzekeres.StructuralChargingNextState578PrivateCaps
prlimit --as=8589934592 -- lake build ErdosSzekeres.StructuralChargingNextState578PrivateCapsCounterexample
```
