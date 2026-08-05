# Middle-bridge route counterexample

Date: 2026-08-05

## Decision question

Can the full local state of two disjoint mutually obstructed `3+3` strong
sixes force either three probes on a common anchored frame or the extreme
`1+5`/`5+1` strong six needed to create a residue carrier?

The second conclusion is the actual parent-level payoff. A shared frame is
useful only if it helps produce that conclusion.

## Bounded falsification

`scripts/check_middle_split_bridge_routes.py` fixes the two crossing strong
sixes from experiment 0019. It imposes the one-change law, side cap-four
avoidance, ambient cap-five and cup-six avoidance, ambient strong-seven
avoidance, and both fixed strong-six laws. Four route negations are SAT:

| Route negation | CNF SHA-256 | Model SHA-256 |
| --- | --- | --- |
| no first-direction shared frame | `27b7a1cfc9056a703682af1d8ca0b52a1d45afe43184fb3b0ab533b629514e7e` | `f365b875b705a0ef042862d2a7e5f27219a404596635b157f7504928ae0ad28d` |
| no second-direction shared frame | `93128a6d2ab1de24d789ee9a149b30127930593f7a40b74b3d760a47db27e385` | `58c4566c4f342bbb602ebc55631ab09021f473d1ec769874151507df11e4bb93` |
| no shared frame in either direction | `b1c8eba64b971910e7a0f84ea08e9c76f4c3abfcf01a505ec33a417207139c2c` | `130c2f4ecb8672f2e17739f7e016bc7ce62b13745178a46cdc875edd679838a4` |
| no extreme crossing strong six | `797c3c0935d49914a5d6b8d9e50e433abb47b697370084fa49b46fc92937c23a` | `c0fa45ce413d17fa0c5023e8dd13192e7056fa6c5723aa48023187c8f7b3dc21` |

All instances have 220 triple variables. The first three have 31,206,
31,206, and 31,242 clauses; the no-extreme instance has 32,322 clauses.
CaDiCaL solved each in under one second. The independent
`scripts/verify_middle_split_bridge_route_model.py` imports no CNF generator
and directly rechecks every condition.

The no-extreme model is the decisive downstream counterexample. It retains
shared frames for all three interior probes in both directions while having
no extreme crossing strong six.

## Evidence ceiling

This is independently checked computational falsification evidence, not a
completed Lean result. A direct kernel-reduction encoding of the 72 extreme
six-subsets exceeded the practical recursion bound; `native_decide` was
rejected because its generated oracle axiom would violate the project trust
standard. The SAT model therefore retires the proposed route but is not
promoted as a theorem.

The result does not refute a theorem using the global 22-point
deletion-packing correlations, and it does not establish that the abstract
coloring is geometrically realizable.

## Disposition

Retire further local certificate refinement as the main route. The next route
decision must compare:

1. a genuinely global packing invariant coupling witnesses from several
   prescribed six-vertex deletions; and
2. reintroducing stronger geometric or realizability constraints that exclude
   abstract one-change colorings.

No new main route should be selected without the bounded Sol/Fable review
required by the Wayfinder protocol.
