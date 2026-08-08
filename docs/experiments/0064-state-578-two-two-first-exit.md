# Experiment 0064: the terminal `2+2` branch and first-exit addresses

## Question

What information do the nine terminal-cap tails retain at the lowest
separating node in the unresolved singleton-lower `(5,7,8)` branch?  In
particular, can five tails inside the node close the branch, or can tails
outside the node be assigned a useful decomposition-tree address?

Only the declarations proved in Lean are completed mathematical results.  The
bounded search that discovered the counterexample below is route-selection
evidence; the separate Lean reconstruction is the completed negative result.

## Exact `2+2` word

`StructuralChargingNextState578TwoTwo.lean` first couples one terminal cap to
both of the previously proved structures: its nine genuine outer tails and
its unique lowest separating node.  In the `2+2` branch, the deep-split law
then determines the cap's sorted child word uniquely:

```text
lower, upper, upper, lower.
```

Consequently a tail vertex that is still inside this node realizes either
endpoint bridge automatically from the crossing law.  The terminal bridge
certificate therefore supplies no additional information on the internal
side of the node.

## Refuted five-internal-tail gate

The exact local proposal `FiveInternalOuterTailGate578` asserted that a
terminal `2+2` cap, no lower six-cup, and five internal outer tails force a
five-cap, seven-cup, or strong eight-set.  A deterministic bounded search with
seed `57822` found a counterexample at trial zero.  The search was stopped
immediately and its output was reconstructed independently in Lean.

`StructuralChargingNextState578TwoTwoCounterexample.lean` defines the
nine-vertex recursive tree

```text
lower = [[5,8],[6,2]]
upper = [[1,[[3,4],7]],0]
cap   = {2,3,4,5}
tails = {0,1,6,7,8}.
```

Lean checks the deep split, terminal cap, `2+2` profile, five outer tails, no
lower six-cup, and absence of every target.  Hence
`not_fiveInternalOuterTailGate578` proves the exact local gate false without
an external oracle.  This does not refute the full 32-vertex singleton-lower
gate because it omits the global `32/23` density and avoidance reservoirs.

## Surviving first-exit invariant

Nine tails partition into at least five inside the lowest node or at least
five outside.  For an outside tail, follow the cap's path from the root and
stop at the first split that separates the tail from the cap.  Lean proves:

- every outside vertex has such a first exit;
- an endpoint bridge makes an exit with the cap in the upper child
  impossible;
- therefore every terminal outside tail first exits with the cap in the lower
  child and the tail in the upper child;
- the relation exposes an actual prefix whose `splitAtPath` lookup is that
  lower-cap/upper-tail node.

The theorem `exists_terminalFourCap_lowestSplit_tailResidual_at_578` threads
this into the actual 32-vertex upper child.  The surviving `2+2` branch now
has the exact alternative: five internal tails, or five external tails each
with a kernel-checked lower first-exit address.

This is genuine directional information but not yet a capacity theorem.
Different tails may leave at different false steps, and no proved bound yet
limits the number or total capacity of these upper-sibling fibers.  The next
consumer must use the inherited global avoidance/density hypotheses to bound
internal tails or aggregate the lower-exit sibling buckets.  First-exit
direction alone is not a selected closure claim.

## Reproduction

```bash
lake build ErdosSzekeres.StructuralChargingNextState578TwoTwo
lake build ErdosSzekeres.StructuralChargingNextState578TwoTwoCounterexample
```
