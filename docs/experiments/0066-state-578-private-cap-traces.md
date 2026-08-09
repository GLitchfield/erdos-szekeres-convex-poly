# Experiment 0066: whole-private-cap traces and route expiry

## Question

Does the endpoint law for a private four-cap turn its owner's lower-directed
first exit into a finite trace contradiction in the open state-578 residual?

The selected route allowed one whole-cap trace layer, then required formal
expiry if a target-free model realized the remaining trace without a new
global capacity constraint.

## Compiling trace layer

Lean now distinguishes pointwise exits from the shallowest event of an entire
set. `FirstSetEscapeAlongPath secondary tree path direction` means that the
whole secondary cap follows the terminal path until the first split where it
no longer fits in the selected child.

The central positive theorem is

```text
FirstSetEscapeAlongPath.exists_two_in_lowerSiblingBucket_of_cap.
```

If a four-cap's shallowest event occurs at a false step, the deep-split
endpoint law places both sweep-middle vertices in that step's upper sibling.
They therefore form a certified two-vertex bucket collision. Consequently a
private cap whose owner exits false later satisfies

```text
IsPrivateFourCapAssignment.
  privateCap_true_firstSetEscape_or_bucketCollision.
```

It either first peeled at a true step or already has the collision sought by
the lower-sibling capacity argument. Pointwise, every uncovered non-owner is
now proved internal to the final node or has a true-directed first exit.

The global reconnection also compiles. The actual state-578 theorem now
returns `HasThreePrivateCapTraceOwners`: either three private owners are
internal, or three external private caps independently satisfy the
true-escape-or-collision dichotomy.

## Decisive counterexample

A bounded eight-vertex search checked the recursive tree

```text
[5, [[[[7,3],2], [[4,0],6]], 1]]
```

with terminal cap `{3,4,6,7}`, private cap `{0,1,2,5}`, owner `1`, and path
`[true,false]`. The whole private cap first peels at the root's true step;
the owner then exits at the next false step. The only lower-sibling bucket is
`{1}`, so no two private-cap vertices collide.

`StructuralChargingNextState578PrivateCapTraceCounterexample.lean`
reconstructs this example and kernel-checks all of the following:

- recursive decomposability;
- terminality of `{3,4,6,7}`;
- private-cap assignment for owner `1`;
- no five-cap, seven-cup, or strong eight-set;
- the exact true whole-cap escape followed by false owner exit;
- absence of a private-cap lower-sibling collision.

This example does **not** have six owners or the `32/23` density package. It
therefore refutes independent cap-by-cap closure, not a genuinely global
six-cap theorem.

## Density reserve

The one allowed density-aware repair proves the strongest density-only
statement available here:

```text
exists_residualFourCap_disjoint_from_small_avoidance_at_32_23.
```

Any set of at most five vertices disjoint from the terminal cap fails to hit
all residual four-caps; density supplies another residual cap avoiding it.
Thus a three-vertex shared core cannot be a transversal of the whole residual
cap family. This does not prevent the six *chosen private caps* from sharing
that core, so it supplies no overlap capacity and does not repair the trace
route.

## Route decision and `41+1` overflow

The selected whole-cap path-trace route lands on expected outcome 3: formal
expiry/counterexample. Its definitions and positive lemmas remain reusable
infrastructure, but it is no longer the main closure route.

The pre-vetted overflow moves to the oriented `41+1` tail. Lean now defines
`SingletonLowerColorDualGate578At32` and proves that this exact 32-vertex
swapped `(7,5,8)` lower gate suffices to close the 41-vertex singleton-upper
tail by restriction and color duality. The same file proves that every
decomposable 23-vertex restriction of this dual reservoir contains a
four-cup. No common straddling-cut theorem is claimed; that asymmetry is the
next mathematical obstruction.

## Review and resource record

Read-only innovation and contrarian audits independently identified the
shallowest whole-cap event as the sound locality boundary. The contrarian
audit supplied the eight-vertex witness; the local deterministic checker
reproduced it before Lean reconstruction. These reviews were proposals and
computational evidence until the declarations above compiled.

One first-pass Lean proof expanded two finite color-agreement facts into 512
cases each. It reached the explicit 8 GiB process ceiling and terminated with
`bad_alloc`; WSL remained stable. Replacing it with two structural
restriction proofs reduced the final counterexample build to about three
seconds. No unbounded search was used.

Safe targeted replay:

```bash
prlimit --as=8589934592 -- lake build ErdosSzekeres.StructuralChargingNextState578PrivateCapTrace
prlimit --as=8589934592 -- lake build ErdosSzekeres.StructuralChargingNextState578PrivateCapTraceCounterexample
prlimit --as=8589934592 -- lake build ErdosSzekeres.StructuralChargingNextState578Dual
```
