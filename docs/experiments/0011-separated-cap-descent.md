# Separated-cap interval charge and the `4+5` gate

## Status

The interval, overlap, reserve-seven, normalized `4+5` cup-block,
arbitrary-block transport, and cup-block cardinal charge compile in Lean. The
exterior descent bound remains open.

## Compiling interval layer

`StructuralChargingIntervals.lean` represents a witness span by its least and
greatest sweep indices. It proves finite interval Helly in the needed
contrapositive form: if a nonempty witness family has no common integer sweep
cut, two witnesses are weakly separated. The result is then specialized to
the executable family of cap witnesses of a fixed cardinality.

Weak separation allows one shared boundary vertex. Lean records both exact
cardinality consequences:

```text
card (earlier ∩ later) ≤ 1
card earlier + card later ≤ card (earlier ∪ later) + 1
```

In particular, two four-vertex witnesses reserve at least seven ambient
vertices. This is arithmetic infrastructure only; it does not assert any new
cup, cap, or polygon outcome.

## Sharp countercontrol

Run:

```text
python3 scripts/check_structural_charging_countercontrols.py
```

The independently enumerated checks use lexicographic triples, least
significant bit first, with `1 = left`, for mask `0xfff0fc01fffff`. They verify
the one-change law, separated four-caps `{1,2,3,4}` and `{4,5,6,7}`, no common
cap-span cut, no five-cap, no five- or six-cup, and no strong six-set. Their
union has seven vertices and residual `{0}`.

Consequently separation alone cannot reserve eight vertices, force a target
outcome, or manufacture a `4+5` cup-block interface.

## Normalized `4+5` gate

Lean names the precise symbolic target `CupBlocks45FinNine`: consecutive cup
blocks `{0,1,2,3}` and `{4,5,6,7,8}`, together with `OneChangeOn`, force a
four-cap, six-cup, or strong six-set. `cupBlocks45_finNine` proves it by eight
turn tests and nine fixed witness leaves. The proof uses no SAT certificate or
coloring-space enumeration. An offline hammer made no progress on the
unexpanded statement; the successful proof instead exposes the fixed
witnesses explicitly.

Reversal proves the normalized `5+4` orientation. Sorted order embeddings then
transport both orientations and close `cupBlocks45Force466`. Consequently
`cup_block_card_add_le_eight` proves unconditionally that two ordered cup
blocks avoiding all `(4,6,6)` outcomes have total cardinality at most eight.

## Quantitative descent target

The reserve-seven theorem exposes the intended Pascal split as seven witness
vertices plus a residual region. The next structural statement is named
`SeparatedCapExteriorBoundAtSix`: under the one-change law and absence of a
five-cap, six-cup, and strong six-set, the exterior of two separated four-caps
has at most eight vertices.

Lean proves that this target implies an ambient cardinal bound of 16, exactly
the diagonal `k = 6` extremal threshold. The missing mathematics is a bridge
from the residual vertices to ordered cup/Pascal-window contributions. The
sharp countercontrol shows that the bridge must use additional root-split or
minimal-counterexample structure, not separation alone.

## Next gate

Strengthen the exterior target with root-split hypotheses sufficient to derive
the residual cup regions and connect them to the completed cup-block charge.
Do not replace the exterior proposition with finite SAT evidence.

The root-aware statement `SingletonRootSeparatedCapChargeAtSix` now compiles.
The proof uses the endpoint transition to show that two weakly separated upper
four-caps already force a parent five-cap. Its numerical consequence reaches
the exact singleton-root bound 16 without state-566. This also closes the
separated-witness branch in every open parent: all upper four-caps must share
the root as a sweep cut. The next gate is therefore a certificate-free descent
of that common-cut family to its first separating decomposition node;
state-566 and equivalent finite upper consequences remain prohibited.

The root-cut fact is now parameterized in Lean: for every positive `a`, if the
parent has no `(a+1)`-cap, every upper `a`-cap span contains the singleton
root's sweep cut. This removes common-cut existence from the open work; the
remaining experiment should test proposed first-separating-node extraction
rules.

## Crossing-root falsifier

`scripts/check_crossing_separated_caps.py` exhaustively tests all decomposable
colorings and all exact decomposable-child roots through eight vertices. It
refutes the proposal that two weakly separated four-caps, each meeting both
children, force a five-cap, six-cup, or strong six-set.

The smallest violation has seven vertices, root lower child `{3}`, and caps
`{0,1,2,3}` and `{3,4,5,6}`. The shared vertex is their weak-separation
boundary and lies in the lower child. Disjointness does not repair the claim:
there are 74 disjoint violations at eight vertices, with smallest root lower
child `{3,4,7}` and caps `{0,1,2,3}` and `{4,5,6,7}`. Both witnesses include
explicit decomposition trees and pass definition-shaped replay. This is
computational evidence, not a Lean theorem or a planar-coordinate certificate.

The next candidate must exploit the existing theorem that a crossing cap uses
at most two lower-child endpoint ports. It should charge port occupancy or
Pascal contributions rather than assert an immediate forbidden outcome.

## Compiling port-capacity replacement

`StructuralChargingPortCapacity.lean` proves the replacement local law for an
arbitrary weakly ordered finite family of crossing caps. Each lower vertex is
used by at most two caps, and a shared use has forced right-then-left endpoint
directions. The bound is sharp on the seven-vertex counterexample. A verified
double-counting corollary bounds total lower incidence by twice the lower-child
cardinality.

This does not yet produce the E3 recurrence. To amortize the local bound over
the recursive configuration, each witness must be assigned to one occurrence
of a separating split. The current existential descent theorem erases that
occurrence, so the next experiment concerns a reified decomposition tree and
minimal separating-node allocation.

`StructuralChargingTreeAllocation.lean` now supplies that allocation layer.
For any fixed explicit decomposition tree and witness of cardinality at least
two, a Boolean path deterministically descends through containing children and
stops at the lowest separating node. Lean proves both the separating-node
specification and uniqueness of the address. The remaining experiment is to
define the `k = 6` overflow demand allocated at that node and test whether
directional port counts plus the child Pascal contributions determine a sound
parent charge.

The formal allocation-to-port coupling is now complete locally: all caps
assigned to one address cross its resolved split, and an ordered family of
four-caps has at most twice as many members as lower-child vertices. This is
sharp in the seven-vertex witness and does not itself advance the 16-point
bound. The next falsifier must therefore target a concrete weighted
overflow-token definition and cross-address nonreuse law; saturation or raw
cap counts are insufficient.

The extended exact-root census enumerates 1,295,559 nonempty weakly ordered
chains of crossing four-caps through eight vertices. It finds no violation of
the endpoint, direction, pointwise multiplicity-two, or summed incidence
bounds. Maximum chain length is two, and 21,347 chains attain coefficient two.
The smallest sharp case has seven vertices, lower child `{3}`, and incidence
`2 = 2 * |lower|`. These are independently replayed computational results,
not Lean theorems. A child-Pascal collision census remains intentionally
absent because no executable overflow-token contribution has yet been defined.

## Route review and missing semantic specification

A blind Sol/Fable review used evidence packet SHA-256
`1a879cf0be9c3bceec4d9ec5e514b4f73a0a9650bfb85435b93e9c79a08899ae`.
Both reviewers returned `not_supported` with high confidence for selecting an
overflow-token route now. The agreement is advisory, but its central objection
is directly checkable: the repository defines neither the semantic owner of a
Pascal overflow unit nor a cross-address resource identity. Raw cap counts
cannot fill either role.

The proposed scopes from that first packet were stale. Fable suggested another
incoming-star state gate, but the repository already has a kernel-checked
nine-vertex incoming-star transition collision and has stopped deterministic
quotient refinement. Sol suggested classifying the `(4,5,5,1,3)` singleton
boundary, but `singleton_root_card_le_seven` already closes that boundary
locally and certificate-free.

A corrected audit used question SHA-256
`116946c9457e8592da499dadaed8cd028562e85ee109429c49b06c90be2ceb80`.
Sol returned `partially_supported` with high confidence and found no precise
finite classification well-posed yet. Its smallest missing object is a
decidable semantic `ChildContribution` relation whose concrete resource
family is counted by each child summand, especially `choose 3 0 = 1`. The
specification must depend only on the coloring, a fixed explicit tree, node
address, side and child state; prove the relevant cardinality; supply
restriction/composition behavior; and preserve an ancestor-comparable resource
identity. It is circular if membership mentions an overflow unit, the target
bound, or successful extraction. The corrected Fable run reached its external
session quota after producing no valid structured answer, so no corrected
consensus is claimed.

The missing semantics were then recovered directly from the journal proof and
formalized in `PublishedInductionSemantics.lean`. The auxiliary parameter is a
maximal threshold index; the corresponding `Q₁'` is an actual retained subset
of child vertices, and the adjacent binomial contribution bounds the actual
complement. Lean now proves the selection and complement inequality, proves
uniformly that index one forces the entire child to be a singleton, and closes
the `(4,5,5,1,3)` branch by applying `singleton_root_card_le_seven`. Thus the
`choose 3 0 = 1` term has a concrete owner and no token census is needed for
this branch. The remaining finite gate concerns auxiliary indices greater than
one but below the active Pascal-window lower endpoint; it must be reviewed
against this corrected source contract before another charging object is
introduced.
