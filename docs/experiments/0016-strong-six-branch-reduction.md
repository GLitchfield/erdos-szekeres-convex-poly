# Strong-six branch reduction at `(5,6,7)`

Date: 2026-08-04

## Question

After the two-four-cap-free-sides reduction, can the proposed sharp
nine-signature cap charge be selected, and if not, what smaller structural
branch replaces it?

## Charge-selector falsification

The deterministic analyzer `scripts/analyze_cap_failure_charge_matching.py`
enumerated every crossing four-cap in three independently validated sharp
21-vertex models (cuts 6, 10, and 11).  For each cap it formed the permissive
bipartite matching problem that allows every outside vertex to choose any
realized failure signature and gives each of the nine signatures capacity two.
The maximum matching ranks were respectively 15, 13, and 14, all below the
17 needed even before requiring a strict fiber.  Each ignored run certificate
contains a maximum matching and a Hall-deficient vertex set; the independent
checker `scripts/verify_cap_failure_charge_matching.py` revalidates both the
ambient coloring and the matching obstruction.

Thus `TwoCapFreeSidesSharpCapCharge567` is not merely unproved: its intended
selector mechanism is false on sharp models.  Its cardinalities also make the
contract circular at total size 22: a four-cap leaves exactly 18 outside
vertices while the stated capacities total only 17.

## Route review

A bounded Sol/Fable review used evidence packet SHA-256
`52f4db63c5a7c2bd0c748a090ed8b6fba056b14cf0dff2335a6c5e468f5fb0f7`.
Both reviewers rejected the bare nine-signature selector.  Fable recommended
separating the no-strong-six and strong-six cases; Sol emphasized a designated
strong-six witness and middle-determinacy failures.  The implemented route is
their common refinement.

## Compiling consequences

`StructuralChargingWitnessBranches.lean` now transports the existing
kernel-checked finite certificates to arbitrary finite `OneChangeOn` sets.
The sixteen-vertex `(5,6,6)` certificate closes the entire no-strong-six
branch, with the stronger ambient bound 15.  It also proves that at total size
22 every six-vertex deletion leaves a strong six-set, so each designated
strong six has a disjoint strong-six partner.

The remaining branch splits again.  Except at the exact `11+11` cut, one side
has at least 12 vertices.  The checked `(4,6,6)` certificate forces a strong
six wholly inside that four-cap-free side.  Every vertex of the opposite side
is then outside the same extreme of the polygon.  Lean proves that its failed
middle extension must use the vertex in the corresponding endpoint role.
This reduces the local bound to:

1. an endpoint-obstructed internal-strong-six branch; and
2. the fixed balanced `11+11` branch.

`StructuralChargingStrongSixSignature.lean` further proves that an internal
strong six in a four-cap-free, six-cup-free side has exactly one right-colored
internal middle position, leaving four signatures rather than ten.
Right-endpoint failures are now normalized again: each is either an anomaly
against one of those four internal reference colors or a nonconstant fan at
the polygon's final vertex. A change in that final fan forces both the earlier
fan color and the intervening bridge color to equal the later polygon-middle
color. This is the first transition law coupling the five anomaly classes to
the four-way polygon signature.

Lean now makes the five classes literal: the four internal positions are
indexed by `Fin 4`, the final fan is a fifth constructor, and every forced
right-endpoint failure realizes at least one class in this finite type.

The balanced branch is no longer opaque either. Adjoining any vertex from one
11-point side to the opposite side activates the checked 12-vertex `(4,6,6)`
state. Since six-cups are excluded, Lean obtains either a four-cap through the
adjoined vertex or a strong six. A strong six not using the vertex already
lies inside the opposite side and redirects to the endpoint branch. After
excluding those internal witnesses, every one of the 22 vertices therefore
carries a through-cap or through-strong-six witness on the opposite side.
Removing the adjoined vertex now gives an exact incidence form in Lean: a
through-cap has a three-vertex residue in the opposite side, while a
through-strong-six has a five-vertex residue. The conversion is an
equivalence, and the final local bound is reduced directly to the endpoint
branch plus this residue branch.

## Endpoint-class capacity falsification

The deterministic analyzer
`scripts/analyze_endpoint_anomaly_classes.py` enumerates every internal strong
six in the independently checked sharp 21-point models and computes all five
classes realized by every opposite-side vertex. Reversing the order is used
only to put a right-side strong six into the already normalized orientation;
class equality and strongness are invariant under that relabeling.

The model SHA-256 values for cuts 6, 10, and 11 are respectively
`0b29ecd05a9477852266b0de180e8ac260beda2b53ec461c36e4b5f522f57ead`,
`a3c419cb4679ebd8cea4c11bb6a24273a7fc774cae7623a655985a8fff76e3c3`,
and `7c60d6a38dcc7c3294a7e2baaa7cf9d9557d330c417cb6bccd6506530961aa1f`.
The independent witness checker revalidated all three assignments.

The direct repetition route fails sharply. On cut 10, one class can be
realized by all ten opposite vertices. On cut 11, one class can be realized
by all eleven, and some strong sixes do not even admit an assignment of their
opposite vertices to the five classes with uniform capacity three; capacity
four is necessary. Thus no useful class-capacity bound follows from the five
labels alone. This is advisory counterevidence, not a Lean theorem.

## Countercontrols

The tempting normalized shortcuts are false in the abstract one-change model.
Deterministic SAT checks found models for:

- two consecutive five-cups avoiding `(5,6,7)`;
- every one of the ten admissible strong-six signatures paired with a
  four-cup; and
- every one of the four cap-free strong-six signatures paired with a
  seven-vertex four-cap-free block.

These models show that the unused vertices on the large side and the full
`11+11` side structure cannot be discarded.  SAT output remains advisory and
none of these computations is recorded as a completed mathematical result.

## Next theorem

The active proof target remains the endpoint-obstructed branch alongside the
exact balanced `11+11` branch, but bare repetition of the five endpoint labels
is now retired. Any endpoint proof must use relations between successive
vertices together with unused vertices of the large cap-free side. The
balanced target is now the more explicit problem of coupling the 22 selected
three- or five-vertex residues. A local `6+7` block theorem is known false and
must not be reproposed.
