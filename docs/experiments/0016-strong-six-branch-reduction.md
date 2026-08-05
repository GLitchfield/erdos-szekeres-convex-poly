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

The active proof target is the endpoint-obstructed branch with one of four
internal middle signatures, alongside the exact balanced `11+11` branch.
The first proof should couple the six forced endpoint-role failures to the
additional vertices of the large cap-free side; a local `6+7` block theorem is
known false and must not be reproposed.
