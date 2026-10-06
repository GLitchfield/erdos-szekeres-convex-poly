# R22 declaration searches

Searches before proof development, 2026-10-02. The exact final PR/commit
review should cite the relevant rows and any later additions.

| Query to `es search` | Result and use |
|---|---|
| `singleton lower Pascal tail five predecessor reservoir` | No result; exact approved target is new. |
| `lowerPascalTailReservoir` | Finite 455, 466, 488, 556, 567, 578 identities; uniform four-diagonal identity. No uniform five predecessor identity. |
| `decomposableThreshold five predecessor choose` | No result. |
| `decomposableThreshold` | Existing eq_window, diagonal, ordinary regime, and finite identities; no uniform five predecessor closed form. Reuse eq_window. |
| `reverse mirror order decomposable` | No result for this broad conjunction. |
| `reverseColor` | StructuralChargingTransport defines reverseColor/reverseOrderedTriple and univ cup, cap, strong containment transports. |
| `cap four free cup layer` | No result. |
| `cup row` | Existing address-matrix row lemmas concern different objects. |
| `card_le_choose` | No result on the frozen baseline. R21's theorem is read from the authorized integration source and will be an explicit input. |
| `consecutive` | Existing CupCap list definitions and fixed-length one-change chain principles; generic Chains.lean equivalences assume realizability. |
| `isCupSet_of_consecutive` | No result. |
| `monochromatic consecutive oneChange` | No result; authorized R20 source inspection found its local H1 chain proof. Expose a reusable baseline lemma. |
| `cup_cap` | CupCap.cup_cap; HasDeepBelowSplit.containsStrongPolygonSet_of_cup_cap; unrelated fixed-state interfaces. |
| `gap_sides_avoid_cap_of_no_parent_succ_cap` | Uniform gap-side reduction in StructuralChargingSaturatedResource. |
| `cup cap endpoints` | No matching general common-endpoint strongness bridge in the returned hits. |
| `chainMax` | Existing Ctx.chainMax, sup bounds and split coupling. It is unanchored, so it does not replace longest-cup-start beta for the row lemma. |
| `cupStart layer`, `longest cup starting` | No results. Formalize the audited equal-cup-start-rank layers with attained witnesses and a maximum contract. |
| `card_le_choose oneChange no cup` | No result. Derive the count from the newly certified cup-start layers and Finset.card_eq_sum_card_fiberwise. |
| `no cap three cup`, `containsCapSet_three` | Only specialized structural results for the broad query; no generic cap-three iff failure of cup-set in exact-name search. |
| `insert cup oneChange min`, `insert cap oneChange` | No results. Decomposable endpoint insertion lemmas use a deep-below split; new chain-based extreme insertion has different hypotheses. |
| `monochromaticSet_insert_max_of_oneChange` | No result; prove the mirror of the newly certified minimum insertion, for either colour. |

Direct source inspection is also part of the search: Decomposable.lean,
StructuralChargingCore.lean, StructuralChargingTransport.lean,
StructuralChargingPascalTails.lean, StructuralChargingPascalTailGates.lean,
StructuralChargingPascalCupBlocks.lean, StructuralChargingCapFreeSides.lean,
Chains.lean, and mathlib's finite supremum, fiber-count, and binomial APIs.

Oversized search replies are preserved by the harness, including
`c46a818f374b1fedca422f61260728ee1add5646fbd83ff36fd008c77d9e136e`
(consecutive) and
`b224f55be025f135a4be46b1aa2af533af311fc61843b24cd9d7f5f926b00245`
(OneChangeOn).
# Z bound search, 2026-10-03T00:52Z

`es search 'card bound square no five cap gap sides four cap free' --full`
returned no results. Reuse the newly certified triangular count and both
insertion lemmas; two-point vacuity and four-cap gap crossing will be local
finite-set arguments in the Z proof.

## Upcoming two-cup and common-endpoint searches, 00:56Z

`es search 'two ordered cup blocks no four cap extend cardinality' --full`
and `es search 'cup cap common minimum maximum union strong polygon' --full`
returned no results. Source inspection found
`isCupSet_insert_two_of_extreme_cup_extensions` in
`StructuralChargingPascalCupBlocks`, and deep-split union strongness in
`Decomposable`, with different hypotheses from the required boundary
extension and common-endpoint bridge. The two-cup proof will reuse the
certified generic chain/insertion principles and the baseline four-point
chain theorem.
## Further toolkit searches, 2026-10-03T01:15Z

No results for `es search 'three ordered cup blocks no four cap cardinal bound'`,
`es search 'one change monochromatic consecutive cup union common core'`,
`es search 'cap three free iff cup set'`, or
`es search 'strong polygon union cup cap shared extrema intersection endpoints'`.
Source has `gap_sides_are_cups_of_no_endpoint_cap_three` with a fixed endpoint
premise, and common-core cup gluing in PascalCupBlocks. Three-cup proof reuses
the accepted two-cup contracts and maximum insertion. The general cap-three
equivalence and common-endpoint bridge require new nodes.

No search results for cap-four/five consecutive-turn containment; source has
`containsCapSet_univ_of_finFour`, whose ambient set is univ. Future restricted
cap witnesses can reuse the baseline finite chain theorems and image API in
local proof steps; no additional wrapper node is needed.

## R2 prefix searches, 2026-10-03T01:42Z

`es search 'cup prefix four-cap-free suffix cardinality choose no strong polygon'
--full` returned no results. The sharp ordered-prefix row-deficit helper is
newly registered; the wrapper will reuse it and the certified triangular
bound. For a full m-1 prefix, moving its maximum to the suffix preserves
four-cap-freeness: a four-cap through that point either extends the prefix
to an m-cup or extends the four-cap to a five-cap.

## Marker and reflection searches, 2026-10-03T01:50Z

`es search 'straddled longest cups endpoint first last three cap marker bound'`
and `es search 'reverse coloring finite set one change cup cap strong decomposable'`
returned no results. Existing `cup_straddles_upper_of_not_containsCupSet_succ`
provides the root singleton straddling premise. Transport contains reversal
for univ witnesses; arbitrary sets and deep splits will need direct transport.
Source inspection found Finset.orderEmbOfFin_mem, its image-univ equality,
and the min/max endpoint equations. They can extract concrete cap triples
without another enumeration algorithm.

`es search 'cardinality marker straddled cups square bound endpoints'`
returned no results. The marker count will define complete endpoint families,
apply the new WE exclusion, and reuse the certified no-cap-three/cup
equivalence and classic square bound. Finset.card_sdiff_add_card_eq_card
is the existing cardinal partition API.

## Full root and gate searches, 2026-10-03T02:22Z

`es search 'cup and cap gain two outer endpoints at a deep split'` and
`es search 'singleton lower five predecessor gate from deep root cardinal bound'`
returned no results. Deep-root crossing supplies simultaneous endpoint gains
directly; Duality.lean is a thin import and transfers the cup proof to caps.
Concrete 2/3/4-cap witnesses use existing
HasDeepBelowSplit.containsStrongPolygonSet_of_cup_cap rather than auxiliary
maximum-rank contracts. The registered root theorem is now original-source
checked; the exact gate wrapper will expose its upper child's deep root.

## Diagonal toolkit searches, 2026-10-03T03:24Z

Exact descriptive queries for an ordered cup/4cf prefix bound choose(u,2)+u-2,
decomposable three cups bounded by3k-8, and adjacent4cf pairs with a3k-6
extremal deficit returned no hits. Broader `es search '"cup prefix"'`
returned the two accepted predecessor R2 lemmas, which will supply the
maximum-prefix transfer. `es search '"three ordered"'` found the accepted
classic3u-6 theorem; the other hits concern context markers, not this geometry.
Its local hglue construction already joins the two middle-cup extensions.

`es search '"deep" "endpoints"'` found the baseline upper/lower endpoint
cardinality facts and `containsCapSet_four_of_outer_lower_inner_upper` in
StructuralChargingNextState578SpanCounterexample. The latter has a larger
import than needed. No generic simultaneous two-endpoint extension was found;
the predecessor root's local proof can supply a thin reusable extension if
needed. Search artifacts c54d6a6869fb8c333b3e2cc1420583daee37433154ae77c14003200bb777e55c
and19dfd2b74e233fa90ac6ee5175e87dbab7b9814972c264581a12ca28a4f6b21f
preserve the broad results. The exact diagonal gate search found no duplicate.

Before R1 proof, broader decomposable/three-cup/cardinality searches returned
no matching theorem; artifact
d8f23037383468f48177e3084301d1d6cce8e206f28fce50520870888a223e76.
The sole structural hit concerned an unrelated next-state578 counterexample.
Reuse accepted classic two/three-cup bounds and simultaneous endpoint gains.

Before adjacent-pair extremal deficit proof, exact descriptive query
`three cups adjacent four cap free pairs strong polygon extremal deficit`
returned no hits. Reuse two-cup forced extensions and the accepted common
endpoint cup/cap union theorem; no new finite enumeration is needed.

Before R2 decomposable cup-prefix/four-cap-free suffix proof,
`decomposable cup prefix four cap free suffix bound Baek uniform pair inputs`
returned no hits. Reuse accepted predecessor R2 for singleton upper child,
Z-prime for cup upper child, R1 for four-cap-free upper three cups, and the
adjacent-pair extremal deficit for the remaining upper four-cap case.

Before full diagonal root proof, exact descriptive query
`diagonal deep split gap five cap no strong cup cardinal two choose plus one`
returned no hits. Reuse accepted predecessor root, simultaneous endpoints,
set reflection/decomposability transport, R1 and diagonal R2.

Before optional upper dual gates, descriptive query
`singleton upper Pascal tail five predecessor diagonal dual gates`
returned no hits. Existing singletonUpperPascalTailGate_iff_lower_dual
at StructuralChargingPascalTailGates.lean:332 supplies the proof, swapping
cap/cup parameters and reservoir formulas under the k>=6 side conditions.
# Optional upper dual gates, 2026-10-03T04:50Z

At05:21Z, `es search 'upper diagonal five singleton Pascal tail gate with
uniform cupblock Baek inputs'` also returned no hits. Reuse the accepted
lower diagonal gate and the same dual iff; preserve exact input binders.

`es search 'singleton upper Pascal tail five predecessor diagonal dual gates'`
returned no hits. Reuse `singletonUpperPascalTailGate_iff_lower_dual` at
StructuralChargingPascalTailGates.lean:332, with `(a,u)=(k-1,5)` or
`(k,5)`, and the two accepted lower gates. No new case analysis.
