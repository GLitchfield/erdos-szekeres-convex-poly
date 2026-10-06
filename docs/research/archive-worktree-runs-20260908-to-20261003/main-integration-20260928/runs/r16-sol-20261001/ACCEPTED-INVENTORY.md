# R16 accepted independent theorem inventory

As of 2026-10-01 16:37Z: thirty accepted helper theorems, each with a targeted
Lean check, locked unchanged statement, no proof holes and only standard axioms.
Every commit is a direct child of approved
5847e155fa613d4d2311eaee86b4b094f630e9a4; parents independently verified.
Each branch commits exactly its one node. No merge, push or integration occurred.
The inventory spans independent proof branches; the current compiled environment
contains the approved base and its own node.

| Result and scope | Commit | Targeted check | Locked type | Exact evidence |
|---|---|---|---|---|
|Extreme-run-end weakening|cd1e05ce4528237b2cae5d120e310f044bcacdaf|20261001-020205-1f077b|6ecc666112a7ba4e|[PART1-HANDOFF.md](PART1-HANDOFF.md)|
|Exact boundary marker erasure|aab76b86245a78f2f5648b83ebb90931b2e9c4dc|20261001-030155-fd7bff|81fb6b0b14b6f62a|[CODE-REVIEW.boundary-exact.md](CODE-REVIEW.boundary-exact.md)|
|Capacity Pascal identity|1839fee7b02a6d9d405b9dabf445025ea1f7772c|20261001-032731-9e217b|909643c533edfebe|[Capacity-pascal.closed.lean](Capacity-pascal.closed.lean)|
|Exact adjacent boundary merge|4ad1c24f2cbc2b96d7263a9c20edcc1ff4ab6dec|20261001-041119-280ff1|98bb67be7dd8f195|[HANDOFF.adjacent-marker-exact.md](HANDOFF.adjacent-marker-exact.md)|
|Both-marked threshold lower, unrestricted axes|52237b4bc87c167ee79ddab868f72687a48778a4|20261001-045854-d7ff87|3cc8ecb823117d12|[HANDOFF.both-marked-point-lower.md](HANDOFF.both-marked-point-lower.md)|
|Global threshold upper, axis <=3|42e07c0555940b8c75cd9a6d46453b8be5d7d2c8|20261001-051403-870405|7b06c7ca92220a2b|[HANDOFF.small-global-threshold-upper.md](HANDOFF.small-global-threshold-upper.md)|
|Both-marked first-child selector, effective axis <=3|10301b1910f55bbc159cbf069865a9da9d29e1d2|20261001-053631-a4510e|c380b1b17be83d25|[HANDOFF.both-marked-small-attainment.md](HANDOFF.both-marked-small-attainment.md)|
|Exact exposed-prefix marker merge|338a9e2b92e93962cc1c83113c83ae56c839f83c|20261001-054505-06eb5d|c499ac52f8ccd38|[HANDOFF.unmarked-prefix-merge.md](HANDOFF.unmarked-prefix-merge.md)|
|Exposed-first/marked-last selector, effective axis <=3|19f3afb270ae9117fc03b0437fdb968eeb09fb57|20261001-060132-eada08|c8e0da0d4fb01920|[HANDOFF.exposed-first-small-attainment.md](HANDOFF.exposed-first-small-attainment.md)|
|Global threshold upper, axis <=4|9c1bbea3ad65cc50f3968b24ca393c6609180f87|20261001-060938-fe682e|2d604b39265c45b4|[HANDOFF.global-four-upper.md](HANDOFF.global-four-upper.md)|
|Both-marked first-child selector, effective axis <=4|969fbbaa55474f6aa839058758f75c90a499ac8b|20261001-062838-278d13|3e9549000369df01|[HANDOFF.both-marked-four.md](HANDOFF.both-marked-four.md)|
|Exposed-first/marked-last selector, effective axis <=4|d2680bd1261a12d78ed9a79d46182711219c009f|20261001-065501-1131c1|4bccab0602b61153|[HANDOFF.exposed-four.md](HANDOFF.exposed-four.md)|
|Marked-first/exposed-last selector, effective axis <=4|67eea57d1668fbf4a3ca70a1a5c6935547f64fab|20261001-071014-c02565|ec1cbd24ca384549|[HANDOFF.mirror-four.md](HANDOFF.mirror-four.md)|
|Exposed-first/marked-last threshold lower, unrestricted axes/runs|30388a5b794e81b6e0af3ca2155aae539cabb7bb|20261001-073044-ff609e|fdb8683f45235ae|[HANDOFF.exposed-first-lower.md](HANDOFF.exposed-first-lower.md)|
|Indexed actual marker and chosen global <=2 imply every-fuel/full zero|56dfcefde8e66cf872a469889c0a34d7c5bae794|20261001-074023-fb5509|f7acd09c609a4ab1|[HANDOFF.marker-two.md](HANDOFF.marker-two.md)|
|One-level absorbed-marker budget upper, opposite global <=3|5d5d5f7b7a962d65f386af5ba5290cd3a6b8739b|20261001-080238-007bfa|60aa6950418d1bf6|[HANDOFF.absorbed-small-opposite-upper.md](HANDOFF.absorbed-small-opposite-upper.md)|
|Neither-marked first-child selector, opposite global exactly three|b8d7aa1ca13f1ca22ab5a5697f343bbab8553b16|20261001-082439-9c20aa|3b3e5de88d9d3684|[HANDOFF.neither-opposite-three.md](HANDOFF.neither-opposite-three.md)|
|First-child selector for raw indexed-marker/global<=2 contexts|58458d6be2f4dbd748eecdc383752c98af51c46f|20261001-083613-140788|904482967a5782bf|[HANDOFF.indexed-two-selector.md](HANDOFF.indexed-two-selector.md)|
|Global threshold upper through axis five below saturation|13352148d99bd290461858f0271a3bfcbd1b8c59|20261001-084317-52ee13|3e8c8349e1fab750|[HANDOFF.five-below-upper.md](HANDOFF.five-below-upper.md)|
|Both-marked first-child selector, opposite global at most five|e5761b3fc9d667392d282031648a5e53f8399290|20261001-085209-a36ede|e828ada3face9803|[HANDOFF.both-five-selector.md](HANDOFF.both-five-selector.md)|
|Neither-marked join-limited all-axis first-cut floor and supported attainment|c5a274622d52c69bcf692d8b492d7baedcfad047|20261001-091003-b5b6e3|e31666b7a0b32f8f|[HANDOFF.neither-join.md](HANDOFF.neither-join.md)|
|Either exposed-end global singleton selector, axis-four or axis-five below saturation|ad77519b3f84908b7ad48b88ef5c4fd3bc196f3d|20261001-092342-9919c0|82c99201718b0fe9|[HANDOFF.exposed-five-range.md](HANDOFF.exposed-five-range.md)|
|Kernel global-end-only counterexample; inner run end attains|aad0cd4939df89e219189c4372b9e629a5f2950e|20261001-094654-b4d99d|62563e2427e2be55|[HANDOFF.global-end-counterexample.md](HANDOFF.global-end-counterexample.md)|
|Raw positive both-globals<=2 multi-run every-fuel zero and first-child selector|7a200c02ee5bab9b6ac63ce9ff86e5949dc760f1|20261001-095702-7d5e18|40a056f1851d356b|[HANDOFF.both-two.md](HANDOFF.both-two.md)|
|Raw boundary marker chosen-global<=3/opposite<=2 every-fuel zero and first selector|3a1b9fe92a9848db270d79ca67ccc71aa2952f06|20261001-100623-a721c7|60d214e11511f371|[HANDOFF.boundary-two-three.md](HANDOFF.boundary-two-three.md)|
|Two-boundary chosen-four/opposite-two zero + first selector|ed2da9914948f3ce7fbce5c1e119204c43929586|20261001-103228-b07c57|935da605832f8f20|[HANDOFF.two-boundary-two-four.md](HANDOFF.two-boundary-two-four.md)|
|Raw marked-global-three<=2 and distinct two-level<=1|7309d4d5d1fc08b5d20972e7753877b7011c32ff|20261001-104449-92507e|ab2d5aded2bc2e93|[HANDOFF.marker-three.md](HANDOFF.marker-three.md)|
|Neither-marked first selector, chosen global3/arbitrary legal oppositeA>=3|8a8519031a2bcb0d64f5a557c2d6741a36b7bf30|20261001-113326-a6d0c3|6c2d934b28f88a8b|[HANDOFF.neither-chosen-three.md](HANDOFF.neither-chosen-three.md)|
|Raw high-maximum/opposite-two multi-run zero and first-child selector|ab116420cc781a232989c286f37c548008cdc364|20261001-114629-186bbb|d29856495f62fe80|[HANDOFF.large-max-two.md](HANDOFF.large-max-two.md)|
|Raw all-children bracketed indexed chosen-global<=3 every-fuel zero|aab5395c45d32470b40458039b26b9a79fcbc0e0|20261001-123039-b16343|ca893a8c2e474cd0|[HANDOFF.bracketed-three.md](HANDOFF.bracketed-three.md)|

The extreme-run-end selector N_ends remains OPEN, registered as
ctx_one_level_root_bound_attained_by_extreme_run_end_singleton_cut,
commit22d8137334ce31f2175aee57f29ff79d92fc1f36 (type32c6d22aba01da18).
Its targeted check20261001-013617-679625 confirms the registered conjecture,
not a closed theorem; it has sorry. Falsifier013208-804918 completed
5976 roots,127472 explicit leaf audits,98688 cut queries,0violations.
The weakening theorem in the first row has an explicit selector premise;
it does not assume the open N_ends constant as an axiom and does not close N_root.

General N_root/N_ends, larger-axis upper, neither-marked exchange and complete
degenerate selector edges remain open. Larger-axis diagnostic Stuck and exact
failed-inequality witnesses are in HANDOFF.larger-axis-upper-stuck.md.
Complete k5/k6 nondegenerate neither-marked probes have0FIRST/LAST failures;
fixed coupling has46/184diagnostic failures. No additional theorem credit.
Consult MATHEMATICAL-HANDOFF.md and the individual handoffs for exact assumptions,
proof receipts/fixtures, failed attempts and reusable geometric observations.
Boundary source SHA correction is in ERRATUM.boundary-source-sha.md.
No independent Astra review under the host no-delegation rule.
