# Accepted k=4 partition upper bound — 2026-10-01 08:17Z

Exact theorem: ctx_partition_value_le_three_of_k_four_and_indexed_maximum.
For raw positive external labels, k=4, one indexed maximum>=1, a kept
source child and an omitted source child, every legal coupling gives both
partition orientation sums<=3. Keep lists may contain duplicates. No WF,
run-count, interleaving, global-width or history/child-length assumption.

Commit5c3f806353848137b9d234aa40f34c52f30dcdf7, own node branch from main;
nodecommit20261001-041151-cb95bb done rc0. Only own module/root/generated
metadata committed; three exact closed helper overlays remain untracked.
Registered type bc818a750172284e. Targeted check20261001-040801-a49c20
passed:121.0s outer/2402MiB/OOM0/build3.216456174850464s. Complete5900B
receipt60775ed0005814b469c9be784915576b898a5a9e19917ac0c3d3da33e7e96e99,
CHECK.k4-upper-three-v2.full.json: closed/noSorry/standard axioms/locktrue/
blocked[]/tagerrors[]/targeted+incrementaltrue. Frozen statement capture:
PROOF.capture-k4-upper-three.json, fixturec5331c584de10777633551f55670a6628d6b13fb216eec6b931d15a349d12b29.
Exact source K4-UPPER-THREE.candidate-v2.txt SHA256
86ed4755e6798e00dfa0f33deb16f9df43b9c77889955206fb5cd7cd478cfa73.

Each proper part has bound<=2: same old/new axis uses SameSideTwo; opposite
axes use BothSidesTwo on the old and fresh indexed maxima. A new maximum2
part has bound<=1 via the closed large-maximum theorem. Legal d is1 or2,
so the two bounds add to3. This is an upper estimate and supplies no
dominating flip lower witness. Before-writing search found no exact theorem;
the commit message cites the relevant searches and this receipt.

First check20261001-040536-149507 failed eight mechanical elaboration
errors: four let-side case substitutions and four opaque complement/filter
atoms. Candidate-v2 explicitly transports the side equations, changes the
paired goal to the let-bound complement, and uses Nat.add_le_add. The full
failure log and candidate-v1 are retained; no failed inequality is inferred.
Registration2ef29a initially lacked two declared closed imports; own forced
claim preceded their addition, and the accepted receipt has no blockers.

Remaining obligation: positive k>=4 universal maximal-segment exchange,
original type dbd0e335b115583d at partial e03d9bc70c29527dec456d5d3621ad5af95f37d1.
Next perform the separate four-result Sol self-review. The active-point
lower shortcut has an unregistered/uncompiled ground counterexample draft
POSITIVE-POINT-ZERO.proof-body-v1.txt. Existing closed chainExt_part_other
and joinExt_part_other in CtxSatisfiesOfDeepBelowSplit already give exact
opposite-axis part transport; reuse them for a restricted one-axis route.
No own job pending after this commit; same R15 goal/deadline.
