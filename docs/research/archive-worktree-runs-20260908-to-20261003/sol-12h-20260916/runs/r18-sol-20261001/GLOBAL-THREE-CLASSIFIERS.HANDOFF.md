# R18 chosen-global-three structural classifiers

At2026-10-01 23:56Z: both marked-end and unmarked exact classifiers locally
Lean accepted. No separate public normal-form node yet.

Marked class: raw max[m], legal globals<=k, k>=3, m<=k-2, uniform one-level
word, >=2 runs, chosen global exactly3, opposite>=3, and at least one actual
word end marked. Full bound=0 if both ends marked, otherwise1.
One-sided active boundary/common rank gives <=1; the accepted extreme fresh-
axis saturated singleton cut gives >=1 when one end exposed. Two marked ends
bracket every child and force zero. No original ROOT-NF premise.

Carrier191046-3c1a82/op-eda35d68943b4394 ACCEPTED63.0641s2118MiB,
standard axioms only; parent exact scopedNFtype1933d0914d56fe0c unchanged.
Stagef4cea43bdbb9a21675ffe197fd95f59b6d15ae6b342d0458917cb0fa575e76d7;
body1aa0943768e482ed4bd9c821bea27368e90c0a6ad1c229c6fbc66183b9420782.
MARKED-GLOBAL-THREE.v1.ACCEPTED.STATUS/RECEIPT/compile.log preserve evidence.
ROOT-NF-GLOBAL-THREE-MARKED.exact-fragment-v1.txt contains the119line new glue;
SCOPED-NF.with-marked-global-three-exact-v1.candidate.txt is3794lines/noholes.
Only the original scoped public body is installed, never this carrier.

Unmarked class: chosen global3, oppositeA with3<=A<=k, k>=3, oldm>=1,
m<=k-3, uniform word, child at both actual word ends, actual old marker,
>=2runs. Proposed exact full bound2. R16 CLOSED selector proof
ctx_one_level_root_first_singleton_cut_attains_of_neither_marked_chosen_global_three,
commit8a8519031a2bcb0d64f5a557c2d6741a36b7bf30,type6c2d934b28f88a8b,
supplies an accepted2228line prelude. Reuse it unchanged: exact first singleton
leaf1 at maximum k-A+1; exact prefix merge of chosen companion maximumA-2;
merged old maximum=max(A-2,m+1)<=k-2 and marked-first/exposed-last lower>=1;
source upper<=2. The same legal coupled cut now yields source>=2, hence2.
This is paired-cut addition, not the refuted independent component domination.

New final consequence47lines; body-v3 uses explicit transport of the bound
target and run hypothesis across Lean's dependent side matches, total2278lines.
ROOT-NF-CHOSEN-THREE-NO-ENDS.exact-signature-v1.txt/body-v3.txt and
ROOT-COMPLEMENT.with-chosen-global-three-no-ends-exact-v2.candidate.txt
(2329lines/noholes) accepted in20261001-194757-d9f82a/op-9819cc2e0e074177:
83.5196s/3618MiB, standard axioms only, parenttype30efac7e8738996c unchanged.
Stage69b5e14bb298f3897ef41b834a1e31814c55075c07ff391b12d014f4b545cfac;
body1b0d2fa28400e74eb44f4387fee35f05b026702bc17e8d7748959718076ed717.
CHOSEN-GLOBAL-THREE-NO-ENDS.v3.ACCEPTED.STATUS.json preserves the receipt.
Earlier v2 check194443-4017fc failed once at dependent-match definitional
conversion, before its new tail estimates; one error/72.9729s/3499MiB.
Failure diagnostic6f06405029a90d6b92414afb8a83478502be930287c278fc1ce26e7cda280d2f
and v2.FAILED.STATUS remain preserved. No mathematical counterexample there.
Search for neither-marked chosen-global-three exact2 returned no indexed hit.

The main MergeLevels dependency was fetched during root-complement registration
192705-96b663; its closed namespace utilities are used, with no broad merge
theorem invoked. Next publish the complete chosen-global-three ROOT-NF body
v2 on its own branch after the current counterexample and boundary helper.
No R16 source/claim/job mutation. Local carrier acceptance alone grants no
independently registered public normal-form theorem credit.

Prepared actual general NFv15 has6345lines, unchanged registered statement,
FULL smaller-root P(n), and three holes. It would discharge all chosenG3 plus
axis2/saturation; its raw adapter/dispatcher are still uninstalled/unchecked.
Prepared public chosenG3NF body-v2 has6177lines/noholes, also unregistered and
unchecked as a whole. Actual generalNFv8 remains authoritative until its own
targeted check. OppositeG3/chosen>=4 and larger axes remain open; no claim that
all minimum-axis-three roots or general ROOT-NF are proved.
