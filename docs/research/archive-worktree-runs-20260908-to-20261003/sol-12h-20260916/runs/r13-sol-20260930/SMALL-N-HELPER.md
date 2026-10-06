# Raw singleton attainment with at most three children

Node`ctx_bound_attained_by_singleton_cut_of_le_three_children`,
hash`bb154cfb31cbe29b`,branch`node/CtxBoundAttainedBySingletonCutOfLeThreeChildren`
frommain41cc0e4b. For any raw sigma with k>=3,numRuns>=2 and childcount<=3,
bound equals a singleton cut at an admissible coupling, either orientation.
The isolated child may be interior. No WF or endpoint premise.

Proof: numRuns>=2 gives2or3children. Compute every proper interval block;
each is a singleton or its complement. Take an attaining value from the
nonempty defining maximum. The closed fuel-stability lemmas identify both
part values with bound. Membership-wise part congruence either keeps the
singleton as the block or swaps the two complementary parts. This gives
exact equality, including zero values.

No invocation of the refuted ctx_bound_attained_by_end_cut. Its module is
imported for independently closed list-maximum,fuel-stability and part
congruence helpers. Whole-parent audit below verifies standard axioms only.
This is the base class of the missing root singleton reduction; it proves
nothing about four or more children and does not meet C1r-from-X alone.

Search: search-small-singleton-attainment.json,no match. Registration
20260930-182142-a9709e checked complete-index duplicates and used targeted
extraction only. Passing scratch20260930-181942-f219cc,
SmallSingletonNormalForm.lean. Early classification compiles failed only
premature list-membership simplification and Ne symmetry; source attempts
and compiler jobs are preserved/logged. The final normal-form compile passed
without errors or warnings.

Captured fixture d3aa292122edd534bdbeee35e8208dd273e0ffb17ca4100dd20490ea03cb74d3.
Isolated proof op-3e4ead331249487c/job20260930-182808-3a9b3f accepted complete
parent hashbb154cfb31cbe29b with propext,Classical.choice,Quot.sound only.
Accepted source hash5f8b25652a21d8dce7e7a18a92f77d4a4cc8da97204d7266c9dccf4e91684240
installed unchanged. Targeted module check20260930-183003-64cb4c confirms
closed,sorry=false,lock_ok=true,no nonstandard axioms.
Evidence NODE.small-N.full.json,PROOFCHECK.small-N.full.json,
RECEIPT.small-N-targeted-check.json and the actual operation receipt
runs/es-operations/20260930-182808-3a9b3f/receipt.json.

Review: no execution algorithm or new workflow script in this proof. The
finite2/3-child list classification is intentionally local; no new library
automation is needed. Separately the diagnostic probes reuse shared context
generation,part construction,compiled evaluation and point-limit APIs.

Committed59809ac4e015f79f8acd2b58ccf07bd60d7257f1,job20260930-183453-a1e76d.
Exactly five node/import/index files;C1r diagnostic receipt remains separately
dirty. Claim released closed. No ignored run artifacts entered the commit.
