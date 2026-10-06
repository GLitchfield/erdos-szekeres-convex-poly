# R16 unrestricted exposed-first lower: Sol self-review

This is the same configured Sol/xhigh agent's review in a separate usage window
window-f30c5cb89a254095. The host forbids delegation; no independent Astra review
has occurred.

The registered statement is unchanged: type fdb8683f45235ae, lock_ok=true.
It assumes legal A,G >=3, k>=3, 1<=m<=k-2, a uniform one-level word whose head
is a child and whose last letter is the old marker, and at least one child.
Conclusion: T(A,min(G-1,k-m),k) <= root.bound, on either side.
There is no small-axis or multi-run premise.

Reviewed the complete new Lean module and the changed proof tail. The 172077-character
prefix reuses the checked geometric, normalization, both-marked lower and Pascal
helpers from the accepted exposed-end selectors. The small-axis upper, raw-context
normalization upper and attainment tail are removed; no hsmall, hSmallUpper or
hRootUpper occurrence remains. New statements were registered through es node add.

The tail uses the exact exposed first-point base when numRuns<=1. For multiple
runs, the first child gives a legal singleton block. Its opposite-side leaf has
bound T(A-1,V,k); its selected-side complement merges the exposed prefix without
changing G, with maximum max(A-2,m+1), and has bound at least T(A,W,k).
Here V=min(G-1,k-m) and W=min(V-1,k-A+2). W=1 gives threshold zero explicitly.
Capacity Pascal supplies the sum T(A,V,k), and ctx_bound_cut_le dominates this
particular legal cut by the original bound. The two orientations use the correct
cut conjunct, and explicitly rewrite the root k projection.

Targeted accepted check 20261001-073044-ff609e, receipt
f82abcd72d868a4fe6c3845eb99401dccfbf109611dff84e0d806790aedfe54a:
53.206103801727295s, 2615MiB, 4G guard; closed, sorry=false,
only propext/Classical.choice/Quot.sound, no blocked/uncovered axioms.
The exact file matches the reviewed v2 candidate (178566 characters, 3831 lines).
Whole-parent fixture 379ee68af41b96c788efa15d5b16d055c49482cade33e70effa78da7b8778ba8.

Failed v1 check 20261001-072726-492880 is frozen: two final definitional projection
mismatches, 133.70856499671936s /2611MiB. The v2 repair adds only two occurrences
of show rho.k=k from rfl (with the actual Greek identifier). No mathematical
hypothesis or statement changed.

No new Python, workflow helper, inline computation or tracked research script was
introduced in this window. Existing guarded node/check/capture/commit commands
were reused. No shared algorithm promotion is warranted for this Lean-only step.
Frozen failed and successful sources remain durable under this run.
General larger-axis upper, full N_ends/N_root, neither-marked exchange and
degenerate selector edges remain open.
