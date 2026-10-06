# Adjacent child contraction preserves run count

Node: `ctx_num_runs_child_letter_contraction`, statement hash
`87d38cf7fc07a108`, branch `node/CtxNumRunsChildLetterContraction` frommain.
For arbitrary raw sigma and `sigma.word=left++[child,child]++right`, the
run counts of sigma and the shortened context are equal.

Proof: map old positions across the deletion. The first duplicate has
the same run-start predicate as the retained child; the second has false
run-start predicate. All other predicates transport along the increasing
position map. The filtered range of starts is therefore mapped bijectively
and has the same length. This argument is extracted from the already closed
child-letter expansion theorem; it assumes no well-formedness or capacities.

Search before writing: `es search "number child runs unchanged deleting
adjacent duplicate child"`, no registered match; artifact
`search-numruns-child-contraction.json`. Registration checked complete-index
duplicates and distinguished numRuns definitions, external contraction,
base contraction and the unrelated unit-axis run-count upper bound.

Passing scratch: `20260930-171623-382c2c`, `NumRunsTransport.lean`.
Registration: `20260930-172337-4acd66`, targeted only.
Isolated whole-parent proof check: operation `op-6fc2a6974e26450b`, job
`20260930-172809-41e2ac`, `proof_accepted=true`, matching type hash and only
standard axioms. Fixture `e041320aa0f292a011086e157e8d9f530c7f4c9ebef87ea2d2332143649174bf`.
Exact accepted source hash `2f7eea656fc0b7059b50bed387e7a557524d6328a7ad628b938fb46ec3042a8c`.
Installed that source unchanged, then targeted-check original module:
`20260930-173003-dade47`. Evidence `NODE.numRuns.json`,
`RECEIPT.numRuns-targeted-check.json`, and isolated operation receipt
`runs/es-operations/20260930-172809-41e2ac/receipt.json`.

The helper transports the single-run base branch and the multi-run
hypothesis for the contraction proof. It does not dominate any cut value.
C1r and C1r-from-the-localized-singleton-exchange remain open. The X
conjecture was committed separately as `eb65ce22`; the explicit singleton
threshold helper separately as `6d494100`.

Review: no new execution helper or mathematical algorithm. The accepted
proof uses the existing position-map geometry with ordinary list lemmas.
Its scratch linter warned about one redundant simp argument inherited
from the existing proof; there were no compiler errors or new axioms.

Committed as `5bfb2e085e2999b10be2bf31fedfd645eb1fb152`, guarded commit
job `20260930-173304-1a85a7`, exactly five node/import/index files. Claim
released closed. The fresh C1r falsifier receipt remains separately dirty.
