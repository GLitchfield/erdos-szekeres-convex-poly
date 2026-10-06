# R22 proof interpretation and review

Updated 2026-10-03T04:53Z. Preliminary review of accepted original-source proofs.
The exact diagonal gate full check20261003-002634-6a5ff2 is accepted,
with locked hash87bbef437ea7141f, no sorry and standard axioms only. Only configured Sol
was used; this is not an Astra review. Separate lower mathematical and
code/maintenance windows subsequently completed; their records are in
LOWER-MATHEMATICAL-REVIEW.md and CODE-MAINTENANCE-REVIEW.md. Final upper
receipt review and inventory refresh were subsequently completed; see
FINAL-MATHEMATICAL-REVIEW.md and FINAL-CODE-MAINTENANCE-REVIEW.md. The
current accepted results and resume state are in MATHEMATICAL-HANDOFF.md.

## What the root split measures

At a genuine deep root A below B, a cup C in A and a cap D in B form a
strong polygon on C union D. The children may interleave in sweep order;
deep crossing makes no child-order assumption. They are disjoint, so its cardinality
is |C|+|D|. Avoiding a strong k-polygon therefore turns a concrete b-cap
in B into absence of a (k-b)-cup in A. This is the structural reason
that the classic square and triangular bounds have the smaller parameters
needed in the audited proof. It is not a fitted cardinality rule.

Upper sweep endpoints extend lower cups; lower sweep endpoints extend
upper caps. Two opposite endpoints may be inserted simultaneously because
the middle child determines each crossing triple. Cap extension explains
why upper regions become cups or four-cap-free sets, while cup extension
explains the lower cup deficit at a normalized root.

## Why chosen points simplify the prefix/suffix proof

Let V=P union Q with P a cup, P before Q and Q four-cap-free, and expose
a decomposable root A below B. Choose lower points in occupied original
blocks, rather than proving membership properties for minA/maxA.

If a is in A intersect P, every upper point of P before a is a left sweep
endpoint of P. Endpoint uniqueness gives at most one such point. If b is
in A intersect Q, any three-cap of upper Q on one side of b would extend
with b to a four-cap inside Q. Thus both upper Q sides are cups. In the
mixed case a<b, a three-cap of B between a and b would gain both lower
endpoints to a five-cap, so that middle is also a cup. The whole upper
region after a is four-cap-free because a four-cap there gains a to a
five-cap. Its middle/final pair consequently has at most2k-4 points by
the supplied pair bound, and B has at most2k-3 points.

Write T=1+choose(k-1,2)+k-4. Pascal gives
T=choose(k-3,2)+3k-8=choose(k-4,2)+4k-12. The accepted R2 proof uses:

| Upper witness | Lower position | Bound on lower child | Bound on upper child |
| --- | --- | --- | --- |
| singleton | arbitrary | predecessor R2: choose(k-1,2)+k-4 | 1 |
| two-point cap, B cup | arbitrary | Z-prime: choose(k-2,2)+k-4 | k-1 |
| three-cap, B four-cap-free | A contained in P | k-4 | 1+choose(k-1,2) |
| three-cap, B four-cap-free | A contained in Q | choose(k-3,2) | decomposable R1:3k-8 |
| three-cap, B four-cap-free | A meets P and Q | choose(k-3,2)+k-5 | 2k-3 |
| four-cap | A contained in P | k-5 | 2+choose(k-1,2) |
| four-cap | A contained in Q | choose(k-4,2) | adjacent-pair deficit:3k-6 |
| four-cap | A meets P and Q | choose(k-4,2)+k-6 | 2k-3 |

All rows sum to at most T for k>=6. The pure-Q/four-cap row is exactly
where the adjacent deficit is necessary at k6: the elementary3k-5 bound
would leave one extra point. The excess pattern forces cup sizes
k-1,k-3,k-1. Large outer cups force middle extensions; the remaining
boundary turns either create a k-cup or a cap triple sharing both endpoints
with a (k-1)-cup, hence a strong k-polygon. That deficit uses adjacent
four-cap exclusions and pair bounds, without a global five-cap assumption.

## Why the diagonal root gains precisely one point

The accepted predecessor root bound is
H=choose(k-1,2)+choose(k-3,2). The accepted diagonal root bound is
G=H+1=(k-3)^2+k-1. Upper singleton cases invoke the predecessor theorem
on a smaller decomposable child after cap coupling excludes(k-1)cups.
Upper cups with at least two points couple to exclude(k-2)cups, giving
lower square(k-3)^2 plus upper k-1, exactly G.

The two sharp both-upper cases are exact: lower square(k-4)^2 plus upper
R1 bound3k-8 equals G; lower triangle choose(k-4,2) plus upper R2 bound T
also equals G. The final both-four-cap case has lower square(k-5)^2 and
upper at most3k-4. For k>=7 the difference from G is2k-13>=1. At k6,
the lower square bound is at most1, contradicting its four-cap witness.
One order reversal preserves child decomposability and covers the opposite
orientation. These arguments are all in the accepted root receipt.

At k6 these budgets are H=13, G=14, R2 targetT=13 and diagonal singleton
reservoir15. The sharp R1 root case is lower4+upper10=14; the sharp R2
root case is lower1+upper13=14. In the pure-Q R2 four-cap row, lower1
plus adjacent-deficit upper12=13, showing the exact small-parameter saving.

The diagonal Pascal window adds choose(k-2,k-2)=1 to the predecessor
window. Its singleton reservoir is therefore G+1. The singleton lower
point makes each gap side four-cap-free through cap endpoint extension.
Decomposability exposes a genuine upper child root, whose accepted bound
G contradicts the reservoir cardinality. The exact gate source implements
this wrapper; its full original-source receipt is accepted in
diag-gate-original-source-receipt.json, commit5d4fa26d8a20192c90624b23ed8a9cef90af8dd1.

## Evidence and code scope

Accepted receipts: zprime-original-source-receipt.json,
endpoint-original-source-receipt.json, r1-original-source-receipt.json,
deficit-original-source-receipt.json, r2diag-original-source-receipt.json,
diag-root-original-source-receipt.json, pred-root-original-source-receipt.json,
pred-gate-original-source-receipt.json and diag-gate-original-source-receipt.json. Exact job IDs, hashes, fixtures
and commits are in MATHEMATICAL-HANDOFF.md. Conditional inputs are the exact
uniform R20 cupblock and R21 Baek statement shapes, not unconditional
imports from the integration worktree.

No Python or shell workflow script was added. The only Lean run artifact
is PredGateAxiomInspection.lean, with #check/#print commands and no theorem
statement. Guarded job commands are Lean diagnostics, es automation, and
isolated git branch/commit operations. Source reuse was through byte-guarded
proof-body replacement; an off-by-one delimiter refusal happened before
mutation and was logged. The root heartbeat failure was repaired by giving
nlinarith only the exact cardinal bounds, preserving all mathematical cases.
No recurring computation algorithm needs harness-library promotion.

Post-acceptance source inspection matched the audited repaired root cases:
the both-four-cap branch separates k>=7 slack from the impossible k6 case;
the order reversal explicitly retains both child decomposability proofs,
deep split and exchanged gap sides. Both one-sided branches use the exact
supplied Baek bound. This is a source-level review supported by the existing
compiled receipt; it is not a new proof test or an independent model audit.
