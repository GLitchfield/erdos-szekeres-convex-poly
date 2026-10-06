# R20 integration guide

The coordinator reports the requested uniform theorem and gate reviewed at
`c89df0e8605272ad2484600507ce342c8cf5f421` and
`82a570723fc014cbd192dee18fa19e8f7a1a15dc`. Their original-source checks are
`20261002-133903-34a3cd` and `20261002-140250-5b9883`. They prove the diagonal
family for every k≥5 through deletion and strong-set growth, using the hand
base theorem rather than the k=9 certificate. No merge or push was performed.

Research ended early by Gavin/coordinator at2026-10-02T23:34:36.971478Z.
The final receipt inspection is in FINAL-DELIVERY-EVIDENCE.json and the final
mathematical account in MATHEMATICAL-HANDOFF.md. The optional size-four deletion
exception compiled during already-started checks but remains uncommitted on
its branch and is excluded from these pins; the coordinator says it is unnecessary.

Each mathematical commit has the same baseline parent, adds one registered
statement, and includes harness metadata. `ALL-MATH-PINS-SEMANTIC-LOCK-AUDIT.json`
records semantic lock differences: exactly its target was added; existing locks
were not changed. Sorted-key rewrites explain the large textual lock diffs.
The commits are independent review units, not a chain to apply verbatim without
resolving shared generated metadata. Use the repository's node integration
workflow after review. Keep each registered theorem type unchanged.

## Mathematical dependencies for later proof cleanup

The independent branches replay accepted helper proofs locally because the
one-node baseline rule prevents sibling imports. After integration, proof bodies
can call the reviewed exports instead; the type locks must remain unchanged.

| Consumer | Reusable facts it can call after integration | Why they are needed |
|---|---|---|
| Uniform singleton gate | Uniform two-cup-block theorem | Gap sides become cups when the parent has no4cap; the reservoir contradicts the linear block bound. |
| General cap/cup strong exclusion | General cap-middle partition | At most j−2 cap interiors leave a cup of at least u points in a strong(u+j−2)-set. |
| Abstract binomial cup-cap alternative | Consecutive-color propagation, existing `CupCap.cup_cap` | The existing recurrence gives consecutive chains; OneChange colors all their triples. |
| Easy a5 short-side count | Abstract binomial alternative | Side capacities are triangular, giving the exact budget when one side is short. |
| Cross-gap B | Ending cup-layer predecessor argument | A four-cap beginning with two equal-rank left points extends to a forbidden five-cap. |
| Cross-gap A | Ending and starting layers, rank-free extension alternative | Local exact ranks and global upper bounds reject both extensions at a hypothetical mixed cap triple. |
| Ordinary square bound | Rank existence, both cup layers, cross-gap A | Lower layers have capacities r; the two top layers form one cup with combined capacity c. |
| Supported strong-set normal form | General cap-middle partition, side-three-cap cup extension | A cup part of size at least k−1 would extend; exactly two cap interiors must remain. |

The insertion moves are independent tools: OneChange and two shielding vertices
permit insertion into a selected cup; the two-point versions iterate this with
exact cardinality. The common-extrema cup/cap union theorem needs OneChange,
but the cap-middle partition and the strong exclusion do not. Rank profiles
exist on every finite support without any color law. Cross-gap A uses exact
local profiles and only upper bounds globally; constant global bounds are valid
in its square-count application.

## Review limits and the next mathematical obligation

All 23 accepted modules load together in guarded job
`20261002-191637-234410`; individual original checks remain the acceptance
evidence. Dependency traces contain only standard axioms and no generated,
certificate or unsafe dependencies. Missing branch sources in the current
checkout remain explicit unknown source owners. Hash observations and loading
compatibility do not attest source-to-olean correspondence.

The coupled a5 cut remains open. At the first active boundary the individual
side polygon bounds already follow from their cap and cup bounds. Only crossing
polygons can yield the missing c−1 savings below the top rank layer. The easy
regimes are proved; the remaining case has (c−1)-cups on both sides and at least
one c-cup. The square bound supplies c², not the desired c²−c+1.

A decomposition-root criterion is accepted at
`75d0d5b1c34d6cc3b72f2a2347f41c88d00eb5b2`, original check
`20261002-191226-3793b9`. Its proof idea is exact: crossing maximum polygons are the Cartesian product of
maximum lower cups and upper caps. A deletion must drop one of those two ranks
and hit maximum polygons in both children. Applying the criterion to both colors
of a proposed partition describes balanced hitting. It still gives no construction
whose gap-side parts are cups and whose removed block obeys the tight size budget.
Children may interleave in sweep order, so contiguous-child assumptions are invalid.

The two workflow promotions are separate review units:
`7242b3e927bb256e61134285b6ca694fc87abf00` adds observational dependency tracing;
`ba9b1946f0c9cd9dd3d0584c40d170b52026e2e1` adds exact pinned-candidate source
identity. They were self-reviewed and tested, but independent coordinator review
remains pending. They grant no theorem credit by themselves. The original
artifacts and failed attempts are preserved in the mathematical handoff and journal.
