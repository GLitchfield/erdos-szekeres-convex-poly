# R18 exact two-level unilateral extension profile

CLOSED theorem `ctx_two_level_unilateral_young_marker_extensions_exact`,
type `88855bc6fde5dd3d`. Independent branch
`node/CtxTwoLevelUnilateralYoungMarkerExtensionsExact` from main
`f112ce1d346d150c0c5f9eb85392f0fb4bba5042`, commit
`766e182f1a8f192b44cdbcf3c1ba1a33911857c2`.

Exact hypotheses: arbitrary raw context, maxima=[1,m], both indexed sides
equal s, a nonempty youngest-marker list entirely right of point p. No
child, well-formedness, positivity, k, global or physical-length assumption.
The theorem gives left extension equal to older-marker presence left of p,
right extension 2 exactly when some youngest marker precedes an older one
(otherwise 1), join extension max(left+right,m+1), and opposite indexed
chain/join extensions zero. Unused old lower levels are included; an unused
old upper level does not satisfy sideAt2=upper because the default is lower.

Proof enumerates four sublists of levels [1,2]. Sorted youngest positions
make their first marker minimal, so the existential thread is equivalent
to nonemptiness of old positions beyond that first marker. Cutoff2 sees
only youngest markers and gives the old join term m+1. Imported named fold
steps are definitionally core-equivalent; the proof has no dependency on
the open parent theorem in their module.

First isolated proof check `20261001-142500-142ecd`, operation
`op-bc3028fed1a2444b`, accepted body
`7569e6ffdfde31bdf433704a3f1529cc200472cc3846f68a69bbf9ea0de512c7`, source
`cbd56a4fff61c2890d4ac92a3e9ae0fb276c2e833cd686b6efd91d3781477783`.
Fixture `bbe039dc3710d486f5e728f7e9b8f4ce228b93e539ff8aa5318279f945e55f68`.
Original-source check `20261001-142601-2cf951` CLOSED in 3.944s/580MiB,
immutable full receipt
`fc98593b6e9606ff2e05e4e002bb2cfe70d197ba16577643df922f7a1c37bf26`.
All audits: no sorry, lock_ok, propext/Classical.choice/Quot.sound only.
Source/candidate/receipts retained with TWO-LEVEL-UNILATERAL prefix.
No compiler failure occurred for this helper. Commit job143217-71f1e4 DONE.

Diagnostic timing/full jobs135957-0a3ce6 and140056-e050f8 checked990 and
219120 comparisons with no failures. Full grid includes14608 valid shapes
of length<=8 and15 raw parameter tuples, using shared extension/lean=True
limit APIs. These comparisons have no C/Python-to-Lean equivalence proof;
the accepted theorem, rather than the enumeration, supplies proof credit.

This settles the direct two-level ordered profile for an outer-run axis-two
cut. Open: positive-path descent and its every-leaf thread-cost criterion,
the positive converse for arbitrary roots, both general paired-cut upper
transports, and multirun NF<=source. The prepared UNIT-AXIS-LEAF candidate
addresses descent in the same R18 trial. ROOT-NF remains OPEN at fc037f7.
No own job pending here; no merge/push/full extract or statement changes.
Inherited lock metadata recovery preserved all type texts/hashes, receipt
LOCK-REPAIR.two-level-unilateral.json. Registration's local8G cap restored
byte-exact to20G before accepted proof check and commit.
