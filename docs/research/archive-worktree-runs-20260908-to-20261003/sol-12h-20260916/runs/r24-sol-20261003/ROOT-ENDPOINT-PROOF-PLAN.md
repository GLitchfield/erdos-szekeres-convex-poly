# General root endpoint consequence

2026-10-03 17:51 UTC. This is the next formal obligation after the accepted
root-incidence proof has completed extraction and been committed. The research
deadline and one-node-per-branch policy remain unchanged.

The existing proof `two_full_cap_blocks_root_structure` has locked type
`84e6237f7f3a6146`, isolated receipt
`d1b02ae6c07291c7d0997408ea5a2093f03716be0701b59c24ff7c7a0b1135e6`, and accepted
original-source check `20261003-134841-d86a75`. Full extraction is running in
`20261003-134932-d2c521`. These receipts establish the incidence and chain
structure; final harness freshness and audit are still pending.

For two sweep-separated full p-cap zones, p>=4, under global cap and strong
limits p, prove that every nonempty deep-below root has a four-cup and contains
both an L-U-L and a U-L-U subsequence. Those subsequences exhibit a gap in each
root child within the parent's order. This is a general geometric consequence,
not a finite example or an assertion about the uncompiled B evaluator.

The proof is explicit. In each zone, enumerate its two lower points x<z. The
existing `lower_mem_cap_isSweepEndpoint` says each is a zone endpoint. Since
x<z, x cannot be the right endpoint and z cannot be the left endpoint. Every
upper point of the zone is therefore strictly between x and z, using root
disjointness to exclude equality. The zone has p-2>=2 upper points.

Take an upper point a in zone0, its last lower point b, the first lower point
c of zone1, and an upper point d of zone1. Zone separation gives a<b<c<d.
Each ordered triple of this quadruple is mixed with lower middle point, so
the deep-split rule colors it left. Hence it is a four-cup. The two endpoints
of zone0 with a between them give L-U-L; a,b,d give U-L-U.

The endpoint enumeration can use `Finset.orderEmbOfFin` on the two-element
lower intersection, preserving actual Finset geometry and avoiding a new
numeric abstraction. Membership cases for the four-point cup are local facts
inside the registered proof body. New statements will be registered only
through `es node add`, after the first node has been finalized and committed.

Search receipt: `es search "deep split two full cap blocks root interval
endpoint four cup"` returned no indexed theorem on 2026-10-03. Reuse the two
already compiled deep-split endpoint and crossing lemmas. The outcome closes
the general forced noninterval-root mechanism; it leaves B attainment,
matrix-state equivalence, the construction's general Lean interface, and the
closed formula for N open.
