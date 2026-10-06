# Possible follow-up: general decomposable threshold lower leaf

Current 2026-10-04 00:43 UTC: fully accepted and committed `aebb6505`;
`THRESHOLD-LOWER-ACCEPTED.md` records unchanged type, isolated receipt,
full source/extraction, independent audits, clean commit and CLOSED release.
Separate fixed-Sol review `1d9178180cc247d8` is complete. All pending and
unadmitted descriptions below are historical proof-development snapshots.

Admitted after separate second review `13ad583096e6466c`. Registration
`195136-0bd13d` passed; locked unchanged type `a3f0da371108b910` is ready
and normally claimed on `node/DecomposableThresholdLowerExists` from fa6dacd1.
Research window `8e448af476d64295`; exact capture `195435-02d257` is pending.
V3 is the complete reviewed draft, not yet candidate accepted. Endpoint is
fully accepted fa6dacd1. The earlier unadmitted snapshot below is historical.

2026-10-03 23:20 UTC. Not registered, claimed or commissioned. Universal
history is accepted0930d3c7; endpoint-lifting op-58b7ff64fee64da9 has passed
candidate/source and is doing full extraction191701-14ca1a. That trial and
its separate review take priority. General type and proof-v3 drafts now exist
under runs, preserving v1/v2; they are unchecked. V3 supplies the explicit
order embedding required by the StrongPolygonSizeAtMost API. Searches
general-threshold-lower-construction-search.json and
general-threshold-lower-final-search.json found no
exact general constructor. This is a structural base for Q4's B construction,
not a special-instance sharpness task and not the unresolved upper N<=T.

The desired unchanged general conclusion is: for every k>=3 and
2<=a,u<=k, a coloring on Fin(T(a,u,k)) is decomposable, sweep-realizable,
all its cups have size<=u-1, all caps size<=a-1, and it avoids strong k.
The empty/unit-axis conventions of the virtual base are separate trivial
cases. Every legal nonzero leaf uses this universal construction.

Reuse accepted generic ordered-color embedding and public agreement transfer
to retain decomposability in the existing geometric ordered append. Reuse
Composition's cap/cup and crossing-strong bounds and public
decomposableThreshold_eq_choose/eq_window for the exact target cardinality.
Existing geometric exists_strongPascalExtremal and row append/prefix are
mathematical models, but their existential API does not retain IsDecomposable
or the cap invariant of a truncated row window. Do not claim those APIs
already supply the exact desired theorem or copy an instance certificate.

A local ordered append constructor suffices for both regimes. Existing
exists_deepComposition_coloring retains exact first/last restrictions;
pushforward and agreement yield decomposition of their images, and the
before/after partition identifies the ambient union. If their cap/cup
limits are pA,qA,pB,qB, the parent has
cap<=max(pA,pB+1) and cup<=max(qA+1,qB), with local strong coupling qA+pB.
The existing cap/cup ChainSizeAtMost recurrences prove the ranks, retaining
their separated-support semantics. Existing leftCount transport and the
crossing strong inequality handle all three strong-polygon cases. The final
finite-set consequences use the increasing enumeration of an arbitrary set,
so the original desired cup/cap/strong statement is retained exactly.

First construct the classical family at every p,q>=0 on choose(p+q,p),
with cap<=p+1, cup<=q+1, strong<=max(1,p+q), AND decomposability. At p=0 or
q=0 use a singleton. The Pascal step puts the(p+1,q) child below the
(p,q+1) child; coupling is(q+1)+(p+1)=p+q+2. Public choose_succ_succ'
gives the exact cardinal sum. The geometric classical source's induction
architecture can be reused, while the new append API retains decomposition.

When a+u<=k+3, choose p=a-2,q=u-2. The classical strong bound is at most
k-1, and the target cardinality is T by the public inactive identity.

Otherwise put d=k-2,L=k-a,U=u-2. For each t with L<=t<=d, inductively
construct the window L..t of size sum_{j in Icc(L,t)} choose(d,j), with
cup<=t+1, cap<=d-L+1, strong<=d+1, retaining decomposition. The first band
is the classical(d-L,L) family and choose symmetry gives choose(d,L).
Append classical(d-(t+1),t+1) at the next step. Its cap isd-t, so the
coupling with the prefix's cup t+1 is exactlyd+1. Its extended cap d-t+1
is at most d-L+1; cups increase to t+2. The new cardinal sum follows from
Icc(L,t+1)=insert(t+1)(Icc(L,t)), with explicit disjointness. At t=U,
the resulting cap/cup limits area-1,u-1 and size is the public active T.

The full unchanged legal statement, source/full checks, audits and exact
receipt review are the Done criterion if this is admitted before the
consolidation boundary. If not, leave it open and preserve this proof idea.
Even acceptance would leave the slot-assignment placement/gluing theorem
and finite recursion induction open; it would not establish B<=N or N<=T.
