# The critical nested-root charge

2026-10-03. General hand construction and an explicit upper-bound conjecture.
No new compiling theorem or general N formula is asserted.

Fix 3≤a≤k−1, 2≤u≤k and a+u≥k+3. Put s=k−1, p=a−1,
q=u−1 and L=k−a≥1. Let Γ be the two-zone cap gap

    Cp = [[p−1,p],[0,p−1]], Cu = [[q,q],[0,q]], r=(0,0).

Its three-zone version has cap diagonal(p−1,p−2,p−1), adjacent limits
p−1, outer limit p and an optional middle. `PROFILE-MAPS.md` identifies their
maxima for all these parameters.

The concrete conjecture is

    N_s(Γ) = G(a,u,k)
           = T(a−1,u,k) + binom(k−3,a−3)
           = T(a,u,k) − binom(k−3,a−2).

The lower inequality has an oracle-free construction. Take the existing
window lower construction of size T(a−1,u,k), as the upper child on the
left, and a classical cap(a−2),cup(L+1) set as the lower child on the
right. Their root coupling is (L+1)+(a−2)=s. Each flank has cap at most
p−1; caps crossing them have at most p points. Cups are at most q:
the right lower child can gain one left endpoint, and L+2≤q is exactly
the stated parameter condition. The size is G. The optional middle is empty.

Now take a classical set A with cap p and cup L, of size

    C = binom(p+L−2,p−1) = binom(k−3,a−2).

Insert A between the two flanks of B=Γ, and make A the root lower child,
B the root upper child. Its root coupling is L+p=s. A cap in B can gain
an A endpoint only when it stays in one flank, where its prior limit is
p−1; a cross-flank cap already has limit p and gains no outside A endpoint.
A cup in A can gain both B endpoints, giving at most L+2≤q. Therefore
the parent has cap p, cup q and strong limit s. Its size is G+C=T(a,u,k).
Pascal's identity says this insertion restores precisely the missing part
of the bottom band. This explains why a *tight classical sibling capacity*
is a plausible exact charge in this critical nested family.

For a fixed root, the lower child already has the coupling limit L. If the
uniform parent maximum were T and Γ's upper conjecture held, the endpoint
refinement would lower the upper child's capacity from T to T−C; the
endpoint penalty would be C and the root contribution C+(T−C)=T.
This is a restricted conjecture with a structural explanation. The Q3
two-profile example already excludes a universal penalty determined only
by standalone child maxima.

At(5,6,7), C=4 and G=15+6=21. The independent cap-gap boundary test
does give diagnostic N21. Its mirror at(6,5,7) has C=1 and G=20+4=24;
the cup-gap upper24 is still pending. All40 DS root cases for cap4/cup5,
strong6 are bounded by25 using classical bounds and the cap-gap result,
except the single enclosed-upper-singleton case relying on that mirror
upper24. These computations test the proposed general charge; they do
not prove its upper inequality for arbitrary parameters.

The unresolved general mechanism is a band allocation for Γ that places
its bottom-band points entirely on one side of the enclosing sibling's
core. Endpoint relabeling simplifies optional zones, but does not prove
that allocation. Repeatedly fitting new scalar losses would bypass this
same obstruction; the next proof should establish the allocation itself.

## The upper charge conditional on the missing invariant

The bottom band j=L has cap limit p and cup limit L+1. Its classical
capacity is

    binom(k−2,a−2) = C + D,
    C = binom(k−3,a−2), D = binom(k−3,a−3).

If a band decomposition places this band wholly on one side of the gap,
that side's cap limit is p−1, reducing the band's classical capacity to
D. The other bands contribute at most T(a−1,u,k). Thus a band partition
with this one-sided placement proves N(Γ)≤G. This gives the same C as the
explicit nested construction: the charge is a specific loss within the
bottom Pascal band, rather than a guessed correction to arbitrary N values.

The mirror(6,5,7) has a5-cup top band of capacity5. One-sided placement
in the cup-gap with diagonal limits4/4 reduces that band to at most4,
giving20+4=24. For the refined diagonal limits4/3, a partition placing
the band on the tighter side would give20+3=23. This requires a choice
of band partition on either side of the shared interval core, not merely
one unspecified side. The refined SAT boundary tests this consequence;
it does not construct the general partition.

BDL plus the required core-placement invariant therefore explains the
whole proposed family. Carrying that invariant through DS root splits
remains open. The earlier upper queries are now complete through independent
replacement proof covers: cap-gap N21, refined singleton N23, mirror cup-gap
N24 and uniform active N25 are diagnostic results. See Q4-Q3-ANSWER.md and
q7-root-cover-complete.json/q7-gap-cover-complete.json. These finite covers
do not establish the general placement invariant; further recursive
narrowing on this route would repeat the same missing invariant.
