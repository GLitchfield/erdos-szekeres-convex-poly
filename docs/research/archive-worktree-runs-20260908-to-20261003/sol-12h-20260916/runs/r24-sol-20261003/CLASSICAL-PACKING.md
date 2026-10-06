# Classical clear zones and a cup-interval invariant

2026-10-03 16:23 UTC. Hand mathematics and diagnostic checks only. This note
does not establish a new Lean theorem or the general happy-ending upper bound.

For a decomposable ordered coloring with cap maximum at most p and cup maximum
at most q, let nu_q be the largest number of q-cup endpoint intervals with
pairwise disjoint open interiors. Intervals may touch at a shared endpoint.
The q-cup intervals meet gaps between successive points, so ordinary interval
stabbing identifies nu_q with the minimum number of gap cuts meeting all of
them. Thus nu_q+1 is the minimum number of consecutive nonempty blocks, each
free of q-cups. If there is no q-cup, this number is one. In particular, a
profile with d consecutive q-cup-free zones forces nu_q <= d-1, including
profiles with empty zones.

The proposed general classical capacity is

    F(p,q,d) = sum_{0 <= h < min(d,p)} choose(p+q-h-3,p-h-1)
             = choose(p+q-2,p-1) - choose(p+q-d-2,p-d-1),

with the last term zero when its lower argument is negative. The conjecture
is |S| <= F(p,q,nu_q+1). This is an explicit invariant proposal, not a fitted
per-zone penalty. It would imply the upper for d uniform clear zones, and
explain why cap/cup4 with three cup3 zones has capacity19 rather than20.

The lower construction for d uniform clear zones has a structural recursion:
place a classical cap-p/cup-(q-1) tree first as the lower child, then a
cap-(p-1)/cup-q tree with d-1 clear zones as the upper child. The two mixed
extensions give global cap p and cup q; the first child supplies one clear
zone. Repeating gives the displayed sum. If d>=p, a classical cap-p/cup-q
construction reaches the full classical value. This is a k-free lower
construction; a strong-size condition must be checked separately.

The interval-packing interpretation itself is elementary: the greedy earliest
right endpoint supplies an optimal stabbing cut and removes exactly the
intervals hit by it. Equivalently, maximum disjoint gap-index intervals equals
minimum stabbing cuts. The endpoints of an interval [i,j] correspond to gap
indices i..j-1, so two such intervals are disjoint exactly when one chain ends
no later than the other begins. This is why touching endpoints are allowed.

Diagnostic job `20261003-121458-774ad0` reused the shared exact decomposable
class enumerator and endpoint-chain DP. All791 colorings on2..6 points obey
the candidate bound, and the greedy packing agrees with an independent DP
for minimum clear-block partition. Runtime0.076s. Evidence:
`classical-packing-n6.json` and `classical_packing.py`. This small census was
commissioned to test the interpretation and refute a false invariant; it is
not evidence of a general theorem.

There is a concrete obstruction to the most obvious induction. The ordinary
cup-cap proof partitions by T, the points starting a p-cap, then reduces the
cap bound on S\\T. It does not necessarily reduce nu_q. On four points take
cup triples012,013,023 and cap triple123. The root is the lower cap {1,2,3}
and the upper singleton {0}. Here p=q=3, nu_3=1, T={1}, and S\\T={0,2,3}
is still a3-cup. Thus nu_3 does not decrease. The candidate bound remains
valid (4<=F(3,3,2)=5), but the proposed recursion

    classical(p,q-1) + F(p-1,q,d-1)

cannot follow by merely applying the standard starts-cap partition. Its
missing information is the endpoint loss or unused capacity in T. This is
the same substantive issue encountered in the DS profile law: a scalar
capacity or packing count does not describe the joint endpoint restrictions.
No larger census is commissioned to conceal that proof obstruction.

Open question: is there a profile-indexed cap-start/interval allocation whose
unused classical capacity pays for every failure to decrease nu_q? A proof
needs the allocation rule and its endpoint monotonicity; a counterexample to
F would reject this interpretation entirely. The present evidence answers
neither question in general.
