# H1 closed by a marker lemma (claude-h1-20261002)

**Status:** H1 and TG are proved by hand for all k >= 5. Neither proof recurses on A's root split, so chains of nested
singletons never come up. Every step was also machine-checked (diagnostic, not Lean).

"Classic" means L|R with each side 4-cap-free. The 4-point rule: for a<b<c<d the sequence χ(abc), χ(abd), χ(acd),
χ(bcd) changes at most once.

## Marker Lemma
Let A be classic with no (m+1)-cup, m >= 3, and suppose every m-cup straddles a gap h. Let E be the left ends and F
the right ends of the m-cups.
- **WE:** E or F contains no 3-cap.
- So that set is a cup on one side of h, with at most m-1 points.
- If A also has no 5-cap, then **|A| <= m(m-1)**: deleting that set leaves no m-cup, and the classic Z bound gives
  (m-1)^2 for the rest.

The bound is tight: m(m-1) is satisfiable and m(m-1)+1 is UNSAT for m=3,4,5 (SAT). The old virtual-marker bound was
m^2-1.

### Proof of WE
Suppose both fail. Take a 3-cap (p,q,e) where e starts the m-cup D=(e,d2,…,dm). Take a 3-cap (f,q',p') where f ends
the m-cup C=(…,c',c'',f).
- **(S1)** (x,e,d2) is a cap for every x<e, and (c'',f,y) is a cap for every y>f. Otherwise there is an (m+1)-cup.
- **(S2)** e < h <= f.
- **(S3)** By (S1), (p,q,e,d2) and (c'',f,q',p') are 4-caps. They cross L|R, so p,c''∈L and d2,p'∈R; hence c''<d2.
- **(S4)** No m-cup ends left of h or starts right of h. So (c',c'',y) is a cap for c''<y<h, and (x,d2,d3) is a cap
  for h<=x<d2. Also (c',c'',d2) and (c'',d2,d3) are not both cups, since C⁻∪D⁺ would have 2m-2 >= m+1 points.

**Lemma X.** Suppose e<c'' and (c'',d2,d3) is a cap.
- The 4-point rule on (e,c'',d2,d3) gives (e,c'',d2) cup.
- The 4-point rule on (q,e,c'',d2) gives (q,e,c'') cap.
- So (p,q,e,c'') is a 4-cap inside L, a contradiction.

**Lemma X'** (the mirror image). If d2<f and (c',c'',d2) is a cap, then (d2,f,q',p') is a 4-cap inside R.

**Cases.**
- **(c',c'',d2) a cup.** Then (c'',d2,d3) is a cap.
  - e=c'' clashes with D.
  - If c''<e, the 4-point rule on (c',c'',e,d2) forces (c',c'',e) cup, contradicting (S4).
  - So e<c'', and Lemma X applies.
- **(c'',d2,d3) a cup.** The mirror image, via Lemma X'.
- **Both caps.**
  - Lemmas X and X' and two coincidence checks leave c''<e<h<=f<d2.
  - Then (S4) and the 4-point rule give (c',c'',e) cap, then (c'',e,f) cup, (c'',f,d2) cap, (f,d2,d3) cap and
    (e,f,d2) cup.
  - So (c'',e,f,d2) reads cup,?,cap,cup, which is impossible. ∎

WE uses only the 4-cap-free sides, the absence of an (m+1)-cup, and the straddle hypothesis. It needs no 5-cap
condition, no convexity and no decomposability. Without the straddle hypothesis, SAT finds a counterexample at n=6.

## Corollaries
- **H1.** If U = A << {b} with b interior, every (k-2)-cup of A straddles b. With m=k-2, |A| <= (k-2)(k-3) = H-1.
- **Chains.** For U = X << b_t << … << b_1, apply H1 to A = U-b_1. So |U| <= H for every t, and no chain invariant is
  needed.
- **TG.** Suppose every m-cup straddles h1 or h2, with h1<h2.
  - The m-cups that miss h1 lie right of h1 and straddle h2. The lemma on A∩[h1,∞) gives a cup X2 of at most m-1
    points meeting them all.
  - A-X2 has all its m-cups straddling h1, so |A-X2| <= m(m-1).
  - Total: m^2-1 = (v-1)^2-1, which is tight (satisfiable for v=4,5).
- **a5c reduction:** H1, TG and CS+straddle are no longer needed. For u=k-1 the a5c table rests on R2 (still SAT-only)
  and the cup-block lemmas.

**Why it is true:** a 3-cap among the left ends forces a 4-cap overhanging the start of a maximal cup. A 3-cap among
the right ends forces one overhanging the end. The 4-cap-free sides pin the two overhangs to opposite sides of L|R. A
4-point interaction between the tail of one cup and the head of the other then yields a 4-cap inside a side, or a
maximal cup on the wrong side of h.

**Chains (diagnostic, moot):** passengers act only through f(x), the LIS of passengers left of x, and g(x), the LDS
right of x. Tight chains are monotone and sit at an end of X; non-monotone chains cost more than t.

## Evidence
- `we_steps.py`: each proof step is UNSAT in a local 10-role model, using only the facts it cites, for m=3..12.
- `conjW_sat.py` (`we_global_sat.txt`): WE is exhaustive for m=3..5, n<=2m+4.
- `classic_marker*.py`: tightness of m(m-1).
- `replay.py` (`replay_out.txt`): 0 violations on 725 H1 instances, 522 chain instances, 2,733 random (set, gap)
  pairs including tight ones, and 29,938 two-gap pairs.

**Next:** R2, and Lean for the marker lemma (short and local).
