# How a new point forces a k-gon (Workstream F), 2026-10-05

[P] = proved here (finite checks exhaustive, code in `extlib.py`). [C] = computed, diagnostic, not Lean.

**Bottom line.** There is no recursive mechanism.
- Two-halves gluing fails in its usable forms (a)–(c) at k = 5, 6, 7. Form (d) holds for k ≥ 6 but is generic.
- Relative to a halving, the forced k-gon is split like a random set.
- What is exact: a local description of the k-gons through q (E1, E2); a reduction of extreme q to C1 (E4); and a
  line-crossing "transfer" form of F (E5). Interior q is the hard core.

## 1. Exact reformulations

**E1 [P].** Put q at position p, and let the pair bit c(a,b) be the colour of the sorted triple {a,b,q}.
- One-change on {a,b,c,q} sees only abc's colour and (c_ab, c_ac, c_bc).
- In all 8 cases the patterns 010 and 101 are illegal, so the bits form a linear order π (the slope order of the lines
  qx).
- **Extensions at p ↔ orders π whose restriction to each triple is one of 4 allowed orders.**

**E2 [P].** An 8-case check shows that {a,b,c,q} is strong iff a, b, c in π-order are ccw.
- **q+G is a k-gon ⟺ every triple of the (k−1)-set G is ccw in π-order** (seen from q, G turns left).
- [C] Equivalently, a,b,q,c,d is a convex pentagon for exactly one edge bc of G (a and d are its neighbours). 0
  exceptions in 260,151 pairs.

**E3 [P].** π = (p, …, n−1, 0, …, p−1) is legal for all X and p ("q at +∞"). It restricts to rotations of x-order, so
its k-gons are q + the (k−1)-cups. **Hence F ⇒ cup(X) ≥ k−1**, and likewise for caps.

**E4, extreme q [P for point sets; one step is [C]].** Let q lie in no triangle of X.
- A 4-set is strong iff no point lies in the triangle of the others [P, 8 cases]. So strongness depends only on
  orientations.
- Some rotation of π is a sweep order. This is the projective chart sending a line through q that misses conv X to
  infinity; for signotopes it is [C], 3,917 of 3,917.
- That chart X^q is again an extremal set, and the k-gons through q are q + its (k−1)-cups.
- So **F at extreme q ⟺ C1 for X^q**, and F_extreme(k) ⟺ C1(k) ⟺ ETV(k; k−1, k).
- Extreme q are 35% (k = 5) and 17% (k = 6) of the extensions.

**E5, crossings [P].** When q crosses the line xy of two π-adjacent points, only triples {x,y,z} change π-orientation.
So:
- only (k−1)-gons G ⊇ {x,y} die or are born;
- the dying ones have G∖{x,y} on one side of xy, the newborn ones on the other;
- dying and newborn gons share only x and y.

A generic path from a far point (E3) reaches every q. So, for point sets, **F ⟺ C1 + transfer: if every k-gon through
q uses x and y and q crosses line xy, then X has a (k−1)-gon through x and y beyond xy that the new q extends.**
- [C] Such critical crossings are 3.3% of all crossings at k = 5 and 0.2% of those sampled at k = 6.
- In all 3,532 critical crossings at k = 5 (40 orbits), the transfer is local in type: if q crosses the segment xy, it moves from
  the pocket of edge xy of G into the pocket of edge xy of G′; otherwise q is adjacent to exactly one of x, y in both.

## 2. Counts [C]

**k = 5, all 4,994 orbits.**
- 3,899,680 extensions (662–978 per orbit), each with a pentagon. This re-derives ES(5) = 9.
- 8.9% have a unique pentagon. Job 20261005-181056-06a29a.

**k = 6, 3,000 samples.**
- All 369,077,555 extensions have a hexagon; 0.46% have a unique one.
- 12–234 halvings per set. Job 20261005-181326-c0b027.

**k = 7.** The heptagon-free-extension SAT search ran on 19 constructions and 152 flip-walk sets, 33 positions each:
5,643 of 5,643 UNSAT. Job 20261005-181738-58513b.

## 3. The two-halves test

**Setup.** X = X0 ⊔ X1 is a halving, and G_i ranges over all (k−1)-gons through q in X_i + q. A pair (G0, G1) is good
if G0 ∪ G1 contains a k-gon.

**Fraction of extensions satisfying each form:**

| form | k = 5, all | k = 6, 3,000 sets | k = 6 interior / extreme (200 sets) | k = 7 |
|---|---|---|---|---|
| (a) ∀h ∀ pair | 21.3% | 0.11% | 0.05% / 0.5% | ≤ 8–39%† |
| (b) ∀h ∃ pair | 73.5% | 74.3% | 72.2% / 90.7% | ≤ 96–97%† |
| (c) ∃h ∀ pair | 99.54% | 97.98%, every set fails some | 98.0% / 98.8% | 22 of 45 fail‡ |
| (d) ∃h ∃ pair | 99.992% (317 fail) | 100% (0 of 369M fail) | 100% | 45 of 45 pass‡ |

- † 10,544 SAT-sampled extensions of 59 sets, with at most 100 halvings per set.
- ‡ The 45 extensions that failed (d) with 100 halvings were re-run against ALL halvings of their sets (12,500–63,504 per
  set). Job 20261005-185759-f094c8.

**No form gives a lemma.** Even with the halving chosen after q, (c) "any two forced half-gons glue" fails at every k.

**Why [C].**
1. **The halving is invisible to K.** The split |(K−q) ∩ X0| is close to hypergeometric:
   - k = 5: observed .28/.49/.23, hypergeometric .24/.53/.24;
   - k = 6: observed .15/.34/.35/.16, hypergeometric .13/.37/.37/.13;
   - k = 7: observed .07/.25/.37/.25/.07, hypergeometric .08/.25/.35/.25/.08.

   K is balanced across the halves, while each G_i lies inside one half.
2. **The forced half-gons often lie in no k-gon.** "Every halving has some G_i that extends" holds for about 70% of
   extensions at k = 5 and 81% of interior extensions at k = 6.
3. **(d) is generic.** At k = 5, random non-halving balanced partitions give (d) 99.86% (halvings 99.99%) but (b) only
   7.5% (halvings 70.6%). Halvings correlate with K; (d) comes from the sheer number of k-gons through q.
4. **The 317 (d)-failures at k = 5 share one structure.**
   - q is extreme, and exactly two pentagons q+A, q+B pass through q.
   - X = A ⊔ B with A and B convex quadrilaterals; all 233 orbits involved have convex layers 4-4.
   - Each half's unique forced quadrilateral is (A∩X_i)+q or (B∩X_i)+q, and their union never contains A or B.
   - Only at k = 5 is 2(k−1) = 2^(k−2).

**Example (k5#8, p = 0, π = 0 4 3 1 2 5 6 7).**
- The pentagons are q+{0,1,3,4} and q+{2,5,6,7}.
- The halving {0,1,3,5} | {2,4,6,7} forces only q+{0,1,3} and q+{2,6,7}. Their union misses 4 and 5.

**Interior (b)-failure (same X, p = 1, π = 7 6 4 5 0 3 2 1).**
- The pentagons are q+{0,1,2,3}, q+{0,4,6,7}, q+{1,2,4,5}.
- {0,2,5,7} | {1,3,4,6} forces only q+{0,5,7} and q+{1,3,4}. Every pentagon splits 2+2.

## 4. Shape of the forced k-gons [C]

**Bands.** The ES-construction mechanism is: q in band j; a (j+2)-cup in X_j+q plus one point per higher band, or a
(k−j)-cap plus one point per lower band.
- Its band profile occurs for 90% (k = 5) and 72% (k = 6) of (stack, q) pairs; with the chain condition, 76% and 49%.
- At k = 5, 24–28 of about 300 stacks per set work for every q. At k = 6, none of 200 stacks did (1 set tested).
- Band transversals are 11% and 1.4% of the k-gons through q. The singleton bands are used at about the random rate.

**Half-planes.** The k-gon through an interior q can be alone in its half-plane. In 191 of 15,119 sampled k = 5
extensions, every half-plane through q that holds a pentagon holds only its 4 points.

**Blocking family** (exact minimum cover of all extensions by R(G) = {q : G+q strong}).
- k = 5: 5–9 of about 30 quadrilaterals (median 7).
- k = 6 (120 sets): 12–17 of 262–805 pentagons (median 14).
- Only 1–6 members are forced, and k = 6 sets usually have 50 or more optimal covers. So there is no canonical family.

## 5. Where this leaves F

**Current proof idea.** Far and extreme q are exactly C1 (E3, E4), which is an ETV instance. Everything else is the
transfer across lines (E5). There is no proof idea for the transfer.

**What every attempt hits.** The k-gon through an interior q is not localised by halves, bands or half-planes, so any
recursion must couple both sides of a line through q. Halvings do not do this.

**Open questions, each with its computation.**
1. **The E4 chart step for signotopes.** Fix the rotation canonically; check it on all 5-point signotopes.
2. **Is the newborn gon at a critical crossing determined by the dying one** (for example as a chart cup beyond xy)?
   Test: tabulate (dying, newborn) pairs exhaustively at k = 5, and sample at k = 6.
3. **(d) at k = 7 with all halvings on unbiased samples.** The result would still be generic, not a mechanism.

**Files** (all under `extension/`):
- `extlib.py` (library) and `extq*.c` (evaluators);
- drivers: `k5_ext.py`, `ext_driver*.py`, `ext_list_driver.py`, `split_driver.py`, `k7_sat.py`, `cover6.py`,
  `k7_dfail_recheck.py`;
- probes: `*_probe.py`, `quant_by_depth.py`, `null_partitions.py`, `band_*.py`;
- data: `k5_ext.jsonl`, `k6_ext/`, `k6_split/`, `k7_sat/`, `k7_halves/`, `k7_dfail_recheck.jsonl`, `cover6.jsonl`.
