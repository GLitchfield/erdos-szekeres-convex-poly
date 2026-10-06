# The E5 transfer at critical crossings (2026-10-05)

[P] = proved for point sets (signotope analogue [C] unless stated). [C] = computed, diagnostic, not Lean.
Code: `tse.py`, `crossq*.c`, `crossing_driver.py`, `cross_support.py`, `survivor_probe.py`, `tse_dec.py`,
`safe_reach.py`, `es6_example.py`. Data: `transfer/`.

**Verdict.** TSE is false, and no edge-local lemma can replace it.
- **(i)** At a segment crossing, the newborn family is exactly the opposite-side family of the crossed edge. At a
  beyond-crossing it is a reach-limited part of that family.
- **(ii)** That family is empty at about 1/3 to 1/2 of the non-hull gon-edges, even in decomposable sets.
- **(iii)** At those edges, the transfer is literally F at the cells just inside the edge.
- **(iv)** Moves certified by births at the crossed edge carry F from the hull into only 1.2% of interior cells at
  k = 5, and into none at k = 6.

So the continuation route cannot be closed edge by edge. The interior k-gons come from the global pocket covering
("survivors").

## 1. Structure of a crossing [P]

Let q cross the line xy at a point c, and write 𝒢_s(xy) for the (k−1)-gons having xy as an edge, with the rest on
side s.

- **L1.** Only gons G ⊇ {x,y} change status, because only the orientation of (x,y,q) flips. Such a G has xy as an
  edge. The dying gons lie on one side of xy, the newborn ones on the other, and the two families share only x, y.
- **L2 (segment crossing, c inside segment xy).** A point near the open segment on side S′ lies beyond the edge xy of
  every G ∈ 𝒢_S. It lies inside every other edge-line of G, since the open segment is strictly inside those lines and
  the adjacent cell inherits this. So **dying = 𝒢_S(xy) and newborn = 𝒢_{S′}(xy)**, whatever c is.
- **L3 (beyond-crossing, c on the ray beyond y).** The vertices q, x, y are nearly collinear, so q is adjacent to y
  in every dying and newborn polygon (…, x, y, q, w, …).
  - G dies iff c lies before the point where the line through w and its next vertex w⁺ meets the ray (the "reach" of
    G).
  - So dying = {G ∈ 𝒢_S : reach(G) > c} and newborn = {G′ ∈ 𝒢_{S′} : reach(G′) > c}.
- **L4 (exposure).** Let Σ(c) be the set of k-gons through q that avoid x or y; it is the same on both sides of c.
  - All k-gons through q lie in Σ(c) iff X−x+q and X−y+q are both extremal (k-gon-free).
  - On the inner side of a one-sided edge (𝒢_{S′} = ∅), **the k-gons through q are exactly Σ(c)**, since a k-gon
    containing x and y would need q in the pocket of xy.

Hence **the segment transfer holds automatically at two-sided edges. At one-sided edges it is equivalent to F at the
cells just inside.**

## 2. Critical crossings [C]

| | k = 5, all 4,994 orbits | k = 6, 300 sets |
|---|---|---|
| cells / directed crossings | 3,899,680 / 14,059,928 | 37,121,174 / 259,709,758 |
| critical | 608,926 (4.3%) | 453,914 (0.17%) |
| segment / beyond-left / beyond-right | 202,720 / 209,834 / 196,372 | 158,442 / 143,320 / 152,152 |

**In every critical crossing:**
- xy is an edge of every dying and newborn gon;
- dying and newborn lie on opposite sides;
- **xy is two-sided and never a hull edge**;
- there is at least one newborn.

**By type:**
- **Segment:** dying = 𝒢_S and newborn = 𝒢_{S′} in 100% of cases (L2).
- **Beyond:** q is adjacent to the near endpoint in 100% of cases. The whole family dies in 72% (k = 5) and 51% (k = 6);
  otherwise reach decides (L3).
- **Sizes:** |dying| and |newborn| are not matched. Pairs (5,1), (1,5), (3,2), … all occur, and there is no bijection
  rule.

## 3. TSE test [C]

**Gon-edges (x, y, side) that are one-sided and not hull edges:**

| | non-hull gon-edges | TSE fails |
|---|---|---|
| k = 5, all orbits | 165,050 | 53,914 (32.7%) |
| k = 6, 3,000 samples | 419,721 | 153,931 (36.7%) |
| k = 6, 5 constructions | 650 | 310 (48%) |
| k = 7, 19 constructions | 9,261 | 4,745 (51%) |
| k = 7, 152 flip-walk sets | 80,955 | 34,167 (42%) |

- Every set has failures. Hull gon-edges fail trivially (15,755 at k = 5), and none is ever critical.
- **No failure occurs at a critical crossing:** 0 out of 1,062,840 critical crossings.
- So TSE's failures never matter, because at a one-sided edge the cells just inside are always covered by Σ(c).

**This covering is robust, not marginal.**
- In ES(6,6,6), the edge 0–11 belongs to 72 pentagons, all on one side. The far side holds a single point, 15 (the
  deep top point).
- Pushing q across the segment at t = 0.1 … 0.9 kills those 72 hexagons, and 348–532 survivors remain.
- Constructions have 6–10 such edges whose far side holds exactly one point.

**Unsupported deaths** (a crossing that kills gons without any birth) are 56% (k = 5) and 65% (k = 6) of all
crossings with deaths. They come in three kinds:
- segment crossings at one-sided edges: 1,496,073 at k = 5;
- beyond-crossings at one-sided edges: 1,734,278;
- reach deficits at two-sided edges: 979,206.

None of them is critical.

**What the survivors look like (k = 5, inner side of a one-sided segment, 11,214 instances).**
- In 86% of instances one survivor is a single exchange G−x+q+w or G−y+q+w, with w on side S. Then w sits in the thin
  wedge where the pockets of G−y+q and G differ.
- In 14% no survivor is related to the dying gons.
- So no fixed exchange rule exists either.

## 4. Type (ii): the X-only analogue fails [C]

The natural X-only form is the reach lemma: along each ray beyond y, the largest reach of 𝒢_{S′} is at least the
largest reach of 𝒢_S. It fails 979,206 times at k = 5 (deaths without births at two-sided edges). It is never needed:
those crossings are never critical, again because of Σ(c).

## 5. Decomposable X [C, with a structural reason]

- TSE fails at 31.9% of non-hull gon-edges of the 722 decomposable k = 5 orbits (non-decomposable: 32.8%).
- **Reason [P].** Lemma M puts B above every A-line, so a gon-edge inside A that faces away from B has only A-points
  beyond it. A G′ there would lie inside A.
  - With a singleton deep part A = {a} (699 of the 722 orbits have only singleton root splits), consider an edge of
    conv B facing a. If a (k−1)-gon uses it, the only point beyond it is a, so TSE fails there.
  - The ES(6,6,6) edge above is an instance.
- So the deep-below structure produces one-sided edges rather than closing them. F's own case gives no shortcut.

## 6. Paths cannot be chosen to avoid the problem [C]

Take the extension graph: cells, line crossings, and sweep moves (q passes the vertical through v when v is extreme
in π).
- **The graph is connected:** 226,227 of 226,227 cells reached, at k = 5 over 300 orbits.
- **Safe moves.** Call a crossing safe if nothing dies or something is born; such a move preserves F with a certificate
  local to the crossed edge.
  - From the 82,667 extreme cells (36.5%, where F = C1 by E4), safe moves reach only 84,398 cells. That is 1,731 of
    143,560 interior cells (1.2%).
  - From the far cells (q at ±∞) they reach 20.3%.
  - k = 6 (2 sets, 224,552 cells, graph connected): from the 30,300 extreme cells, safe moves reach **0** interior
    cells; from the far cells they reach 1.0%.
- So almost every interior k-gon is a survivor: it is never inherited through a birth at the wall just crossed.

## 7. Proof attempt and what it shows

- **Proved [P]:** L1–L4, the TSE ⇒ segment-transfer implication (with the reach caveat for type (ii)), and the
  equivalence "segment transfer at a one-sided edge ⟺ F just inside it".
- **The chart idea for TSE is dead.**
  - Sending line xy to infinity turns 𝒢_{S′}(xy) into (k−3)-chains of the far side that are convex towards both
    points at infinity.
  - But the far side can be a single point (ES(6,6,6); every singleton-split decomposable set). So no cups–caps or
    ES(k−1) count on the far side can force TSE.
  - Extremality constrains the whole set, not one side of a gon-edge.
- **What is not proved:** any transfer at one-sided edges or reach-deficient lines. Section 6 shows the route needs it
  for 99–100% of interior cells.

**Understanding.**
- A k-gon through an interior q survives a crossing because of other pockets, not because of the crossed edge. The
  E5/F continuation route therefore has the same core as F: the covering by pockets is global.
- The obstacle is quantitative and grows with k. One-sided edges rise from 33% to 37% to 42–51%, and unsupported
  deaths from 56% to 65%.

**Open questions, each with its computation.**
1. Is there a canonical survivor? For example, a k-gon through q using a hull vertex of X. Test: mine the
   survivor families of the 11,214 k = 5 instances for an invariant shared by all of them.
2. Covering potential. Does Σ(c) along a one-sided segment have a lower bound in terms of |𝒢_S|? Test: tabulate
   min_c |Σ(c)| against |𝒢_S|.
