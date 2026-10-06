# F: the structure of extremal sets (2^(k−2) points, no convex k-gon)

Living document for Gavin's 10-05 direction: "characterize mathematically all arrangements of 2^n points without an
n-gon and see what we can say". Convention: k-gon, with 2^(k−2) points (the extremal size). Objects are rank-3
signotopes, i.e. abstract sweeps. Every signotope with at most 8 points is realizable.

## Why this matters for F, and what it cannot avoid

F says: a decomposable extremal S plus any new point q contains a k-gon.
- **F implies the diagonal case of Theorem 8 [P].** Subsets of decomposable sets are decomposable. So
  (2^(k−2)+1)-point decomposable counterexample minus any point = a decomposable extremal S plus q.
- Therefore F cannot bypass B's lock by tree induction. The hope is global structure of extremal sets.

## Data so far (all [C], diagnostic)

| k | n | extremal signotopes | notes |
|---|---|---|---|
| 4 | 4 | 4 (1 orbit) | n = 5 UNSAT: ES(4) = 5 |
| 5 | 8 | **19,870 (4,994 orbits)**, complete | n = 9 UNSAT: ES(5) = 9; 722 orbits (14%) decomposable |
| 6 | 16 | about 10^15–10^18 (Knuth estimate, 25 walks) | full enumeration impossible; SAT samples |
| 7 | 32 | ? | lazy-gon SAT samples (job 20261005-164523-5cbc85) |

**k = 5, every extremal set (complete):**
- cup = cap = 4;
- a BDL band partition with full bands 1 + 3 + 3 + 1. This is weak at k = 5: just a point, a 3-cap, a 3-cup and a point.

Chain counts, point profiles and the number of overfull points all vary.

**k = 6 (job 20261005-164412-2bdf1e, interim 1,500 / 3,000):**
- every sample has cup = cap = 5 and a full band partition 1 + 4 + 6 + 4 + 1;
- none is decomposable;
- all have overfull points.

Contrast: BDL FAILS on tight off-diagonal general sets, at (7,5,7) with n = 26 (claude-hypergraph-20261003).

## The universal structure found: full band stacks (FBDL) [C]

**FBDL (full-range diagonal band lemma).** Every k-gon-free signotope X partitions into bands j = 0..k−2 with
cup(X_j) <= j+1 and cap(X_j) <= k−1−j.
- By the classical cups–caps bound |X_j| <= C(k−2, j), so **FBDL ⇒ ES**. Extremal sets are exactly the full
  stacks: every band is a classical extremal (k−j, j+2) block.
- Band 0 and band k−2 are single points, band 1 is a (k−2)-cap, and band k−3 is a (k−2)-cup.

**Evidence.**
- ALL pentagon-free signotopes, every n <= 8 (24,692 sets).
- 3,000 / 3,000 random extremal k = 6 sets.
- Every stored construction at k = 6, 7, 8 (ES, Valtr, Baek–Balko Theorem 19).
- k = 7 flip walks: so far all endpoints, at Hamming distance about 140–200 from the constructions.
- The known own-range BDL counterexamples (X14; the three tight (7,5,7) n = 26 sets) all satisfy FBDL. Their
  failures were caused by restricting the band range to [k−1−cap, cup−1].

**What is NOT universal (the structure is loose):**
- **Decomposability:** 14% of the k = 5 orbits; none of the random k = 6 samples.
- **FLAG-BDL** (prefix unions have no (j+2)-cup and suffix unions no (k−j)-cap, as in the ES construction): fails
  on 67% of the k = 5 orbits, including 158 / 722 decomposable ones.
- **Canonical bands:** at k = 5, 99% of point-instances can sit in any band; at k = 6 nearly all can.
- **Rigid blocks:** classical extremal (4,5) blocks number 61,784 up to reversal; only 5% are decomposable.

So the picture is a rigid count, a loose partition and flexible gluing.

**Consequences.**
- F ⟸ FBDL on S ∪ {q}. FBDL for general signotopes is ES-strength.
- For decomposable sets, FBDL makes the root composition lock-free: put A below band p and B at or above band p.
  But L(A) and U(B) still need own-range partitions deeper down, where the lock (and its mirror) recurs.

## Candidate characterizations (to test)

- **C1:** cup = cap = k−1. Holds at k = 5 (complete) and k = 6 (samples). For general k this would follow from ETV.
- **C2 (diagonal band structure):** X = ⊔_j X_j with |X_j| = C(k−2, j), each X_j a classical extremal
  (k−j, j+2) cups–caps set. With the Moshkovitz–Shapira bijection inside each band, this gives a bijection
  X ↔ {0,1}^(k−2), with band = weight.
- **C3 (halving = diagonal PSL):** X = Y ⊔ Z with Y, Z both (k−1)-gon-free of size 2^(k−3), i.e. both extremal for
  k−1. Recursively, X carries a complete binary tree of halvings, which gives another X ↔ {0,1}^(k−2).
- **Converse question (constructive characterization):** which unions of two extremal (k−1)-sets, or which band
  stacks, are k-gon-free? This is the gluing condition.

## Open questions, each with the computation that answers it

1. Does C2 hold at k = 7 (diagonal)? Run the k = 7 sampling job. A failure kills C2 as a characterization.
2. Does C3 hold on k = 6 and k = 7 samples? Is the halving unique? Run a SAT halving search on the samples.
3. Are the band partitions or halvings of extremal sets unique, or canonical up to a small family? Count them at
   k = 5 (complete) and on k = 6 samples.
4. Gluing: for the halving X = Y ⊔ Z, what cross-triple patterns occur? Is the colour of a cross triple determined
   by the positions in the two halves' trees?


## Round 3 (10-05 evening): the counting skeleton of extremal sets [C]

**Gavin's focus:** characterize the extremal sets themselves (2^(k−2) points, no convex k-gon).

**Universal on every extremal set tested.** Coverage: all 4,994 orbits at k = 5; 3,000 SAT samples at k = 6; at
k = 7, 19 constructions plus 152 flip-walk sets (Hamming distance 140–200 from the constructions); at k = 8, 3
constructions (bands only).
1. **Chains:** cup = cap = k−1.
2. **Full band stack:** bands of sizes C(k−2, j), each a classical extremal (k−j, j+2) cups–caps block.
3. **Halving:** X = X_0 ⊔ X_1 with both halves extremal for k−1.
4. **Cube labelling:** a bijection φ: X → {0,1}^(k−2) such that
   - every prefix class X_w is extremal for k−|w| (no (k−|w|)-gon);
   - each weight class inside X_w is a classical block (cup <= j+1, cap <= k−|w|−1−j).
   This is exactly the skeleton of the Erdős–Szekeres construction: a hierarchy of band-compatible Pascal halvings,
   with band = word weight.
   Characterization form: X is extremal iff X is k-gon-free and carries a cube labelling. The "if" direction is the
   size count. The "only if" direction is the conjecture, true on all data.

**Not rigid (the skeleton exists in many ways, and nothing finer is universal).**
- **Multiplicity:**
  - thousands of cube labellings per k = 5 set (3,200 to over 5,000);
  - 36–106 halvings per k = 6 set;
  - nearly every point can sit in any band.
- **Finer structure that fails to be universal:**
  - decomposability: 14% of k = 5 orbits, 0 of the k = 6 samples;
  - the ES flag;
  - deep-below or x-separated gluing of halvings;
  - convex-layer profiles: 2 at k = 5 (3-4-1, 4-4), 23 among 300 k = 6 samples, 78 among 152 k = 7 sets;
  - rigid blocks: the classical (4,5) blocks alone number 61,784.

**Reading.** Extremal sets are "anything that carries the ES counting skeleton and avoids k-gons". The skeleton is
forced; the geometry on top of it is free. A list classification exists only at k = 5.

**For F and ES.**
- Showing that EVERY k-gon-free set carries the skeleton at its own size (FBDL / PSL) is ES-strength.
- F needs it for S ∪ {q}.
- The open mathematical question is the gluing rule: which unions of two extremal (k−1)-halves are k-gon-free, and
  how adding q breaks it.

## Round 4 (10-05 late): gluing and extension, run in parallel (gluing/GLUING.md, extension/EXTENSION.md)

**Gluing.**
- **Every pair of halves occurs:** all type pairs at k = 5 and k = 6.
- **k = 5 [P]: exact pairwise rule.** A mixed pentagon is a triangle of one half plus two points of the other. The
  arc-separation condition on the line zz′ decides it. So every extremal 8-set is two triangle-plus-interior sets side
  by side, glued by 8 slope labels.
- **Twin lemma [P, given ES(k−1)].** Points of one half indistinguishable to the other, whose line misses it, force a
  k-gon. Halves must twist; deep-below gluing never glues halves.
- **k = 6:** not pairwise ((3,3)-hexagons). No compression found.

**Extension.**
- **Counts.**
  - All 3.9M extensions at k = 5 and 369M at k = 6 contain the k-gon.
  - k = 7: 5,643 SAT instances UNSAT. No 33-point heptagon-free extension of the 171 known and walked sets.
- **The two-halves mechanism fails as a lemma.** Forms (a)–(c) fail; (d) holds but is generic. The forced k-gon
  splits across a halving like a random set.
- **Exact facts [P].**
  - Extensions are slope orders π.
  - q + G is a k-gon iff G turns left in π-order.
  - q at +∞ is always legal, so F ⇒ cup = k−1.
  - **F at q outside conv X ⟺ C1 in the projective chart X^q ⟺ the ETV(k; k−1, k) instance.**
  - **E5, line crossings:** moving q, k-gons through q die or are born only when q crosses a line xy, and only gons
    through x, y change. So F ⟺ C1 + a local TRANSFER statement at critical crossings.
- **Hard core:** q inside the hull. The forced k-gon is not localised by halves, bands or half-planes.

**Synthesis: the only new proof SHAPE from this round is continuation.** Start q at infinity (a k-gon exists by
C1). Move q along a generic path. The k-gons through q change only at line crossings, and the transfer must supply
a new one whenever all current ones die. At k = 5 all 3,532 critical crossings are local in type. Open: is the
newborn gon determined by the dying one (exhaustive at k = 5, sampled at k = 6)? Note: for all extremal X,
C1 + transfer is ES itself.
