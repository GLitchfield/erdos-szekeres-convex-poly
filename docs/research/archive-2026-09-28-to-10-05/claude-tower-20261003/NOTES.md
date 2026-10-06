# Q17: does a finite tower of lifts close the induction? (claude-tower-20261003)

[P] proved by hand; [C] computed exactly (all band partitions enumerated, no caps), diagnostic, not Lean.

## Tower context

Per side (bottom shown: floor F, orientation G; G′ is the mirror; top = complement):
- position cut s: band F ≤ s−1;
- neighbour cut: band F+1 lies on one side of a gap;
- tower: t_1 ≤ … ≤ t_m (m = k−2−F), meaning no L-cap of band F+1 ends before t_L.

**Rule** (Z classic sibling). The Z-points the cut forbids are lifted to band F+1. Each lifted z adds (m, gap z) and
(L, gap z) for every inherited pair (L+1, t) with z < t. The height is at most β−1.

## Tower Closure Lemma [P]

Let X0 = Z1<<X1, …, X_{r−1} = Z_r<<W be absorptions (cap β throughout), with all Z-points right of L*(X0) and in band
lo+1. Then P∪Z is valid iff P is valid and |D| + g(D_end) ≤ β−1 for every cap D of P's band lo+1, where g is the
longest inner-to-outer chain of Z-points after D_end.

*Proof.* At the outermost level a chain meets, apply DS:
- cups ≤ cup Z_j + 2 ≤ lo+2, by the node condition;
- a cap is either D + (a chain after it), or starts at a Z-point and then has length ≤ β−1 by the key fact.

So the tower is the **exact** criterion along nested absorptions. A lift forced left of L* creates caps z+D; the
neighbour cut on the near side removes them.

## Q9f's framework [C]

Q9f's fixed parent contexts and its menu, re-implemented exactly; this reproduces Q9f's counts.
- **Q9f's 40:** 40/3340 fail; with the tower entry, **0**.
- **All of n = 7, ≥3-band absorption:**
  - Z<<B: 432 fail, 8 with the tower, **0** with the neighbour cut;
  - A<<Z: 38 fail, **0** with the top-side rule.
- **2-band classes:** 73/73 close (1/25 sample).

## Realisable contexts [C]

Contexts are generated from the trivial root context (one tree, every k). The menu is keep → reserve → lift, each
plain / either / right / left. 2-band nodes are truth-only base nodes.

| rule (greedy) | n ≤ 7 (23,286 roots) | n = 8 |
|---|---|---|
| backtracking | 0 fail, tower and single | 1/10: 0 |
| lift-first | 30 (tower) vs 150 (single) | |
| keep-first, orientation from Z | 18 vs 18 | |
| + deferred side ("either") | 0 vs 0 (3 trees: 0/69,858) | 1/10 single: 0 |
| + no truth oracle on the child | 0 vs 0 | 5/18,296 (partial) |
| + **side inheritance (final)** | **0** | **all: 0 / 442,930** (198,274 colourings; job cd5696) |
| final, 2-band nodes recursed | 49/11,613; 9 with the opposite-orientation rule | |

- **Truth:** the final rule delivers only non-empty contexts to base nodes (n <= 8). **False from n = 10, see Resumed.**
- **Towers on that path are rare.** Backtracking proofs at n = 8 use 946 two-level towers and no partial three-level
  profile.
- **Side inheritance.** Without it, two nested forced lifts into one band got opposite sides and emptied the band
  (masks 33284373919049749 and 67555026272288668). Same-side cuts compose like s.

## More than one band?

Not on the final path. A cut on band F+2 appeared only after bad greedy choices and at 2-band nodes. Even such a cut
is finite: O(k²) cuts in all. **No unbounded parameter.**

## Double induction

- **Outer:** the tree. **Inner:** the profile level i ≤ β−1.
- **Base:** classic-classic nodes and 2-band nodes.
- **Steps,** each exact by DS [P]:
  - wide-wide: inheritance, since cap Y = cap A and cup Y = cup B are forced;
  - keep (F = lo, cup Z ≤ lo);
  - lift: the Tower Closure Lemma;
  - forced lift: the near-side cut;
  - concatenation: reserve [P] (Z alone in band F); 'keep' there is verified only by computation.

So BDL reduces to one claim: **the final determined rule delivers only non-empty contexts to base nodes.**

**Obstacle.** The 2-band nodes. Both of their bands are extreme, so the two sides' cuts must be complementary
(Q9c's OSJ), and the recursion through them still fails. Partial classical proof [P]: with one cut right of the cup
core's edge, putting the first points of the max cups on top works. Base truth otherwise is computational
(BRL+-type).

## Verdict

- **The tower closes Q9f's regrowth** with one more finite coordinate (the neighbour cut). There is no regress.
- **But the induction does not need the tower.** Keep-first absorption avoids lifts, and the single pair does as well
  through n = 8.
- **It needs instead:**
  - an inherited one-bit side for the neighbour cut;
  - a 2-band argument;
  - base truth.

## Evidence

Logged on the node. Code: tw/clos/rules/realis/recheck3/findfail*.py, exp/ (final rule, preal.py). Jobs:
- 9fe83a (the 40); 66c391; 1fd2a1; 1f57d5;
- 4a1a73 (n = 8 backtracking); c9726a; 065590; 593dfa; c941ac;
- cd5696 (final n = 8).

## Resumed (second instance, 10-03 19:20 onward): the large-instance tests refute the reduction

All entries are [C] (diagnostic, not Lean) unless marked [P].

**n = 8 [C].** The exhaustive final rule has 0 failures on 442,930 roots (198,274 colourings, one tree each), and
every base node is true (job cd5696):
- 205,758 contextual 2-band nodes;
- 198,560 trivial 2-band nodes;
- 38,672 classic–classic nodes.

The single profile at 1/10 of n = 8 also has 0 failures (41,910 roots).

**Tool.** exp/bigrule.py is a SAT/CEGAR evaluator of the same rule. Closure is decided exactly: for every P_C it
searches for a Z-placement. No partition is enumerated, so it runs at n = 41.
- It matches realis.prove on all 21,796 n = 7 roots: identical results and option traces (job 8daf67).
- It also matches on n ≤ 6 and on 108 large-instance comparisons (t_cross.py).
- Drivers:
  - big_run.py, with modes greedy, oracle, back, backwide and Xg/Xo/Xb custom menus;
  - gen_samples.py, which uses Q9's SAT generator and marks the TDF failures.
- Dissection tools: dissect_big.py, dead*.py, classify.py, famtest.py, oracle_anat.py and twosided_root.py.

**Results.** Columns: G = final rule; O = greedy with a truth oracle; B = backtracking, final menu; W = backtracking,
broad menu (lift, keep, own, reserve, liftall, no side inheritance); W2 = W with two-sided towers. Entries are
failing roots / roots tested.

| set | G | O | B | W | W2 |
|---|---|---|---|---|---|
| (5,5,6)-type n = 9, 10, 11 (3,587) | 0, 1, 17 | 0, 0, 11 | 0 | 0 | 0 |
| tight (5,5,6) n = 12–14 (1,200; includes 42 TDF-failing sets) | 100 | 71 | 3 | 0 | 0 |
| tight corpus k = 6, 7, n ≤ 30 (1,032) | 41 | 33 | 1 | 0 | 0 |
| bdl-induct residue (863) | 1 | 0 | 0 | 0 | 0 |
| named: TDF E14/E17, osj n = 25, 7 n = 14 trap/stuck sets (20) | 1 (osj) | 0 | 0 | 0 | 0 |
| tight (5,6,7) n = 25 nested (80) | 15 | 6 | 0 | 0 | 0 |
| tight (6,5,7) n = 25 nested (80) | 14 | 6 | 4 | **4** | 0 |
| (6,5,7) nested n = 14, 17, 20, 22 (798) | | | | 0 | 0 |
| tight (6,6,7) n = 30 (45) | 1 | 0 | 0 | 0 | 0 |
| (4,7,7) n = 16 nested; (4,8,8) and (8,4,8) n = 22 (240) | 0 | 0 | 0 | 0 | 0 |
| tight (5,5,7) n = 20 nested (3; the generator rarely succeeds) | 0 | 0 | 0 | 0 | 0 |
| k = 8: tight (5,7,8) n = 41 (24) | 0 | 0 | 0 | 0 | 0 |
| k = 8: (6,6,8) n = 40 (24) | 0 | 0 | 0 | 0 | 0 |

**Every tree, not just the label tree.** W2 was run on up to 7 decomposition trees per set (trees_run*.py; jobs
de3a39, 4208f4, 7bea99), with 0 failures:
- tight (5,5,6) n = 12–14: 8,278 roots over 4,139 trees;
- residue sets: 6,004 roots over 4,058 trees;
- tight corpus without (6,6,6): 6,295 roots over 3,393 trees;
- (5,6,7) and (6,5,7) n = 25 nested: 560 + 560 roots over 280 + 280 trees;
- tight (6,6,6) n = 16: 832 roots over 208 trees (job 7bea99).

The backtracking search is heavy-tailed. On some 5-band sets one root needs about 100 s, 10^5 SAT calls and 857
node-contexts explored. Finding the proof inside the language is a real search.

**Mechanisms.**
1. **Vacuous closure** (every G-failure checked: all 100 at n = 12–14, o_classify_g556.txt). Without an oracle, an
   option whose child context is EMPTY is accepted. The smallest witness found is n = 10 (PROOF-DRAFT §6). At osj
   n = 25, keep@L asks for "top band ≤ 12", which is empty.
2. **True but dead** (every O-failure). Each ends at a 3-band node with a 2-band child and a 1–2 point sibling, after
   both sides were born; no option is true and closed there.
   - The fatal choice is keep versus lift for a single-point sibling, several levels up.
   - Lookahead does not fix it: 71, 50, 28, 19 of 1,200 failures for lookahead 0, 1, 2, 3. Every menu order tried
     fails.
   - The tower language suffices at those nodes: an exact Pareto-fibre test (famtest.py) finds a closed true
     context at all 11 dead nodes at n = 11.
3. **Narrow final menu** (B). Side inheritance plus the missing own/liftall modes. Caterpillars at n = 13 and 14.
4. **One-sided language** (W, 4/80 at tight (6,5,7) n = 25).
   - All four have the root {z} << C with the max-cap core degenerate at z: L* = R* = z.
   - In g657n25d1-32 all 56 partitions put z in band 2, with band 1 = {5,6,16,17,18} straddling z.
   - The lift needs "no 4-cap of band 2 ends before z AND none starts after z". SAT check: each one-sided context is
     true but not closed; the two-sided one is true and closed.
   - Fixed by the opposite tower (ctx2.py, mode liftall+2).

**Single-point absorption, exact [P]** (PROOF-DRAFT §4.5). For Y = {z} << C, the triple rule gives:
- cups through z are exactly (x, z, y);
- caps through z are exactly D + z and z + D′.

Hence:
- z stays in band lo iff lo ≥ 2, or (lo = 1) C's band 1 is one-sided at z;
- z lifts to lo+1 iff band lo+1 has no (β−1)-cap ending before z and none starting after z;
- one-sided towers suffice unless R* ≤ z ≤ L*.

So the Tower Closure Lemma's hypothesis ("Z right of L*") is exactly what Mechanism 4 violates.

**Base-node shapes (task 2).** At n ≤ 8, counting disjuncts separately (205,841 in all):
- position cuts only: 186,103;
- with tower entries: 19,728;
- with pos2: 640;
- cut on both sides: 62,705;
- floor lowered or ceiling raised: 114,115.

The n = 9–14 samples show the same shapes (o_shapes_greedy.txt).

**Hand proofs (task 3).** Not attempted for base truth. The reduction they would complete is false, so effort went
into the mechanisms and §4.5 instead.

**PROOF-DRAFT.md (task 4).** Written:
- schema, contexts and rule;
- step lemmas with proofs: wide–wide [P re-derived], keep in absorption [P re-derived], Tower Closure Lemma [P],
  reserve [P], single-point absorption [P, new];
- the base-shape census;
- the refutation table with witnesses and mechanisms;
- the precise open obligation.

**Also run:** findfail2 at n = 7, the first instance's Q9f fixed-context test (o_ff2_n7.txt). It finds 112 parent
contexts at 2-band absorption nodes where even the full tower menu fails. This is consistent with treating 2-band
nodes as base nodes.

## Report (resumed instance, about 800 words)

**n = 8.** The final determined rule passes every n ≤ 8 case: 0 failures on 442,930 roots (198,274 colourings, one
tree each), and every base node is true (job cd5696). The "all" entry above is filled.

**The large instances refute the reduction.** The claim was "BDL ⇐ the final rule delivers only non-empty contexts
to base nodes". I wrote exp/bigrule.py, which decides closure exactly by SAT/CEGAR (for every P_C, it searches for
a Z-placement) and so runs up to n = 41. It reproduces the enumerative realis.prove on all 21,796 n = 7 roots, with
identical traces.

The final rule (G) fails on:
- 1 of 1,199 roots at n = 10 and 17 of 1,200 at n = 11, in the (5,5,6)-type samples;
- 100 of 1,200 tight (5,5,6) roots at n = 12–14 (5 of these on the 42 TDF-failing sets);
- 41 of 1,032 tight-corpus roots (k = 6, 7);
- the osj n = 25 set;
- 15 of 80 and 14 of 80 nested tight (5,6,7) and (6,5,7) roots at n = 25.

The k = 8 sets pass: (5,7,8) n = 41 and (6,6,8) n = 40.

**Mechanisms** (PROOF-DRAFT §6).
1. **Vacuous closure.** This is the cause of every G-failure classified: all 100 at n = 12–14, plus osj. Without an oracle, the rule accepts an option whose
   child context is EMPTY.
   - Smallest witness found, n = 10: keep@L, then keep/right empties band 2 for C = {0,1,2,5,8}; reserve would
     work.
   - osj: keep@L asks for "top band ≤ 12", which is empty.
2. **True but dead.** No one-step rule is safe, even with a truth oracle (O).
   - O fails 71 of 1,200 roots, and still 50, 28 and 19 with 1, 2 and 3 levels of lookahead. Every menu order
     tried fails.
   - The fatal choice, keep versus lift for a single-point sibling, comes several levels above the death. The death
     is at a 3-band node with a 2-band child, after both sides of the context were born.
   - At the dead nodes some tower context does work (an exact Pareto-fibre test). The menu fails there, not the
     language.
3. **The final menu is narrow.** Backtracking over it fails on 3 of 1,200 (caterpillars at n = 13 and 14). The broad
   menu (own and liftall, no side inheritance) proves them.
4. **The one-sided language fails.** Broad backtracking fails on 4 of 80 tight (6,5,7) n = 25 sets.
   - All four have the root {z} << C with the max-cap core degenerate at z: L* = R* = z.
   - The bottom band is forced to straddle z (in g657n25d1-32, all 56 partitions), so z must be lifted.
   - By SAT, lifting needs "no 4-cap of band 2 ends before z AND none starts after z": one-sided contexts are true
     but not closed, and the two-sided one is closed.
   - **Repaired by a two-sided tower** (exp/ctx2.py).

**With two-sided towers**, broad backtracking (W2) has **0 failures on every set**:
- 7,996 label-tree roots, at n ≤ 41 and k = 6, 7, 8;
- 22,529 roots over 12,358 trees (up to 7 per set).

**New lemma [P]: single-point absorption, exact.** For Y = {z} << C:
- the cups through z are exactly (x, z, y), and the caps through z are exactly D + z and z + D′;
- z stays in band lo iff lo ≥ 2, or (when lo = 1) C's band 1 is one-sided at z;
- z lifts to lo+1 iff C's band lo+1 has no (β−1)-cap ending before z and none starting after z;
- one-sided towers suffice unless R* ≤ z ≤ L*. This is exactly the hypothesis that the Tower Closure Lemma assumed
  away.

**Base-context shapes (task 2).** At n ≤ 8 there are 205,841 disjuncts:
- 186,103 with position cuts only;
- 19,728 with tower entries: (3,), (4,), (5,), (1,2,3) or (1,2,3,4);
- 640 with a neighbour cut;
- 62,705 cut on both sides;
- 114,115 with the floor lowered or the ceiling raised by one band.

They are not near-classical. The n = 9–14 samples show the same shapes.

**Hand proof of base truth (task 3).** Not attempted. The reduction it would complete is false, so the hard-instance
order made it moot. §4.5 was proved instead.

**PROOF-DRAFT.md (task 4).** Written. It contains:
- the definitions, the schema and its soundness [P];
- the step lemmas: wide–wide and keep in absorption (re-derived) [P], the Tower Closure Lemma [P], reserve [P], and
  single-point absorption [P, new];
- the base census [C];
- the refutation table with witnesses and mechanisms;
- the precise open obligation.

**Proof idea, what was learned, the obstacle.**
- **Proof idea.** Carry two-sided tower contexts down the tree. Every step is a DS consequence. BDL follows from an
  intrinsic family 𝒞 of contexts that contains the root, is closed under some menu step, and is non-empty at base
  nodes.
- **Learned.**
  - (i) Inside the two-sided language, a proof exists on every instance and every tree tested.
  - (ii) Two-sided towers are needed exactly when an inner point lies in a degenerate cap core [P].
  - (iii) The context cannot be chosen locally: oracle plus lookahead 3 still fails, and backtracking is
    heavy-tailed.
- **Obstacle.** Defining 𝒞 intrinsically. 𝒞 must exclude non-empty but dead contexts, and membership depends on
  structure at least 4 levels down. This is the LOCKED nested split in a new form: the keep-versus-lift decision for
  an inner point relative to the outer part's core.
- **Next computation.** The bottom-up feasibility profile: the Pareto frontier of attained two-sided signatures per
  node. Test whether it has a closed form that composes over the tree.

## Q25: the attainable contexts ATT(v) bottom-up (about 700 words)

All results are [C] (diagnostic, not Lean). Code: exp/att.py and exp/q25_*.py. o_q25_func7.txt and o_q25_shape.txt
are from runs cancelled to respect the job limit, so they are partial; draw no conclusions from them.

**Object.** At node v (natural range), each side gets the orientation-free two-sided signature
(min E, −max E, e_1..e_m, −g_1..−g_m). Here E is the extreme band, and e_L / g_L are the earliest end and latest
start of an L-chain in the neighbour band.
- Every two-sided tower context (PROOF-DRAFT §2) is a threshold on part of this vector.
- So ATT(v) is the down-closure of the attained signatures, and frontier(v) is their Pareto maximum.

**1. Shape: large antichains, not chains, not determined by statistics.**
- **Size is close to the partition count:**

  | k = 6 | n ≤ 6 | n = 7 (1/10 sample) |
  |---|---|---|
  | 2 bands: frontier / partitions | 28.6 / 28.8 | 33.0 / 34.6 |
  | 3 bands: frontier / partitions | 177 / 325 | 316 / 709 |
  | one oriented side, mean (max) | 10.5 (17) | 14.1 (22) |

- **The size grows with n.** The one-sided frontier is a function of (position cut, neighbour cut) in only 42–88% of
  cases.
- **Single-point one-side frontiers** occur only in the degenerate cases lo = 0 or hi = k−2, where the extreme band
  holds at most one point.
- **Hard instances** (o_q25_hard.txt): full frontier 12–7,125 points, one oriented side 1–39.
- **Tight nested sets are rigid.** g657n25d1-32 at k = 7 has 56 partitions and a one-point bottom frontier.
- **Not determined by statistics.** At n ≤ 6, all 290 classes of equal (k, n, α, β, L*/R* of caps and cups,
  first-point and last-point sets) that have ≥ 2 members contain ≥ 2 different frontiers.

**2. Composition: no local rule, and the language is not closed.**
- **The frontier identifies C** (n ≤ 6). So "frontier(Y) is a function of frontier(C)" holds, but vacuously.
- **No pointwise rule** (all n ≤ 7, job 17f71b). Two partitions of C with the same signature, completed by the same
  sibling placement, differ in validity or in Y-signature at 606–1,390 nodes per split type.
  - The cause: chains of the extreme band through the sibling (e.g. D + z inside band lo) are not recorded.
  - The refinement that restores locality (interval profiles of the four boundary bands) separates all partitions at
    ≤ 3 bands, so it compresses nothing.
- **ATT is not self-inductive.** Some frontier contexts of Y have no non-empty closed child context:
  - n ≤ 6, full signature: 2,155 of 31,495 and 1,408 of 20,464, at concatenation nodes with a 2-band child;
  - n ≤ 6, oriented projections: more, including absorption nodes (173 of 786);
  - n = 7 (1/25 sample, job 44959b), full signature: failures at every split type, including absorption with Y and C
    3-band (658 of 11,366 and 426 of 6,858).

  Witness (n = 5, k = 5): z is forced into the top band, where caps z + (x, y) matter. The child's signature does not
  record top-band caps.
- **So the W2 proofs exist** only because the root needs special contexts.

**3. The one closed-form element, and why it does not induct.**
- **Always attained:** the four strongest single cuts, band lo ≤ L*cap, band lo ≥ R*cap, band hi ≤ L*cup and
  band hi ≥ R*cup. This holds at every colouring n ≤ 7 and every k.
  - They are the strongest possible, because band lo meets every β-cap.
  - This is Q9's P, now on both sides.
- **Pairs** (one bottom cut, one top cut) are attained at ≥ 3 bands when both cores are non-empty. LL and RR fail
  4–15% of the time when a core is empty. At 2 bands pairs are often impossible (OSJ).
- **Not inductive** (exact closure, all n ≤ 6).
  - The singles fail from n = 5 at 3-band nodes, e.g. 36 cases of C<<Z absorption with Y and C 3-band.
  - Adding the pairs still fails, e.g. 6 cases at the same node type and 78 at concatenation.
  - The reason: a single sibling point near the core needs a cut or a tower on the other side too, so the hypothesis
    must carry sibling positions from above. That is the top-down choice, which is non-local (§Resumed).

**4. Verdict.** ATT has no small closed form:
- its frontier carries almost as much information as the partition set;
- the tower signature does not compose locally;
- the attainable sets are not self-inductive in the language.

They encode global structure: the lock.

**Proof idea, what was learned, the obstacle.**
- **Proof idea:** Q25 yields none. P on both sides is a clean statement that holds in every case tested, but every
  closed-form family containing it that was tested fails to be inductive.
- **Learned:**
  - frontiers are near-injective and grow with n;
  - tight nested sets are rigid;
  - the failure point is always a single sibling point near the core.
- **Obstacle:** a parent needs, for every possible sibling position, where the child's boundary-band chains start
  and end. That is not compressible into finitely many statistics of the child.
