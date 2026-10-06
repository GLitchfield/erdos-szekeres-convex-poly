# The tower induction for BDL: draft and status (claude-tower-20261003)

Tags: **[P]** proved by hand (here, or by the first Q17 instance as noted); **[C]** computed exactly (CaDiCaL or full
enumeration), diagnostic, not Lean; **[F]** false, with a witness.

**Status.** The induction schema is sound, and its step lemmas are proved. Its reduction is false.
- **The reduction tested:** "BDL ⇐ the final determined rule delivers only non-empty contexts to base nodes."
  - It holds on all n ≤ 8: 442,930 roots.
  - It fails from n = 10 (§6).
- **No one-step choice rule** of this kind works, even with an oracle for context truth and 3 levels of lookahead.
- **The one-sided tower language also fails**, at tight (6,5,7) n = 25. The fix is a two-sided tower (§4.6).
- **With two-sided towers**, backtracking over the menu finds a proof on every instance tested.
- **What remains** is an intrinsic description of the contexts that can be carried (§7).

## 1. Setting

- X is a decomposable point set in sweep order, given by a decomposition tree: Y = A << B at each node, A the lower
  part.
- **Node condition:** cup A + cap B ≤ k − 1. It is equivalent to "no strong k-set" by Lemma DS.
- **BDL (target).** If α + β ≥ k + 1, X has a band map b : X → [k−1−β, α−1] where band j has cup ≤ j+1 and
  cap ≤ k−1−j.
- A node is **wide** if α + β ≥ k + 1 and **classic** otherwise.
- **Lemma DS** (audited). For Y = A << B:
  - a cap of Y meeting B is a cap of B, extended by at most one A-point before it and one after it;
  - a cup of Y meeting A is a cup of A, extended by at most one B-point on each side.
- **Triple rule.** For x < y < z, the triple is a cup iff the middle point y lies in the lower part at the first
  tree level where the three points are not all on the same side.

## 2. Contexts

A context on a node Y is c = (F, H, bot, top): bands lie in [F, H], and each side is free or a side condition.
- The bottom side has floor F and works with caps. Its neighbour band is F+1, and its chain limit is m = k − 2 − F,
  which is the cap limit of band F+1.
- A one-sided condition is (o, s, s2, t_1..t_m), with o ∈ {L, R}.

| coordinate | o = L | o = R |
|---|---|---|
| position cut s | band F ⊆ indices < s | band F ⊆ indices ≥ s |
| neighbour cut s2 | band F+1 ⊆ indices < s2 | band F+1 ⊆ indices ≥ s2 |
| tower t_L | no L-cap of band F+1 ends at an index < t_L | no L-cap of band F+1 starts at an index ≥ t_L |
| **opposite tower u_L** (two-sided only, §4.6) | no L-cap of band F+1 starts at an index ≥ u_L | no L-cap of band F+1 ends at an index < u_L |

- The top side is the mirror: ceiling H, cups, neighbour band H−1, m = H.
- S(Y, c) is the set of valid band maps satisfying c. Disjunctions ('either') are allowed; S is then the union.
- Every coordinate is a threshold on a monotone signature, so a context is a threshold vector and S(Y, c) shrinks as
  c grows (exp/tw.py side_sig; ctx2.py for u).

## 3. The induction schema [P]

`prove(Y, c)` holds if one of the following applies:
- **base:** Y is classic–classic, or Y has exactly 2 natural bands, and S(Y, c) ≠ ∅;
- **wide–wide:** prove(A, c_A) and prove(B, c_B) hold for the inherited contexts (§4.1);
- **one classic child Z** (the sibling) with wide child C: some menu option c′ for C is closed, and prove(C, c′)
  holds.

c′ is **closed** when every P_C ∈ S(C, c′) extends, by some placement of Z, to an element of S(Y, c).

**Soundness [P].** prove(Y, c) implies S(Y, c) ≠ ∅, by induction up the tree. In particular, prove of the trivial
root context implies BDL for X.

**Menu** (realis.child_options; ctx2.child_options2 adds the '+2' variants). The facing side, bottom if Z is the
lower part, is rebuilt by the tower rule. The other side is inherited, re-indexed to C.
- Orientation: inherited, or chosen at the side's birth from Z's position.
- Modes:
  - final rule: keep, reserve, lift;
  - broad menu: keep, reserve, lift, own, liftall.
- Side bit for band F+1: plain, either, right or left.
- Also: flip, free, and C's natural floor or ceiling.

**The tower rule** (rules.tower_rule):
- The canonical placement of Z is j0 = max(cup Z − 1, F).
- When j0 = F, the Z-points on the wrong side of the cut are lifted to F+1 and the rest stay in band F. The cut is
  s; in lift mode, if s is unset, it is the parent's core edge.
- Each lifted z creates the pair (m, gap z), plus (L, gap z) for every inherited pair (L+1, t) that z lies inside.
- keep also cuts C's band F to the near side of the kept Z-points.
- reserve keeps C out of band F.

## 4. Step lemmas

### 4.1 Wide–wide inheritance [P]

The children's contexts are c_A = (F, α_A − 1, bot, free) and c_B = (k − 1 − β_B, H, free, top), re-indexed.

*Proof.*
- **Disjoint bands.** The node condition gives α_A − 1 ≤ k − 2 − β_B < k − 1 − β_B. So every band of Y lies
  inside A or inside B, and its chains are chains of A or of B.
- **Bottom side.** A is wide, so [F, α_A − 1] has at least two bands, and bands F and F+1 consist of A-points.
  Every bottom-side coordinate is then a statement about A alone, and re-indexing it to A is exact. The top side is
  the same with B.
- Hence S(A, c_A) × S(B, c_B) ⊆ S(Y, c). ∎

### 4.2 Keep, absorption at the floor [P]

*Hypotheses:* F = k − 1 − β_Y, cup Z ≤ F, and no Z-point violates s.

*Proof.*
- **Caps.** Band F's cap limit is β_Y, which holds automatically.
- **Cups.** By DS, a cup through a Z-point is a cup of Z plus at most one C-point on each side. Keep puts C's band F
  on one side of the kept Z-points, so such a cup has length ≤ cup Z + 1 ≤ F + 1.
- The remaining conditions are inherited.

Z-points that violate s are forced lifts (§4.3). Keep in the concatenation case (cap C < cap Y) is [C] only.

### 4.3 Tower Closure Lemma [P, first instance]

*Setting:* a chain of absorptions X_0 = Z_1 << X_1, …, Z_r << W (cap β throughout), with every Z-point strictly right
of L*(X_0), lifted to band lo+1 (lo = k−1−β).

*Claim:* P ∪ Z is valid iff P is valid and |D| + g(D_end) ≤ β − 1 for every cap D of P's band lo+1. Here g is the
longest inner-to-outer chain of Z-points after D_end.

*Proof.*
- Cups: ≤ cup Z_j + 2 ≤ lo + 2.
- Caps: a cap is D followed by Z-points, or it starts at a Z-point. A cap starting at a Z-point has length ≤ β − 1,
  because no β-cap starts right of L*. ∎

### 4.4 Reserve [P]

Z is alone in band F (j0 = F gives cup Z ≤ F + 1), and the cap limit β_Y holds automatically. C lies in bands
≥ F + 1, plus lifted Z-points, which §4.3 covers.

### 4.5 Single-point absorption, exact [P] (new)

*Setting:* Y = {z} << C with z a single lower point, β_Y = β, lo = k − 1 − β, and P_C a valid band map of C.

*Fact.* By the triple rule, (x, z, y) is a cup for x < z < y in C, while (x, y, z) and (z, x, y) are caps. Hence:
- the cups through z are exactly the triples (x, z, y);
- the caps through z are exactly D + z, with D a cap of C ending before z, and z + D′, with D′ a cap of C starting
  after z.

*Consequences:*
- (a) z can be kept in band lo always when lo ≥ 2. When lo = 1, it can be kept iff C's band 1 lies on one side of z
  (keep@L or keep@R). When lo = 0, C's band 0 must be empty. Caps through z have length ≤ β automatically.
- (b) z can be lifted to band lo+1 iff C's band lo+1 has no (β−1)-cap ending before z **and** no (β−1)-cap starting
  after z. Cups through z have length 3 ≤ lo + 2.
- (c) The first clause of (b) is automatic when z < R*(Y), since no β-cap of Y ends at z. The second clause is
  automatic when z > L*(Y). So **a one-sided tower suffices unless R* ≤ z ≤ L***: the core of the β-caps is empty
  or degenerate at z. This is exactly the hypothesis that §4.3 excludes.

### 4.6 Two-sided towers [P for single points, C in general]

- **Representation.** A side carries both towers, (o, s, s2, t, u). The '+2' modes add, for each lifted z, the pair
  (m, gap z) and the nested pairs to u as well as to t (exp/ctx2.py).
- **Single-point case.** By §4.5(b), liftall+2 for a single point is exactly closed.
- **Several lifted points.** A cap z_1 + D + z_2 with lifted points on both sides of D is not captured by two
  independent towers. Closure is therefore always checked exactly (§6), and the menu only proposes contexts.

## 5. Base nodes

- **2-band nodes.** The natural bands are {lo, lo+1}. The node sits inside its ancestors' range [F, H], with one or
  two side conditions.
- **Classic–classic nodes.** Both children are classic.

**Base contexts delivered by the final rule on its successful roots [C].**
- **n ≤ 8, exhaustive** (o_final8_tower_all.txt): 205,758 contextual 2-band base nodes and 38,672 classic–classic
  base nodes, all true. Counting each disjunct separately (205,841 in all):
  - position cuts only (L or R): 186,103;
  - with tower entries, (3,), (4,), (5,), (1,2,3) or (1,2,3,4): 19,728;
  - with the neighbour cut pos2: 640;
  - cut on both sides: 62,705.

  114,115 have a floor lowered or a ceiling raised by one band; 91,726 have the natural range.
- **n = 9–14 samples** (o_shapes_greedy.txt): the same shapes, including two-sided pairs LR, LL, RL, RR, each with
  or without a tower.

**Base truth is not near-classical**: it includes two-sided contexts with tower entries. No hand proof was attempted,
because the large-instance tests (§6) remove the reduction that base truth was meant to complete.

## 6. Computations: the reduction is false [F, C]

**Evaluator.** exp/bigrule.py decides closure exactly by SAT/CEGAR: for every P_C, it searches for a Z-placement.
- It reproduces realis.prove (full enumeration) on all 21,796 n = 7 roots, with identical results and option traces
  (job 8daf67).
- It also agrees on n ≤ 6 and on 108 large-instance comparisons (t_cross.py).

Columns: G = final rule (greedy, no oracle); O = greedy with a truth oracle; B = backtracking, final menu;
W = backtracking, broad menu, one-sided towers; W2 = the same with two-sided towers. Entries are failing roots /
roots.

| instances | G | O | B | W | W2 |
|---|---|---|---|---|---|
| all n ≤ 8, exhaustive | 0/442,930 | | | | |
| (5,5,6)-type, n = 9, 10, 11 (3,587) | 0, 1, 17 | 0, 0, 11 | 0 | 0 | 0 |
| tight (5,5,6), n = 12–14 (1,200; 42 sets are TDF failures) | 100 | 71 | 3 | 0 | 0 |
| tight corpus k = 6, 7, n ≤ 30 (1,032) | 41 | 33 | 1 | 0 | 0 |
| bdl-induct residue sets (863) | 1 | 0 | 0 | 0 | 0 |
| named: TDF cases, osj n = 25, n = 14 traps (20) | 1 | 0 | 0 | 0 | 0 |
| tight (5,6,7), n = 25, nested (80) | 15 | 6 | 0 | 0 | 0 |
| tight (6,5,7), n = 25, nested (80) | 14 | 6 | 4 | **4** | 0 |
| tight (6,6,7), n = 30 (45) | 1 | 0 | 0 | 0 | 0 |
| (4,7,7) n = 16 nested; (4,8,8) n = 22; (8,4,8) n = 22 nested (240) | 0 | 0 | 0 | 0 | 0 |
| (6,5,7) nested, n = 14, 17, 20, 22 (798) | | | | 0 | 0 |
| k = 8: tight (5,7,8), n = 41 (24) | 0 | 0 | 0 | 0 | 0 |
| k = 8: (6,6,8), n = 40 (24) | 0 | 0 | 0 | 0 | 0 |

**Every tree.** W2 on up to 7 decomposition trees per set has 0 failures: 22,529 roots over 12,358 trees (the
(5,5,6) n = 12–14 sets, the residue sets, the whole tight corpus and the n = 25 nested sets). The backtracking
is heavy-tailed: on some 5-band (6,6,6) sets one root needs 10^5 SAT calls and about 2,000 node-contexts.

### Mechanism 1: vacuous closure (the oracle-free rule)

- **What happens.** An option whose child context is EMPTY is vacuously closed, and the rule takes it. This accounts
  for all 100 G-failures at n = 12–14.
- **Smallest witness found: n = 10, k = 6.** Labels `111010000 111000000 111011000 101000000 101100000 111100000
  101010000 000000000 110000000 100000000`. The tree is (7 << ((9 << ((3<<6)<<4)) << (8 << ((1<<(0<<2))<<5)))).
  - keep@L puts C's band 1 left of 7.
  - At the next node, Z = {3,4,6,9} and C = {0,1,2,5,8}. Keep lifts 9 and cuts C's band 1 to {0,1,2}, and 'right'
    empties band 2.
  - C does not fit in bands {1,3}: (0,1,2) is a cup, and (x,5,8) is a cap for each x in {0,1,2}.
  - reserve was true and closed.
- **osj n = 25.** keep@L at the root asks for "top band of C ≤ 12", which is empty.

### Mechanism 2: true but dead (any one-step rule)

- **Where it ends.** Every O-failure ends at a 3-band node whose wide child is 2-band and whose sibling has 1–2
  points, after both sides of the context have been born. No option there is both true and closed.
- **The fatal decision is earlier:** keep or lift for a single-point sibling (g556n11d1-55 needs liftall@R at
  depth 1).
- **Lookahead does not fix it.** With an oracle and k levels of lookahead, O fails 71, 50, 28 and 19 of 1,200 roots
  at k = 0, 1, 2, 3. Every menu order tried fails, and lift-first orders are worse (132).
- **The language is not at fault there.** At all 11 n = 11 dead nodes, some full tower context of C is true and
  closed (famtest.py, exact). The menu's thresholds are what fail.

### Mechanism 3: the final menu is too narrow

B fails on g556n13d0-62 and g556n14d0-63 and -64: caterpillars of single points, ending at an 8-point node with
|S(Y,c)| = 4. The broad menu proves all three.

### Mechanism 4: the one-sided language fails

- **Where.** W fails on 4 of 80 nested tight (6,5,7) n = 25 sets: g657n25d1-6, -32, -34 and -35. It has no failure
  at n = 14, 17, 20 or 22 (400 samples).
- **The shared root.** All four have the root X = {z} << C with the β-cap core degenerate at z: L*(X) = R*(X) = z.
- **g657n25d1-32 in detail.** X has exactly 56 partitions. In all of them, z is in band 2 and band 1 = {5,6,16,17,18}
  straddles z. So keep and reserve are empty and z must be lifted, which by §4.5(b) needs the two-sided tower.
- **SAT check.** Each one-sided tower is true but not closed; the two-sided one is true and closed (twosided_root.py,
  for all four roots).
- **Repair.** W2 proves all four, with liftall+2 at the root and then reserve.

## 7. What remains

- **Proved:**
  - the schema (§3);
  - wide–wide inheritance (§4.1);
  - keep in absorption (§4.2);
  - the Tower Closure Lemma (§4.3);
  - reserve (§4.4);
  - single-point absorption (§4.5).
- **Computed:**
  - keep in concatenation;
  - closure of multi-point two-sided lifts;
  - base truth along the computed paths.
- **False:**
  - a determined local choice rule (§6, Mechanisms 1–2);
  - the one-sided tower language (Mechanism 4).

**The open obligation.** Find an intrinsic family 𝒞(Y) of two-sided tower contexts such that:
- (i) the trivial root context is in 𝒞(X);
- (ii) every c ∈ 𝒞(Y) at a one-classic-child node has a closed menu option in 𝒞(C), and wide–wide inheritance stays
  inside 𝒞;
- (iii) S(Y, c) ≠ ∅ for every c ∈ 𝒞 at a base node.

Then BDL follows by §3.
- **Existence per instance.** W2 succeeding everywhere says that such a family exists for each instance tested.
- **𝒞 cannot be "all true contexts".** It must exclude the true-but-dead ones.
- **Membership is non-local.** It depends on structure at least 4 levels down.
- **So 𝒞 must be global:** an invariant of the sub-tree, such as a bottom-up feasibility profile of thresholds,
  not a function of the sibling's position.

**This is the LOCKED nested split again**, now resolved into two concrete pieces:
- **Two-sided lifts are needed.** When the core is degenerate at the inner point, the point must be lifted, and its
  lift constrains caps on both sides (§4.5).
- **The keep-versus-lift decision for an inner point** relative to the outer part's core cannot be made locally
  (Mechanism 2).

## 8. Q25: bottom-up attainable sets [C]

Details are in NOTES §Q25.

**The question.** Can the induction be carried by an explicit invariant 𝒞(v) = "these contexts are attainable at
v", where 𝒞(v) is given by statistics of v? The data answer no, within the two-sided tower language.
- **The frontier of attainable signatures is too large.** It is close to the number of partitions, grows with n, and
  differs within every class of equal core statistics.
- **No local composition rule.** The tower signature of C does not determine what happens when the sibling is
  inserted.
- **The attainable sets are not self-inductive.**
- **The explicit families tested are not inductive.** These are the four strongest single position cuts, which are
  always attained (Q9's P, now on both sides), and those cuts with pairs added. The first failure is at n = 5.

**What remains is the open obligation of §7**: an invariant that is global rather than statistical. A candidate for
such a statement is P on both sides, provided it can be strengthened into an inductive form.
