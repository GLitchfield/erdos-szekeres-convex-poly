# Q7: an induction hypothesis for BDL (claude-bdl-induct-20261003)

Tags: **[P]** proved by hand; **[C]** computed (exact search; diagnostic, not Lean).

## 0. Rotation (coordinator)

**[P]** A<<(Blo<<Bup) and (A<<Blo)<<Bup are the same colouring iff no Blo-point lies strictly (in x) between an A-point
and a Bup-point. The gap case is a special case; the new root is non-interleaved, so it is never R or R'.

**[C]** Rotation does not remove case R. On case-R samples (B has ≥2 bands):

| | k=6 | k=7 |
|---|---|---|
| gap rotation applies | 9/400 | 4/400 |
| every root split of X is R/R' (residue) | 261/400 | 322/400 |

The residue usually has a unique root split, with A in one B-gap that B's tree does not cut.

## 1. Reduction: BDL ⇐ G [P]

Budgets (a,u) mean cap ≤ a−1 and cup ≤ u−1; the bands are [k−a, u−2].

**Generic split.** At X = A<<B pick m ∈ [max(cupA−1, k−a), min(k−2−capB, u−3)].
- A gets bands [k−a, m]; B gets [m+1, u−2]; the partitions concatenate.
- No m exists only if capB = a−1 or cupA = u−1.

**capB = a−1.** This nests A inside B's max caps.
- Non-tight A is absorbed into band k−a.
- Tight A is case R. It closes by **G(B)** at the cut just left of A.

> **G(X,t):** if cap(X∩(t,∞)) ≤ a−2, then X has a BDL partition with band k−a ⊆ (−∞,t].

Consequences:
- G(t) ⟺ G(L*), so G is invariant P made unconditional.
- G is trivial for classic sets, so the F-trick is unnecessary.
- G with 2 bands is canonical: bottom band = the first points of the max caps.

## 2. Hypothesis H

**H** = one-sided placement of the extreme bands, with budgets:
- G and its mirror G';
- the cup duals T, T';
- the opposite-side joints (bottom left with top right, and the reverse).

H must be extended by **Lemma M** (§4), a band-tagged context statement.

## 3. Closure evidence [C]

**What holds.**
- G, G', T, T': 186k cut tests, 0 failures (n ≤ 12, k ≤ 8).
- Opposite-side joints: 2031/2031.

**What fails.**
- Same-side joints, at exactly 3 bands: 5/1500 and 17/1500.
- Arbitrary hitting sets, middle intervals, staircases and the monotone layout.
- Exchange restricted to bands j0, j0+1.

**Hand case analysis of G.** Verified against *every* child partition satisfying the stated clause, k=6..8, 0
failures in 646 splits. It closes except:
- **S1:** capB = a−2 and A has points right of t;
- **S2:** capB = a−1 and A has points right of t.

These two sub-cases are about 23% of splits.

**Black-box closure of the menu fails**, at the S1/S2 configurations:

| k | G at case-R roots | G at other roots |
|---|---|---|
| 6 | fails 15/43 | fails 28/736 |
| 7 | fails 6/15 (G' 11/15) | fails 9/464 |

## 4. Explanation and the missing lemma

**Why the cut menu cannot close S1/S2.** E = A∩(t,∞) cannot use the bottom band, so it must enter band k−a+1. There it
conflicts with the (a−2)-caps D of B's band that start ≤ t and end before a point of E. This is a constraint on *which
caps are monochromatic*, relative to the sibling's extremes, not on where band points lie.

**What H must remember.** Per band (at least the bottom two and the top two): the sibling's band-tagged extreme
points, and which maximal chains of the band they extend. This is a DS context with band tags.

**Forcing fills the gap.** A child piece that fits a band alone can be placed wholesale into it. In about 75k tests
(k=6,7) there were 4 failures, each a child surrounding its sibling forced into the far extreme band.

**Lemma S** (E wholly in band k−a+1, together with G) had 0 failures: k=6 5,896; k=7 all; k=8 518.

**Lemma M (missing).** Let X = A<<B be decomposable with ≥3 bands. Suppose capB ≥ a−2, cap(X∩(t,∞)) ≤ a−2, and
E ≠ ∅. Then X has a G(t)-partition with E ⊆ band k−a+1.
- **M ⇒ G ⇒ BDL ⇒ Theorem 8.** This also needs the opposite-side joint for the cupA = u−1 case, whose own induction is
  not done.
- **M is not a property of B alone.** The rigid form (B only in bands ≥ k−a+1) is false in S1: 25/368, 8/350, 3/356
  at k=6,7,8. So M is a context statement with two tagged pieces: A≤t in band k−a and E in band k−a+1.
- **Next computation:** whether that context system closes under B's splits.

**Why it should hold.** The extreme bands act like the ends of the Erdős–Szekeres chain: each can be pushed to either
side, and opposite sides can be achieved jointly. Points right of L* start no maximal cap, so they never need the bottom
band.

**Obstacle every attempt hits.** Lifting a lower piece into the second band is decided by that band's monochromatic
maximal caps, which no positional invariant records.

## 5. Evidence

- **Library:** `bl.py`.
- **Scripts:** `t_G2.py`, `t_LB*.py`, `t_GT.py`, `t_MG.py`, `t_exch.py`, `t_rot.py`, `t_closure.py`, `t_force2.py`,
  `t_lemS.py`, `t_Gproof.py`, `t_S1.py`.
- **Outputs:** `o_closure_k{6,7}.txt`, `o_force2_k{6,7}.txt`, `data_resid_k{6,7}.pkl`.
- **Jobs:** 20261003-112125-f1547b, 20261003-112125-debbbb, 20261003-112751-6ae6fe, 20261003-112752-16b0d6.

## Q7b: does the Lemma-M context close under B's splits?

**Context (Lemma DS).** Fix a tree and a partition π. A node v sees the band-tagged points of the siblings along its
root path, one *piece* per ancestor level.
- Caps of v are extended by lower pieces and cups of v by upper pieces; the shell decomposition was checked on 49k
  chains.
- v's points also extend the pieces' cores. These are **gates**.

**[P] The shape regrows syntactically.** At B = B1<<B2:
- B2 inherits P0 and P1 together with B1's merge-band piece, which is a second level.
- B1 gets B2's pieces as upper tags, a new kind of tag.

**Three measures [C].** Each is minimised over all BDL partitions (and over trees where stated).

| measure | random, n ≤ 12 | extremal (\|X\| = T) |
|---|---|---|
| F: ancestor levels in one tight chain through v | ≤ 2 (3,100 sets) | 2 at k=6, 3 at k=7 (≤3000 trees) |
| raw gate levels | – | 2–3 at k=6, 3–5 at k=7 |
| **C: fewest levels that keep v's valid completions unchanged** | max 4 (150 sets, k=7) | ≤ 4 |

So the raw context grows with k. C is exact: a subset of a decomposable set is decomposable.

**Exact count C per family (k=6, 7, 8).**

| family | bands | C values |
|---|---|---|
| T(5,5,6) | 3 | 2, 3, 3, 3, 4, 4 |
| T(4,6,6) | 3 | 2, 3, 3, 3 |
| T(5,6,6) | 4 | 2, 3, 4 |
| T(4,6,7) | 2 | 1×5, 4 |
| T(4,7,7) | 3 | 2, 3, 4 |
| T(5,5,7) | 2 | 1, 1, 2 |
| T(4,7,8) | 2 | 1, 2, 2 |
| T(4,8,8) | 3 | 2, 2 |

**Saturation.** Along a depth-9 path the needed set saturates at 4. Each child's minimal set lies inside its parent's
set plus the new sibling, so the deeper levels are implied by earlier ones.

**No canonical selection.**
- Keeping the r root-most levels needs up to 6 (T(4,6,7)) and 8 (T(4,7,7)).
- Keeping the nearest levels needs up to 7 (T(5,5,6)).
- Minimal sets are not unique: 18 alternatives at one node. They mix lower and upper siblings, and include bands the
  node itself does not use.

**Verdict.** Neither (i) nor (ii) cleanly.
- The *information* does not regrow: ≤ 4 tagged sibling pieces always suffice, independently of k and depth.
- Every *positional* rule for which pieces to keep does regrow.
- So an H* would read: "BDL for v in a context of ≤ 4 band-tagged sibling pieces chosen by the parent". The selection
  rule, and the hypothesis that makes such contexts admissible, are not identified. This is the old sibling-penalty
  pattern in a weaker form: the context is bounded, but depends on choices made above.

**Not done.**
- No proof of H*.
- 5-band sets (T(6,6,6)) are not covered: the job was cancelled as too slow.
- C is an upper bound on what an induction needs, since it preserves all completions. Restricting v to its actual band
  span undercounts, because single-band nodes then need nothing.

**Files.** `t_regrow.py`, `t_gates.py`, `t_ext*.py`, `t_nerode.py` (rules min/outer/inner), `t_ner_why.py`,
`t_Mctx.py`; outputs `o_regrow_*`, `o_gates_*`, `o_ext2_*`, `o_ner_*`.

## Q7c: an intrinsic admissibility condition?

**Result: negative within the DS context shape.** I found no intrinsic condition that gives both truth (a) and
inheritance (b).

**Universe (why these contexts).** In the budget-form induction (§1), siblings either get disjoint band ranges or a
classic sibling is merged monochromatically into an extreme band of the window sibling. So a context is:
- v's band range [lo,hi] ⊇ v's own BDL range;
- lower pieces tagged lo and upper pieces tagged hi.

**Candidates tested [C] (`t_adm.py`, `t_adm2.py`).**
- **The coordinator's weak candidates fail truth.** Pieces valid among themselves, plus each extreme point / every
  point / every pair of points of v having a compatible band: 232, 229 and 211 uncompletable contexts out of 1500
  (k=6). The smallest failures are tags the induction never makes, e.g. a lower point that extends v's caps tagged
  inside v's range.
- **Adm_DS.** D1: pieces fit their bands. D2: cap(v ∪ lower pieces) ≤ k−1−lo. D3: cup(v ∪ upper pieces) ≤ hi+1.
  Also strong(v ∪ pieces) ≤ k−1.
  - Truth held in every random context tested: 1227/1227, 686/686 and 1272/1272 (k=6,7; up to 4 pieces of up to 5
    points).
  - Without D2 or D3, failures appear (78–93 per run).

**Inheritance of Adm_DS.**
- (c) The empty root context is admissible.
- (b) **[P]** Generic splits inherit every clause: all clauses are monotone under subsets, and the child ranges follow
  from D2/D3 and the choice of m.
- **[C]** Forced merges (classic child placed wholesale into lo or hi) keep it in 3000/3000 splits (`t_inh.py`).

**But truth fails on the contexts the induction creates.** I ran the proof as an algorithm (`t_solve.py`):
- moves: whole placement, generic m, wholesale merges;
- every generated context is admissible;
- yet the root fails in 262/1500 random sets (k=6) and 118/800 (k=7).

Failing admissible contexts are of two kinds:
1. **No completion at all** (426 of 471 at k=6). Merges accumulate monochromatic pieces in one extreme band. Later a
   node is forced alone into that band and straddles their tight cups.
2. **Completable but unreachable by DS moves** (45/471; on extremal T(4,6,7) 23 of 25).

**Repair attempt.** I added Lemma M's move: cut a classic child, put its left part in lo and its right part E into
the sibling's bottom band.
- Root failures drop to 11/1500 and 5/800.
- But it creates children outside Adm_DS: E extends the sibling's maximal caps (D2 violated in 214 calls).
- It still fails on extremal sets for **every** independently sampled tree in 3/8 T(4,6,7), 2/10 T(5,5,6) and 3/4
  T(4,7,7) sets (`t_solve_trees.py`). Choosing the tree does not rescue it.

**Mechanism.** On extremal sets a merged classic child must sometimes be split across lo and lo+1 according to the
sibling's *deeper* structure. That is lookahead: the parent cannot decide from the bounded context. The lo+1 part is
Lemma M's second-band piece. Whether it is admissible depends on which of the sibling's caps are monochromatic, which
is not intrinsic; the rigid form was already false in Q7.

**So (a) forces Adm to exclude the induction's own contexts, and then (b) needs moves outside the shape.** The bounded
context of Q7b is not enough by itself. Information of size ≤ 4 pieces exists, but it is fixed by a global partition,
not by local data.

**Unresolved.** Contexts with second-band pieces (lo+1, hi−1) under an exact rather than intrinsic admissibility
condition; that is, whether the existence statement itself could serve as a hypothesis via a different, non-DS
decomposition.
