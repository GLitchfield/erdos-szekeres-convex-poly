# Q9: is there a canonical band rule? (claude-bandrule-20261003)

Tags: **[P]** proved by hand here; **[C]** computed (CaDiCaL/pysat, diagnostic, not Lean).
Provenance: my code and outputs are in `q9/`, plus the early top-level files `bl.py bands.py e1-e8.py exh.py pascal.py
sigsat.py trees.py show*.py tight_sample.py data_t*.pkl o_e5_k6.txt o_e7_n8.txt`. All other top-level files came from a
duplicate instance the coordinator stopped. I have not checked them and do not use them.

## Answer

**No canonical rule exists among the kinds proposed.** Band partitions are massively non-unique. Every explicit rule
fails at the same place: case R with a sibling B that has three or more bands. There the valid choice depends on where
the nested sibling sits relative to the core of B's max caps. A context-free property that works may still exist
(§4).

## 1. Uniqueness on tight sets [C]

Six SAT samples per parameter set, `q9/tight_stats.py`. Partition counts are capped at 20000.

| (a,u,k) | partitions | forced points |
|---|---|---|
| (4,5,6) | 12–41 | 0 |
| (5,5,6) | 161–475 | 0 |
| (5,6,6) | 938–6050 | 0 |
| (6,6,6) | >20000 | 0 |
| (5,5,7) | 178–507 | 0 |
| (5,6,7) | 458–>20000 | 2 of 150 |
| (6,6,7) | >20000 | 0 |
| (5,6,8) | ≈20000+ | 0 |

- A point can usually sit in almost any band: 4.8–5.0 of 5 bands at (6,6,6).
- Under 2-point band swaps the partitions split into 3–15 components (`e16.py`). The freedom is global, not local
  exchange.
- **Tight sets therefore do not determine a rule.**

## 2. Rules tested

**Own-chain lookup tables.** The signature is (k, α, β, cup-end, cup-start, cap-end, cap-start). SAT over all tables
is UNSAT on the exhaustive set n ≤ 6, with a core of 14 instances (`e8.py`). The cause: some points have
cup-end + cap-start > k, so their band must break a long chain somewhere else.

**Tree-shaped partitions.** Tested on 853 sets (bdl-induct residue sets at k=6 plus nested samples), over all trees up
to 200 per set (`e5.py`):
- bands as intervals of the leaf order: fail for every tree on 11 sets;
- maximal classic subtrees kept in one band: fail for every tree on 44 sets.

**Other rules.**
- NAT (natural concatenation): 84% on random sets, 27% on residue sets.
- Lowest-band greedy in x-order: 99.5%, with 19 failures out of 3558. Each of its four variants fails somewhere.

**TDF: the best explicit rule** (`q9/tdf.py`).
- At A << B with interval [p,q], cut at the lowest m in [max(p, cupA−1), min(k−2−capB, q−1)].
- If cap B = cap Y, A joins band p. **[P]** This is valid when cup A ≤ p−1, by DS: cups gain at most 2.
- Case R (cup A = p): band p = A ∪ H, where H = first points of B's max caps (or last points if that fails), and B∖H
  goes recursively into [p+1, q]. The R′ case is the mirror.
- **[P]** TDF is correct whenever every case-R sibling has at most 2 bands. The classical bound cup(F_B) ≤ cup B − 1
  is then ≤ k − β, and B∖H has cap ≤ β−1, which keeps the invariants.
- **[C]** Exhaustive n ≤ 8, 2 trees per colouring: 885,860 (tree, k) instances with 0 failures; 91k case-R and 165k
  case-R′ corrections were used.
- **But it fails from n = 12** at (5,5,6), and at 8/160 instances at tight n = 14. A variant that first tries to absorb
  A into a band of B's canonical partition (AFL) fails from n = 13.

## 3. Why TDF fails: the structural obstacle [C]

Anatomy of the failure (`e14.py`, `e17.py`): X = {a} << B with B 3-band, and cup(F_B) = cup(L_B) = 3 > k−β = 2.

Of the 350 valid partitions:
- 267 **lift** a into band p+1. This needs every (β−1)-cap of B's band p+1 to span a.
- The others put a in band p with a bottom band that is a one-sided 3-subset which does **not** hit all of B's max caps.
  The remainder then needs a raised-floor partition, with B's max caps split across bands p+1 and p+2.

Both are Lemma-M-type statements about B relative to its cap core. Inside any canonical rule they recreate the context
regrowth found in bdl-induct.

## 4. A context-free invariant that does hold [C]: U

**Statement.** B has *one* band partition that extends to every case-R completion A << B, where:
- A is a (k−1−β)-cup in any core gap or gaps, or an ES(k−1−β, c) block, c ≤ β;
- A's bands are free.

**Evidence** (`q9/univ.py`, `e15`, `e18`–`e22`): U held jointly
- on 583/583 residue upper parts,
- on 70 sampled cored B's (k = 6, 7, 8),
- and on the counterexample's B.

**It is a real restriction.** In the counterexample's B, 203 of 944 partitions qualify. All G-type partitions qualify:
these have bottom band ≤ L* (15) or ≥ R* (43). The other 145 qualifying partitions work by lifting.

**Why it matters.** U is weaker than G and contains the lifting option that G's proof needs (S1/S2, Lemma M). It is my
suggested replacement hypothesis for Q7.

**Not tested:** siblings interleaved with B inside the core.

## 5. Side finding: Pascal split PSL [C]

**Statement.** X = R ⊔ Bl with:
- R: cap ≤ β−1 and strong ≤ k−2;
- Bl: cup ≤ α−1 and strong ≤ k−2.

**Evidence.**
- Holds for all 198,274 colourings n ≤ 8 (job 20261003-120336-c6aedf).
- Holds for every sample at k = 6, 7, 8 that finished, including tight (6,6,7) n=30 and (5,7,8) n=40. The (6,6,8) n=45
  run was killed at the 2G memory cap.

**Why it matters.** With T(a,u,k) = T(a−1,u,k−1) + T(a,u−1,k−1), PSL proves Theorem 8 by induction on k in a
hereditary class, with no context.

**Caveat.** In its own tree induction, only the strong-number part composes freely. The cup/cap reductions meet a
case-R analogue, so PSL is not obviously easier than BDL.

## Proof idea, learned, obstacle

- **Proof idea for BDL:** concatenate the children's natural ranges. This is valid except at case R.
- **Canonical fixes:** handle ≤ 2-band siblings (classical F/L peel).
- **Obstacle every attempt hits:** a ≥ 3-band sibling, which needs lifting or raised floors.
- **Open:** prove U, or a form of PSL, by tree induction.

## Evidence

**Jobs:**

| job | what |
|---|---|
| 20261003-115949-e2b6eb | all-trees test |
| 20261003-120336-c6aedf | PSL, n ≤ 8 |
| 20261003-121305-cc72e0 | TDF, n ≤ 8 |
| 20261003-121907-27f662 | uniqueness |
| 20261003-120751-b9e395 | PSL sweep (cancelled, partial) |
| 20261003-122405-6ccd7b | PSL sweep 2 |

**Outputs:**
- `o_e5_k6.txt`, `o_e7_n8.txt`;
- `q9/o_e13_n8.txt`, `q9/o_tight_stats.txt`, `q9/o_psl_sweep*.txt`.

## Q9b: is U general, and does it compose? (q9/; [C] = diagnostic, [P] = proved by hand)

**Roles.**
- U(Y): Y is an upper part; one band map of Y extends to every case-R completion A<<Y.
- U′(Y): the mirror, for a lower part with upper siblings in its cup core. It is computed by complementing labels and
  reflecting j → k−2−j.
- Bi-universal means both U and U′.

### (1) Generality: no counterexample [C]

**Sibling class.** Every decomposable A with cup A = k−1−β and |A| ≤ 6, interleaved in any way with B's points
inside the cap core, such that cap(A<<B) = β. Non-tight siblings always extend, by DS.

**Method.** CEGAR (`univ_gen.py`). Each context check is a SAT call, verified against brute force (1920/1920).

**Result.** A universal partition existed in every case:
- 583/583 residue upper parts. The sibling class is complete for m=2 (caps), and for k=7, β=3, m=3.
- 134 (B,k) instances on 80 sampled cored B's at k=6,7,8, with up to 6175 contexts per instance.
- By type: 43 G, 47 G′, 44 lifting.

**Gap.** For m ≥ 3, coverage beyond the k=7 residues is thin.

**[P] Two easy facts.**
- G ⟹ U, since a bottom band at or left of L* is one-sided for every sibling. U is strictly weaker than G.
- U holds for 2-band B: take the bottom band F_B, whose cup is ≤ cup B − 1 = k − β.

### (2) Composition: U does NOT compose [C]

**Tests.**
- Exhaustive over n ≤ 6: all colourings, one tree, every k, siblings |A| ≤ 5 (`c5.py`).
- A sample at n = 7: 250 of 505 sampled colourings, siblings |A| ≤ 4. The job was killed at 2G; the rest is left
  open.

Every X has a bi-universal partition. Counts for concatenation splits:

| test | n = 6 | n = 7 |
|---|---|---|
| every concatenation P_A∪P_B of bi-universal child partitions is bi-universal | 561/652 | 269/330 |
| no concatenation works at all | 77 | 48 |
| every bi-universal P_B extends to X | 369/652 | 197/330 |

Always true (all 1,378 nontrivial (X,k) checked): some bi-universal P_X restricts to bi-universal partitions of both children
(heredity), and some P_B extends. Universal partitions can be **chosen** compatibly, but cannot be **built** from
arbitrary ones.

**How it fails** (`c4.py`, `c6.py`, `c7.py`). Smallest example: X = (1<<4)<<((0<<2)<<3), k=6, P_A=(1,1), P_B=(2,2,2).
- A 2-point upper sibling in X's cup core extends through B only via band 1, which in X belongs to A.
- The bi-universal partitions of X split by position. One is (1,1,2,2,2): the bottom band is left of the cap core and
  the top band is right of the cup core.

At n ≤ 6, failing (pair, role) instances are of two kinds:
- **cross-child lift (38):** X's max chain is carried by the child at the end of the range, and the sibling's lift
  lands in the other child's band;
- **mixed (113):** X's max chain uses both children, so the sibling is a context of neither child alone.

### (3) Proof

**[P] U ∧ U′ for all decomposable sets ⟹ BDL**, by tree induction:
- a generic cut: concatenate the two partitions;
- a non-tight absorption: put A into band p (by DS);
- case R: use U(B); case R′: use U′(A).

**The missing step** is U's own step: *X = A<<B has a universal partition.* The data show it cannot be built from the
children's universal partitions. The required bands cross the A/B boundary, and one sibling constrains both children.
This is the context regrowth again, now as band floors and ceilings.

**Verdict.** U is a sound context-free *target*, but not an inductive invariant. A proof needs a positional
construction. The candidate is the opposite-side G/G′ joint seen in the failure, which is bi-universal [P].

**Jobs.**

| job | purpose |
|---|---|
| 20261003-123836-9f9e2a | generality sweep |
| 20261003-130420-5bbf8f | rerun of a B killed at 2G |
| 20261003-124654-c6cdee | composition, n ≤ 6 |
| 20261003-125618-d1b90f | failure classes |
| 20261003-130544-f193c0 | composition, n = 7 (partial) |

## Q9c: opposite-side joints (q9/; [C] = diagnostic, [P] = proved by hand)

**Definitions.** A *joint* is a partition whose bottom band is one-sided w.r.t. the cap core (G: ≤ L*, or G′: ≥ R*)
and whose top band is one-sided w.r.t. the cup core (T: ≥ R′*, or T′: ≤ L′*).
- OSJ = V1 = G+T; V2 = G′+T′; S1 = G+T′; S2 = G′+T.
- V3/V4 put the extreme bands inside the first/last points of the max caps/cups.

### (1) Existence [C]

**Exhaustive n ≤ 8, ≥ 3 bands** (243,956 (X,k); job 20261003-133532-df3779): V1–V4 always exist. With 2 bands OSJ
fails structurally, since every point lies in an extreme band, but G and T always hold.

**Samples, k = 6–9:** V1 fails in 6/178 cases, all with **both cores empty**.

**Counterexample** (`cex_osj.txt`, tight (5,6,7), n=25, k=7):
- V1–V4 all fail, and so does G: no partition has its bottom band ≤ L* = 18 (two independent searches).
- This refutes bdl-induct's G(X, L*) as stated; that was tested only to n ≤ 12.
- Only S2 survives.

So OSJ in a fixed orientation is false. A joint in *some* orientation held in every ≥ 3-band case tested.

### (2) Composition

**[P] Concatenation lemma.** Let X = A<<B with both children *wide* (cup + cap ≥ k+1), and take natural-range
partitions P_A (bottom one-sided) and P_B (top one-sided). Then P_A ∪ P_B is a joint of X with the same orientations.
- X's bottom band is A's if cap A = cap X, and empty otherwise.
- X's max caps contain A's, so L*_X ≥ L*_A and R*_X ≤ R*_A. The top is dual.
- A lower child needs only a one-sided bottom and an upper child only a one-sided top. So 2-band children (classical
  F peel) suffice.

**[C] Failures.** Exhaustive n = 7 (jobs 20261003-135015-85b4ed, -135550-337bb3).

| split type | (X,k) | disjoint | touch | cross (no concatenation or one-band merge is OSJ) |
|---|---|---|---|---|
| concatenation | 10,892 | 5011 | 3022 | 2859 (26%) |
| absorption | 308 | 0 | 287 | 21 |

- **Every cross-only case has a classic (one-band) child.** None has two wide children.
- By chain, 2297 are mixed (the max chain runs through both children), and 556 have one child carrying both max
  chains.
- The samples agree: 39/172 are cross-only, all with a classic child.

**Mechanism.** A classic block at an extreme band must be split by position: its in-core part moves one band inward,
into the other child's extreme band (cross-child). Case R is the nested instance: OSJ forces the block out of the
bottom band, which is Lemma-M lifting.

**Canonical rule.** A canonical 3-band OSJ rule (`r3.py`) fails in 70/8806 cases at n ≤ 7.

### (3) Proof

- **Hypothesis J:** every decomposable Y has a natural-range joint in some orientation. For 2-band Y, only the side its
  role needs.
- **J ⟹ BDL:** case R uses B's one-sided bottom band.
- **The step is proved for wide–wide splits** (the lemma above).
- **The single open step is classic-block insertion.** Given a joint of the wide child W and a classic ES-block
  sibling Z (nested or not), produce a joint of the union. Z must be split along its own core, and W's extreme band
  must absorb or yield one band. This step contains case R; point insertion is its smallest instance, which
  runs/claude-insert-20261003 is studying, so it is not attempted here.
- **Recommendation:** target J (any orientation), not OSJ, and prove classic-block insertion.

## Q9d: classic-block insertion (CBI) (q9/; [C] = diagnostic, [P] = proved by hand)

### 1. Restated statements

- **G_core:** if L* < R*, some BDL partition has its bottom band ≤ L*. **G′_core** is the mirror (bottom band ≥ R*).
- **J:** some natural-range partition has its bottom band on one side of the cap core and its top band on one side of
  the cup core, in any orientation. This is for ≥ 3 bands; a 2-band set needs only the side its role uses.
- **[C]** Both hold on all n ≤ 8 and on the k = 6–8 samples (344 J, 217 G_core; `o_d0.txt`). This includes the n = 25 OSJ
  counterexample: its cap core is empty, so G_core is vacuous, and J holds via S2.

### 2. CBI, exactly [C]

**Setting.** X = Z<<W or W<<Z, with any interleaving. Z is classic and W is wide. W's joint is fixed; Z's bands are
free.

**Exhaustive results, n = 7, 8** (`o_d1_n8.txt`):

| case | every joint of W extends to a joint of X | some joint of W extends |
|---|---|---|
| W ≥ 3 bands, concatenation type (cap W < cap X; mirror for Z upper) | 67,183/67,183 | all |
| W ≥ 3 bands, absorption (Z nested in W's core) | 63–67% (every joint does extend to a BDL partition) | 50,929/50,929 |
| W 2-band (role side only) | 99.0% | all but 28 |

In the 28 failures the extendable partitions of W are one-sided only w.r.t. **X's** smaller core (`d7.py`).

**Strongest true version:** CBI_concat (every joint, for W with ≥ 3 bands) and CBI_abs (some joint).

### 3. The canonical split of Z

**Rule.**
- Z stays in its lowest band j0 = max(cup Z − 1, lo).
- If j0 = lo, the points on the wrong side of X's cap core move up to lo+1: z > L*_X for orientation G, z < R*_X for
  G′.
- X takes W's bottom orientation. Z upper is the mirror.

**[C]** For W with ≥ 3 bands at concatenation-type splits it works for **every** joint of W:
- 558/558 at n ≤ 6;
- 2890/2890 at n = 7;
- 10,731/10,731 at n = 8 (every 6th colouring, `o_d2b_n8.txt`).

All of its failures (≈ 0.5%) have a 2-band W.

**[P] Proof** (concatenation type, Z lower, W ≥ 3 bands, W's cap core nonempty).
- Band lo holds only Z's good side, since W's floor is ≥ lo+1.
- Z's lifted part contains no cap of length cap X, because every max cap starts at a point ≤ L*_X.
- If W's floor = lo+1, a long chain through the lifted points would force a contradiction in every case:
  - a cup w+C+w′ with w′ ≤ L*_W: then z+D₀, with D₀ the max cap of W starting at L*_W, is a max cap of X starting at
    a point z > L*_X;
  - a cap starting at a lifted point: the same contradiction;
  - D+z′ with D a full max cap of W: impossible, because a one-sided bottom band contains no max cap of W.
- The top band of X is inherited from W.

### 4. Absorption: the remaining step

**[P] Exact lift criterion** (0 mismatches on 7784 instances, `d6.py`). For a G-joint of W, the lift is a joint of X
iff no (cap−1)-cap of W's band lo+1 lies entirely left of a lifted Z point.

**[C] Universal joints** (one joint for every nested Z with |Z| ≤ 4, any interleaving): 261/261 at k = 6 and 314/322 at
k = 7.
- In the 8 failures W has two joints, one G and one G′. Z on the left of the core needs G, Z on the right needs G′
  (`d4b.py`).

**The single open step (Lift Lemma).** For nested classic Z, W has a joint whose orientation is chosen from Z's
position (G or G′) and whose band lo+1 has no (cap−1)-cap on the far side of a lifted point. For 2-band W the
condition must refer to the parent's core: G(W, t) with t = L*_X.

**Verdict.** The induction for J closes at wide–wide and concatenation-type classic splits [P]. What remains is
bdl-induct's Lemma M, sharpened to an exact criterion with a context of one cut point and one orientation.

## Q9e: the Lift Lemma as a property of (W, t) (q9/; [C] = diagnostic, [P] = proved by hand)

**Definition.** Let W be wide with bands lo..hi, β = cap W, and cap core L* < R*. A cut t is a gap index: a
sibling point at t sits between W-points t−1 and t, and t is a core cut iff L*+1 ≤ t ≤ R*.
- **LL_G(W,t):** some natural-range partition has its bottom band ≤ L*, its top band one-sided (when W has ≥ 3
  bands), and no (β−1)-cap inside band lo+1 ending before t.
- **LL_G′(W,t):** the mirror, with bottom ≥ R* and no (β−1)-cap of band lo+1 starting at or after t.
- **LL = LL_G or LL_G′.** The top-side version LL^top is the cup/cap mirror, acting on band hi−1.

### 1. Truth [C]

All decomposable colourings with n ≤ 8, every core cut (`ll.py`, `e1q.py`, job 20261003-145040-61219e):
- **W with ≥ 3 bands: LL holds at every core cut** (228,823 (W,k), 0 failures).
- The structure is monotone: LL_G holds on an initial segment of cuts and LL_G′ on a final segment.
- The boundary cuts LL_G(L*+1) and LL_G′(R*) always hold.
- The fixed-orientation form LL_G(R*) (condition M) fails in 4,039 3-band cases, so the orientation really must be chosen from t.
- **2-band W fails at a middle cut** in 130/171,923 cases. Example: core (0,7), G holds for t ≤ 3, G′ for t ≥ 5,
  neither at t = 4.
- **Two-sided LL** (a bottom cut and a top cut in one partition) holds for all 162,848 cut pairs at n ≤ 7 (`e2q.py`).

### 2. Closure

**[P] Wide–wide concatenation.** LL_G(W,t) follows from LL_G(A, t_A) when cap A = cap W, with t_A = t read in A's
coordinates. W's band lo+1 is then A's band lo+1, so its caps are A's caps. Also t lies in A's core and L*_A ≤ L*_W.
If cap A < cap W, the step is vacuous: band lo+1 is A's bottom band, and a one-sided bottom band contains no max cap
of A when A's core is nonempty. **The cut passes down unchanged, and no new cut appears.**

**[C] Information form (heredity with determined cuts).** Does some LL_G(W,t) witness restrict to wide children that
satisfy their own-core LL at the mapped cut? In absorption the sibling's extreme position is added and combined by
max (`e5q.py`).
- **≥ 3-band children:** 621/621 at n ≤ 6, and 1436/1437 on a 1/12 sample of n = 7. The one exception is a test
  artifact: the test lowered all of Z.
- **2-band children:** about 75–83% only, even with one-sidedness measured against the parent's core. The witnesses
  put a 2-band child's points **below its natural floor**. For example, B's first point drops into W's bottom band
  because W's max caps are B's caps extended by the classic sibling.

**[C] Fixed constructive moves** (`e3q.py`, n ≤ 6) do not close:
- *Classic-block splits:* the canonical split ignores t. The lifted block can carry a (β−1)-cap ending before t, and
  the split works in only 449/776 cases.
- *Absorption:* t and the sibling can demand opposite orientations. In 3/122 (Z lower) and 146/359 (Z upper) cases no
  child partition meets the requirements.

**Does it regrow? No, in count.** Same-orientation cuts on a side combine by max, because LL_G is monotone in t. A
child's context is therefore bounded: per side, a floor, a position cut, an LL cut and an orientation, all set by the
parent and the sibling. **But** closure of that family is not established: lowered floors and orientation conflicts
may break it.

### 3. Proof status of the J + LL induction

| step | J | LL |
|---|---|---|
| wide–wide | [P] Q9c | [P] above |
| classic block, concatenation type | [P] canonical split (Q9d) | open: needs a cut-aware split |
| absorption | [P] exact criterion, given the child's LL at max(t, z) | open: orientation conflicts |
| 2-band children | open: lowered floor plus the parent's core | open |

The key fact behind every [P] step is that every max cap starts at or left of L*, so lifted points cannot start one.
It does not settle forced-orientation conflicts or floor drops.

**Verdict.** LL is true and its cut does not multiply. Three concrete steps remain:
- a cut-aware split for classic blocks;
- the orientation choice when t and the sibling disagree;
- floor lowering for 2-band children.

## Q9f: the bounded context family, tested for closure (q9/ctx.py, f1.py; [C] diagnostic, [P] by hand)

**Family.** On each side a context is (F, o, s, t):
- F is an absolute floor (natural, or lowered by one); o is the orientation;
- s is a position cut on band F; t is an LL cut on band F+1, applied to caps of length k−2−F.

S(W,c) asks for a partition in [F, ceiling] meeting both conditions. A context counts as **realisable** only if an LL
cut comes with a position cut.

**Closure test.** A step closes if, for **every** child partition in the child's context, the classic sibling can be
re-banded so that the union lies in S(W,c). Child contexts come from determined rules: inherit; inherit + sibling cut;
own core; flipped; free. The test uses bottom-side contexts of W, with the top left free.

### 1. Truth and closure at n ≤ 6 [C]

Exhaustive run, 23,600 true contexts with ≥ 3-band W (`o_f1h.txt`).
- **Closed for every split whose wide child has ≥ 3 bands.**
- With a 2-band child it is closed except for 10 of 10,894 (A<<Z concatenation).

This needed three **refinements of existing parameters**:
- **R1:** a second position cut on band F+1, with the LL cut moved onto that band. This is the child's own bottom when
  the floor is lowered, and it repairs the empty-core gap in the CBI proof (Z<<B concatenation, empty core: 188/188).
- **R2:** a raised ceiling, the mirror of the lowered floor.
- **R3:** the floor band reserved for the classic block. With it, the 2-band empty-core cases reach 1644/1644.

At this size: (i) the cut-aware classic split exists (R1, R3); (ii) absorption orientation conflicts all close for
≥ 3-band W; (iii) "floor = parent's bottom band" is right, provided the child also gets R1.

### 2. Closure fails at n = 7, and the failure needs a NEW parameter [C]

The run covered every 10th colouring with the full refined menu (`o_f1h_n7.txt`, job 20261003-153734-ea09fe).

**Still closed:**
- A<<Z absorption: 8336/8336;
- concatenation with ≥ 3-band children: 16,136/16,136.

**New failure:** Z<<B absorption with W and child both ≥ 3 bands fails in **40/3340** cases.

**Anatomy.** Take W = Z<<B, k = 6, with W's context (1, G, 3, 5).
- The inherited LL cut t = 5 lies beyond the nested Z.
- The lifted Z then completes caps D+z with |D| = cap−2 inside band lo+1, for example (2,3,4). These end before t and
  violate W's LL.
- **The child needs a second LL condition of shorter length:** no (cap−2)-cap of B's band lo+1 may end before Z's
  cut. With it, every remaining child partition extends in all 4 failing contexts (56/56, 56/56, 94/94, 94/94).

**This is regrowth, not a refinement.** Each level that lifts a nested sibling into the same band adds a
(length, cut) pair (lengths cap−1, cap−2, …). The context becomes a non-increasing cap-length profile along the band:
the DS zone-profile context again, bounded only by cap−2 entries. This matches Q7c's k-dependent piece count.

**Other n = 7 failures:**
- 2-band children: 20/22,518 (A<<Z) and 36/5,222 (Z<<B, empty core);
- 2-band W in absorption: 171/10,912 and 46/6,220.

**Caveat:** at n = 7 the child-partition enumerations hit the 200 cap in 186,535 tests, so the "closed" verdicts there
are only partial.

### 3. Status and target

- **Proved by hand:**
  - J at wide–wide splits and at classic concatenation (Q9c, Q9d);
  - LL at wide–wide splits (Q9e);
  - the exact lift criterion (Q9d).
- **Computed:**
  - the family with R1–R3 is closed through n = 6;
  - at n = 7, two nested siblings that lift into the same band force a cap-length profile.
- **Relation to R25's BRL+:** S at the trivial context (natural floor, own-core cut, no LL) is BRL+, i.e. G_core,
  which held in every test. The J + LL induction would prove BRL+ only if the family closed. It does not: the
  absorption step regrows a cap-length profile.
- **Target recommended:** BRL+ itself, by a direct realignment (exchange) argument. R25 found that one-point moves
  and frozen higher-band repairs fail. The profile is what a chain of band moves must preserve: band lo+1 keeps every
  cap of length cap−j ending at or after the j-th lifted position. The bounded-context positional induction is
  refuted at n = 7.

## Q9g: BRL+ by realignment (q9/realign.py, g1r–g5r; [C] diagnostic)

**Setting.**
- Y has ≥ 3 bands and an open max-cap core (L*, R*).
- π is any valid partition whose bottom band is not one-sided.
- d(π) is the smallest number of points whose band must change to reach a valid one-sided partition, on either side.
  It is computed with a SAT totalizer.
- m(π) is the number of bottom points on the wrong side, minimised over the two sides. It is a lower bound for d.

**Coverage.**
- Exhaustive n ≤ 6: 99,398 partitions π.
- n = 7, every 5th colouring: 384,490.
- n = 8, every 40th colouring: 1,058,999. Partitions were capped at 300 per (Y, k), so this is a sample.
- Nested samples at n = 14, 16 (k = 6) and n = 26 (k = 7).

### 1. Distance [C]

| range | d | d − m | d = m |
|---|---|---|---|
| n ≤ 8 | ≤ 5 | ≤ 3 | 90–96% |
| n = 14, 16 | ≤ 7 | ≤ 4 | – |
| n = 26 (4 bands) | up to 11 | up to 10 | 21/120 |

The repair is **not bounded by a constant, nor by m**. It grows with |Y|.

### 2. Monotone cascades [C]

| realignment type | n ≤ 6 | n = 7 | n = 8 | n = 26 |
|---|---|---|---|---|
| upward only | 93.7% | 95.3% | 98.0% | 33/120 |
| up + refill (allowed-side points may drop into the bottom band) | all | all | all but 21 | 100/120 |
| side-monotone (wrong-side points never move down) | all | all | all but 8 | 104/120 |

- Monotone cascades fail.
- At 3 bands, up + refill held for all 6.9M partitions checked at n = 8. That covers 6000 of the 23,361 colourings
  in an every-8th sample; the job was stopped and the rest is left open.
- **Side-monotone counterexample** (n = 8, k = 5). There is a single max cap (0,1,3,5), with core (0,5). The bottom
  band has cup limit 1, so it is a single point. Every one-sided partition moves some wrong-side point down.
- **Typical failure, a rotation trade** (n = 14):
  - the wrong-side bottom points {7,13} jump two bands up;
  - the allowed-side points {3,4} drop from that band into the bottom;
  - a secondary swap 0 ↔ 6 between the two middle bands repairs the rest.
- Optimal realignments are thus **equal-size swaps between band pairs, with secondary swaps**: alternating chains, not
  cascades.

### 3. Invariant [C]

None of the three candidates explains termination.
- **Key fact** (every max cap starts at or left of L*): it makes upward moves of wrong-side points cheap, which is why
  up-only works ~95% of the time at n ≤ 8. It cannot rule out the needed downward moves.
- **Cap-length profile:** it is not preserved along the optimal chains, which cross bands in both directions.
- **Potential Σ band·position:** not monotone along any optimal realignment, which mixes up and down moves.

### 4. Proof status

**No exchange proof.**
- BRL+ itself (G_core or G′_core, given that BDL holds) held in every test (n ≤ 8 exhaustive; samples).
- From an arbitrary π the realignment is a global alternating swap structure.
- This matches R25's report that one-point moves and frozen higher-band repairs fail.

**The single step that would close an exchange argument.** An augmenting-chain lemma: if π's bottom band contains a
wrong-side point, there is an alternating chain of swaps
- wrong-side point up, allowed-side point down, between band pairs (lo, j₁), (j₁, j₂), …,
- each swap restoring validity except at the next pair,

that ends in a valid partition with strictly fewer wrong-side bottom points.

**Suggested tractable case.** Exactly 3 bands. There, up + refill (a one-swap chain) never failed on 6.9M partitions;
a hand proof would use the classical first-point facts.

**Recommended structure.** A Hall/augmenting-path formulation fits this structure (cf. Q12). Proving BRL+ as a pure
existence statement may also be easier than realignment from an arbitrary π.

## Q9h: the base of the augmenting chain (q9/h1–h5, h3.py; [C] diagnostic, [P] by hand)

### 1. Three bands, L = lo, M = lo+1, T = lo+2

**[P] Reformulation.** Write α = cup Y and β = cap Y; with 3 bands, α + β = k+2. A 3-band partition is valid iff:
- (i) L ∪ T meets every α-cup and every β-cap;
- (ii) cup L ≤ α−2;
- (iii) cap T ≤ β−2.

The remaining limits are vacuous: cap L ≤ β, and cup T ≤ α.

**[C] One-swap lemma (BS+MT).** From any valid π (orientation G; G′ is the mirror), with W the wrong-side bottom
points, there is a valid one-sided σ obtained by:
- sending every w ∈ W up to M or to T;
- dropping some allowed-side points (≤ L*) of M ∪ T into L;
- lifting some points of M to T.

Nothing else moves.

| scope | partitions | BS+MT holds | without the M→T moves (pure bottom swaps, BS) |
|---|---|---|---|
| n ≤ 6, exhaustive | 77,198 | all | all |
| n = 7, every 4th colouring | 1,334,826 | all | all but 10 |
| n = 8 sample (earlier up+refill run) | 6.9M | all | – |

Swaps with a single band only, SW(M) or SW(T), cover about 99%.
- The refill must sometimes come from T (n = 5, k = 5: the bottom band is one point and only a T point is on the
  allowed side).
- Rule-based variants (drop the first points of the max caps, lift the last points of the max cups) fail in 3% of
  cases (`h1.py`).

**[P] Partial proof.** Set L′ = L₀ ∪ Q, M′, T′ = (T∖Q) ∪ W_T, with W = W_M ⊔ W_T.
- **Condition (i):** it requires only the chains that lose all their (L∪T)-points to W_M to be met by Q∩M.
- **β-caps:** such a cap has its first point ≤ L* (key fact), and that point is in M. Dropping it repairs the cap.
  *This part is proved.*
- **Open, and the exact remaining step:**
  - α-cups whose M-points all lie on the wrong side force some w ∈ W_T, which creates (iii)-obligations in T;
  - the drops Q must keep cup(L₀ ∪ Q) ≤ α−2, i.e. condition (ii).

  The strong-number bound (strong ≤ α+β−3) is not yet used. Since BDL fails for general signotopes, it must enter
  exactly here, at (ii) and (iii).

### 2. Chain shape for more bands [C]

**Adjacent chain:** every point moves at most one band.

| bands | failures | at |
|---|---|---|
| 3 | 2 / 892k | n = 8 |
| 4 | 56 / 167k | n = 8 |
| 4 | 16 / 120 | n = 26 |
| 5 | 3 / 240 | n = 16 |

**Path chain:** moves only between consecutive members of a single increasing band sequence lo = b₀ < b₁ < … (jumps
allowed).

| bands | failures | at |
|---|---|---|
| 3 | 1 / 892k | n = 8 |
| 4 | 8 / 120 | n = 26 |

- At 3 bands, the obstruction is a **star**: the bottom must swap with M and with T simultaneously (n = 8 example: 2 up
  to M, {5, 7} up to T, 1 down from T).
- At 4–5 bands, the obstruction is a star plus **secondary** swaps between middle bands.

**Answer to (2): no.** No realignment visits each adjacent band pair once, so there is no induction on the number of
bands along a chain.

### 3. The augmenting structure, as far as the data supports it

**[C] Realignment = bottom star + repair.**
- *Bottom star:* the bottom band exchanges points with several bands at once. Wrong-side points go up; allowed-side
  points come down.
- *Repair:* swaps among the higher bands. They are empty at 3 bands (apart from M→T lifts) and needed in about 1–20%
  of cases at 4–5 bands.
- No monotone, path or adjacent chain form is universal.

**The lemma the data supports.** For 3 bands, BS+MT (§1) holds on all 8.3M partitions tested, and its proof reduces to
one step: an assignment W → {M, T} together with refills Q satisfying (i)–(iii). The β-cap part is done.

**Recommended next step.** Prove the 3-band lemma as a 2-colouring problem on W with refills; the strong-set bound
must supply (ii)/(iii). Beyond 3 bands an exchange proof needs a principle other than chains; the CORE route (Q15)
may be the better target.

## Q19: is CORE inductive under DS splits? (q9/c19b.py, c19c.py; [C] diagnostic)

**Definitions, as in Q15.** B is a cored window set: cup+cap ≥ k+2, strong ≤ k−1, and an open max-cap core. A
colouring (R, T) of B satisfies:
- **PSL⁺(B):** cap R ≤ β−1, cap T ≤ β−1, cup T ≤ α−1, and strong R, strong T ≤ k−2;
- **PSL:** drops "cap T ≤ β−1";
- **HIT:** drops "cap R ≤ β−1".

Thus PSL⁺ = PSL ∧ HIT.

**Method.** Each decomposable root split B = B₁<<B₂ is classified by:
- which child carries the max cap;
- which carries the max cup;
- each child's type: cored window, window, 2-band or classic.

A rule (o₁, o₂) **works** at a split if every child colouring in a universal class oᵢ ∈ {PSL⁺, PSL, HIT, red, blue},
each child measured with its own cup and cap, combines with an existential choice ("free") for the other child into
a PSL⁺(B) colouring.

Data: exhaustive n = 7 (10,379 cored (B,k)) and every 5th colouring at n = 8 (43,542).

### 1–2. Classes and composition [C]

**Wide–wide cored splits are almost absent** (12 at n = 8). They compose under (PSL⁺ or PSL, PSL).

| split class (n = 8) | splits | carrier universal (CORE at the child) | sibling-first relief |
|---|---|---|---|
| cored child carries the max cap only, classic sibling | 7244 | **(PSL⁺, free): 7244** | – |
| cored child carries the max cup only, classic sibling | 6106 | **(free, PSL⁺): 6106** | – |
| cored lower child carries cap **and** cup, classic sibling | 5746 | (PSL⁺, free): 4903; PSL: 840; HIT: 840 | (free, HIT/red/blue): 5746 |
| cored upper child carries cap **and** cup, classic sibling | 4733 | (free, PSL⁺): 4413; others 0 | (red/blue/HIT, free): 4733 |
| 2-band lower carrier, classic sibling | 10,697 | (PSL⁺, free): 10,610 | (free, red/blue): all |
| 2-band upper carrier, classic sibling | 11,796 | (free, PSL): 11,782 | (red/blue, free): all |

**CORE composes where the cored child carries one maximum. It fails where it carries both** and the classic sibling
then sits inside its core (the PSL forms of case R and R′): an arbitrary PSL⁺ colouring of the carrier fails to extend
in 7–15% of these splits.

**Mechanism.** At n = 6, k = 5, take W = {0,2,3,4,5} (cored, carrying both maxima) and Z = {1}.
- W's PSL⁺ colouring R_W = {0,2,3} does not extend.
- If Z is blue, it extends W's blue (α−1)-cup (4,5) to a blue α-cup.
- If Z is red, it completes a red (k−1)-gon with W's red points.

So the carrier's colouring must satisfy a cut condition at the sibling's position. This is the same regrowth as H_U (Q14)
and LL (Q9f).

### 3. Monochromatic-child relief [C]

The relief (sibling monochromatic, or HIT, with the carrier chosen afterwards) works at every double-carrier split:
5746/5746 and 4733/4733. **But it reverses the order**: the classic sibling is fixed first and the carrier is
adapted to it. The carrier's statement must therefore take the sibling as input. That is exactly a context; it is not
a context-free hypothesis on the carrier.

### 4. Verdict

**CORE is not inductive with context-free child hypotheses. It needs context (regrowth)** at double-carrier splits
with a nested classic sibling.

| step | status |
|---|---|
| single-carrier and 2-band-sibling splits, with universal hypotheses | [C] composes; hand proof not attempted |
| double-carrier splits | need "PSL⁺ in a one-sibling context": no blue (α−1)-cup extendable through the sibling's gap, and no red gon completed by it |
| the double-carrier step | it is CR1/H_U's cup-side twin, with the same growth under further nesting |

**Recommended next steps.**
- Test whether a "universal" PSL⁺ colouring exists: one colouring of the carrier that serves every admissible nested
  classic sibling, the U-analogue of Q9b.
- If it does, check whether it composes. Q9b's U did not.
