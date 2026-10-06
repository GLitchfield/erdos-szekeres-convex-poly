# Q10: PSL versus BDL, and the tree induction for PSL (claude-psl-20261003)

**[P]** proved by hand. **[C]** computed (diagnostic; own C/pysat code, no DRAT, not Lean).

**Notation.**
- X = A << B, with α = cup X, β = cap X, strong X ≤ k−1, in the window α+β ≥ k+2.
- *Own PSL* of a set Y: cap R ≤ cap Y−1 and cup Bl ≤ cup Y−1, with both parts of strong number ≤ k−2.
- ext_Z(D) = the number of sides of D on which Z has a point.

## 1. Relation

**FULL labelling.** Each point gets a word in {U,D}^(k−2), subject to three sets of bounds:
- PSL bounds on every prefix class;
- BDL bounds on every class #U = j;
- classical Erdős–Szekeres bounds inside every band.

**[P]** FULL implies PSL (first letter) and BDL (#U). Conversely, FULL holds iff all of the following do:
- X has a PSL split (R, Bl);
- FULL(R) and FULL(Bl) hold;
- **merge**: R^j ∪ Bl^(j−1) is a band for every j.

**[C] Evidence.**
- Every PSL split extends to FULL: all decomposable n ≤ 8, 26.4M splits.
- Some BDL partitions extend to no FULL labelling: 783 of 2.29M at n = 7.
- PSL holds on all 1.05M non-decomposable 8-point signotopes, as BDL does.

**Verdict.**
- No implication is proved either way.
- No small signotope class separates the two statements.
- PSL ⇒ BDL is exactly the iterated merge condition.
- BDL ⇒ PSL cannot start from an arbitrary band partition.
- The underlying difference: BDL is tree-aligned (the children's band ranges are disjoint outside case R). PSL is tree-transversal: at tight nodes, R and Bl each meet both children.

## 2. Tree induction for PSL

**[P] Uniform rules.** Take unions of own PSL splits of the two children.
- Strong numbers always compose.
- If cap B ≤ β−2 and cup A ≤ α−2, the union is a PSL split of X.
- If cap B ≥ β−1 and the node is not tight, put A wholly into Bl.
- Mirror rules handle cup A ≥ α−1.

**Where the rules fail.** At tight nodes (cup A + cap B = k−1) with
- **R**: cap B = β, or
- **R1**: cap B = β−1,

and at their mirrors. In both, the sole condition is |D| + ext_{R_A}(D) ≤ β−1 for every cap D of R_B.

**[C] Exhaustive, n ≤ 9.**
- Only these classes lack a uniform rule.
- Splitting A first (with any own PSL), then B with an own PSL, always works.
- Splitting B first fails on 146k case-R splits.

**Versus BDL.**
- R is exactly BDL's case R. R1 is extra: BDL closes it freely.
- PSL's condition is narrower. BDL needs both a one-sided bottom band (P) and lifting (M). PSL only needs A's R-points not to extend B's near-maximal R-caps: one direction, one colour.

## 3. Strengthened PSL

**Candidates.**
- **H_U (case R).** B has an own PSL split in which:
  - every (β−1)-cap of R spans the core of B's β-caps;
  - every (β−2)-cap of R strictly inside that core contains, within its x-range, a (β−1)-cap of B.
- **R1U (case R1).** B has an own PSL split in which every (cap B−1)-cap of R contains, within its x-range, a cap-B cap of B.

**[C] H_U survives.**
- All realisable cases with n ≤ 9: 3.0M sets that have a core.
- 176 near-extremal nested samples with k = 6–8 and n ≤ 38: 0 failures. A-first worked for all 142 sampled R_A with |A| ≥ 2.

**[C] R1U is refuted.**
- It holds for n ≤ 8, but fails on 26 window sets at n = 9 (cup B = 4, cap B = 3, k = 6).
- There it would force every 2-cap of R to cover a 3-cap of B.
- So case R1 needs the actual R_A, i.e. context, already at the root.

**[P]** Each property closes its own class at the root.

**Neither composes.** [C] At n = 8, take rules of the form "every p-split of A, union every q-split of B", where p and q range over PSL, H_U, R1U, their duals and conjunctions.
- No such rule yields H_U(X) on 14.8k of 24.2k case-R splits.
- No such rule yields ALL4, the conjunction of all four (which holds for every X), on 19.0k of them.

**Why** (`show_hu.py`). R contains caps a+D, with D a (β−2)-cap of R_B and a ∈ R_A inside the core. These caps end inside X's core, so the next nested sibling extends them. Excluding them constrains caps one length shorter, and so on through every length. So B's split must see R_A.

**CR1.** For every admissible one-level lower context Z, B has an own PSL split with cap_Z(R) ≤ β−1.
- [C] It holds on 269M contexts, n ≤ 9.
- [P] It closes every cap-side root.

## 4. Missing step

**The context grows.** At B = B1 << B2, B2 sees R_{B1} inside R_A (two levels). B1 sees a cup context from Bl_{B2}.

**[C] CR2 (two-level version).**
- Holds for n = 5–8 (387M contexts).
- Fails only for a lone 4-cap. That failure disappears when Bl may use the parent's cup budget.

**[C] Real depth-2 nodes (n ≤ 9).**
- A valid order of the two children always exists, but it is not a function of (cup B1, cap B2).
- The rule "B2 first iff cup B1 = α" holds for n ≤ 8 and fails at 164 nodes at n = 9.

**Missing lemma.** PSL in a DS context:
- lower R-points extend caps, and upper Bl-points extend cups;
- the parent's budgets apply;
- only realisable contexts are allowed;
- each node has a rule for which child goes first.

## Proof idea, what was learned, obstacle

**Proof idea.** Tree induction. At cap-tight nodes, take the lower child first and the upper child second, in a cap context of one colour. Cup-tight nodes are the mirror.

**Learned.**
- PSL's entire obstruction is cap extension of R_B by R_A at tight nodes.
- At the root, case R has a positional universal fix (H_U).
- Case R1 needs the context form CR1.

**Obstacle.** The context regrows in cap length, and the order of the children depends on the instance. This is the sibling penalty in one colour.

## Evidence

Code: `psl.c`, `univ.c`, `r1u.c`, `hucomp2.c`, `ua.c`, `cr2.c`, `depth2.c`, `joint.py`, `psl_big.py`. Outputs: `o_*`.

Jobs (prefix 20261003-):
- 130316-{5068e5, e8b3e7}
- 131336-{df39bf, ff82ad, 101300, fb2b01}
- 130638-{031a4d, 5d1195}
- 131002-292d7b
- 131604-fbb54c
- 133358-a34b2e
- 133826-060132
- 134320-63c38c
- 133239-9b405b

Job 132331-ea3c70 is superseded (sampling bug).

## Q13: PSL in a realisable separable context (PSL-sep)

Same tags as above: **[P]** proved by hand, **[C]** computed (diagnostic).

**Set-up** (`sep.py`). Fix a decomposition tree, take k = strong(X) + 1, and simulate the induction.
- At each node w = w1 << w2, choose an order (f, s) of the children.
- Also choose shares b_R and b_Bl of the two strong cross terms cup(χ∩w1) + cap(χ∩w2) ≤ k−2, one for each colour χ.
- The first child f may be **any** split that respects its separable context:
  - lower red and upper blue points already processed count exactly;
  - the unprocessed sibling's points count as worst-case extenders of chains cored in f;
  - chains cored in s are deferred to s.
- Then s is coloured in the exact context: R_s's caps extended by R_f, Bl_s's cups extended by Bl_f, and the remainders of the strong cross terms.
- Check(w) holds iff some order and shares give Check(f), and Check(s | τ) for **every** valid split τ of f.

This is exactly the step "PSL-sep for the children ⇒ PSL-sep for the parent". "Try either order" is logically the same condition, since ∀τ1 ∀τ2 (ok1 ∨ ok2) ⟺ (∀τ1 ok1) ∨ (∀τ2 ok2).

**1. Truth: false on realisable contexts.**
- On arbitrary separable profiles it is false trivially: take one point whose cap and cup profiles are both saturated.
- [C] Realisable contexts produce exactly this, already in the k-free case.
  - n = 5 (idx 17, cup = cap = 3; also at k = 99): the first child [0,4] validly colours both its points red.
  - Point 2 is then squeezed. Red completes the cap {0,2,4}. Blue completes the cup {1,2,3}, where 1 is blue and 3 is a worst-case extender.
- [C] The window analogue, n = 7 (idx 1268, cup 3, cap 4, k = 5): leaf 3 has context 0b 1r 2r 4b 5r 6r.
  - Red makes the R-cup {1,3,6} exceed the strong share cup(R∩w1) ≤ k−2−cap(R_{2}) = 2.
  - Blue completes the Bl-cup {0,3,4}, which has α points.

**2. Closure: not closed.** [C] Results on the canonical tree, with all orders and shares:

| n | instances | window sets that close | classic sets that close |
|---|---|---|---|
| 5 | 62 | 38/38 | 22/24 |
| 6 | 718 | 522/522 | 188/196 |
| 7 (every 4th colouring) | 2,649 | 2,054/2,070 | 557/579 |

- Not just the canonical tree: these colourings fail on **every** decomposition tree:
  - classic: 8 of 8 at n = 6;
  - window: n = 7 idx 1268, 3876, 5368, 8244, 9292 (5 of the 9 failures checked).
- Both orders fail at every failing node.
- The two-sided worst case fails at n = 3 (the 3-cap). There the first child also protects chains cored in the unprocessed sibling.
- Restricting first children to own PSL splits fails more often: 21 at n = 6. Allowing either class: 8 at n = 6.

**3. No induction proof.** The step that fails is the same every time.
- A separable profile records how many red or blue extenders lie beyond each point. It does not record which later point they squeeze.
- So a context-valid split of the first child can saturate both colours' profiles at one point of the second child.
- To exclude this, the first child must satisfy "no point of s is saturated for both colours". That is a joint, positional condition on the sibling's chains, and it leaves the separable class.
- The failure already occurs k-free, where PSL is just the Erdős–Szekeres split. That split's proof is a sweep (R = last points of maximum cups), not a tree induction with contexts.
- **Missing combinatorial step.** A canonical rule for the first child's split that never squeezes a later point. One candidate is a contextual "last points of maximum cups" rule. It needs the full upper context to the left of each point, so it suggests replacing the tree order by a sweep order.

**Evidence.**
- Code: `sep.py`, `sep_trees.py`, `sep_explain.py`, `sep_dbg.py`.
- Output: `o_sep7_stride4.txt`. The n ≤ 6 runs took under a minute and were run directly.
- Job 20261003-140313-2db0e1 (full n = 7 run) was cancelled before it started, because the memory budget was full. The remaining 3/4 of n = 7 is not counted.

## Q14: is there a canonical or sweep rule for PSL?

Same tags as above. **[C]** here means: every decomposable window set with n ≤ 8 (157,806 sets) or n ≤ 9 (3.37M sets), at k = strong + 1. Code: `rule.c` and `q14.py`.

**Classical classes.** The four classical classes of X are:
- Lu, Fu: the last and the first points of α-cups;
- Fp, Lp: the first and the last points of β-caps.

[P] Lu ∩ Fp = ∅ and Fu ∩ Lp = ∅. This is the classical exchange argument.

**1. The classical splits.** [C]
- Each of the four splits R = Lu, R = Fu, Bl = Fp, Bl = Lp is a PSL split in only 50% of sets (n = 8).
- The monochromatic strong (k−1)-set usually sits in the *large* class. For Bl = Fp, the set R = X∖Fp keeps such a set in about 78k sets; its cup part has 4–5 points and its cap part 2–3.
- Bl = Fp itself keeps one in 646 sets. This is the known "long cup among the first points" failure.
- Keeping both classical classes (R ⊇ Lu and Bl ⊇ Fp) is impossible in 1,330 sets at n = 8. Keeping all four is impossible in 4.

**2. Repairs tested, all refuted.**

| rule | result |
|---|---|
| colour(x) = g(α, β, k, own chain data of x) | UNSAT |
| sweep in x-order, colour(x) = g(whole prefix X[0..x], α, β, k) | UNSAT at n ≤ 7, core 7 sets |
| greedy sweeps (blue-first, red-first, classical-first) | fail on ≈1.2% of sets at n = 7 |
| Bl = Fp ∪ (first or last points of the strong (k−1)-sets inside X∖Fp), and the mirror rules | fail on ≈0.5–0.8% |
| two-case rule: Bl ⊇ Fp if Fp is strong-free, else R ⊇ Lu | fails on 160 sets at n = 9, and on a k = 7 sample |

- **Lookup rules on chain data.** "Own chain data" ranges over three families:
  - (cupEnd, capStart): UNSAT at n ≤ 6, core 5 sets;
  - (cupEnd, cupStart, capEnd, capStart): UNSAT at n ≤ 7, core 13;
  - the same plus the largest strong sets with x leftmost, rightmost or inside, and the number of maximum strong sets through x: UNSAT at n ≤ 7, core 11.

  These families cover "first points of max caps that start no long cup" and every lexicographic mix of Fp and Lu.
- **The sweep result is the sharpest.** The classical split *is* such a sweep: x is red iff the longest cup ending at x has α points. PSL has no sweep of any kind.
- **Why the repairs fail.** The added points create an α-cup or a new strong (k−1)-set in Bl.
- **The two-case rule** rested on an n ≤ 8 pattern: Bl ⊇ Fp is impossible exactly when Fp contains a strong (k−1)-set. That pattern fails at n = 9: 80 sets have Fp strong-free and still no extension.

**3. What survives** (conjectural, [C]).
- **(a)** Fp and Lu never both contain a strong (k−1)-set (n ≤ 9).
- **(b)** At least one of the four one-sided classical frames extends to a PSL split: Bl ⊇ Fp, Bl ⊇ Lp, R ⊇ Lu, or R ⊇ Fu.
  - It holds on every window set with n ≤ 9.
  - It holds on 277 near-extremal samples at k = 6, 7. In 8 of these, only Lp or Fu works.
  - The four frames are the images of one frame under reflection and colour duality. So (b) says: *some symmetric image of X keeps all first points of its maximum caps blue.*

No rule is known that picks which frame to use, or how to extend it.

**4. Why no rule.** [C]
- In tight sets (|X| = T; 2,862 at n = 8) there are 16–36 PSL splits, and **no point has a forced colour**. So the colour is not a function of X, and any rule must break ties by a convention.
- No convention of local or causal type works. The forbidden structures of the classical split close at a single point: an α-cup is completed by its last point. The exchange argument then makes a pointwise label (cupEnd, capStart) work.
- A strong (k−1)-set is a cup plus a cap meeting at both ends. Its colouring must be coordinated between two chains. The SAT cores show that the needed information is neither in the point's own chains nor in its past.

**5. Missing step.** A proof would have to take two steps:
- choose one of the four symmetric frames;
- find a hitting set E ⊆ X∖Fp for the strong (k−1)-sets of X∖Fp such that Fp ∪ E has no α-cup and no strong (k−1)-set.

Neither step has a canonical description. The second is a constrained hitting-set problem, and in tight sets it forces |Fp ∪ E| = T(a, u−1, k−1). I have no proof idea for it.

**Evidence.**
- Code: `rule.c`, `q14.py`, `q14_big.py`, `run_q14*.sh`.
- Outputs: `o_rule9.txt`, `o_q14_big.txt`, `o_q14b.txt`.
- Jobs: 20261003-141958-a404cc, 20261003-141828-fe6570, 20261003-142130-2f545f.

**Open follow-up.** Does a sweep that also sees its own suffix chain data (cupStart, capStart; the Fp-type lookahead) become UNSAT at n = 8?
- At n ≤ 7 it is SAT, but uninformative: 12.7k table keys for 8.8k sets.
- The n = 8 run was attempted twice, with no result:
  - job 20261003-142221-c32b04 hit the 2G memory cap;
  - its rerun on a subset was cancelled while still queued, because the shared memory budget was full.
