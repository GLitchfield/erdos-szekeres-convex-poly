# Track A findings: a deterministic exchange rule for `ctx_bound_prefix_suffix_domination`

Run `claude-uniform-mechanism-20260928`, Track A (`claude-code:17de3bb4-…/track-a`), 28 Sept 2026.
(Saved by the coordinator from the subagent's report, with Gavin's approval; the harness blocked the
subagent's own write.)
All numbers are diagnostic: finite abstract contexts, evaluated with the shared evaluator
`harness.research.recursive.evaluator(..., semantics='context-bound-zero-children-v1')`. Nothing is
Lean-certified, except that the coordinator later confirmed the §3.1 counterexample by a Lean `#eval`
(`../certify/`). The journal record is `es journal` findings 1–13 on the node, plus the
coordinator-test entries.

## 0. Summary

**The orientation clause is vacuous (proved).** The node is equivalent to `∀K,d: V_σ(K,d) ≤ M(σ)`, where
`M(σ)` is the best prefix/suffix cut over both orientations and all couplings (§1.2).

**The node survives k = 7.** Tested range: s≤4, e≤2, two levels, at (4,5,7) and (5,6,7). It also holds at
k=5 (s≤5) and at k=6 (s≤4), including the boundary cases (3,5,6), (6,6,6), (4,6,6), (3,6,7) and (4,7,7).
The end-strip strengthening (END) holds except at a = 3 (§2.1).

**No deterministic selector exists in any family tried.**
- The families were: pattern alone; pattern plus end limits; mirror with 56 tie-breaks; membership-side
  strip at the same coupling; a bounded coupling shift; marker-to-an-end.
- The needed |d′−d| reaches 3 at (5,6,7).
- A working (end, side, coupling) depends on part values (§2.3–2.5).

**Lemma split of the mirror strip.** Here Y is the part of the partition that does not contain the
stripped end e (§1.1).
- L2 is SWAP. It is exact on every membership-side strip and is already closed in Lean.
- L1 is MERGE. It had 0 failures in general form (k=5–7) and has a paper proof (§5.2).
- The remaining inequality, PAIR, is false. This holds even as a four-leaf inequality when Y is a single
  run; the failures are low-value corner losses (§2.7).

**The same-partition strip step (STRIP) fails.**
- It fails at (5,5,6) (marker levels) and at (5,6,7), including 8 in-domain partitions.
- It fails at u = k and at a = 3.
- It holds at (4,4,5), (5,5,5), (4,5,6) and (4,5,7) (§2.6).

**Coordinator's test.**
- For every partition tested, some interval tree rooted at a prefix/suffix cut dominates every k-optimal
  partition tree in the k world and both Pascal-reduced worlds at once.
- It does NOT dominate leaf by leaf in (cup, cap) limits.
- It does NOT dominate while also carrying the partition tree's N11 leaves across (§4.5).

**Pascal (step 3).**
- Conjecture P is refuted (Track B, confirmed by the coordinator), so this report does not use a P-based
  framing.
- The per-partition Pascal certificate fails exactly on N11-defective parts (§4.1).
- Extreme-coupling (marker) partitions are not easier to exchange (§4.3).

**Side result.** `ErdosSzekeres.ctx_bound_attained_by_end_cut` appears FALSE. There are 24 WellFormed
multi-run counterexamples at (3,4,5) and 36 at (3,5,6). All of them have bound 1 and best end cut 0.
They were confirmed by an independent literal transcription of the Lean definitions (§3.1).

## 1. Setting and statements

### 1.1 Notation

Child positions are p₀ < … < p₍ₙ₋₁₎. K is a nonempty proper subset of them, and the coupling d lies in
[1, k−2].

**Lower frame.** A lower part sees sibling maximum d, and an upper part sees k−1−d.

**Partition value.**
`V_σ(K,d) := bound(σ.part K lower d) + bound(σ.part Kᶜ upper (k−1−d))`.

**Best prefix/suffix cut.**
`M(σ) := max{V_σ(I,d′) : I = take j or drop j, 0<j<n, 1≤d′≤k−2}`.

**End strip.** `W(e,s,t)` is the cut that isolates an end e on side s at coupling t:
- `W(e,lower,t) = V_σ({e},t)`;
- `W(e,upper,t) = V_σ(pos∖e,t)`.

**Parts relative to an end.** X is the part containing e, and Y is the other part.

**Classes of contexts and partitions.**
- Extreme context: some maximum is 1 or k−2.
- Extreme coupling: d ∈ {1, k−2}.
- In-domain: neither.

### 1.2 Orientation reduction (proved)

The node's second conjunct is `V_σ(Kᶜ,d) ≤ V_σ(Iᶜ,d′)`, and taking complements permutes the
prefix/suffix cuts. Hence the node is equivalent to `∀ K, d: V_σ(K,d) ≤ M(σ)`.

`M(σ) = bound σ` except on single-run contexts of bound 1, where every partition value is 0. There are 36
such contexts at (4,5,6) and 36 at (4,5,7).

### 1.3 Statements tested

**END (end-strip strengthening).** `V_σ(K,d) ≤ max_{e,s,t} W(e,s,t)`.

**STRIP (same-partition strip step).** There exist e, s₁, t, d₂ with
`V_σ(K,d) ≤ bound(σ.part [e] s₁ t) + V_R(K∖e, d₂)`, where `R = σ.part (pos∖e) s₁′ t`.
Together with `ctx_bound_cut_le` and `ctx_bound_additive_prefix_suffix`, STRIP implies the node by
induction on n.

**Deterministic selectors.**
- `memd`: e = p₀, on e's membership side, t = d.
- `MIR`: e = the first end whose X-part bound is attained by a strip at e; (s₁, t) = the first optimal
  X-strip, ordered by membership side, then |t−d|, then t.
- `MIR2`: MIR with both sides.
- 56 end-choice × tie-break variants.
- Coupling-free end/side choices.
- "Marker to an end".

**Lemma split along a mirror strip.** Tree 1 cuts the partition first and then strips e inside X; tree 2
strips e at the root and then cuts the partition in R.

| symbol | meaning |
|---|---|
| T1 | base of e in X-part |
| T2 | bound of (X-part minus e) |
| T3 | bound of Y-part |
| U1 | base of e at the root |
| U2, U3 | the same partition inside R |

The lemmas are L1: `T1≤U1`, L2: `T2=U2`, L3: `T3≤U3`, and PAIR: `T1+T3≤U1+U3`.

**General level lemmas.**
- SWAP: exchange adjacent levels with different sides, together with their maxima. Claim: bound is
  unchanged.
- MERGE: relabel an adjacent same-side level l+1 as l, shift the higher levels down, and give the merged
  level the inner, outer, max or min of the two maxima. Claim: bound does not decrease.

## 2. Evidence

The contexts come from `scripts/decomposable_additivity_test.contexts` with consecutive occupied levels.
Scripts are in `exchange/` and data in `exchange/tables/`. Job ids are es job ids.

### 2.1 The node and END

Both orientations are counted.

| case | range | partitions | node fails | END fails | same d′=d | shift needed 1/2/3 | job |
|---|---|---|---|---|---|---|---|
| (4,4,5) | s≤5 e≤2 l2 | 288,408 | 0 | 0 | 283,604 | 4,804/0/0 | 20260928-141657-5cf812 |
| (4,5,6) | s≤4 | 155,472 | 0 | 0 | 147,852 | 7,600/20/0 | 20260928-141657-b22ec0 |
| (5,5,6) | s≤4 | 155,472 | 0 | 0 | 141,648 | 13,224/600/0 | 20260928-142210-b58654 |
| (4,6,6) | s≤4 | 155,472 | 0 | 0 | 145,708 | 9,620/144/0 | 20260928-150933-c1c734 |
| (6,6,6) | s≤4 | 155,472 | 0 | 0 | 140,488 | 13,168/1,816/0 | 20260928-150933-c1c734 |
| (3,5,6) | s≤4 | 155,472 | 0 | **360** | 154,540 | 932/0/0 | 20260928-150933-c1c734 |
| (4,5,7) | s≤4 | 298,900 | 0 | 0 | 284,808 | 14,052/40/0 | 20260928-143303-fba147 |
| (5,6,7) | s≤4 | 298,900 | 0 | 0 | 265,108 | 28,428/5,360/**4** | 20260928-143732-e4c9b8 |
| (3,6,7) | s≤3 | 42,820 | 0 | 0 | 42,256 | 564/0/0 | 20260928-150933-c1c734 |
| (4,7,7) | s≤3 | 42,820 | 0 | 0 | 38,432 | 4,222/166/0 | 20260928-150933-c1c734 |

Additional cases, lower orientation only, with n ≥ 3:
- (4,4,5), (4,5,5), (5,5,5): 33,654 each, with node fails 0 and END fails 0.
- (3,4,5): 33,654, with node fails 0 and END fails **80** (job 20260928-144216-d95c83).

**The shift-3 cases at (5,6,7).** These are `S1LSS1LS` with maxima (1). The partition has an interior
lower marker at d=5. It is dominated only at d′ ∈ {1,2}, by making an END vertex the marker on the other
side.

### 2.2 Deterministic selectors

Counts are failures of `W ≥ V`, lower orientation.

| case | partitions | memd | memd both ends | MIR | MIR2 | MIR2 both ends | ∃mirror | ∃mirror side-free | ∃END |
|---|---|---|---|---|---|---|---|---|---|
| (4,4,5) | 33,654 | 2,342 | 1,412 | 1,700 | 566 | 328 | 8 | 0 | 0 |
| (4,5,5) | 33,654 | 2,684 | 1,970 | 1,842 | 888 | 648 | 18 | 10 | 0 |
| (5,5,5) | 33,654 | 3,106 | 2,616 | 2,008 | 1,258 | 1,016 | 24 | 24 | 0 |
| (3,4,5) | 33,654 | 1,007 | 320 | 600 | 223 | 114 | 88 | 80 | 80 |
| (4,5,6) | 77,736 | 8,176 | 5,570 | 5,047 | 2,376 | 1,610 | 38 | 4 | 0 |
| (5,5,6) | 77,736 | 10,058 | 8,444 | 5,070 | 3,166 | 2,412 | 76 | 72 | 0 |
| (4,6,6) | 77,736 | 8,443 | 6,200 | 5,291 | 2,948 | 2,270 | 72 | 32 | 0 |
| (4,5,7) | 149,450 | 17,949 | 11,194 | 10,486 | 4,637 | 2,916 | 130 | 12 | 0 |
| (5,6,7) | 149,450 | 23,910 | 20,112 | 9,643 | 6,203 | 4,816 | 172 | 150 | 0 |

The best of 56 orders fails 3,861 (MIR) and 2,360 (MIR2) at (4,5,6). Scripts: `rule_eval.py`, output
`rules-*.json`.

**Coupling left free, end and side chosen.** Columns: first end on its membership side / first end either
side / attained end either side / every attained end either side.

| case | first end, membership side | first end, either side | attained end, either side | every attained end, either side |
|---|---|---|---|---|
| (4,4,5) | 598 | 120 | 96 | 0 |
| (5,5,5) | 28 | 0 | 0 | 0 |
| (4,5,6) | 2,239 | 233 | 180 | 4 |
| (5,5,6) | 1,132 | 218 | 202 | 44 |
| (4,5,7) | 6,633 | 759 | 576 | 12 |
| (5,6,7) | 3,336 | 459 | 406 | 92 |

Single-run σ never fail once d′ is free, because there the node is single-run additivity via the window
split. Script: `end_side_selectors.py`.

### 2.3 Feature consistency at (4,5,6)

The test asks whether the working end-strip choice is a function of the feature. A class is inconsistent
when the dominating sets of its members have empty intersection.

| feature | classes | inconsistent classes |
|---|---|---|
| (pattern, d, runs) | 256 | 110 |
| + end-run limits | 4,232 | 22 |
| + full run-limit matrices | 8,840 | 0 (a table, not a rule) |
| (word, pattern, d) | 6,024 | 80 |

Script: `feature_consistency.py`.

### 2.4 STRIP

| case | partitions | fails (d₂ free) | fails (d₂ = d) | where the failures are |
|---|---|---|---|---|
| (4,4,5) | 33,654 | 0 | 0 | — |
| (5,5,5) | 33,654 | 0 | 0 | — |
| (4,5,6) | 77,736 | 0 | 0 | — |
| (4,5,7) | 149,450 | 0 | 0 | — |
| (4,5,5) (u=k) | 33,654 | 8 | 16 | `S2US1USS`, `SS1US2US`, maxima (1,1) |
| (4,6,6) (u=k) | 77,736 | 40 | 72 | the same words, maxima in {1,2}², including in-domain (2,2) |
| (3,4,5) (a=3) | 33,654 | 80 | 92 | the bound-1 contexts of §3.1 |
| (5,5,6) | 77,736 | 48 | 112 | 12 contexts `S1L2USSS`-family, maxima (1,1) |
| (5,6,7) | 149,450 | 128 | 264 | the (1,1) family, plus 8 in-domain: `S2US1USS`/`SS1US2US` with maxima (2,2), e.g. pattern 0010, d=3, V=B=18 |

**Relation to an existing refutation.** The (5,5,6) family is the certified
`ctx_same_side_strip_fixed_block_counterexample`. It is generalized here to every end, side and coupling.

**No deterministic sub-rule, even where STRIP holds.** At (4,5,6):
- fixing the end fails 1,697 times;
- using the mirror side fails 774 times;
- using the membership side fails 1,274 times;
- t ∈ {d−1, d, d+1} fails 94 times.

Scripts: `strip_step.py`, `strip_step_rules.py`.

### 2.5 Lemma split

The rows are the membership-side mirror strip at the first attained end.

| case | strips | L1 fails | L2 fails / L2 not an equality | L3 fails | PAIR fails |
|---|---|---|---|---|---|
| (4,4,5) | 30,054 | 0 | 0 / 0 | 4,160 | 3,138 |
| (4,5,6) | 68,461 | 0 | 0 / 0 | 12,296 | 7,195 |
| (5,5,6) | 68,850 | 0 | 0 / 0 | 12,990 | 7,094 |
| (4,5,7) | 128,998 | 0 | 0 / 0 | 24,497 | 13,449 |

**The membership-side strip step is equivalent to PAIR.** L2 is an exact equality, so only PAIR remains.

**PAIR with Y a single run (a four-leaf threshold inequality).** No optimal coupling works in:
- 3,090 of 99,180 instances at (4,5,6);
- 5,902 of 187,356 instances at (4,5,7).

The failures are corner losses. Each entry is (T3 → U3, gain U1 − T1): count at (4,5,6) / count at (4,5,7).

| loss pattern | (4,5,6) | (4,5,7) |
|---|---|---|
| (1→0, 0) | 2,896 | 5,270 |
| (2→0, 0) | 146 | 476 |
| (2→1, 0) | 40 | 108 |
| (3→1, 1) | 8 | 48 |

**Termwise decompositions.** Even with every coupling offset allowed, there is no termwise decomposition for
1,310 partitions at (4,5,6) and 3,378 at (4,5,7). Scripts: `analyze_strips.py`, `pair_single_run.py`,
`analyze_offsets.py`.

### 2.6 General SWAP / MERGE

Job 20260928-145355-1256e6; outputs in `lemmas/`.

| range | contexts | SWAP pairs, fails | MERGE pairs, fails (inner/outer/max/min) |
|---|---|---|---|
| (4,4,5) s≤3 e≤3 l3 | 46,512 | 42,696, 0 | 42,696, 0/0/0/0 |
| (4,5,6) s≤3 e≤3 l3 | 105,728 | 98,944, 0 | 98,944, 0/0/0/0 |
| (5,5,6) s≤3 e≤3 l3 | 105,728 | 98,944, 0 | 98,944, 0/0/0/0 |
| (4,5,7) s≤3 e≤3 l3 | 201,200 | 190,600, 0 | 190,600, 0/0/0/0 |
| (5,6,7) s≤3 e≤3 l3 | 201,200 | 190,600, 0 | 190,600, 0/0/0/0 |
| (4,5,6) s≤4 l2 | 3,968 | 1,984, 0 | 1,984, 0/0/0/0 |
| (4,5,7) s≤4 l2 | 6,200 | 3,100, 0 | 3,100, 0/0/0/0 |

Swapping two SAME-side levels changes the bound in 40–78% of cases, so the order of same-side levels
matters.

## 3. Failures and counterexamples

### 3.1 `ctx_bound_attained_by_end_cut` is false at a = 3

The example is (3,4,5) with word `1L S S 2U S S` and maxima (3,1). It is WellFormed with 2 runs.
- bound = 1.
- Every end cut (either end, either side, d = 1..3) is worth 0.
- The bound is attained only by the prefix {1,2} (the run boundary) and by interior singletons.

**Scope.** There are 24 such multi-run contexts at (3,4,5), s≤4. The words are `1LSS2USS`, `2LSS1USS`,
`S1LS2USS`, `S2LS1USS`, `SS1L2USS`, `SS1U2LSS`, `SS2L1USS`, `SS2U1LSS`, `SS1US2LS`, `SS2US1LS`, `SS1USS2L`,
`SS2USS1L`, each with two maxima pairs. There are 36 more at (3,5,6), where the lower-level maximum is 4.

**Verification.**
- All 24 at (3,4,5), and two at (3,5,6), were re-checked with `exchange/lean_literal.py`, an independent
  literal Python transcription of `DecomposableContext.lean` and `decomposableThreshold`.
- The shared evaluator equals the literal transcription on all 1,292 (3,4,5) s≤3 contexts. No end-cut
  failures occur at s≤3.
- A Lean `#eval` would certify the counterexample. (The coordinator has since done this: job
  20260928-153807-8b8ad8, `../certify/`.)
- The node's falsifier only runs a ≥ 4.
- List: `verify/endcut-cex-345-s4e2l2.txt`.

This does NOT refute `ctx_bound_prefix_suffix_domination`.

### 3.2 Other failures

- STRIP and PAIR: see §2.4 and §2.5.
- Every deterministic selector: see §2.2.
- END at a = 3: see §2.1.

## 4. Relation to Pascal (step 3)

### 4.1 Certificate and N11 defect

Conjecture P is refuted in both directions (Track B; confirmed by the coordinator, e.g. (5,5,6)
`1L2US1L2US` (2,2) gives 5 vs 3+3). The certificate below is therefore descriptive only.

**The per-partition certificate.** `V ≤ Vc+Vu ≤ Bc+Bu ≤ B`. It needs three things:
- descent on both parts;
- additivity at k−1;
- ascent on σ.

**Results, s≤4, e≤2, two levels.**

| case | non-extreme contexts with P exact | in-domain partitions certified |
|---|---|---|
| (4,5,6) | 1,167/1,167 | 6,904/10,484 |
| (5,5,6) | 1,167/1,167 | 8,524/10,484 |
| (4,5,7) | 2,493/2,493 | 25,742/33,654 |
| (5,6,7) | 2,493/2,493 | 30,648/33,654 |

In this range, ascent and k−1 additivity never fail in-domain. Ascent does fail at larger e, per the
coordinator's counterexamples.

**The shortfall is part descent.** It always overshoots by exactly 1. The failing part types
(F; Fcap, Fcup) at (4,5,6) are:
- (1;0,0): 1,768
- (2;0,1): 1,028
- (2;1,0): 944
- (3;1,1): 168

This is the N11 defect.

Jobs: 20260928-142433-6f04df and 20260928-144800-49dde5. Scripts: `pascal_route.py`,
`pascal_route_failures.py`.

### 4.2 Why extreme couplings are not simpler

At d ∈ {1, k−2}, the marker part is always worth 0 or 1. Yet the dominating cut usually needs a
non-extreme coupling.

Failures per case, in the order (4,4,5)s5 / (4,5,6) / (5,5,6) / (4,5,7) / (5,6,7):
- "Marker to an end": 472 / 1,504 / 2,344 / 2,876 / 5,754.
- Any extreme-coupling cut: 328 / 1,394 / 2,332 / 2,658 / 5,720.

Example: at (4,5,6), `SSS` pattern 010 at d=k−2 is worth 8, while every extreme cut is worth ≤ 7.
MIR also fails more often on extreme couplings (11.7%) than in-domain (5.0%). Script: `marker_rule.py`.

### 4.3 Complementarity (an observation only)

**Coverage.** "Certificate OR STRIP (d₂ free)" covers every partition at (4,5,6), (5,5,6), (4,5,7) and
(5,6,7). In each of these, every STRIP failure is certified. Script: `residual_rules.py`.

**Where it fails.** It fails at the boundary:
- u = k: 2 at (4,5,5) and 8 at (4,6,6);
- a = 3: 80 at (3,4,5).

The certificate itself is not a valid general statement, since P is refuted.

### 4.4 Coordinator's leaf test

Job 20260928-152053-83fb41. Scripts: `leaf_domination.py`, `leaf_domination_n11.py`; outputs in
`leafdom/`.

**Setup.**
- τ_P is a k-optimal partition tree.
- τ_I is an interval tree rooted at a prefix/suffix cut (PS) or at an end strip (END).
- Tree values are (vk, vc, vu), using Track B's leaf convention.

**All three worlds at once.** Some PS-rooted τ_I dominates EVERY k-optimal τ_P:

| case | partitions | failures |
|---|---|---|
| (4,5,6) s≤4 | 77,736 | 0 |
| (5,5,6) s≤4 | 77,736 | 0 |
| (4,5,7) s≤3 | 21,410 | 0 |
| (5,6,7) s≤3 | 21,410 | 0 |

With END roots, 80 fail at (4,5,6). These are the `1LSS2USS` family with a k−2 maximum: τ_P = (1,1,0),
while the best END tree is (1,0,0).

**Leaf by leaf in (cup, cap) limits: FAILS.**
- When every k-optimal τ_P must be dominated: 25,534 / 24,948 / 8,384 / 7,560 failures.
- Even ignoring zero-limit leaves: 5,056 / 7,628 / 1,840 / 2,830.
- Leaf counts differ. For example, the root `SSS` sandwich 010 has 3 leaves (2,3), (3,2), (4,2), but a
  prefix/suffix tree of a single run has 2.

**(vc, vu, N11) simultaneously: FAILS** at s≤3.
- (4,5,6): 423 partitions where no k-optimal τ_P is dominated; 1,314 where some is not.
- (5,5,6): 222 and 1,092.
- Example: `1LSSS` with maxima (3), pattern 010, d=1. Here τ_P = (1,0,0,N11=1), while the best PS tree is
  (3,2,1,0).
- The per-tree identity vk = vc + vu + N11 held on every tree evaluated.

## 5. Proof status

### 5.1 Orientation reduction

Proved in §1.2.

### 5.2 MERGE (paper proof; the strongest variant, merged maximum = max(m_l, m_{l+1}))

**Step 1: nothing about the children changes.** childPositions, numRuns and blocks are unchanged.

**Step 2: extensions do not grow.** Take a merged sublist of levels on side s. It lifts to a strictly
increasing σ-sublist: the merged level goes to l or l+1, according to which level the greedy-chosen letter
belongs to. That letter is the rightmost letter of the union left of the current end, so it is also the
rightmost letter of its own level. The σ-walk therefore visits the same letters. Hence `leftExt` and
`rightExt` do not increase, for every `top`.

**Step 3: joins do not grow.**
- The merged-N term is `ext_{<l} + max(m_l, m_{l+1})`. It is at most the maximum of the σ-terms at l and
  at l+1, because `ext_{<l+1} ≥ ext_{<l}`.
- Higher N terms are handled by Step 2.

**Step 4: limits and base do not decrease.** The limits do not decrease. Base is monotone in the limits:
`decomposableThreshold` is monotone, and T(3,3,k) = 2 ≥ 1.

**Step 5: induction.** `part` commutes with merging, so induction on fuel finishes the proof.

**Corollaries.**
- The other three variants follow by `ctx_bound_antitone`.
- L1 is a corollary.
- MERGE also gives T3 ≥ U3, which is exactly why L3 fails.
- `es search` found no existing equivalent. The closest is `ctx_erase_level_bound_mono`, which is
  different.

### 5.3 SWAP

Closed as `ctx_bound_opposite_level_swap` and `ctx_bound_opposite_removals_commute`.

### 5.4 Refuted

- Every deterministic selector family tried.
- PAIR.
- STRIP.
- END and `ctx_bound_attained_by_end_cut` at a = 3.
- Leaf-by-leaf limit domination.
- (vc, vu, N11) domination.

### 5.5 Surviving (evidence only)

- The node up to k = 7.
- END for a ≥ 4.
- STRIP at (4,4,5), (5,5,5), (4,5,6) and (4,5,7).
- Three-world domination by PS-rooted trees.

No proof is known for any of these.

## 6. Recommendation

1. **Don't register a deterministic exchange rule.** None survives k = 6. The needed coupling shift is
   unbounded in k, and the choice depends on part values.
2. **`ctx_bound_attained_by_end_cut`.**
   - Certify `1L S S 2U S S` (3,1) at (3,4,5) by a Lean `#eval`.
   - Then refute the node or restate it with `4 ≤ a`, via `es node restate`.
   - Add a = 3 to its falsifier.
   - Re-check its consumer `ctx_bound_two_run_boundary_domination` at a = 3.
3. **Register MERGE as a formalization target.** It is general, true on every test, and has a paper
   proof. Any rotation or exchange argument needs it alongside SWAP.
4. **Attack the low-value corner directly.** It is the common obstruction, appearing as:
   - the N11/(1,1)-leaf defect of Pascal descent;
   - the 1→0 PAIR losses;
   - the a = 3 END failures;
   - the fact that three-world domination holds but N11 cannot be carried across.

   The positive lead is §4.4: a prefix/suffix-rooted interval tree dominating in all three worlds exists
   for every partition tested. A k-uniform proof would need a lemma that absorbs N11(τ_P) into
   vc + vu slack, e.g. "each (1,1) leaf of τ_P costs at most one unit of reduced-world slack of τ_I".
   This is untested.
5. **Decision gate.** No Track A conjecture with a credible proof path survived k = 7.

## 7. Files

Everything is under `runs/claude-uniform-mechanism-20260928/exchange/`.

**Producers.**
- `dump_part_tables.py`
- `dump_reduced_tables.py`
- `strip_dump.py`
- `lemma_tests.py`
- `leaf_domination.py`, `leaf_domination_n11.py`
- Shard runners: `run_shards.sh`, `run_batch.sh`

**Analyses.**
- `explore_rules.py`, `explore_ends.py`
- `feature_consistency.py`
- `rule_eval.py`, `end_side_selectors.py`
- `strip_step.py`, `strip_step_rules.py`
- `analyze_strips.py`, `analyze_offsets.py`, `pair_single_run.py`
- `pascal_route.py`, `pascal_route_failures.py`, `residual_rules.py`
- `marker_rule.py`
- `lemma_summary.py`, `leafdom_summary.py`
- Shared helper: `rulelib.py`

**Verification.**
- `lean_literal.py`
- `verify_endcut_cex.py`
- `verify/`

**Outputs.**
- `*.json` next to the scripts
- `tables/`, `lemmas/`, `leafdom/`

**Ad hoc code review.** All code is new and none of it has been promoted. `lean_literal.py` is a candidate
for promotion to `harness/research/` as a slow reference oracle.
