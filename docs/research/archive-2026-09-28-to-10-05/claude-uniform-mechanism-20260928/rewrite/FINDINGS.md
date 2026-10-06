# Track C findings: equivariant rewriting from partition trees to interval trees

Restored 29 Sept 2026 (Gavin approved) from the Track C subagent's hand-back to the coordinator
of run `claude-uniform-mechanism-20260928` (transcript
`~/.claude/projects/-home-gavin-git-erdos-szekeres-convex-poly/17de3bb4-f81b-48a5-b73d-2d86b781322f.jsonl`,
line 2507; subagent transcript `.../17de3bb4-f81b-48a5-b73d-2d86b781322f/subagents/agent-a8a447b2f3de25235.jsonl`).
The text below is verbatim except for removing the hand-back indentation. On 28 Sept the harness
blocked the subagent from writing this file itself. All findings are diagnostic, not Lean-certified.

---

## Summary

**The brief's induction route is refuted.** This is diagnostic evidence plus short paper arguments; nothing is Lean-certified. The route: an equivariant R from partition trees to interval trees that never decreases N11, closed by Track B's Theorem 4.

1. **Condition 2 cannot hold for any R, even at world k itself.**
   - Counterexample: (4,4,5), σ = `1LS1LSSS`, maxima (2). The context is non-extreme and multi-run.
   - The root partition is K = {1st, 3rd child vertex} upper, d = 2 (in-domain). Its tree t is k-optimal: value 3 = bound σ.
   - t has N11 = 3. The maximum N11 over all Lean interval trees of σ is 2, and still 2 when prefix/suffix cuts are allowed at every single-run node (the GIT class).
2. **The corrected strong forms also fail.**
   - The δ form: the Möbius defect, equal to N11 at Theorem-4-valid worlds.
   - The minimal route form: δ at valid worlds, values at the boundary endpoints.
   - Both fail for every target class, on single-run and multi-run contexts. The failures are in the bulk: non-extreme contexts, in-domain couplings, k = 5–7. They are not confined to coupling 0, a = 3 or u = k.
3. **Structural obstruction (paper argument).**
   - Theorem 4 needs a, u ≤ k−1, and the boundary {a = k} ∪ {u = k} is absorbing under both reductions.
   - `decomposableStateUpper_all` needs a = u = k, which lies on that boundary, so no Theorem-4 k-induction can reach it.
   - The tree identity has positive defects (+1, +2, +4) at boundary worlds.

**Surviving: conjecture W**, the weak necessary condition. One Lean interval tree dominates t's value in every Pascal world at once. It had 0 failures on every range tested:
- k = 5, s ≤ 4, all σ;
- k = 6, s ≤ 3, six cases;
- k = 6, s ≤ 4 at (4,5,6) and (5,5,6);
- Track B's misaligned families with 2 inserted vertices, at (5,5,6) and (6,6,7).

W is stronger than additivity and has no known proof mechanism.

**Question 2 is moot.** No rewriting, value-independent or not, can satisfy condition 2.

**Recommendation:** do not register an R, N11 or Theorem-4 node; keep the §5 fixtures. The harness blocked the FINDINGS.md write, so the full text is below. Everything is in `runs/claude-uniform-mechanism-20260928/rewrite/`, and journal findings 1–9 plus a final entry are logged.

---

# Track C findings: an equivariant rewriting from partition trees to interval trees

Run `claude-uniform-mechanism-20260928`, Track C (`claude-code:17de3bb4-…/track-c`), 28 Sept 2026.

Everything computational here is **diagnostic**. It comes from exhaustive or frontier computations over bounded abstract contexts, with semantics `context-bound-zero-children-v1` and the Lean `base` convention (a (1,1) leaf is worth 1). It is **not Lean-certified** and earns no theorem credit. "Paper argument" means a short proof written here and not checked in Lean. Journal: `es journal`, Track C findings 1–9 plus a final entry.

## 0. Verdict

**The brief's route is refuted.**

1. **Condition 2 fails.** N11 monotonicity, `N11(R(t)) ≥ N11(t)`, fails already at the top world k, for every map R (value-independent or not) into interval trees. It fails even when the targets may use prefix/suffix cuts at every single-run node (GIT).
   - The counterexample is k-optimal and multi-run.
   - Its context is non-extreme, and its coupling is in-domain (§5.3).
2. **The corrected strong forms fail too.**
   - The δ form: N11 generalized to the Pascal defect δ, in every world.
   - The minimal route form: δ at Theorem-4-valid worlds, values at the boundary endpoints.
   - Both fail on single-run and multi-run contexts, in the bulk.
3. **There is a structural obstruction independent of R (§3.3).**
   - Theorem 4 needs a, u ≤ k−1.
   - The boundary {a = k} ∪ {u = k} is absorbing under both reductions.
   - The chain needs a = u = k, which lies on that boundary, where Theorem 4 never applies.
   - So a Pascal-in-k induction can at best move interior cases onto the boundary.

**The necessary condition survives in its weak form W (§2).** One interval tree dominates the partition tree's values in every Pascal world at once. There were 0 failures on every range tested. W strictly strengthens additivity. No proof mechanism is known, and Theorem 4 cannot supply one.

## 1. Setting

### 1.1 Worlds

**Reductions commute.** capRed `(a−1, min(u,k−1), k−1)` and cupRed `(min(a,k−1), u−1, k−1)` commute. Lower maxima decrease by 1 per cap step and upper maxima by 1 per cup step. So a world is determined by `w = (i, j)` (#cap, #cup).

**Liveness.** A world is dead when a' ≤ 1 or u' ≤ 1, since then every leaf is worth 0.

**Maxima.**
- Maxima are clamped at 0. A maximum ≤ 0 is a ghost level: its join term never exceeds the chain extension (Track B, proof of Lemma 1), so clamping is exact.
- The image of a node's context is `(word, reduce_w(maxima))`.
- Tree couplings are maxima of new levels, so a lower coupling d becomes d − i and an upper coupling c becomes c − j (Track B, Lemma 2).

### 1.2 Tree classes

| class | definition |
|---|---|
| **LEAN** | Lean interval trees (`σ.blocks`, d ∈ [1,k−2]). A single run is a leaf. `bound` = max over LEAN. |
| **LEANPS** | LEAN, plus a prefix/suffix root cut when σ is a single run. Value ≤ bound by `ctx_bound_additive_prefix_suffix` (closed). |
| **GIT** | Every single-run node may also be prefix/suffix-cut, recursively. Value ≤ bound by the same closed lemma, inductively. |
| **RPT** (source) | Root cut by ANY nonempty proper K (both orientations, d ∈ [1,k−2]); subtrees LEAN. Closed under the reductions; exactly the class that `ctx_bound_additive` needs. |

For multi-run σ, a root K that is an interval or co-interval gives a LEAN tree, so only "other" K are informative.

### 1.3 Vectors

| name | definition |
|---|---|
| `VAL(t)` | `(val(t↓w))_w` over live worlds |
| `N11` | per-world count of (1,1) leaves |
| `δ_w(t)` | `val_w − val_{w+cap} − val_{w+cup}`, with dead or absent worlds counting 0 |

**Möbius inversion.** `val_w = Σ_{w'≥w} #paths(w→w')·δ_{w'}`.

**Relation to N11.** At a Theorem-4-valid world (k' ≥ 3, a', u' ≤ k'−1), δ = N11. This is Theorem 4, re-checked on every frontier point of 900 contexts: 0 violations.

**Route worlds.** These are reachable from (0,0) through valid worlds; the endpoint may be invalid.

**Frontiers.** Tree vectors are kept as Pareto frontiers, so existence questions are answered exactly.
- The fast leaf evaluator matches `limits_from_signature(lean=True)` on 8.67M checks, with 0 mismatches.
- The LEAN frontier's (0,0) component equals the shared evaluator's bound.

## 2. Statements and verdicts

Throughout, `t ∈ RPT(σ)` and `τ ∈ C`.

| # | statement | verdict |
|---|---|---|
| **W** (weak, necessary) | `∃τ, ∀ live w: val(τ↓w) ≥ val(t↓w)` | **0 failures** everywhere (§4.1); C = LEAN suffices |
| **S-N11** (brief's strong form) | W and `∀w: N11(τ↓w) ≥ N11(t↓w)` | **refuted** for every C at s ≤ 3 |
| **S-δ** (what equivariant R needs with no base cases) | `∀w: δ_w(τ) ≥ δ_w(t)` | **refuted** for every C: single-run from s = 3, multi-run from s = 4 |
| **S-route** (boundary worlds as base cases) | δ at valid route worlds, VAL at invalid endpoints | **refuted** for every C including GIT: multi-run, non-extreme, in-domain |
| **N11@k** | `N11(R(t)) ≥ N11(t)` at world k | **impossible for any R** (§5.3) |

W is equivalent to the statement that at each world, t's δ excess is paid by τ's reduced-world slack. It has no known inductive proof.

## 3. Structural results (paper arguments)

### 3.1 Commutation

- **Parameters.** cap∘cup gives `(min(a−1,k−2), min(u,k−1)−1, k−2)`, which equals cup∘cap `(min(a,k−1)−1, min(u−1,k−2), k−2)`.
- **Maxima.** The reductions act on disjoint sides and commute with `max(0,·)`.

### 3.2 Valid region

Let a, u ≤ k−1. Then world (i,j) is valid if and only if `i ≤ k−1−u` and `j ≤ k−1−a` (with k' ≥ 3). This was checked exhaustively for k ≤ 15 (2,028 steps, 0 violations).

| start | valid worlds |
|---|---|
| (4,4,5), (5,5,6) | only (0,0) |
| (4,5,6) | (0,0), (0,1) |
| (4,4,6), (5,5,7), (6,6,8) | (0,0), (0,1), (1,0), (1,1) |

### 3.3 The boundary is absorbing and contains the target

**Claim.** If a = k, then capRed gives a−1 = k' and cupRed gives min(a, k−1) = k'. The mirror statement holds for u.

**Consequences.**
- `decomposableStateUpper_all` needs all a, u ≤ k, and `Ctx.part` keeps (a,u,k).
- The case a = u = k (no convex k-gon, hence no k-cap and no k-cup) has route {(0,0)}, which is invalid.
- So **no Theorem-4 k-induction proves `ctx_bound_additive` at a = u = k**.

**The identity fails at boundary worlds, with positive defect** (`boundary-identity.txt`):

| case | defect values seen |
|---|---|
| (6,6,6) | 0, +1, +2, +4 |
| (5,5,5) | 0, +1, +2 |

**Minimal example: the leaf `1LSS`, maxima (1), at (4,4,4).**
- Limits (3,2); value 3.
- Both reduced worlds are (3,3,3), with limits (2,1), each worth 1.
- 3 ≠ 1 + 1 + 0.
- The chain term is clipped by k'−1.

### 3.4 Single runs

**W is additivity in every world.** A single run's only LEAN tree is its leaf. So W on single runs is exactly single-run additivity in every reduced world.

**Why the strong forms fail.** The leaf's δ mass sits only at deep worlds. A partition puts δ mass at shallow worlds, even at far lower value (§5.1). So no R into LEAN, LEANPS or GIT satisfies S-N11, S-δ or S-route on single runs.

**Multi-run contexts do not escape.** Multi-run σ are closed under the reductions (target `ctx_bound_additive_multi_run`), but they fail too (§4.3, §5.3).

## 4. Evidence

"fail" means the number of root cuts `(K,o,d)`, both orientations, that have some undominated t; "ctx" means the number of contexts with a failure. The source is `contexts(s,e,L,k)`, with e ≤ 2, two levels and maxima in [1, k−2] unless stated. Every job peaked at ≤ 1.31 GiB.

### 4.1 Weak form W (VAL, every live world): 0 failures in every row

| case | range | σ | contexts | root cuts | classes C | source |
|---|---|---|---|---|---|---|
| (4,4,5) | s≤3 | all | 1,292 | 34,824 | LEAN, LEANPS, GIT | interactive `scratch/t445s3b.json` |
| (4,4,5) | s≤4 | all, all K | 2,493 | 135,708 | all 3 | job 20260928-205607-8229f0 (this case finished before the cancel), `q1/val-s4-445.json` |
| (4,5,6),(5,5,6),(4,4,6),(3,5,6),(4,6,6),(6,6,6) | s≤3 | all | 2,234 each | 80,320 each | all 3 | job 20260928-205607-103126, `q1/val-s3-*.json` |
| (5,5,6) | s≤4 | single-run, all K | 1,275 | 74,800 | LEAN (the leaf) | job 20260928-211844-9783b7, `q1w/` |
| (4,5,6) | s≤4 | single-run, all K | 1,275 | 74,800 | LEAN | same job |
| (5,5,6) | s≤4 | multi-run, other K | 3,040 | 26,496 | all 3 | same job |
| (4,5,6) | s≤4 | multi-run, other K | 3,040 | 26,496 | all 3 | same job |
| (4,4,6),(4,5,6) | s≤4 e≤1 L1 | multi-run, other K | 48 | 384 | all 3 | interactive |
| (5,5,6) | families `1L2US1L2US`, `S1L2US` (Track B misalignment), +2 child vertices | multi-run, other K | 336 | 5,376 | all 3 | job 20260928-213138-fb14ed, `q1f/fam-val-556.json` |
| (6,6,7) | same families, +2 child vertices | multi-run, other K | 525 | 10,500 | all 3 | same job, `q1f/fam-val-667.json` |
| (5,5,6),(6,6,7) | same families, +1 child vertex | all | 80 / 200 | 3,840 / 12,000 | all 3 | interactive |

### 4.2 Strong forms, all σ, s ≤ 3

Columns give failing root cuts for LEAN / LEANPS / GIT. All of these failures are single-run σ (at s ≤ 3, multi-run K are all intervals or co-intervals).

| case | form | fail | ctx | source |
|---|---|---|---|---|
| (4,4,5) | S-N11 | 9,012 / 876 / 100 | 398 / 73 / 25 | interactive |
| (4,4,5) | S-δ | 7,716 / 780 / 108 | 398 / 73 / 25 | interactive |
| (4,5,6) | S-δ | 21,366 / 2,686 / 1,018 | 730 / 184 / 148 | job 20260928-210226-20f0f7, `q1d/` |
| (5,5,6) | S-δ | 19,716 / 2,860 / 1,732 | 730 / 211 / 199 | same job |
| (4,4,6) | S-δ | 22,368 / 2,512 / 300 | 730 / 157 / 49 | same job |
| (3,5,6) | S-δ | 16,566 / 832 / 78 | 554 / 52 / 13 | same job |
| (4,6,6) | S-δ | 20,390 / 2,512 / 1,038 | 730 / 184 / 138 | same job |
| (6,6,6) | S-δ | 18,636 / 2,292 / 1,136 | 730 / 199 / 167 | same job |
| (4,4,5) | S-route | 4,408 / 772 / 0 | – | interactive |
| (4,4,6) | S-route | – / 2,512 / **296** | – / 157 / 49 | interactive |

Roughly half of the failing cuts are at in-domain couplings, and many are in non-extreme contexts.

### 4.3 S-δ on multi-run σ, non-interval non-co-interval K, s ≤ 4

| case | range | contexts | root cuts | LEAN / LEANPS / GIT fail | ctx (non-extreme) | source |
|---|---|---|---|---|---|---|
| (4,4,5) | e≤2 L2 | 1,752 | 11,448 | 264 / 264 / 248 | 62 (10) | job 20260928-210708-1d7a18, `q1m/` |
| (4,5,5) u=k | e≤2 L2 | 1,752 | 11,448 | 64 / 64 / 32 | 12 (0) | same job |
| (3,4,5) a=3 | e≤2 L2 | 1,752 | 11,448 | 0 / 0 / 0 | 0 | same job |
| (5,5,5) | e≤2 L2 | 1,752 | 11,448 | 0 / 0 / 0 | 0 | same job |
| (5,5,6) | e≤2 L2, first 1,798 contexts only | – | – | ≥760 / ≥760 / ≥728 | – | job 20260928-210708-05b17f, cancelled once the verdict was clear |
| (5,5,6) | families +2 vertices | 336 | 5,376 | 728 / 728 / 668 | 69 (16) | job 20260928-213138-fb14ed |
| (5,5,6) | e≤1 L1 | 48 | 384 | 72 / 72 / 72 | 10 (6) | interactive |
| (4,5,6) | e≤1 L1 | 48 | 384 | 96 / 96 / 84 | 8 (4) | interactive |
| (4,4,6) | e≤1 L1 | 48 | 384 | 48 / 48 / 32 | 4 (2) | interactive |

### 4.4 S-route on multi-run σ, target GIT (the most generous class), s ≤ 4, e ≤ 1, L1

| case | root cuts | GIT fail | ctx | non-extreme ctx |
|---|---|---|---|---|
| (4,4,5) | 216 | 0 | 0 | 0 |
| (4,4,6) | 384 | 32 | 4 | 2 |
| (4,5,6) | 384 | 72 | 6 | – |
| (5,5,7) | 600 | 232 | 18 | 12 |

These runs were interactive; outputs `scratch/t{445,446,456,557}s4e1-route-mo.json`.

## 5. Minimal counterexamples

All were re-checked by explicit enumeration of every tree (`explain.py`, `brute_route.py`).

### 5.1 Single run, S-δ

**Setting.** (4,4,5), σ = `SSS` (root context), K = {middle} lower, d = 1.

| world | (0,0) | (0,1) | (1,0) | (0,2) | (1,1) | (2,0) | (1,2) | (2,1) |
|---|---|---|---|---|---|---|---|---|
| t, VAL | 2 | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| t, δ | 0 | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| leaf σ, VAL | 6 | 3 | 3 | 1 | 2 | 1 | 1 | 1 |
| leaf σ, δ | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 1 |

W holds by a wide margin, yet t's δ mass sits at shallow worlds, where the leaf has none.

### 5.2 Single run, S-route with GIT

**Setting.** (4,4,6), `SSS`, K = {middle} upper, d = 2 (in-domain).

**The tree t.** The middle vertex upper (c = 3), and the outer pair lower (d = 2), cut at couplings 1 | 4. Its route vector (δ00, δ01, δ10, δ11 | v02, v20, v12, v21) is (0,1,0,0 | 1,1,0,1).

**Why it is undominated.** The 545 GIT trees of `SSS` realize 14 distinct route vectors. Those with δ01 = 1 are (0,1,0,0 | 1,1,1,0), (0,1,0,0 | 1,1,0,0) and (0,1,0,0 | 0,1,0,1); none dominates t.

### 5.3 Multi-run, non-extreme, in-domain, k-optimal: N11@k is impossible

**Setting.** (4,4,5), σ = `1L S 1L S S S`, maxima (2). Every maximum is in [2, k−3]. K = {1st, 3rd vertex} upper, d = 2.

**The tree t.**
- The K-part is cut upper at d = 1 into two leaves.
- The rest is cut lower at d = 1 into two leaves.
- The four leaves have limits (1,1), (1,1), (1,1) and (3,0).
- `val_k(t) = 3 = bound σ`, so t is k-optimal. N11(t) = 3, and δ(t) = (3,0,…).

**Why N11@k fails.**
- The maximum of N11 at world k is 2 over LEAN trees and also 2 over GIT trees.
- The trees with 2 isolated vertices have VAL (3,0,1,…) or (3,1,0,…). They dominate t in value only through reduced-world slack.

### 5.4 Multi-run, S-δ and S-route

**First failure found.** (4,4,5), `S S 1L S S`, maxima (1), K = {1st vertex of each run} lower, d = 2. The tree t has VAL (4,1,1,…) and δ (2,1,1,…). Every LEAN tree with 2 isolated vertices has VAL ≤ (3,0,1,…) or its mirror.

**Non-extreme route failure.** (4,4,6), `SS1LSS`, maxima (2), same K and d. Its route vector is (2,1,0,0 | 0,1,0,0), and no GIT tree dominates it.

## 6. Question 2: moot

**The strong condition fails, so no R exists.** S-N11, S-δ and S-route all fail, and N11@k fails against every candidate target (§5.3). So no rewriting, value-independent or not, can satisfy condition 2. Measuring natural candidates (first alternation, end strip, hull) would add nothing.

**Remark (not decisive).** A root rule `(I, o', d+g) = f(word, K, o)` with g ∈ {−1,0,1} and free subtrees already fails for W. It fails in 16 of 24 classes at (4,4,5) s = 4 e ≤ 1 L1 (`probe_rule.py`). Example: `SSS1LS`, K = {0,2}; with maxima (1), d = 2 needs block {0} upper, while d = 3 needs block {0} lower.
- This is not a necessary condition. An equivariant R may read lift-invariant data: a−d, u−c, m_l−d for lower levels and m_l−c for upper levels.
- At a fixed (a,u,k) that allows nearly any dependence, so the real constraints are across worlds.
- That cross-world test was not built, since condition 2 is already impossible.

## 7. Question 3: the obstruction

**The Pascal ledger charges isolated vertices at full price.**
- Theorem 4 books each (1,1) leaf once, at its own world.
- A non-interval partition can isolate more vertices at a shallow world than any interval tree can: 3 vs 2 at equal k-value (§5.3).
- The interval tree recovers the difference only through reduced-world slack.
- A per-world N11 or δ monotonicity cannot see that compensation.

This is the same phenomenon as Track B's R4 (uncompensated isolated vertices), Track A's PAIR "1→0 corner losses", and Track A's RED2N failures.

**Where the failures are.**

| class | failures? |
|---|---|
| coupling 0 only | **No.** The top world itself fails (§5.3). |
| a = 3 only | **No.** At (3,4,5), multi-run S-δ has 0 failures; the failures are interior. |
| u = k only | **No.** (4,5,5) fails only in extreme contexts, but the interior fails in the bulk. |
| bulk | **Yes.** Non-extreme contexts, in-domain couplings, single-run and multi-run, k = 5–7. |

**The absorbing boundary is a second, independent obstruction (§3.3).**

## 8. Status

**Refuted (diagnostic plus paper arguments).**
- R with N11 monotonicity through Theorem 4.
- The δ and route strengthenings.
- Any Theorem-4 k-induction reaching a = u = k.

**Surviving (evidence only).** Conjecture W:
`∀σ WellFormed, ∀(K,o,d), ∀ LEAN subtrees, ∃τ ∈ LEAN(σ), ∀ live w: val(τ↓w) ≥ val(t↓w)`.
- On single runs it is equivalent to additivity in every reduced world.
- On multi-run σ it extends Track A's three-world domination to all worlds and all t, not only k-optimal t.
- It is stronger than the goal, and no proof path is known.

## 9. Recommendation

1. **Do not register** an R/N11 node, or any Theorem-4 k-induction for `ctx_bound_additive`. Record §3.3 next to Track B's Theorem 4, so that the Pascal-in-k route is not retried for a = u = k.
2. **Keep §5 as regression fixtures**, especially §5.3. Any future "charge isolated vertices" lemma must pay from reduced-world slack, not world by world.
3. **Register W only if a paper mechanism appears.** One candidate is a lattice-path or charging argument on the Möbius mass δ. The harness is ready: `probe_domination.py --kind val`.
4. **The isolated-vertex obstruction (§3.4, §5.3) is common to Tracks A, B and C.** Nothing here supersedes Codex's fixed-k charge accounting, which handles such vertices locally.

## 10. Files

Everything is under `runs/claude-uniform-mechanism-20260928/rewrite/`.

**Library.** `worlds_lib.py`: world lattice, route worlds, the fast leaf evaluator, frontiers for LEAN, GIT and partition trees, and the val, n11, joint, δ and route vectors. It reuses `descent/pascal_lib.py`.

**Probes.**
- `probe_domination.py`, with the `--kind`, `--family`, `--only-multirun`, `--only-other` and `--only-singlerun` options
- `probe_rule.py`, `inspect_rule.py`
- `explain.py`, `brute_route.py`
- `boundary_identity.py` (output `boundary-identity.txt`)
- `selfcheck.py`, `check_fast_leaf.py`
- `summarize.py`
- Runners: `run_cases*.sh`, `run_weak.sh`, `run_fam.sh`

**Outputs.** `q1/`, `q1d/`, `q1m/`, `q1w/`, `q1f/` and `scratch/`. The files in `q1/` were moved there from a nested path created by a runner-path slip.

**Code review note.** Nothing was promoted. `worlds_lib.py` is the only candidate for `harness/research/`, if all-world evaluations recur.

**Process notes.**
- Two interactive commands overran a minute. Each was capped by `timeout` and used under 1.5 GiB.
- Job 20260928-210708-05b17f was cancelled once the S-δ verdict was clear.
