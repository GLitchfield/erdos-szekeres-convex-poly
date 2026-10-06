# Experiment 0125: the MIXED ROOT lock: where Theorem 8 is stuck, and every route that failed there

Date: 2026-10-06 (covers work of 2026-09-28 to 2026-10-05).

Status: open. This is the single unproved step of the band route to Baek–Balko Theorem 8 for decomposable sets
(Workstream B). It is also where Workstream F stalls. This note is the canonical tracked record. The source
documents (formerly in the git-ignored `runs/`) are archived under
`docs/research/archive-2026-09-28-to-10-05/`, and the harness journal for the period is in
`journal-log-entries.json.gz` there.

Tags: [L] Lean, compiled on main. [P] hand proof, audited unless stated. [C] exhaustive or extensive computation,
diagnostic, not Lean.

## 1. The target and what is proved

**Theorem 8 (Baek–Balko).** A decomposable set with no a-cap, no u-cup and no strong k-set has at most T(a,u,k)
points:
- T = C(a+u−4, a−2) when a+u <= k+3;
- otherwise T = Σ_{j=k−a}^{u−2} C(k−2, j).

The published induction has a gap exactly at the step described below (experiment 0123 and the correspondence
draft).

**Proved and compiled [L] (main 701ff379 and its parents):**
- **Lemma DS** (`deepSplit_strong_avoidance_iff`, `deepSplit_endpoint_constraints_iff`). For X = A << B,
  strong(X) = max(strong A, strong B, cup A + cap B). Chains meeting the other part see only its extreme points.
- the classical cups–caps bound (`card_le_choose_of_oneChange_no_cap_no_cup`);
- the lower construction for all parameters (`decomposable_threshold_lower_exists`);
- gluing and pushforward;
- the a = 4 and a = 5 gates; ES(6) = 17; predecessor-half at k = 6;
- **Theorem 8 from BDL** (`decomposableStateUpper_all_of_bands`). It assumes the BDL hypothesis below, guarded by
  j < k, and proves `DecomposableStateUpper a u k` for all a, u, k.

**BDL (Band Decomposition Lemma) [C].** Exhaustive for n <= 9, plus large and adversarial samples up to n = 40,
with no decomposable failure. Statement: a decomposable X with no strong k-set, cup α, cap β and α+β >= k
partitions into bands X_j (k−1−β <= j <= α−1) with cup X_j <= j+1 and cap X_j <= k−1−j.
- It is FALSE for general signotopes in its own-range form: X14 at k = 6, and three tight (7,5,7) sets with n = 26.
- The full-range form (bands 0..k−2) holds on all of these (§6).

## 2. The reduction to one configuration

**[P] Level cut.** At a root split X = A << B with p = cup A:
- T(a, p+1, k) + T(k−p, u, k) = T(a, u, k) for k−a < p < u−1. This identity was checked for all k <= 12.
- So induction plus DS proves the bound at every such split. This is the published Pascal-window step.

**The only failing splits are degenerate: p = k−a, or the mirror q = k−u.**
- There A's window share is empty, yet A can hold C(k−3, p−1) points.
- In Boolean terms, A must displace a star of level p of B_{k−2}.
- [C] All 98 non-level-cut tight root splits in the corpus are of this kind.

**[P, audited as a conditional reduction] BDL ⟺ MIXED ROOT** (Sol R25,
`archive/sol-r25-sol-20261003/`).

**MIXED ROOT (the lock).** The setting at a root split X = A << B:
- s = k−1, β = cap X = cap B, and p = cup A = s−β, so the split is tight;
- A sits strictly inside the common core of B's maximum β-caps: every max cap of B starts before A and ends after
  A;
- some maximum β-cap of X is mixed, i.e. an A-point extends a (β−1)-cap of B.

**The requirement:** given that B has a valid band partition, produce a valid band partition of X on the same band
range. Points of B may change bands.
- The single-point case |A| = 1 is the residue that R26 isolated: general ROOT is constructed when strong B = cap B.
- The general case adds simultaneous keep/lift choices for A.

## 3. What is understood about the lock

- **Exact local conditions [P].**
  - Lifting z to band p+1 is valid iff that band has no (β−1)-cap ending before z and none starting after z.
  - Keeping a set K in band p is valid iff band p "straddles" no p-cup of K.
  - Deciding WHICH points to lift is global.
- **The A-side choice is cheap [C]** (survey D). The feasible keep/lift vectors depend only on the number kept, and
  local rules force it. The real content is choosing B's partition.
- **No re-partition flow is needed [C]** (star_flow, cex40). Relative to the best partition of B, zero B-points move;
  A is lifted to p+1. So the content is choosing B's partition in view of A's cut positions.
- **The certificate is bounded but non-local [C].**
  - At most about 4 tagged pieces of sibling information suffice at any node.
  - A proof always exists inside a finite two-sided "tower" context language.
  - No local rule selects it, and the witness automaton does not compress: one state per colouring.
- **Meta-insight.** Statements that hold for general signotopes (PSL, CORE, SH, FBDL) would prove ES for
  signotopes. So a feasible proof must use decomposability essentially.

## 4. Every route tried at the lock, and how it failed

| Route | Failure mode | Where |
|---|---|---|
| Scalar induction on (a,u,k) (the published proof) | sizes cannot see where A sits among B's caps; first failure (4,5,5,1,3): 1+7 > 7 | exp 0123, correspondence draft |
| Context-indexed bound N(P; α, β) (R1–R19) | guessed bound function stalled at additivity; kill-set rule exact only on single-gate profiles | exp 0116–0124, claude-residue, claude-killset |
| Tree induction with bounded context (positional cuts, tower profiles, universal partitions, admissible contexts) | the context regrows, or selection needs lookahead | claude-tower, claude-bandrule, claude-bdl-induct |
| Canonical, lookup or sweep rules for bands or for PSL | impossible by SAT (UNSAT cores); tight sets have no forced choices | claude-psl, claude-bandrule |
| Point insertion / augmenting repair | repair distance unbounded; needs multi-band swap "stars" | claude-insert |
| Hall condition | insufficient: X14 satisfies Hall with no partition | claude-hypergraph |
| Matroid partition / submodular exchange | band families are not matroids | claude-hypergraph, R26 |
| Greene–Kleitman shape / simultaneous saturation | no shape; profile not concave; witness n = 8 | claude-hypergraph, survey C |
| Polymorphisms (lattice, majority) | none; a 1-in-β relation appears | claude-lattice |
| Bounded width | width grows with n | claude-lattice |
| Lovász Local Lemma | fails by a factor growing with k (≈250 strong sets per point at k = 6, n = 16) | claude-hypergraph |
| Polyhedral (LP integrality) | residual polytope not integral (odd cycle) | claude-hypergraph |
| Rectification by local moves | monotone paths exist, but every potential plateaus | claude-rectify |
| BRL+ (bottom band one-sided of the core) | FALSE at n = 24 | Sol R25 |
| P both-sided / S1 one-sided (lo >= 2) | P false at n = 19; S1 false at l = 2, n = 40 (configuration H, 25 counterexamples) | claude-plo2, claude-configH |
| ZLOCK (singleton) via stay-only | stay branch fails (n = 13, n = 24); lift branch needed exactly at tight two-sided mixed z | claude-zlock |
| Endpoint-frame peel; one-point max-cup-transversal peeling; lowercup <= 2 at full-cell roots; Y-map fixed-budget reduction | refuted on paper (R26 papers 37, 73, 72, 70) | Sol R26 |
| Survey of combinatorial tools: Scarf, kernels, Gale–Shapley, topological Hall, Nullstellensatz, shifting, LYM/Sperner, SCD, RSK, substitution, tree automata, higher Bruhat | each works on B alone and fails exactly at the mixed root | exp 0126 |
| Mirsky window band(v) ∈ [cupEnd−1, k−1−capEnd] | fails on 13/1,116 configH sets (n = 21) | survey C |
| Baek's ETV technique (exact a = 4) | a canonical peel; the author says it stops at a = 4 | survey |

**Pattern.** Every one-sided or local simplification fails, at n = 13, 19, 21, 24 or 40, while BDL itself never
failed. The lock needs keep-or-lift flexibility, chosen globally.

## 5. The common obstacle, stated once

At the degenerate level, B's partition must be chosen knowing A's cut positions inside the core of B's maximum caps.
That choice depends on B's chain structure several tree levels down, and every local, inductive or generic existence
method fails to supply it.

The same globality reappeared in Workstream F (exp 0127): the k-gon forced by a new interior point is not localised
by halves, bands, half-planes or crossed edges.

## 6. Related facts found on the way (not proofs)

- **FBDL** (full-range bands 0..k−2) holds:
  - on every pentagon-free signotope;
  - on all known extremal constructions to k = 8;
  - on X14 and the tight (7,5,7) sets.

  It implies ES. For decomposable sets it removes the lock at the root, but L(A) and U(B) recreate it one level
  down (exp 0127, PICTURE.md).
- **SH** (canonical Moshkovitz–Shapira labels plus one matching) holds everywhere tested, including general
  signotopes. It is ES-strength.
- **Purity, easy half** [C, |X| <= 8]: every constrained decomposable set below T extends by one point. The other
  half is Theorem 8.
- **Canonical layering** (band = cupEnd − 1) is valid except at overfull points, cupEnd + capEnd >= k+2 [P]. These
  come from mixed caps.

## 7. Live leads, and what not to retry

**Untested leads.**
- Deficiency submodularity at the lock: is the capacity B loses a rank function of A's gap set?
- A potential on the k-free chain-type congruence τ.
- Learned all-k invariants over the tower language (costly).
- Asking Baek–Balko for their intended argument. Declined on 2026-09-04; Gavin's call.

**Do not retry without a new idea:**
- every row of §4;
- any further one-sided narrowing of MIXED ROOT.

**Falsification not yet done.** A structured search for a BDL counterexample at k = 7 or 8 near the bound. A
counterexample would kill the route, not the theorem: Theorem 8 is implied by ES via realizability and the
Erdős–Tuza–Valtr equivalence.

## 8. Evidence index (archive paths)

All paths are under `docs/research/archive-2026-09-28-to-10-05/`.

- **Synthesis:**
  - `claude-general-picture/GENERAL-PICTURE.md` (the living document);
  - `claude-general-picture/LOCK.md` (lock synthesis and updates).
- **Sol runs:**
  - `sol-r25-sol-20261003/` (BRL+ refutation, BDL ⟺ MIXED ROOT);
  - `sol-r26-sol-20261003/` (MIXED-ROOT.md papers 1–73, MATHEMATICAL-HANDOFF.md).
- **Lock variants:** `claude-zlock-20261003/`, `claude-plo2-20261004/`, `claude-configH-20261004/`.
- **Generic tools:** `claude-hypergraph-20261003/`, `claude-lattice-20261003/`, `claude-rectify-20261003/`.
- **Induction routes:** `claude-tower-20261003/`, `claude-bandrule-20261003/`, `claude-psl-20261003/`.
- **Coordinator records:**
  - `claude-pascal-20261002/HANDOFF.md`;
  - `claude-coordinator-20261002/RESUME.md`.
- **Survey:** `claude-survey-20261004/` (exp 0126).
- **Extremal sets / F:** `claude-extremal-20261005/` (exp 0127).
- **Harness journal:** `journal-log-entries.json.gz` (5,094 log entries, 2026-09-28 onward).
