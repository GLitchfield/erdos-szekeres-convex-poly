# R25: prove the Band Decomposition Lemma (one Sol trial, gpt-6.1-sol)

**Approval and roles.**
- Approved by Gavin on 2026-10-03: "put all available resources towards generalization efforts".
- Coordinator: `claude-code:f3e0818a-9388-430b-9c32-aeb7dc5d297b` (Claude), who owns the synthesis.
- Callbacks are unverified, so never wait for replies. Keep PROGRESS.md current. This is one trial; never reset
  the deadline.

**Worktree.** `runs/worktrees/sol-12h-20261002`, new branch `research/r25-bdl-20261003` from main `d63b3fb8`.
Preserve the R21/R22/R23 branches. R24 runs in another worktree; do not touch it.

## Read first
- AGENTS.md, especially the rule that specific cases serve the generalization.
- In the main checkout, `/home/gavin/git/erdos-szekeres-convex-poly/`:
  - `runs/claude-general-picture/GENERAL-PICTURE.md`, the coordinator's working document; its BDL section is the
    target;
  - `runs/claude-uniform-20261003/NOTES.md`: BDL, evidence, the DS induction, case R, invariant P;
  - Lemma DS: `runs/claude-r26u1-20261002/PROOFS.md` (audited in
    `runs/claude-audit-667-20261003/AUDITED-PROOF-667.md`).

## The statement

**BDL.** Let X be decomposable with no strong k-set, α = cup X, β = cap X, α+β >= k. Then X partitions into bands
X_j, k-1-β <= j <= α-1, with cup X_j <= j+1 and cap X_j <= k-1-j.

**Why it matters.**
- BDL implies Baek–Balko Theorem 8 for ALL (a,u,k) with no gate lemmas: classical Erdős–Szekeres gives
  |X_j| <= C(k-2,j), and the band sums are T(a,u,k). Lean already has the per-band bound
  `card_le_choose_of_oneChange_no_cap_no_cup` (R23, commit bad5a94e on its node branch in this worktree).
- The map point ↦ (band, classical path inside the band) is the injective labelling behind the formula.
- Evidence (diagnostic): exhaustive for decomposable n <= 8, plus samples at k <= 8. An independent audit is
  running.

**Structure known.**
- At X = A << B, the children's band index ranges are disjoint by the node condition cup A + cap B <= k-1, so the
  partitions concatenate.
- Every root split closes except **case R**: cap B = cap X = β and cup A = k-1-β, with A nested in the core of B's
  β-caps. This is exactly the Baek–Balko gap.
- Case R closes if B's bottom band can be placed on one side of A (invariant P, diagnostic). But P is not known to
  survive root splits.

## Goals, in priority order
1. **A complete, rigorous paper proof of BDL**, or the exact minimal missing lemma with evidence.
   - Write every closing case carefully: classic children, non-tight nested absorption, and case R when B is
     classic, one-band, or has a one-sided bottom band.
   - Then find an induction hypothesis that carries through case R. "BDL in context" means bands constrained
     relative to the sibling extreme points that Lemma DS says are visible. Prove that it is preserved at every
     root split.
   - Check each claimed step on small decomposable instances. A short checker is fine; reuse the scripts in
     `runs/claude-uniform-20261003/` and the library (`es lib search`).
2. If BDL is proved on paper: register BDL via `es node add` (kind formalization; the decomposable statement,
   general k), and its consequence `decomposableStateUpper_all` from BDL. Then start the Lean proof of
   BDL ⇒ Theorem 8, using the per-band classical bound. Do NOT formalize BDL's own proof before the paper proof is
   complete and logged.
3. If BDL is refuted (an independent re-check of any counterexample is required): characterise the failure, and
   propose the corrected statement that the data supports.

## Constraints
- `es job run` for anything over a minute (2–4G for Python); no self-chosen timeouts; progress output.
- `es log` every finding (diagnostic vs proved). New statements only via `es node add`. No merge or push.
- Write BDL-PROOF.md (or BDL-OBSTRUCTION.md) and MATHEMATICAL-HANDOFF.md in this run directory before the
  deadline.
