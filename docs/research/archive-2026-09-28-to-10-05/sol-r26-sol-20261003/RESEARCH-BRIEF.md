# R26: MIXED ROOT, the exact residue of BDL (one Sol trial, gpt-6.1-sol)

**Approval and roles.**
- Approved by Gavin on 2026-10-03 ("I approve all those": the evening plan, item 3, a new Sol run on the precise
  lemma that emerges).
- Coordinator: `claude-code:f3e0818a-9388-430b-9c32-aeb7dc5d297b` (Claude), who owns the synthesis.
- Callbacks are unverified, so never wait for replies. Keep PROGRESS.md current. This is one trial; never reset the
  deadline. Read any COORDINATOR-NOTE-*.md files appearing in this directory.

**Worktree.** `runs/worktrees/sol-12h-20261002`, new branch `research/r26-mixedroot-20261003` from main `daf3e6a6`.
Main now contains Lemma DS in Lean, the classical bound, the cap-start peel, the lower construction, and gluing and
pushforward. Preserve the R21/R22/R23/R25 branches.

## Read first
- AGENTS.md: the rule that specific cases serve the generalization.
- R25's final handoff and reduction, in THIS worktree:
  - `runs/r25-sol-20261003/MATHEMATICAL-HANDOFF.md`;
  - `runs/r25-sol-20261003/BDL-CORE-REDUCTION.md`;
  - `runs/r25-sol-20261003/BDL-OBSTRUCTION.md`, papers 68–82 inside it.
- In the main checkout `/home/gavin/git/erdos-szekeres-convex-poly/runs/claude-general-picture/`:
  - `LOCK.md`: the lock synthesis, ZLOCK, and the R25 update;
  - `GENERAL-PICTURE.md`.
- The day audit: `/home/gavin/git/erdos-szekeres-convex-poly/runs/claude-audit-day-20261003/AUDIT.md`. Note its
  repairs, especially that single-point absorption needs a lo = 0 clause and that "reserve" fails with lifts.

## The target: MIXED ROOT (R25's exact obligation; BDL ⟺ MIXED ROOT by R25's conditional size induction)

Fix s = k−1, and let c, d, σ be the cup, cap and strong maxima. The hypotheses:
- β >= 4, p = s−β >= 1, 3 <= m <= β, α = p+m;
- X = A<<B decomposable with c(A) = p, c(B) = α, d(B) = d(X) = β, σ(X) <= s;
- a valid band partition of B on p, …, α−1 is supplied;
- a maximum β-cap of X meets BOTH A and B (a MIXED max cap).

The task: construct a valid partition of X on the same bands. Every point may change band.

**Known.**
- Paper81 closes all hard roots with NO mixed max cap, for every supplied B map.
- BRL+ (full-core one-sided bottom) is FALSE at n = 24 (brl24).
- Frozen-child extension is false, so repairs need band-transfer cycles.
- Paper74 mechanism: an inner insertion keeps the max-chain families but creates a regional (β−1)-cap that an outer
  point extends.
- The coordinator's synthesis: across all approaches tried (partitions, colourings, towers, lattices, LLL, moves),
  the hard core already appears with ONE nested point (ZLOCK, LOCK.md). Single-point absorption: z stays in band lo
  iff lo >= 2 or B's band 1 is one-sided of z; z lifts to lo+1 iff band lo+1 has no (β−1)-cap ending before z and
  none starting after z, AND (if lo = 0) band 1 is one-sided of z.

## Goals, in priority order
1. **MIXED ROOT with |A| = 1** (A = {z}, the single-point lock). Prove it on paper, or refute it with an
   independently checked witness. With one point, a mixed max cap means z extends a (β−1)-cap of B; analyse it
   exactly.
2. **Reduce general MIXED ROOT** to the single-point case (point-by-point absorption with band-transfer cycles), or
   identify exactly what extra structure a multi-point A adds.
3. If MIXED ROOT is proved on paper: register it via `es node add` and start Lean on top of the main foundations.
   There is also a coordinator node in progress on its own branch: `decomposableStateUpper_all_of_bands`
   (BDL ⇒ Theorem 8).

**Done:** a complete rigorous paper proof (or an independently certified refutation) of goal 1, plus goal 2 as far as
it goes, in MIXED-ROOT.md and MATHEMATICAL-HANDOFF.md.

## Constraints
- `es job run` for anything over a minute (2–4G for Python); no self-chosen timeouts; progress output.
- `es log` every finding (diagnostic vs proved). New statements only via `es node add`. No merge or push.
- Diagnostics test hypotheses about WHY; the SAT and exact checkers from R25/R24 and runs/claude-tower-20261003/exp
  are reusable (es lib search).
