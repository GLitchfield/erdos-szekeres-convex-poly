# R24: is the context bound the true maximum, and how does the true maximum compose? (one Sol trial, gpt-6.1-sol)

**Approval and roles.**
- Approved by Gavin on 2026-10-03: "put all available resources towards generalization efforts".
- Coordinator: `claude-code:f3e0818a-9388-430b-9c32-aeb7dc5d297b` (Claude), who owns the synthesis.
- Callbacks are unverified, so never wait for replies. Keep `PROGRESS.md` current. This is one trial; never reset
  the deadline.

**Worktree.** `runs/worktrees/sol-12h-20260916` (R19's), new branch `research/r24-ctxexact-20261003` from main
`d63b3fb8`. Preserve the R18/R19 branches.

## Why this run exists (read the new working rule in AGENTS.md first)

The goal is the GENERAL proof of Theorem 8 for decomposable sets. The coordinator's working document is
`/home/gavin/git/erdos-szekeres-convex-poly/runs/claude-general-picture/GENERAL-PICTURE.md`; read it in full.

Its reformulation, from the audited Lemma DS (`runs/claude-r26u1-20261002/PROOFS.md` in the main checkout; audit
in `runs/claude-audit-667-20261003/`):
- "no strong k-set" is local: cup(A)+cap(B) <= k-1 at every internal node;
- each part sees its ancestors only through siblings' extreme points per zone.

So Theorem 8 is a finite tree recursion for N(P; α, β), the maximum size under a zone profile P. **The general
formula we need is a closed form for N.**

The context route (R1–R19, your own record) attached a CONJECTURED bound function to contexts. It stalled at
additivity, the sibling penalty. **This run answers question Q4 of the document, then Q3:**

- **Q4. Does the context bound function equal the true maximum N on every context?** It is defined by
  `harness/research/context_bound.py` (library id `research.compiled-context-bound`) and the Lean
  `Ctx.Context.bound`.
  - If yes: the remaining problem is proving additivity for the TRUE maximum, and R1–R19's failures are instances
    of a real inequality that we must understand.
  - If no: find exactly where it over- or under-estimates and why. The corrected function becomes the candidate
    general formula.
- **Q3. How does the true maximum compose at a root split?** State exactly the inequality the true N satisfies
  between parent and children: the sibling penalty, written as an identity or inequality over the true N.

## How
1. FIRST summarize what the R1–R19 record (es journal, handoffs, accepted counterexamples such as end-cut, PEEL,
   FLANK-SWAP, absent flank) already establishes about Q4. Do not recompute known facts.
2. Exact values:
   - `decomposable.exact-context-bound` (`scripts/decomposable_context_exact.py`, enumerated class data);
   - for larger contexts, an exact evaluator built on Lemma DS, which is audited for all k (see
     `runs/claude-r26u1-20261002/zdp.py`, `hyb.py` in the main checkout).
   Use `decomposable.context-limits` and `decomposable.context-enumeration` for contexts.
3. Compare exact N with the bound on all contexts within reach (k = 5..7, bounded depth/length). For each mismatch,
   give the smallest witness and an explanation in terms of the tree structure (what the bound function
   mis-counts).
4. For Q3: on exact data, test candidate composition laws. Each test is a hypothesis about WHY: for example,
   whether the union deficiencies seen in the kill-set run (`runs/claude-killset-20261002/NOTES.md`, multi-gate
   failures) are exactly the bound function's error.

Use `es lib search` before writing code, and record every finding with `es log` (diagnostic vs proved). Lean work
only if a general structural lemma (such as Lemma DS itself) is needed to settle a question; no Lean for specific
instances.

**Done:** a research note `Q4-Q3-ANSWER.md` with:
- exact definitions;
- the answer to Q4 (yes/no, with the minimal mismatch witnesses and their explanation);
- the exact composition law or the precise obstruction for Q3;
- what this implies for the general formula.

Also write MATHEMATICAL-HANDOFF.md before the deadline.

## Constraints
- `es job run` for anything over a minute (memory caps of 2–4G for Python); no self-chosen timeouts. Progress
  output for long jobs.
- `es log` every finding; no statements without `es node add`; no merge or push.
- Do not touch `runs/worktrees/sol-12h-20261002` (R23, finishing).
