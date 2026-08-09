# Erdős--Szekeres convex-polygon research guidance

This repository is an AI-assisted formal mathematics project initialized from
`open-math-research-template`.

> **Project:** Formal research on the exact Erdős--Szekeres happy-ending
> conjecture.
>
> **Destination:** Prove that the least number of planar points in general
> position forcing `n` points in convex position is `2^(n-2) + 1` for every
> `n ≥ 3`, with a compiling Lean 4 proof. Intermediate progress consists only
> of explicitly stated, compiling Lean theorems that remove a documented
> obstruction or establish a reusable part of that proof.

## Completion and claim discipline

- A mathematical result is complete only when its stated theorem compiles with
  no `sorry`, `admit`, unsafe axiom, or unverified external oracle.
- Prose, experiments, SAT output, and informal arguments may be useful evidence
  but are not completed results. Label them accordingly.
- Distinguish the classical planar conjecture, its exact small cases, asymptotic
  bounds, and stronger or relaxed variants. A variant is in scope only when it
  supplies machinery, an equivalent formulation, an obstruction, or formal
  infrastructure for the exact formula. Implication or equivalence between
  models must itself be proved or precisely cited.
- State all general-position, coordinate-order, orientation, convex-position,
  and degeneracy conventions explicitly. Treat order types and realizable
  planar configurations as different objects until a bridge is proved.

## Primary formal system

- Lean 4 with mathlib, pinned by `lean-toolchain` and `lakefile.toml`.
- Project declarations live in the `ErdosSzekeres` namespace.
- `lake build` is the proof gate. `make test` runs both Lean and repository
  workflow checks.
- Prefer reusable definitions and small lemmas over one opaque theorem script.
- External Lean developments are read-only references unless their licenses and
  exact revisions are recorded before reuse.

## Sources and reproducibility

- Prefer original papers, publisher pages, arXiv records, and official source
  repositories. Record DOI/arXiv identifiers and retrieval date.
- The living survey is `docs/literature_review.md`; the source ledger is
  `docs/bibliography.md`. Never call the ledger exhaustive without a documented
  database query and citation-chaining audit.
- Keep papers and third-party code out of the repository by default. If a local
  snapshot is genuinely needed, put provenance and license metadata in
  `data/reference/README.md`.
- Computational searches require bounded Wayfinder criteria, deterministic
  inputs, a compact certificate, and an independent checker. Machine-local
  activity belongs under ignored `runs/`.

## Wayfinder

- The canonical map is `docs/wayfinder/map.md`; decision tickets are under
  `docs/wayfinder/tickets/`.
- Start strategic work by reading the map and running
  `python3 scripts/wayfinder_status.py`.
- Resolve one consequential ticket per session. Use the repository's bounded
  Sol/Fable review before selecting or changing the main route.
- Launch provider reviews directly with the exact prefix
  `python3 scripts/adversarial_review.py run`. Request out-of-sandbox execution
  for that command; the trusted project rule authorizes this one prefix without
  a repeated prompt after session startup. Do not add a shell wrapper.
- Keep the map, README, survey, and Lean statement aligned when scope changes.

## Multi-agent orchestration

- The canonical role manifest and execution protocol are
  `docs/agents/manifest.toml` and `docs/agents/README.md`.
- Keep durable persona profiles separate from immutable task packets. Every
  delegated assignment must freeze its objective, inputs, ownership, budget,
  evidence gate, success condition, and stop conditions before dispatch.
- The top-level orchestrator owns integration files and serializes shared-file
  edits, project builds, repository tests, commits, and Wayfinder changes.
  Specialists are read-only unless a task packet grants exact, non-overlapping
  write paths.
- Treat agent output as an untrusted proposal. Record the precise evidence
  level; consensus, prose, and computation do not become Lean proofs through
  review or repetition.
- Store transient task packets, transcripts, and results under ignored
  `runs/agents/`. Promote durable conclusions into existing Wayfinder tickets,
  experiments, source documents, or Lean theorems rather than creating a
  second strategic tracker.
- Use bounded Sol/Fable review for route selection or route changes. Ordinary
  implementation of a vetted frozen theorem contract does not require another
  strategic review.

## Multi-hour plan approvals

- Before presenting any plan expected to take two hours or more, inventory all
  reasonably foreseeable actions that need user or platform approval. Include
  external provider or network calls, out-of-sandbox commands, software
  installation, resource-limit increases, process termination, destructive
  operations, and external repository or review mutations.
- Resolve exact commands, targets, resource ceilings, and reusable approval
  prefixes before requesting approval whenever the plan already determines
  them. Present one consolidated approval request with the plan, distinguishing
  actions already authorized, actions needing new approval, and conditional
  actions that cannot yet be made exact.
- Plan approval does not bypass a platform approval prompt. Trigger every
  foreseeable prompt at the beginning of the approved work block rather than
  waiting until the dependent item is reached.
- If an unanticipated approval becomes necessary later, pause only the
  dependent branch, continue any safe independent work, and ask for the narrow
  additional authority. Never broaden the approved mathematical or operational
  scope merely to avoid another prompt.

## Git discipline

- Preserve user work and unrelated changes. Stage only intended files.
- Run `make test` before each commit, then push when a remote is configured.
- This managed checkout mounts `.git` read-only. Local metadata is in ignored
  `.git-data`; use `git --git-dir=.git-data ...`. The GitHub repository and
  normal clones use standard Git metadata.

## Current resource policy

- No unbounded searches. Default exploratory computation limit: 30 minutes,
  8 CPU cores, 16 GiB RAM, and 5 GiB under `runs/`, unless a ticket declares a
  different bound.
- Neighboring repositories, the template repository, published formalizations,
  and provider services are read-only references.
- The project source is MIT-licensed. Third-party papers and code retain their
  own licenses.
