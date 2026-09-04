> **Harness note (2026-09-04).** Evidence tiers under the harness: kernel theorem
> (closed node, `es check` reports no `sorryAx` and only standard axioms) >
> allowlisted external certificate (`harness/allowlist.json`) > `native_decide` /
> falsifier `pass` (computational evidence) > solver output without a checked proof.
> Falsifier results in `harness/falsify/<node>.json` are the canonical record of
> computational evidence for a conjecture node; datasets live in `harness/dataset/`.
> A falsifier result that retires a node still needs an independent replay.

# Reproducibility contract

## Evidence levels

Use explicit labels in notes and reports:

- **Theorem:** proved from stated assumptions, with a proof or proof-assistant
  artifact.
- **Exact computation:** finite symbolic or discrete calculation replayed from
  committed inputs.
- **Certified numerical result:** numerical claim with rigorous enclosures and
  a complete error budget.
- **Numerical observation:** reproducible but not rigorously enclosed.
- **Heuristic:** useful evidence without a completeness or error guarantee.
- **Conditional:** conclusion depending on a named external theorem, dataset,
  convention, or unverified implementation.
- **Failed or inconclusive experiment:** a scoped negative result, including its
  stopping bound and the claims it does not settle.

## Committed result manifest

Every derived result should record, directly or through a companion manifest:

- experiment identifier and question;
- Git revision and whether the tree was clean;
- producer and independent-checker hashes;
- exact input paths and hashes;
- software, CAS, package, and compiler versions;
- parameters, seeds, thresholds, conventions, and resource limits;
- start and completion timestamps when relevant;
- output hashes and a compact summary of every gate;
- certification scope and known omissions.

## Independent verification

An independent checker should reconstruct the claimed property from the
smallest useful committed artifact. Avoid importing producer helpers when a
short independent implementation is feasible. Test the checker against:

- one known positive fixture;
- one known negative fixture; and
- deliberate mutations of each convention or field the checker claims to
  validate.

## Long computations

A long run is allowed only when it has:

- a Wayfinder decision it can resolve;
- deterministic shards and stable shard ownership;
- resumable, atomic checkpoints;
- bounded time, memory, storage, and search scope;
- a merge rule that detects missing and duplicate work; and
- an independent coverage or exhaustiveness certificate.

Machine-local checkpoints stay under `runs/`. Commit compact final evidence,
the merger/checker, and enough provenance to regenerate or independently audit
the result.
