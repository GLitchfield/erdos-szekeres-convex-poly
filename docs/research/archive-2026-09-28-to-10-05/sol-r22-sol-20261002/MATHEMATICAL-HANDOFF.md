# R22 mathematical handoff

Updated 2026-10-03T11:40Z. All four gate theorems are accepted. Approved
proof work is complete; the research deadline has passed. No proof job
or claim remains active. Finalization proceeds in the single allowed turn.
Native goal marked COMPLETE at2026-10-03T11:40:33Z after supported review.
The goal API records3803401 tokens and43199 seconds (about12 hours);
late finalization accounting remains in the explicit usage snapshots.
Agent `codex:agent-run-c94853b9754648ba`, thread
`01a0fefb-d883-7cc1-8d31-dc8f00948974`. Only configured Sol was used.
Baseline `6e4d0e66274e9d3dd1ccdbacf9fd747deb5e1d14` remains fixed.

## Exact current obligations

Both required lower gates and both optional upper gates are accepted,
committed and released CLOSED:

| Theorem | Original-source check | Locked hash | Commit |
| --- | --- | --- | --- |
| `singletonLowerPascalTailGate_five_pred_of_six_le` | `20261002-223942-093363` | `d717e6e0c539a549` | `0281d8bbf6ec782323840a4c2643153a648124fb` |
| `singletonLowerPascalTailGate_five_diag_of_six_le_of_inputs` | `20261003-002634-6a5ff2` | `87bbef437ea7141f` | `5d4fa26d8a20192c90624b23ed8a9cef90af8dd1` |
| `singletonUpperPascalTailGate_pred_five_of_six_le` | `20261003-010620-a45c42` | `f3116a1be4927653` | `cb87071e20d5a1199e014e943c267ddd729d357a` |
| `singletonUpperPascalTailGate_diag_five_of_six_le_of_inputs` | `20261003-013823-62cacb` | `f4788b174428c98` | `c79e55d04dffaa123194174c3a282374132654c2` |

All four receipts say CLOSED, lock matches, sorry=false, and dependencies use
only propext, Classical.choice and Quot.sound. Exact statements were not
edited. Receipts are `pred-gate-original-source-receipt.json` and
`diag-gate-original-source-receipt.json`. Proof fixtures are respectively
`e86015cb7af73eca2deba396c8f52527ee0c0efd73d5904efbc2d4f2cf0cc4e4`
and `7ac8e061d29029089b5b7affd65d074b1d2527edf7510f17aeff910d85acf26f`.
Commit jobs are `20261002-231745-d44e7a` and `20261003-004916-0f0642`.

The accepted interfaces are in these modules:

- `ESBlueprint/B/SingletonLowerPascalTailGateFivePredOfSixLe.lean`
- `ESBlueprint/B/SingletonLowerPascalTailGateFiveDiagOfSixLeOfInputs.lean`
- `ESBlueprint/B/SingletonUpperPascalTailGatePredFiveOfSixLe.lean`
- `ESBlueprint/B/SingletonUpperPascalTailGateDiagFiveOfSixLeOfInputs.lean`

All are present in the final cumulative branch. Each accepted theorem was
committed on its own node branch; no integration merge was performed.

Optional upper predecessor is ACCEPTED and released CLOSED: exact
upper(k-1,5,k), check `20261003-010620-a45c42`, hash `f3116a1be4927653`,
no sorry and standard axioms only. Job895.4s,peak5655MiB; audit clean.
Commit `cb87071e20d5a1199e014e943c267ddd729d357a`, commitjob
`20261003-012135-aeee96`; capture `20261003-012135-3cb48f`, fixture
`f64e5b4e5b2847a704922a38fe928e528fac17344d7c158d2b55de96e2827e4c`.
Receipt `upper-pred-original-source-receipt.json`; concise account
`UPPER-PREDECESSOR-HANDOFF.md`. The body applies the existing dual iff
at(a,u)=(k-1,5) to the unconditional accepted lower gate; source first try.

Optional upper diagonal is ACCEPTED and released CLOSED. Its full check
`20261003-013823-62cacb` took893.4s,peak5684MiB; receipt
`upper-diag-original-source-receipt.json` has the exact locked hash above.
Capture job `20261003-015344-5fc88b` produced fixture
`b6cfeee3a45fb24a11c29974eea88a5ec6426a8c5ee7b91d4c5c5d3118357f99`.
Commit job `20261003-015354-a4d87f` produced the final SHA above, which is
current HEAD on `node/SingletonUpperPascalTailGateDiagFiveOfSixLeOfInputs`.
`UPPER-DIAGONAL-HANDOFF.md` records the accepted result and claim release.
Both upper bodies apply `singletonUpperPascalTailGate_iff_lower_dual` at
(a,u)=(k-1,5) and (k,5), respectively, to the accepted lower proofs. Their
four numerical side conditions follow from k>=6. Uniform hblocks/hbaek
cover the dual colouring, so the diagonal upper requires exactly the same
inputs. No new assumption or case restriction was introduced.

No mathematical obstruction remains for this run's exact targets. The
final review inspected all four receipts, source/fixture fingerprints,
dual side conditions, branch ancestry and preserved R21 refs; see
`FINAL-MATHEMATICAL-REVIEW.md`. Final code/library review is also complete;
see `FINAL-CODE-MAINTENANCE-REVIEW.md`. Its guarded inventory job
`20261003-015928-aac142` terminated successfully and records the final
source and inline commands. Neither an inventory nor process exit is used
as theorem credit. The monitor's observational10000-output-token target
was exceeded (snapshot14048); this overage is recorded without resetting
usage or claiming savings. Handoff/late-usage work is now accounted in
window-b838ed868e1b4c3e, separately from proof writing and reviews.
Native goal and fixed research deadline are unchanged.
Scheduled consolidation began at11:08:37Z. Fresh canonical types still
confirm all four exact locks/CLOSED/no-sorry/standard axioms and null claims.
Git is clean at the same final SHA; baseline ancestry and both R21 refs
were verified again. All four current source fingerprints match accepted
captures. No queued or active proof job remains; only the native host runs.
`CONSOLIDATION-REVIEW.md` records this review and late accounting.
The global happy-ending conjecture remains open. The conditional diagonal
gate still requires coordinator instantiation of its inputs after integration.
`INTEGRATION-NOTES.md` records the exact source-level input application;
it is deliberately labelled an uncompiled integration sketch.

## Why the lower gates hold

Let H=C(k-1,2)+C(k-3,2) and G=H+1=(k-3)^2+k-1. A singleton q deep below
the upper reservoir defines its gap. Any four-cap on one gap side extends
with q to a forbidden five-cap. The reservoir has a genuine decomposable
root with lower child A and upper child B. A lower cup and upper cap form
a strong polygon regardless of how the children interleave in sweep order.
Avoiding a strong k-polygon therefore converts an upper b-cap witness into
absence of a (k-b)-cup below. Endpoint extensions impose further cup/cap
deficits on the regions determined by the gap.

The predecessor proof bounds every such root by H. Four-cap-free regions
have triangular size bounds from cup-start layers. Gap-separated regions
have square bounds; marker cup endpoints and the sharp ordered cup-prefix
bound handle the remaining mixed cases. One order reversal covers the
opposite orientation, and the one-sided cases are included. Its reservoir
is exactly H+1, so the root bound closes the predecessor gate.

The diagonal proof allows one further cup point and has root bound G.
Singleton upper children reuse the accepted predecessor bound on a smaller
decomposable child after cap coupling excludes (k-1)-cups. A nontrivial
upper cup gives lower square (k-3)^2 plus upper k-1, exactly G. The sharp
three-cap/four-cap cases use stronger decomposable R1 and R2 bounds.
The diagonal Pascal window differs from the predecessor by its final
C(k-2,k-2)=1 term, hence its reservoir is G+1. The accepted diagonal root
bound G supplies the contradiction for the exact wrapper.
The predecessor result is applied at the same k. This step does not
assume a (5,k-1,k-1) theorem or recurse on cardinality.

## What makes the diagonal refinements work

The decomposable three-cup R1 theorem gives 3k-8 using chosen lower
witnesses in the occupied original blocks and the supplied uniform
two-cup bound. The cup-prefix/four-cap-free-suffix R2 theorem gives
T=1+C(k-1,2)+k-4. Classify the lower child as lying in the prefix, the
suffix, or both. Lower witnesses extend upper caps, making upper regions
cups or four-cap-free pairs. Chosen witnesses avoid unnecessary proofs
about extrema membership. Z-prime transfers the maximum prefix point into
the suffix: a new four-cap would force a forbidden cup or five-cap, saving
the needed point in the resulting triangular count.

The difficult R2 suffix case needs an adjacent-pair three-cup deficit
3k-6. The only excess size pattern is k-1,k-3,k-1. Forced middle cup
extensions and the remaining boundary turns give either a k-cup or a
cap triple with the same endpoints as a (k-1)-cup, whose union is a strong
k-polygon. This theorem needs adjacent four-cap exclusions and pair bounds;
it does not need decomposability or a global five-cap hypothesis.

At k=6, H=13, G=14 and T=13. The sharp diagonal root cases are lower4+
upper10 and lower1+upper13. In the pure-suffix R2 case, lower1+upper12=13;
the elementary three-cup estimate would leave one extra point. In the
both-four-cap root case, the square estimate at k=6 is <=1, contradicting
the lower four-cap witness. For k>=7 the same case has arithmetic slack
2k-13. These are certified proof cases, not experimental extrapolations.

## Reusable accepted proof receipts

The predecessor root interface is stronger than its gate application:
it needs nonempty children and `HasDeepBelowSplit`, but neither child
decomposability proof. It assumes OneChange on their union, q outside,
no four-cap on either q-gap side, and whole-union exclusions of five-caps,
(k-1)-cups and strong k-sets. Its conclusion is the H bound.

The diagonal root additionally needs both child decomposability proofs,
fixed-k uniform hTwo/hBaek and whole-union no-k-cup; it concludes G.
Its hTwo bounds two ordered cups avoiding four-caps and strong k-sets by
2k-4. Its hBaek bounds any OneChange four-cap-free set avoiding strong
k-sets by 1+choose(k-1,2). Both quantify over all colourings at this fixed
k. The gate wrapper supplies them from its stronger uniform input binders.
The diagonal prefix/suffix R2 interface needs decomposability of the
union, ordered cup prefix, four-cap-free suffix, whole no-five-cap and
no-strong-k; it derives no-k-cup internally. Preserve these exact scopes
when reusing the results; no numerical count alone replaces them.

| Result | Original-source check | Commit | Receipt |
| --- | --- | --- | --- |
| Predecessor full root bound H | `20261002-223031-d2569c` | `00b7765074fc4ac92787c64c29b0d0bb5c393b81` | `pred-root-original-source-receipt.json` |
| Z-prime prefix transfer | `20261002-234842-f12d34` | `7dfceae54b23364066f9cf5894e7a7812c0dbb42` | `zprime-original-source-receipt.json` |
| Two simultaneous endpoint extensions | `20261002-235448-9f5cae` | `710a3245135450e7fe2274abe9809dd29fa7b292` | `endpoint-original-source-receipt.json` |
| Decomposable three-cup R1, 3k-8 | `20261003-000353-78b053` | `edd0792efd9360a3045dbc99d3e4dd0f36f77b7a` | `r1-original-source-receipt.json` |
| Adjacent-pair deficit, 3k-6 | `20261003-000935-deaead` | `63858d9e73769ac2de02a7e5312ad7b94c642c24` | `deficit-original-source-receipt.json` |
| Decomposable prefix/suffix R2, T | `20261003-001609-4350b7` | `d73bb74dc4068b0163c2e17ce82f54ca9f136123` | `r2diag-original-source-receipt.json` |
| Diagonal full root bound G | `20261003-002306-951371` | `2bce9cc2f6b0b99005852f82285bf7ce35f56940` | `diag-root-original-source-receipt.json` |

All have inspected exact locks, no sorry and standard axioms only.
The earlier triangular layer, square, two-/three-cup, marker, common-end,
sharp predecessor R2 and reflection results have exact checks, fixtures
and commits in `MATHEMATICAL-HANDOFF-ARCHIVE-0450.md`. Each statement was
registered through es node add, each body proved on its own node branch,
and each accepted result retained an original-source receipt.

## Exact external hypotheses and integration boundary

The diagonal lower gate assumes:

```lean
(hblocks : ∀ k, 5 ≤ k → DiagonalCupBlocksForce4kk k)
(hbaek : ∀ {n k : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)},
  3 ≤ k → OneChangeOn χ s → ¬ContainsCapSet χ s 4 →
  ¬ContainsStrongPolygonSet χ s k → s.card ≤ 1 + Nat.choose (k - 1) 2)
{k : ℕ} (hk : 6 ≤ k) : SingletonLowerPascalTailGate 5 k k
```

These match the exact R20/R21 source shapes read in the integration
worktree. Their proofs were not imported or cherry-picked. Inputs are
uniform over every colouring, so the upper diagonal dual needs the same
hypotheses, without a separate colour-dual theorem assumption. Preserve
R21 branches and the fixed baseline; coordinator integration is the next
consumer action after this run's proof review.

## Failures, limits and code review

No audited mathematical case was refuted or dropped. The documented Lean
failures were elaboration issues: subset binder naming, endpoint namespace,
Pascal summand commutativity, missing exfalso for contradictory turn
equalities, and an unrestricted nlinarith hitting 200000 heartbeats.
Using nlinarith only on the exact cardinal bounds fixed the root proof
without changing its statement or case coverage. A guarded proof-body
delimiter check refused an off-by-one replacement before mutation.
All compiler failures and corrections are in es journal and the source-N
logs under this run directory.

The first predecessor full-check reservation was too small for nested
extraction; the unchanged source passed with the explicit 28G full path.
Full checks took 1930s (predecessor) and 1284.1s (diagonal), with peaks
5630/5670MiB. Module scanning progress does not measure the later record
presentation phase; checkpoint estimates used matched whole-run timings.
The diagonal full check completed before a checkpoint decision was needed.
Callbacks remain unverified, so live job reporting must stay in this thread.

No Python or shell workflow script was added. The only ad hoc Lean run
artifact is PredGateAxiomInspection.lean, four #check/#print lines without
new statements. Inline jobs use existing es commands and isolated git
operations. No recurring computational algorithm currently needs promotion.
`MATHEMATICAL-REVIEW.md` is a preliminary Sol interpretation. Separate
lower mathematical and code/maintenance review windows are now complete
as named above. Final mathematical and code reviews are complete in
`FINAL-MATHEMATICAL-REVIEW.md` and `FINAL-CODE-MAINTENANCE-REVIEW.md`.
The final inventory is artifact
`7e9f3dcf3b9b3360c3f59a039fc9d2675695d90f05b21fbc16bc20ad4879be9d`.
The scheduled consolidation refresh is artifact
`5a7975c61791c45dbdc3ac0663d00d2d29be8908cd0b86e1ef3e8c5a97d256e1`,
job `20261003-071011-e127fd`, terminal success0.4s/42MiB. Its complete
inventory comparison confirms unchanged tracked code and artifact scripts;
the sole new inline command is the existing inventory refresh. No new code
requires promotion. The snapshot's self-job pending entry is now terminal.
A capture/commit ordering mistake was logged: the commit was queued before
the bounded capture wait had returned terminal success. Both terminal
outputs and exact fixture parent/type/source hashes were then inspected
before release; no source changed after acceptance. No theorem credit was
inferred from an empty intermediate output. Do not claim an Astra review:
delegation was forbidden for this run.

## Resume and deadline discipline

On resume, inspect es status, the relevant journal and this handoff first.
There is no pending proof job or active claim. All gate and supporting
claims are released CLOSED. Preserve original scaffold
branches and R21 branches; no merge, push, reset or cherry-pick.
Consolidation starts 2026-10-03T11:08:33.055867Z. Research ends
2026-10-03T11:38:33.055867Z. Do not mark the native goal complete before
that instant. Reconcile all-in usage, including failed/setup/review work;
no matched savings comparison has been established.
Research and proof work completed early; bounded standby preserved the
user's fixed deadline. Its recorded usage is included in the handoff
accounting window, with late response reconciliation still required at
the final report. Finalization is permitted through12:08:33.055867Z.

Finalization11:40Z: the host paused admission at the original deadline.
Fresh status remains nonstale with no problems, the worktree is clean,
and all four saved original-source receipts were re-inspected: CLOSED,
matching exact locks, no sorry and standard axioms only. No new research,
compiler check or job was admitted. Handoff accounting window
window-b838ed868e1b4c3e is complete; handoff-accounting-final.json is its
factual record. usage-final-report.json preserves the reconciled snapshot
through11:38:43Z, and usage-late-finalization.json includes later recorded
finalization responses. The final response itself may lag these snapshots.
No usage limit or deadline was reset, and no savings claim is made.
The exact approved proof obligations are fulfilled; the compact report
is supported by the checks, commits and source/fixture review above.
