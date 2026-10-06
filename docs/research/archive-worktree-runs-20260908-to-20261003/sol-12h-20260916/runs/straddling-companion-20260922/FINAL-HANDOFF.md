# Exact actual-marker companion bound: final handoff

## Result

The node
`ErdosSzekeres.ctx_two_actual_marker_opposite_between_companion_eleven_bound`
is closed on branch
`node/CtxTwoActualMarkerOppositeBetweenCompanionElevenBound`.

The theorem is in
`ESBlueprint/B/CtxTwoActualMarkerOppositeBetweenCompanionElevenBound.lean`.
Its source SHA-256 is
`656ecc22333c57d8e54e73a7ce75359e09b9207c88956fef2f6db3c657a2963a`
and its extracted type hash is `921f91ce0bd5254e`.

Commits:

- `ac5a9ba7556b5f5d0eb42a2c7458d18528083a01` — theorem, root import,
  and statement lock.
- `21b999f5f6041f69c0d359ed421be789688d17b6` — fresh generated frontier
  metadata.

## Requirement audit

| Requirement | Evidence | Outcome |
| --- | --- | --- |
| Actual complementary cut | The theorem defines `B := σ.part (σ.childPositions.filter (· ∉ keep)) t n`; lines 37–43 derive the physical marker from membership in the kept part. | Proved |
| `n = 1`, physical opposite-axis marker, and `maximumAt 1 = 1` | Hypothesis `hn : n = 1`; lines 40–50 prove `p ∈ B.extPositions 1`, `B.maximumAt 1 = 1`, and `1 ∈ B.levels`; lines 51–53 identify the marker side as `t`. Lines 215–222 transport and rewrite maximum one in the displayed boundary budget. After that rewrite, however, the minimum is bounded through its left branch using the opposite global parameter, so maximum one is retained and used syntactically but is not logically necessary for the stronger inequality. | Proved; logical dependence removed by stronger theorem |
| Marker strictly between the two chosen markers, both orientations | The exact disjunction is a theorem hypothesis and is split at line 293. Both orientation branches prove complementary `5 + 6` pair-support bounds. | Proved |
| Every fuel approximation and full recursive bound | The conclusion contains both `∀ fuel, boundFuel fuel B ≤ 11` and `B.bound ≤ 11`; lines 440–445 close both. | Proved |
| No missing low/high pair-cardinality-sum assumption | There is no input pair-cardinality hypothesis. Lines 292–426 derive a new spatial pair-cardinality sum internally from the ordered marker positions. | Proved |
| Preserve high witness and the documented residual structure | The exact actual-cut interface retains `high`, `hhighmem`, `hhigh`, `hchosen`, and `hbetween`. The proof is strictly stronger: it does not require the active-low-straddling, overlap-three, or oriented-high-support consequences. Guarded job `20260922-163320-0d704a` instantiates the full established residual-package theorem and the direct bound together under the identical inputs. | Subsumed by stronger theorem and integration-checked |
| Real coupled invariant rather than finite-probe evidence | Child runs are colored by physical position relative to `p`; lines 430–437 apply the actual-marker run decomposition. The two boundary-rank unions are bounded at lines 254–268, and the coupled spatial `5 + 6` budget is proved at lines 292–426. | Proved in Lean |
| No arbitrary classification | The only classification is the canonical spatial split `q < p` versus `p < q`; run constancy follows because the actual marker cannot be a child of `B`. | Proved in Lean |

The crucial semantic point is that `levelsOn _ 1` contains indexed levels
strictly below one. Positive indexing makes that history empty, so both
spatial prunings are boundary-ready. The chosen-axis markers then confine rank
pairs to regions of cardinalities five and six (swapped in the reverse
orientation).

## Formal receipts

- Durable finalization operation `op-5bed17e7e0194734`: succeeded.
- Proof fixture `b1d78c62fc05dc8b0207462d16a5ff349940a02e00375b5c6d4c25935bea6279`;
  accepted declaration-body artifact
  `7f55345fad7357214482e7d8971ef47c3946e4c3c1efcb50c868cb1d788ac221`;
  search receipt
  `723b75472cdd38d74a085a0d3839783a6009cf0b0ca8e7fbdbd6948c5aff0222`.
- Candidate proof job `20260922-154233-b858aa`: accepted; only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Original-source check job `20260922-154245-9dd678`: closed, no `sorry`,
  matching type hash.
- Corrected full extraction job `20260922-155452-c0b02c`: 319 nodes,
  12,910 declarations, zero problems, frontier tree
  `c3a185864f2c7d40`.
- Audit/layer job `20260922-160342-9a1b66`: 336 declarations audited,
  zero failures, zero layer violations.
- Review job `20260922-160353-e1fd88`: accepted source hash
  `656ecc22333c57d8e54e73a7ce75359e09b9207c88956fef2f6db3c657a2963a`.
- Post-release extraction job `20260922-160543-f360c0`: refreshed generated
  metadata with no live claim; tree `623069f1721345ab`.
- Clean post-commit `es extract --check` job `20260922-161519-9dad91`:
  succeeded on the committed tree, 319 nodes and 12,910 declarations.
- Fresh clean-tree fixture
  `5b35e1407d3ddc36ab6d1e82d834e40ce164dab18c1a78b389aba4f72bd362dd`
  and replay operation `op-7c189cde09f24d7e` / job
  `20260922-162544-2de07d`: accepted the unchanged body artifact
  `7f55345fad7357214482e7d8971ef47c3946e4c3c1efcb50c868cb1d788ac221`
  in the isolated no-network checker. It reproduced source hash
  `656ecc22333c57d8e54e73a7ce75359e09b9207c88956fef2f6db3c657a2963a`,
  type hash `921f91ce0bd5254e`, and exactly the three standard axioms.
- Exact consumer-interface smoke job `20260922-161918-554d20`: compiled
  `ConsumerInterfaceSmoke.lean`, whose statement is the complete old
  `ctx_two_actual_marker_opposite_between_eleven_or_active_low_straddles`
  interface and whose proof selects the direct-bound disjunct using the new
  theorem. The checked file's SHA-256 is
  `b46e5e9e20b8191bfc6e994f05f19fcbe1b2c11527f5dcc80ae4dab7b32b40f8`.
  This verifies the handoff at Lean elaboration level, not just by comparing
  printed types.
- Exact residual-coverage smoke job `20260922-163320-0d704a`: compiled
  `ExactResidualCoverageSmoke.lean`, SHA-256
  `9a32142572c6cb283f59f55e156854911128484bdd29f5374edc7dedb4557977`.
  Under the same complete input list, it first instantiates
  `ctx_two_actual_marker_opposite_between_intersection_three_and_oriented_high_support`
  (the package containing the active low straddle, overlap-three, and oriented
  high-support alternatives) and then closes every fuel and the full bound by
  the new theorem. The successful compiler log is empty and the source contains
  no `sorry`, `admit`, `native_decide`, axiom declaration, or `unsafe` command.
- Independent integrity pass at `2026-09-22T20:35:56Z`: the working-tree and
  committed theorem files both hash to `656ecc22333c57d8e54e73a7ce75359e09b9207c88956fef2f6db3c657a2963a`;
  `ESBlueprint.lean` imports the module; `harness/nodes.json` and
  `harness/statements.lock` both record type hash `921f91ce0bd5254e`; and a
  forbidden-token scan of the theorem plus both smoke files was empty. Direct
  decoding of stage receipt `260ea114887c1860262de49745f61b3383db7bb0396c6dc9bbf08ba672d0ab7b`
  reproduced the body, fixture, source/type hashes, isolation mode, and the
  three standard axioms reported above.

The fixture was captured after the proof had already been inserted into the
new module, so the final review's fixture-to-source diff artifact is empty.
This is not treated as independent change evidence: theorem credit comes from
the candidate audit, rebuilt original-source check, full extraction/audits,
clean-tree extraction check, and the committed baseline-to-branch Git diff.

The first full-extraction attempt, `20260922-154357-36521d`, was deliberately
cancelled after detecting an orphan uppercase lock key from an initial naming
mistake. That key was removed before the successful extraction and is absent
from both commits.

## Diagnostic evidence

The bounded corrected probe in job `20260922-153442-2d1f86` found 780
signatures and 412 mixed cases at levels 3 / `s_max = 4`; all 72 structural
straddling signatures had the expected high-pair containment. This was used
only as corroboration. The Lean proof does not invoke or trust the probe.
The exact finite semantics were `context-bound-zero-children-v1`, fixed
`(a,u,k) = (5,5,6)`, three indexed levels, `s_max = 4`, fresh pruning barrier
level four, and `all_chosen_maxima = false`. The reused reviewed probe source
was
`runs/sol-12h-20260918/review/probe_companion_group_charges_corrected.py`,
SHA-256
`ab793ce2dbcc3976cf2b40d83d91629de6b57ff8818353141fee8bf826fb777f`.
The larger `s_max = 5` diagnostic (`20260922-151027-6917a0`) timed out and
produced no evidence.

## Failed mechanisms and repairs

- The inherited low/high pair-cardinality-sum route still lacked a proof of
  `|pairs 0| + |pairs 1| ≤ 11`. It was not assumed or hidden in a wrapper.
  The run logged an explicit method change to the spatial child-run split at
  the physical marker.
- An apparent obstruction from arbitrary opposite-axis history was resolved,
  not assumed away: inspection of `levelsOn` showed that `levelsOn _ 1`
  contains only indexed levels strictly below one and is therefore empty under
  positive indexing.
- The `s_max = 5` corrected diagnostic exhausted its 20-minute guard with an
  empty output. It was not rerun unchanged; the smaller `s_max = 4` run is
  reported with its finite domain above.
- First proof compile job `20260922-153716-caf631` contained Lean type errors.
  Its shell pipeline lacked `pipefail`, so the recorded outer return code was
  zero; `build-spatial-v1.log` records the actual inner failure. The proof was
  repaired before any theorem credit was claimed.
- Recompile job `20260922-153807-a0764d` built the exact module successfully,
  then a redundant nested 30 GiB stage was refused under its 20 GiB outer cap.
  The later pipefail-protected targeted check, full extraction, audits, and
  clean-tree check are the authoritative gates.
- The first `es node add` used an uppercase declaration name. The corrected
  lowercase add overwrote the same module but left an orphan uppercase lock
  key. The first full-extraction attempt was deliberately cancelled, that
  orphan was removed, and all successful extraction/check receipts postdate
  the cleanup.
- First consumer smoke job `20260922-161852-23bd76` exposed dependent `match`
  normalization in the old wrapper's elaborated binders. Explicit case
  normalization produced the successful exact-interface job
  `20260922-161918-554d20`.
- A first clean-tree replay attempt, operation `op-cf28559718344a24` / job
  `20260922-162509-e43589`, correctly rejected the original fixture before
  compiling because finalization had subsequently regenerated
  `harness/statements.lock`. A fixture freshly pinned to the committed tree
  produced the successful replay above; both attempts resolved to the same
  proof-body artifact.
- The first three versions of the run-local residual-coverage smoke
  (`20260922-163031-33751a`, `20260922-163116-d4fa16`, and
  `20260922-163225-e8d297`) exposed, respectively, one outer-parenthesis error
  and two dependent-match normalization mismatches in the older package's
  elaborated type. The final smoke case-splits both sides before instantiating
  that package; job `20260922-163320-0d704a` is the authoritative success.

## Placement and scope

The theorem covers exactly the actual complementary part with `n = 1` when
the transported physical marker satisfies either `x < p < y` or `y < p < x`.
It handles both orientations, global parameters at most five (hence the exact
five/five residual), arbitrary child counts, additional history, inactive
children, unused levels, and independent fuel.

It does **not** prove that every remaining legal cut has a between-marker
point. Exterior and active-separated cases were already available before this
run; the broader consumer still needs to assemble placement cases. No claim is
made here about that separate assembly theorem.

## Code, command, and pending-job inventory

- Tracked changes are only the theorem/root/lock commit and generated frontier
  metadata commit listed above. No tracked Python, workflow helper, generated
  certificate, or harness implementation changed.
- Run-local code consists of `ConsumerInterfaceSmoke.lean` and
  `ExactResidualCoverageSmoke.lean`, two one-off elaboration checks. They
  introduce no reusable algorithm and were not promoted. Other run-local files
  are the frozen brief, submission/host state, diagnostic JSON, handoff, and
  command logs.
- Long/Lean inline commands are durably recoverable from these job records:
  corrected probes `20260922-151027-6917a0` and
  `20260922-153442-2d1f86`; proof builds `20260922-153716-caf631` and
  `20260922-153807-a0764d`; targeted check `20260922-153941-afa1a0`;
  node-finish stages `20260922-154233-b858aa`,
  `20260922-154245-9dd678`, `20260922-155452-c0b02c`,
  `20260922-160342-9a1b66`, and `20260922-160353-e1fd88`; metadata refresh
  and clean check `20260922-160543-f360c0` and
  `20260922-161519-9dad91`; consumer checks
  `20260922-161852-23bd76` and `20260922-161918-554d20`; clean-tree proof
  replay jobs `20260922-162509-e43589` and `20260922-162544-2de07d`; commits
  `20260922-160425-6bcbf4` and `20260922-161434-a16059`; residual-coverage
  smoke iterations `20260922-163031-33751a`, `20260922-163116-d4fa16`,
  `20260922-163225-e8d297`, and `20260922-163320-0d704a`.
- No mathematical job is queued, starting, or running. The only live job is
  outer host `20260922-150750-451bdb`, which must remain live until the native
  deadline and final reporting turn.

## Usage windows

- Sol research/finalization: `window-160337a09c374681`, complete with one
  accepted result; 268 recorded responses, 106,197 output tokens, 46,404
  reasoning-output tokens, six linked jobs, 1,229.9 worker-seconds, and peak
  8,312 MiB.
- Final mathematical review: `window-c596722d5dbf4fbe`, complete with zero new
  accepted results; eight responses, 2,470 output tokens, and 879
  reasoning-output tokens.
- Code/library maintenance: `window-a84f6b464603421c`, complete with zero new
  accepted results; three responses, 1,071 output tokens, and 544
  reasoning-output tokens. The review found no tracked script change and no
  promotion candidate.
- Clean-branch proof replay: `window-0cd61f5699624d5e`, complete with one
  accepted replay, two linked jobs (the stale-fixture rejection and the fresh
  fixture acceptance), 11.0 worker-seconds, and peak 2,711 MiB. It has no
  separately attributable model-response snapshot because those responses
  were already assigned to the earlier explicit windows.
- The later exact-residual coverage audit added four guarded scratch-compile
  jobs totaling 13.8 worker-seconds with peak 1,374 MiB. They are individually
  journaled above but are not attached to another explicit usage window;
  response usage was already assigned to the prior windows.
- All three windows have reconciled recorded snapshots. Coordinator setup/root
  monitoring and terminal host accounting remain owned by the outer host/root
  workflow rather than being reassigned to a Sol result window.

## Remaining risk and next action

There is no known proof or repository-state risk for this node. The broader
consumer `ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end` remains
open because its surrounding case assembly is a different node. Its actual
opposite-axis, `n = 1`, between-marker branch should call the new theorem
directly. This call was compiled against the exact old residual-wrapper
interface in `ConsumerInterfaceSmoke.lean`. The older low/high
pair-cardinality, active-straddle, collision, and overlap residual chain is
unnecessary for that branch.
