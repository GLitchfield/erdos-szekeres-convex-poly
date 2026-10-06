# R16 Part 1 registration and weakening

Authorized main base: `5847e155fa613d4d2311eaee86b4b094f630e9a4`.
One node per independent branch; no merge/push.

N_ends registration committed `22d8137334ce31f2175aee57f29ff79d92fc1f36`, exact
parent5847e155. Type hash32c6d22aba01da18, compiling conjecture, sorry=true.
Thin registration20261001-012853-0ea1c5 passed; registered falsifier
20261001-013208-804918 passed,5976roots/127472explicit-T audits/98688selector cuts,
0violations. Targeted check20261001-013617-679625 passed; immutable receipt
99837175bd83963572ec457b7b8276546fe74708f3b3104c56805f54bb6df62f (`CHECK.n-ends.json`).
Commit job20261001-014135-4acb01 passed, staged exactly7 node files.
Source/falsifier snapshots `N-ends.registered.lean`, `N-ends.falsifier.py`.
Weakening registered and closed on its independent main-based branch,
commitcd1e05ce4528237b2cae5d120e310f044bcacdaf (parent5847e155),
job20261001-022026-a9d34d. Locked type6ecc666112a7ba4e, sorry=false,
nonstandard_axioms=[], standard axioms propext/Classical.choice/Quot.sound.
Targeted check20261001-020205-1f077b passed; immutable receipt
991be85828438d7ff956f52180772f70f96d8be9f55630edc52fde8964383315,
build3.06194s,587MiB. CHECK.weakening.json, Weakening.closed.lean and
RECEIPT.commit-weakening.json preserve the result. Closed fixture
2424d496c068f5b790e6b772d06981e15bd82a51ce465dfbe4c6b5a8bed2a450.
The proof first reduces local lets, then discards candidate membership.
Part1 is complete; N_ends and N_root themselves remain open.

The first weakening body failed: intro introduced the leading let context
instead of the run-count proof. FAIL.weakening-let-intro.json and body-v1
preserve that compiler failure; dsimp only repaired it without a statement edit.
Registration20261001-014714-60c395 passed93.5s,2534MiB after a4GiB refusal
of the nested20GiB dependency fallback. The later check waited for admission.
Conservative resources reconciliation20261001-021330-3d57cb released no
leases; both were active R15 leases, not stale locks on this worktree.
Guarded dispatcher20261001-021819-04f641 returned the terminal compiler
failure; its timing does not establish that it caused check admission.

N_ends retains every N_root hypothesis and its explicit-T singleton cut value.
The witness must additionally belong to four (possibly repeated) child positions:
first child, first run end, last run start, last child. The run-start filter is
the existing `numRuns` predecessor test; the end filter explicitly tests word
length because `letterAt` defaults to child outside the word.
With at least two runs, all four entries are real endpoints of the two extreme
runs. `N-ends.signature.txt` records the exact proposed statement.

`Weakening.signature.txt` is the pointwise conditional from this selector claim
to N_root; `Weakening.body.txt` simply discards membership in the four candidates.
It takes the selector conclusion as a hypothesis and uses no open theorem in its
proof, so it can be independently closed on its own main-based branch.
Composition with a future proof of N_ends is by supplying its instance as `hends`.

Before statement/proof writing, `es search` queries
`singleton cut one level root extreme first last run`,
`run boundary first last child`, and
`singleton attainment conditional extreme selector weakening` found no existing
extreme selector or weakening. The second query found the known general end-cut
counterexample and its open restrictions. Search for
`ctx_single_level_limits_exact` located the closed explicit one-level formulas.
These are research-search citations for any eventual PR; no PR is authorized.

Falsifier reuses `research.singleton-cuts`, `research.context-part` and
`research.compiled-context-bound`, after `es lib search/show`. It enumerates all
singleton choices but restricts its attaining witness to the exact four-candidate
set, and audits each leaf against its explicit threshold. All evaluations remain
diagnostic `context-bound-zero-children-c-v1`, with no theorem credit.
Default scope: 2..4 runs, lengths 1..2, at most 4 children, one marker per gap,
optional single end markers, both sides; k5 all globals 1..5, k6 globals (5,5)
and (6,6), all legal m. General repeated markers and unbounded parameters remain
outside this finite falsifier scope.

Cold timing `20261001-010658-86caab`: longest four-child/four-run k6 root,
0.07699s and 51MiB, 32 cuts/explicit leaf audits, 16 selected cuts. Evidence
`n-ends-timing.json`. Falsifier executable bit set before submission.
Registration job `20261001-010647-2c6f98` refused before Lean: nested dependency
guard requested 20GiB above the 4GiB parent. Module kept; no lock written.
Identical registration20261001-010756-d2fff1 used20GiB but hit the harness
default1200s guard,0modules built,20480MiB peak: omitted import selected the
large ErdosSzekeres root. It supplied no theorem result. Corrected thin
registration20261001-012853-0ea1c5 retained exactly the statement and passed;
no chosen-time cancellation or full extraction.

Part 2 must distinguish exactly one unmarked word end from neither-marked ends.
Existing coordinator diagnostic witness (2,3,5,1), `SSLSS`, has root bound 1 and
only positions 1,3 attaining; global endpoints 0,4 fail. This prevents an
overbroad exposed-global-end lemma, but does not refute N_ends.
