# R17 — Done (narrowing), active verification checkpoint

Checkpoint: 2026-10-01 20:02 UTC. This is the single authorized R17 window,
using only gpt-6.1-sol at xhigh, without delegation. Research ends
2026-10-02 01:57:51 UTC; consolidation begins 01:27:51 UTC and finalization
ends by 02:27:51 UTC. The native goal remains active until that deadline.

X now composes five strictly narrower registered, finite-tested inputs.
Three inputs are closed and exactly two remain open. X's original statement
and locked type `a68960f119792789` are unchanged. This meets Done (narrowing);
it does not close X or the Erdős–Szekeres conjecture.

The composition is commit `68e415c5b428759b4a06fcda816410150f094bf6`, on
`node/CtxOneLevelRootSingletonBaseExchangeR17`, from the approved base
`5847e155fa613d4d2311eaee86b4b094f630e9a4`. Original targeted job
`20261001-140317-82ff5c` passed: 279.2 seconds and 15,228 MiB peak for the
whole guarded 20G scope. Its inner cached build time is not the scope peak.
Receipt: `78339ca9f2416a94afddc5bd1051446535907c8388194abc22eb35716e226542`.
The receipt identifies precisely the inside-pair and outside-multirun
blockers, with expected transitive `sorryAx`; there is no direct proof hole
in the composition.

Seven independent closed theorem commits passed isolated complete-parent
and original-source targeted Lean checks, with unchanged registered types,
no proof holes, and only standard axioms:

| Result | Commit | Original targeted job |
|---|---|---|
| Outside-pair explicit singleton leaf equality | f3c21cb85f0eccc1a21ad2d5b1be4583f44e26d8 | 20261001-101508-cb8b72 |
| Inside-pair explicit singleton leaf monotonicity, with another child | dff190112c32d08f2648a74d2aa6b397cde08b9b | 20261001-103958-ef6757 |
| Raw outside-pair one-run complement equality | 9905f302ac33e05a31abda1a3cba3445adcc5266 | 20261001-112811-271572 |
| Full X on unit global axes | b55ab7cbe98190f87d2f583c337d7a36180b2c76 | 20261001-114533-4b9cdf |
| Full X when the old chosen axis is at most two | fac5fc67d0d3417ee0de71dfca46f9986d4570a0 | 20261001-124644-6cb79a |
| Full X outside the pair with a one-run source complement | b2584679e9ec6723983084fca19d1e5a2c0a161b | 20261001-130242-35fceb |
| Exact obstruction to a leaf-only rescue orientation | 3b8a2dce55b334284f9908183eb79df833d6b723 | 20261001-143341-7b14b1 |

Every commit has approved parent 5847e155; each is on its own node branch.
[ACCEPTED-INVENTORY.md](ACCEPTED-INVENTORY.md) and the per-node REVIEW and
RECEIPT files contain locked hashes, proof bodies, memory measurements,
finite scopes, and commit receipts.

The two remaining registered full-sum obligations require positive axes
and old chosen axis at least three:

| Open input | Commit | Finite actual-domain check | Original targeted check |
|---|---|---|---|
| Inside the doubled pair | ea862da6270624d4b3b7897aa3ab647eb42f62f5 | 20261001-130751-ae58e4: 55,744 cuts passed | 20261001-131902-9af698 |
| Outside the pair, source complement with at least two runs | 80b86c74ce2fc2267c252a0decc6177bb71fa0cd | 20261001-132715-d255ee: 60,032 cuts passed | 20261001-133838-e604d0 |

These checks compile the registered open statements and retain their expected
proof holes. They supply no closed-theorem credit. Both claims were released
partial. The remaining mathematical step is a joint legal side/coupling
allocation for the singleton threshold plus the complement bound.

The original-family classifier `20261001-100200-6e833a` checked 516,096
source cuts at k=6: 276,480 outside and 239,616 inside, with no X failure.
Of 10,084 cases needing a different target cut, 40 are outside and 10,044
inside. Every outside leaf audit agrees. One retained outside witness loses
13 to 10 at the same cut entirely through the complement, 12 to 9; other
legal cuts restore 13.

Leaf and global parameters alone do not supply a common rescue orientation.
The new kernel certificate checks two a=4,u=5,k=6,m=1 inside roots with
source value 6 and matching source/shortened leaf cap 3, cup 1. Root A has a
Lower/2 rescue and every legal Upper cut below 6; root B has an Upper/2 rescue
and every legal Lower cut below 6. All four target couplings are certified.
This refutes that selector strategy, while both witnesses satisfy X.
Its original check passed in 5.305 seconds, 825 MiB under 4G; locked type
`5bf8d6c3f662df4d`, receipt
`22500f3b5287b3fd98d269025d69be6f301f1bdd6659851fcbbc60f79930b243`.

The compressed root-region lookup recovery `20261001-132926-e3125f`
completed successfully: 516,096 cuts, 737,280 explicit threshold audits,
313,344 finite cells, zero selected-rule failures or empty intersections,
2,821.8 seconds, 423 MiB under 2G. Stream roundtrip, selected-rule membership
and hashes were verified. Scope: k=6, all axes 1..6, m=1..4, two or three
runs of lengths 1 or 2, at most five children. This is a finite selector
table, without an unbounded or Lean-proved selector claim.

Original job `20261001-122744-73c012` reached the cut counts but failed
during final cell output by 2G OOM. Its missing final artifact remains a
failure. Bounded per-axis streaming was first validated by
`20261001-132623-a306a6`; the successful rerun preserves the same mathematical
candidate and cap. The stronger chosen-three every-child-best formula also
failed: `20261001-123641-f0a552` retained 60 failures in 460 checks. It is
not assumed or registered, and none of those is an X counterexample.

Integration requires the five dependency nodes together with X. The X
commit contains five tracked node/registry files; the assembled workspace
also holds eleven exact untracked dependency modules, the shared falsifier
and its five finite receipts. [MANIFEST.X-inputs.json](MANIFEST.X-inputs.json)
and [DEPENDENCIES.X-composition.json](DEPENDENCIES.X-composition.json) record
the independent commits and hashes. The parent alone on 5847 is not a
standalone build. Archive restoration `20261001-144421-10588d` passed exact
comparison. Preserve this run directory: requested ignored artifact includes
were omitted by the harness's Git-status filter. No harness repair or
force-staging was performed.

Additional verification at this checkpoint:

- `20261001-140131-0fc299`: six pinned longer-word timing roots, 2G. The first
  seven-child row completed in4,474.0566 seconds:280cuts/296leaf audits,
  all280features untrained, two default-same rule failures and no X failure.
  Word SSSS,1L,SSS at a=u=k6,m1,oldLower,ends0/0: source Upper/4 value15
  shortens to12 at y0,p1,q0 and y6,p6,q6. Upper1/2/3 or Lower2/3/4 restore15.
  This rejects that lookup default on new features; it does not refute X
  or the compressed feature scheme. Row2/final manifest remain pending.
  A74.6-minute heavy row does not justify a wider seven-child family.
- `20261001-144835-bcb692`: restored-assembly original targeted X check
  passed55.9s/2345MiB under20G. Locked type and exactly two expected blockers
  verified from receipt48565a4ad2545a783cf862a2616b9c01db34b34856dbfb06c66173959f3a91c6.
- `20261001-155851-155460`: finite ordered case-predicate audit passed
  516096cuts/22MiB under1G. The first145327-c327fc failed127 before execution
  because python was absent; the unchanged script succeeded with python3.
  Ordered counts unit157696,chosen2 71680,inside133120,outside-one10240,
  outside-multi143360 sum to the original cut total. It computes no bounds.
- `20261001-150923-099d84`: one five-child/four-run boundary completed
  40cuts/72leaf audits/0.785s under2G,286MiB scope peak, then failed its
  inherited six-row completion assertion. Original rc1 and missing final
  remain preserved. Verification160000-ab08bb writes a distinct recovered
  manifest without repeating bounds:2untrained-default failures,0X violations.
  No larger four-run sweep has been admitted.
- `20261001-155409-694b0e`: SSS,1U,SS at a=u5,k6,m1,oldUpper completed
  120cuts/136leaf audits/0.624s under2G,270MiB scope peak. The retained
  outside feature guard passed; all6known-feature cuts passed. Two untrained
  default failures remain,0X violations/0old-training intersection failures.
  Its rc2 reports a completed negative default candidate, not an execution
  failure or X refutation. Source/streams were verified160000-ab08bb.
- Old-fixture geometry145457-a0cd4d and155904-f1794e failed before Lean
  (absent source, then pre-proof capture mismatch); recapture was unknown-node
  in X's registry. Proper new-node registration160147-dc4382 is queued on
  node/CtxInsidePairLeafThresholdMonoOfTwoRuns from approved5847. This is
  not an eighth closed result. Fresh generated X index/old closed source are
  preserved;11 untracked dependency copies and X archive remain unchanged.
- Shared shape builder160611-368724 passed:176restricted words include
  all72original words and104extra. Six representative five-child timings
  160645-7464cd are queued; the proposed fixed-axis416-root extension is
  awaiting their measured receipt. It is not completed evidence.
- Retained-rescue tradeoff audit160934-d3ce85 is queued under1G; it reads
  pinned old records and derives leaf gain/complement loss without bounds.
  No results or new proof credit are claimed before terminal inspection.

20:15UTC update: registration160147-dc4382 succeeded, new two-run leaf
typeca8c8fa7a2e9b812; dependency refresh161218-97afe3 is queued before claim
and proof capture. It remains open. Six representative timings160645-7464cd
completed640cuts/752audits/4.208s/276MiB2G,10untrained-default failures,
0X violations, complete outputs. Fixed-axis extra416root probe161424-ba2af1
is now queued after that timing/review; no completed extension claim yet.
Retained tradeoff audit160934-d3ce85 passed:9488inside zero leaf gain,
556inside gains1/2,40outside zero; complement drop exceeds gain by the exact
same-cut deficit. Full retained witnesses, no new bounds or kernel credit.

20:23UTC fixed-axis extension161424-ba2af1 completed:416roots/32256cuts/
41728T audits,365.5s scope/361.9789s mathematics/420MiB2G,0OOM/no missing
outputs. All156old trained cuts pass;600untrained-default failures and0X
violations/0old-cell conflicts. All32768merged compressed cells are nonempty
for46592old+new cuts. Saved streams/hashes/counts checked. Finite scope:
a=u5,k6,m1..4,176restricted shape words including72original; no universal
or Lean selector claim. Node refresh161218-97afe3 and pinned long timing
140131-0fc299 remain pending. Release X partial during final consolidation
before01:59:28UTC lease expiry.
20:29UTC: max-axis6 representative timing162759-0d30d4 is queued2G;
no all-axis probe admitted. Own pending140131-0fc299/161218-97afe3/
162759-0d30d4. Read-only20:25 snapshot shows20G refresh fits40G with14G
live caps and44.22GiB available; dispatch delay cause remains unestablished.
No worker, reservation, configuration or other-job control.

Shared database lock and moving-base failures were preserved and recovered
without primary checkout repair, worker/configuration changes, duplicate
submission or other-agent job control. Both 4G/8G extraction-cap refusals are
retained as operational failures. No merge, push, full extraction, existing
statement edit, custom axiom, native_decide or second trial occurred.

Sol reviewed own candidate scripts, falsifier and inline callers; shared
parts, root enumeration, limits and evaluators were reused. Independent
Astra review is forbidden by the native model/delegation contract and is
deferred. The immutable review checkpoint
`b5940b86fd833063afa1c5d5dfb387e84eec6fafb6a65c1f53cc684d75561803`
records seven accepted proof receipts and the four pending jobs. Its 162
changed-tracked entries compare the initial old 433d1b3 checkout to the
current branch, rather than identifying R17-authored code.

Continue verification and handoff in this same window. At the fixed
deadline, inspect all terminal outputs, record any incomplete jobs, release
X partial, import final usage and refresh the run review. The safest next
research action is the inside-pair full-sum allocation or the outside
multirun allocation, using the closed leaf facts and retained exact rescue
witnesses. [MATHEMATICAL-HANDOFF.md](MATHEMATICAL-HANDOFF.md) gives their
statements and the evidence limits.
