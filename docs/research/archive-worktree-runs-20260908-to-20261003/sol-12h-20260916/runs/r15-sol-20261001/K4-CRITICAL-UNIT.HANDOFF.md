# R15 critical κ4 necessary unit-history reduction

ACCEPTED first proof attempt, typeb8c097958adbdaaa, committed 4e59d48e8654f46ae5b30cbf087f43d652096297.
Commit job20261001-080101-d0a693 terminal0, exactly own node files, six
dependency overlays excluded. Full CHECK.k4-critical-unit-v1.json SHA256
7db2cecc6e0935b39ff37e8b757a3efcf2e6b275f0de5477122d45ae3ed052c1:
closed/standard axioms/noSorry/locked/no blockers/errors, targeted+incremental
true. Check20261001-075853-7af218 DONE0,108.7s2410MiB/noOOM/no budget exceeded,
build3.138845682144165s. Source K4-CRITICAL-UNIT.candidate-v1.txt SHA256
b25e7da55a609a375966a97145eab0c1ff32970898cdd4827cf7de54246b5a14.
Registration20261001-075145-df287e DONE0/326.3s2489MiB; normal ready claim and
capture94fbba929b919cd95aa0738d9a8e8a8defc2794f643895090af1223258b22f23 preceded proof.
Branch node/CtxKFourCriticalPartitionForcesUnitSiblingMaxima from main,
created by guarded terminal job075116-3adbcf. Node
ctx_k_four_critical_partition_forces_unit_sibling_maxima.

Exact obligation: positive actual external labels, k=4, every declared source
maximum >=1, an actual kept child p and actual omitted child r, and legal
coupling d. For either orientation, paired value>2 implies every declared
source maximum=1. Arbitrary raw contexts, unused indexed levels, keep lists
and globals; no well-formedness/run/interval/interleaving premise.

Proof plan: for each indexed source N, its positive maximum and κ4 imply
near-saturation. Apply the closed old/fresh estimate25 to both proper parts;
legal κ4 coupling ensures both fresh maxima>=1=k-3. Paired value>2 and each
part<=2 force both parts positive. Apply the positive-part history ceiling24
on N's axis and combine with its source positivity to obtain maximumAt N=1.
For reversed orientation exchange the two parts and commute the sum. Empty
source levels give a vacuous conclusion; no source-level witness is assumed.

Dependencies are separate closed commits24 fc33578a09d63832a3d1d6a00345d2b910eb561a
and25 afb36431268c2e326f2f443846205346b3c0f85e, with their dependency DAG
5/9/10/11 restored exactly from accepted text archives. Node-add writes both
direct import lines through the verified literal template import parameter;
the locked statement is not manually edited. Exclude/remove all six overlays
after terminal check and commit. Searches for critical κ4 partition/unit
source maxima and positive complementary parts/unit history returned none.

Admission ordering limitation: running100 was truncated and its full artifact
was fetched immediately after submission instead of before. It shows only
two R16 Python probes and the host observers, no compiler; starting100 empty.
No force/bypass. The defect was logged before the next substantive attempt.

This necessary reduction does not supply a lower witness after any flip.
All-unit source histories alone do not imply positivity (closed counter20).
Full FLIP positive κ>=4 remains open; source-history length remains unbounded.
